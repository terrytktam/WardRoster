include "globals.mzn";

% Constants
enum WEEKDAYS = {Mon, Tue, Wed, Thu, Fri, Sat, Sun};
enum DUTIES = {N, A, P, O};
enum GRADES = {APN, RN1, RN2, RN3};
enum RULES = {MandatoryDuty,          % request duty constraint
              FiveDayWorkingOff,      % 5-day working O entitlement constraint
              WeekendOff,             % # of weekend O constraint
              NoWeekendPP,            % no weekend PP constraint (mandatory)
              MinWardStaffReq,        % daily ward requirement constraint (mandatory)
              NormalDutyStateDiagram, % normal AN constraint
              NormalNightFrequency,   % at most 1 N for CN days constraint (mandatory)
              Consecutive3Duties,     % no triple-A/P and POA constraint (mandatory)
              NormalOffFrequency,     % at least 1 O for NW days constraint (mandatory)
              };
enum MINS = { shift, total, apn, rn1, rn2, rn3 };
enum MAXS = { grade, night, am, pm, off };

% Parameters
int: CCYYMM;      % current month
int: nMthDays;    % number of days in the month
int: MW;          % maximum number of consecutive shifts
int: CN;          % number of consecutive days with at most 1 N
int: nAPN;        % number of APNs
int: nRN1;        % number of RN1s
int: nRN2;        % number of RN2s
int: nRN3;        % number of RN3s
WEEKDAYS: MONTH_START;
array[int, int] of int: min_ward;
array[RULES] of bool: active_constraints;

% Tuples
type GradeMins = tuple(GRADES, MINS);
type DutiesMaxs = tuple(DUTIES, MAXS);

% Derived Parameters
enum STAFFS = APN(1..nAPN) ++ RN1(1..nRN1) ++ RN2(1..nRN2) ++ RN3(1..nRN3);
int: nStaffs = card(STAFFS);
int: nWeekends = card(weekends);
int: nDuties = card(DUTIES);
int: nGrades = card(GRADES);
array[GRADES] of int: nGradeStaffs = [nAPN, nRN1, nRN2, nRN3];
array[GRADES] of GradeMins: GRADE_MINS = [(APN, apn), (RN1, rn1), (RN2, rn2), (RN3, rn3)];
array[DUTIES] of DutiesMaxs: DUTIES_MAXS = [(N, night), (A, am), (P, pm), (O, off)];
set of MAXS: SHIFT_MAXS = {night, am, pm};
set of WEEKDAYS: WEEKEND = {Sat, Sun};
set of DUTIES: SHIFTS = {N, A, P};
set of DUTIES: OFF = {O};

% Derived Parameters (for cross-month calendar generation)
int: mthStartAt = (8-enum2int(MONTH_START)) mod 7 + 1;
int: nPrevMthDays = max([MW,CN]) - mthStartAt + 1;
int: nNextMthDays = (enum2int(Sun)-enum2int(MONTH_START)+35+1-nMthDays) mod 7 + 1;
enum DAYS = V(1..nPrevMthDays) ++ C(1..nMthDays) ++ X(1..nNextMthDays);
array[DAYS] of WEEKDAYS: DAY_WEEKDAYS = array1d(DAYS,[weekday(i) | i in DAYS]);
set of DAYS: weekends = array2set([i | i in DAYS where DAY_WEEKDAYS[i] in WEEKEND]);
int: nDays = card(DAYS);

% Derived Parameters (for ward max manpower generation)
array[SHIFTS, MINS] of int: MIN_WARD = array2d(SHIFTS, MINS, min_ward);
array[GRADES] of set of STAFFS: GRADE_STAFFS = [array2set([APN(i) | i in 1..nAPN]),
                                               array2set([RN1(i) | i in 1..nRN1]),
                                               array2set([RN2(i) | i in 1..nRN2]),
                                               array2set([RN3(i) | i in 1..nRN3])];
array[int] of int: colmajor_1d = set2array(GRADES) ++ 
                                [nGradeStaffs[i] - sum([MIN_WARD[l, m] | l in SHIFTS, m in MINS where j != l /\ (i, m) in GRADE_MINS]) 
                                | i in GRADES, j in SHIFTS, k in MAXS where (j, k) in DUTIES_MAXS] ++
                                [nGradeStaffs[i] - sum(col(MIN_WARD, j)) | i in GRADES, j in MINS where (i, j) in GRADE_MINS];
array[int] of int: transpose = [colmajor_1d[(i-1) * nGrades + j] | j in 1..nGrades, i in 1..card(MAXS)];
array[GRADES, MAXS] of int: GRADE_MAXS = array2d(GRADES, MAXS, transpose);

% Decision Variables
array[STAFFS, DAYS] of var DUTIES: roster;
array[DAYS, DUTIES] of var set of STAFFS: ward;

% Channel constraints for roster/ward
constraint forall(i in DAYS) (
    partition_set(row(ward,i), STAFFS)
);
constraint forall(i in DAYS) (
    int_set_channel(col(roster,i), row(ward,i))
);

% Rule feature toggle constraints
constraint active_constraints[FiveDayWorkingOff] -> rules2();
constraint active_constraints[WeekendOff] -> rules3();
constraint active_constraints[NoWeekendPP] -> rules4();
constraint active_constraints[MinWardStaffReq] -> rules5();
constraint active_constraints[NormalDutyStateDiagram] -> rules6();
constraint active_constraints[NormalNightFrequency] -> rules7();
constraint active_constraints[Consecutive3Duties] -> rules8();
constraint active_constraints[NormalOffFrequency] -> rules9();

% Rule 2: constraint of # of 5-day working O for every nurse in a month
int: min_weekend_O = round(card(DAYS) div 15);
predicate rules2 = (forall(i in STAFFS) (
    global_cardinality(row(roster,i), OFF, [min_weekend_O], [nWeekends])));    % how to deal with public holidays/extra O

% Rule 3: constraint of >=2 weekend Os for every nurse in a month
predicate rules3 = (forall(i in STAFFS) (
    global_cardinality([roster[i,j] | j in weekends], OFF, [min_weekend_O], [nWeekends])
));

% Rule 4: constraint of no both-P for the same weekend
predicate rules4 = (forall(i in STAFFS) (
    forall(j in weekends where enum_next(j) in weekends) (
        roster[i,j] == P -> roster[i,enum_next(j)] != P
    )
));

% Rule 5: constraint of min # of nurses of all types in every N/A/P duties
predicate ward_req(array[STAFFS] of var DUTIES: a) = (
    global_cardinality(a, SHIFTS, col(MIN_WARD,total), [nStaffs | _ in SHIFTS]) /\  % upper bound can be more tightened
    forall(i in GRADES, j in MINS where (i, j) in GRADE_MINS) (
        let {
            array[SHIFTS] of int: d = array1d(SHIFTS, [col(MIN_WARD,j)[k] | k in SHIFTS]),
            array[SHIFTS] of int: e = array1d(SHIFTS, [row(GRADE_MAXS,i)[k] | k in SHIFT_MAXS])
        } in 
        global_cardinality(a[GRADE_STAFFS[i]], SHIFTS, d, e))
);
predicate rules5 = (forall(i in DAYS) (
    ward_req(col(roster,i))
));

% Rule 6: constraint of normal N requirement (w/o long night)
int: Q1 = 7;
int: q0 = 1;
set of int: STATE1 = 1..Q1;
array[STATE1, DUTIES] of int: t1 = 
  [| 5, 3, 4, 2      % state 1 (allow N at the 1st day)
   | 0, 3, 4, 2      % state 2
   | 5, 2, 2, 2      % state 3 (only A can enter this stage)
   | 0, 2, 2, 2      % state 4 (cannot have N)
   | 0, 0, 6, 2      % state 5 (if not O, can only P)
   | 0, 7, 7, 2      % state 6 (if not O, can only have A/P)
   | 0, 0, 0, 2 |];  % state 7 (can only have O)
predicate rules6 = (forall(i in STAFFS) (          % how to exclude long night?
    regular(row(roster,i), Q1, nDuties, t1, q0, STATE1)
));

% Rule 7: constraint of at most one N in consecutive CN days (w/o long night)
int: Q2 = CN;
set of int: STATE2 = 1..Q2;
array[STATE2, DUTIES] of int: t2 = array2d(STATE2, DUTIES, [2,q0,q0,q0]++
                                                           [if j == N then 0 else i endif | i in 3..CN, j in DUTIES] ++
                                                           [0,q0,q0,q0]);
predicate rules7 = (forall(i in STAFFS) (          % how to exclude long night?
    regular(row(roster,i), Q2, nDuties, t2, q0, STATE2)
));

% Rule 8: constraint of no consecutive 3A/3P and POA sequence for every nurse in a row
int: Q3 = 6;
set of int: STATE3 = 1..Q3;
array[STATE3, DUTIES] of int: t3 = 
  [| 1, 2, 3, 1      % state 1
   | 1, 4, 3, 1      % state 2
   | 1, 2, 5, 6      % state 3 
   | 1, 0, 3, 1      % state 4 (cannot A again)
   | 1, 2, 0, 1      % state 5 (cannot P again)
   | 1, 0, 3, 1 |];  % state 6 (cannot A)
predicate rules8 = (forall(i in STAFFS) (
    regular(row(roster,i), Q3, nDuties, t3, q0, STATE3)
));

% Rule 9: constraint of at least 1 O for every nurse in every consecutive MW days
int: Q4 = MW;
set of int: STATE4 = 1..Q4;
array[STATE4,DUTIES] of int: t4 = array2d(STATE4, DUTIES, [if j == O then q0 else i endif | i in 2..MW, j in DUTIES] ++
                                                          [0,0,0,q0]);
predicate rules9 = (forall(i in STAFFS) (
    regular(row(roster,i), Q4, nDuties, t4, q0, STATE4)
));

% Objective functions
var int: score1 = sum([roster[i,j] == P /\ roster[i,enum_next(j)] == A | i in STAFFS, j in DAYS where enum_next(j) in DAYS]);

solve :: int_search(roster, first_fail, indomain_min) maximize score1;

% Helper function
function WEEKDAYS: weekday(DAYS: day) = 
    let {
        int: temp = (enum2int(day) - enum2int(C(1)) + enum2int(MONTH_START)) mod 7
    } in
    if (temp == 0) then Sun else to_enum(WEEKDAYS, temp) endif;

% Verify data input and derived parameters
output ["Whole calendar: "] ++ [show(i) ++ " " | i in DAYS] ++ ["\n"];
output ["Whole calendar: "] ++ [show(DAY_WEEKDAYS)] ++ ["\n"];
output ["Available weekends: "] ++ [show(weekends)] ++ ["\n"];
output ["Duty generation period with last N: ("] ++ [show(C(mthStartAt)) ++ "," ++ show(X(nNextMthDays))] ++ [")\n"];
output ["Available APNs: "] ++ [show(i) ++ "\t" | i in GRADE_STAFFS[APN]] ++ ["\n"];
output ["Available RN1s: "] ++ [show(RN1(i)) ++ "\t" | i in 1..nRN1] ++ ["\n"];
output ["Available RN2s: "] ++ [show(i) ++ "\t" | i in GRADE_STAFFS[RN2]] ++ ["\n"];
output ["Available RN3s: "] ++ [show(i) ++ "\t" | i in GRADE_STAFFS[RN3]] ++ ["\n"];
output ["Index sets of MIN_WARD: "] ++ [show(index_set_1of2(MIN_WARD)) ++ "\t" ++ show(index_set_2of2(MIN_WARD))] ++ ["\n"];
output ["Min staffs/APNs/RN1s/RN2s/RN3s in N/A/P: \n"] ++ [show2d(MIN_WARD)] ++ ["\n"];
output ["colmajor_1d: "] ++ [show(colmajor_1d)] ++ ["\n"];
output ["transpose  : "] ++ [show(transpose)] ++ ["\n"];
output ["Index sets of GRADE_MAXS: "] ++ [show(index_set_1of2(GRADE_MAXS)) ++ "\t" ++ show(index_set_2of2(GRADE_MAXS))] ++ ["\n"];
output ["Max Offs/Ns/Ps/As in APN/RN1/RN2/RN3: \n"] ++ [show2d(GRADE_MAXS)] ++ ["\n"];

% Result printing
output[if i == 1 then "\t" else "" endif ++ if i in weekends then "S" else " " endif ++ " " ++ if i == X(nNextMthDays) then "\n" else "" endif | i in DAYS];
output[if j == 1 then show(i) ++ "\t" else "" endif ++ show(roster[i,j]) ++ " " ++ if j == X(nNextMthDays) then "\n" else "" endif | i in STAFFS, j in DAYS];
output["# of PAs= " ++ show(score1) ++ "\n"];
