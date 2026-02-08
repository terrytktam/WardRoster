include "globals.mzn";

% Constants
enum WEEKDAYS = {Mon, Tue, Wed, Thu, Fri, Sat, Sun};
enum DUTIES = {N, A, P, O};
enum GRADES = {APN, RN1, RN2, RN3};
enum RULES = {WardReqDuty,            % ward request duty constraint
              EntitledDayOff,         % 5-day working + public holiday O entitlement constraint
              WeekendOff,             % # of weekend O constraint
              NoWeekendPP,            % no weekend PP constraint (mandatory)
              MinWardStaffReq,        % daily ward requirement constraint (mandatory)
              NormalDutyStateDiagram, % normal AN constraint
              NormalNightFrequency,   % at most 1 N for CN days constraint (mandatory)
              Consecutive3Duties,     % no triple-A/P and NPA/NPP constraint (mandatory)
              NormalOffFrequency,     % at least 1 O for NW days constraint (mandatory)
              ReqAnnualLeaves,        % requested annual leaves (mandatory)
              LongNightDuties,        % requested long night duties (mandatory)
              PublicHolidayOff        % # of public holiday O constraint
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
array[int, int] of int: staff_req_duties;
array[int, int] of int: ward_req_duties;
array[int, int] of int: annual_leaves;
array[int, int] of int: long_nights;
array[RULES] of bool: active_constraints;
set of DAYS: public_holidays;

% Tuples
type GradeMins = tuple(GRADES, MINS);
type DutiesMaxs = tuple(DUTIES, MAXS);
type ReqDuties = tuple(STAFFS, DAYS, DUTIES);

% Derived Parameters
enum STAFFS = APN(1..nAPN) ++ RN1(1..nRN1) ++ RN2(1..nRN2) ++ RN3(1..nRN3);
int: nStaffs = card(STAFFS);
int: nWeekends = card(weekends);
int: nDuties = card(DUTIES);
int: nGrades = card(GRADES);
int: nPHs = card(public_holidays);
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
array[DAYS] of WEEKDAYS: DAY_WEEKDAYS = [weekday(i) | i in DAYS];
set of DAYS: weekends = array2set([i | i in DAYS where DAY_WEEKDAYS[i] in WEEKEND]);
int: nDays = card(DAYS);

% Derived Parameters (for ward max manpower generation)
array[SHIFTS, MINS] of int: MIN_WARD = array2d(SHIFTS, MINS, min_ward);
array[GRADES] of set of STAFFS: GRADE_STAFFS = [APN(1..nAPN), RN1(1..nRN1), RN2(1..nRN2), RN3(1..nRN3)];
array[int] of int: colmajor_1d = set2array(GRADES) ++ 
                                [nGradeStaffs[k] - sum([MIN_WARD[l, m] | l in SHIFTS, m in MINS where i != l /\ (k, m) in GRADE_MINS]) 
                                | i in SHIFTS, j in MAXS, k in GRADES where (i, j) in DUTIES_MAXS] ++
                                [nGradeStaffs[i] - sum(col(MIN_WARD, j)) | i in GRADES, j in MINS where (i, j) in GRADE_MINS];
array[int] of int: transpose = [colmajor_1d[(i-1) * nGrades + j] | j in 1..nGrades, i in 1..card(MAXS)];
array[GRADES, MAXS] of int: GRADE_MAXS = array2d(GRADES, MAXS, transpose);

% Derived Parameters (for requested duties)
array[int] of ReqDuties: STAFF_REQ_DUTIES = req_duties(staff_req_duties);
array[int] of ReqDuties: WARD_REQ_DUTIES = req_duties(ward_req_duties);
set of STAFFS: special_staffs = array2set([i | i in STAFFS where has_annual_leave(i) \/ card(long_night_rows(i)) > 0]);
array[STAFFS, DAYS] of bool: is_annual_leave = array2d(STAFFS, DAYS, [exists(row in 1..length(col(annual_leaves,1))) (
                                                                      i == annual_leaves[row,1] /\ 
                                                                      j >= annual_leaves[row,2] /\ 
                                                                      j < annual_leaves[row,2] + annual_leaves[row,3]
                                                                      ) | i in STAFFS, j in DAYS]);

% Function to check if staff has annual leave on a specific day
function bool: has_annual_leave(STAFFS: s) =
    exists(row in 1..length(col(annual_leaves,1))) (
        s == annual_leaves[row,1]
    );
                                                                                                                                                                                                             
% Function to return the matching long night duty row of the input day
function int: long_night_row(STAFFS: s, DAYS: d) =
    let {
        set of int: matching_rows = {row | row in long_night_rows(s) where
                                      d >= long_nights[row,2] /\
                                      d < long_nights[row,2]+14}
    } in if card(matching_rows) > 0 then min(matching_rows) else 0 endif;

% Function to return all matching rows of long night duties 
function set of int: long_night_rows(STAFFS: s) =
    {row | row in 1..length(long_nights) where s == long_nights[row,1]};

% Function to get mask value for specific staff/day (P/O/<> pattern)
function opt DUTIES: get_special_mask(STAFFS: s, DAYS: d) =
    let {
        int: row = long_night_row(s,d)
    } in
    if row > 0 then
        if d == long_nights[row,2] then 
            if occurs(long_night_duties[s, enum_prev(d)]) then O else P endif  % First day
        else O endif    % Next 13 days after start
    else <> endif;      % All other days

% Create the mask array
array[STAFFS, DAYS] of opt DUTIES: special_mask = 
    array2d(STAFFS, DAYS, [get_special_mask(s,d) | s in STAFFS, d in DAYS]);

% Function to apply mask
function array[DAYS] of var DUTIES: apply_special_mask(STAFFS: s, array[DAYS] of var DUTIES: staff_roster) =
    array1d(DAYS, [if occurs(special_mask[s,d]) then deopt(special_mask[s,d]) else staff_roster[d] endif
                  | d in DAYS ]);

% Decision Variables
array[STAFFS, DAYS] of var DUTIES: roster;
array[DAYS, DUTIES] of var set of STAFFS: ward;
array[STAFFS, DUTIES] of var int: staff_duty_counts;

% Channel constraints for roster/ward
constraint forall(i in DAYS) (
    partition_set(row(ward,i), STAFFS)
);
constraint forall(i in DAYS) (
    int_set_channel(col(roster,i), row(ward,i))
);
constraint forall(i in STAFFS) (
    global_cardinality(row(roster,i), DUTIES, row(staff_duty_counts,i))
);

% Rule feature toggle constraints
constraint active_constraints[WardReqDuty] -> rules1();
constraint active_constraints[EntitledDayOff] -> rules2();
constraint active_constraints[WeekendOff] -> rules3();
constraint active_constraints[NoWeekendPP] -> rules4();
constraint active_constraints[MinWardStaffReq] -> rules5();
constraint active_constraints[NormalDutyStateDiagram] -> rules6();
constraint active_constraints[NormalNightFrequency] -> rules7();
constraint active_constraints[Consecutive3Duties] -> rules8();
constraint active_constraints[NormalOffFrequency] -> rules9();
constraint active_constraints[ReqAnnualLeaves] -> rules10();
constraint active_constraints[LongNightDuties] -> rules11();
constraint active_constraints[PublicHolidayOff] -> rules12();

% Rule 1: constraint of matching roster with WARD_REQ_DUTIES
predicate rules1 = forall(i in STAFFS, j in DAYS, k in DUTIES where has_element((i,j,k), WARD_REQ_DUTIES)) (
    roster[i,j] == k
);

% Rule 2: constraint of # of Os (5-day working + public holidays) for every nurse in a month
int: min_weekend_O = round(card(DAYS) div 15);
int: min_O_count = min_weekend_O + nPHs;
int: max_O_count = nWeekends + nPHs;
function array[DAYS] of var DUTIES: staff_masked_roster(STAFFS: i, array[DAYS] of var DUTIES: staff_roster) =
    array1d(DAYS, [if is_annual_leave[i, j] then N else staff_roster[j] endif | j in DAYS]);
predicate rules2 = (forall(i in STAFFS) (
    let {
        array[DAYS] of var DUTIES: masked = staff_masked_roster(i, row(roster,i))
    } in global_cardinality(masked, OFF, [min_O_count], [max_O_count])
));

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
            array[SHIFTS] of int: d = [col(MIN_WARD,j)[k] | k in SHIFTS],
            array[SHIFTS] of int: e = [row(GRADE_MAXS,i)[k] | k in SHIFT_MAXS]
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
predicate rules6 = (forall(i in STAFFS) (
    let {
        array[DAYS] of var DUTIES: masked = apply_special_mask(i, row(roster,i))
    } in regular(masked, Q1, nDuties, t1, q0, STATE1)
));

% Rule 7: constraint of at most one N in consecutive CN days (w/o long night)
int: Q2 = CN;
set of int: STATE2 = 1..Q2;
array[STATE2, DUTIES] of int: t2 = array2d(STATE2, DUTIES, [2,q0,q0,q0]++
                                                           [if j == N then 0 else i endif | i in 3..CN, j in DUTIES] ++
                                                           [0,q0,q0,q0]);
predicate rules7 = (forall(i in STAFFS) (
    let {
        array[DAYS] of var DUTIES: masked = apply_special_mask(i, row(roster,i))
    } in regular(masked, Q2, nDuties, t2, q0, STATE2)
));

% Rule 8: constraint of no consecutive 3A/3P and NPA/NPP sequence for every nurse in a row
int: Q3 = 7;
set of int: STATE3 = 1..Q3;
array[STATE3, DUTIES] of int: t3 = 
  [| 4, 2, 3, 1      % state 1
   | 4, 5, 3, 1      % state 2
   | 4, 2, 6, 1      % state 3 
   | 4, 2, 7, 1      % state 4
   | 4, 0, 3, 1      % state 5 (cannot A again)
   | 4, 2, 0, 1      % state 6 (cannot P again)
   | 4, 0, 0, 1 |];  % state 7 (cannot A/P again)
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

% Rule 10: constraint of staff entitled annual leaves
predicate rules10 = forall(i in STAFFS, j in DAYS) (
    is_annual_leave[i,j] -> roster[i,j] == O
);

% Rule 11: constraint of requested long night duties   
array[STAFFS, DAYS] of opt DUTIES: long_night_duties = 
    array2d(STAFFS, DAYS, [get_long_night_duty(i,j) | i in STAFFS, j in DAYS]);
function opt DUTIES: get_long_night_duty(STAFFS: s, DAYS: d) =
    let {
        int: row = long_night_row(s, d),
        int: day_offset = d - if row > 0 then long_nights[row,2] else 0 endif + 1
    } in if row == 0 then <> else to_enum(DUTIES, long_nights[row, 2 + day_offset]) endif;
predicate rules11 = forall(i in STAFFS, j in DAYS) (
    occurs(long_night_duties[i,j]) -> roster[i,j] == long_night_duties[i,j]
);

% Rule 12: constraint of >=1 public holiday Os for every nurse in a month if # of public holidays >= 3
int: min_ph_O = round((nPHs-1)/3);
predicate rules12 = (forall(i in STAFFS) (
    global_cardinality([roster[i,j] | j in public_holidays], OFF, [min_ph_O], [nPHs])
));

% Objective functions
var int: score1 = sum([roster[i,j] == P /\ roster[i,enum_next(j)] == A | i in STAFFS, j in DAYS where enum_next(j) in DAYS]);
var int: score2 = sum([roster[i,j] == N /\ roster[i,enum_next(j)] == P | i in STAFFS, j in DAYS where enum_next(j) in DAYS]);
var int: score3 = sum([roster[i,j] == P /\ roster[i,enum_next(j)] == O /\ roster[i,enum_next(enum_next(j))] == A 
                  | i in STAFFS, j in DAYS where enum_next(j) in DAYS /\ enum_next(enum_next(j)) in DAYS]);
var int: score4 = length(STAFF_REQ_DUTIES) - sum([roster[i,j] == k | i in STAFFS, j in DAYS, k in DUTIES where (i,j,k) in STAFF_REQ_DUTIES]);
var int: score5 = sum([max_diff_shifts([col(staff_duty_counts,i)[j] | j in STAFFS where not (j in special_staffs)]) | i in SHIFTS]);

solve :: int_search(roster, first_fail, indomain_min) maximize score1 - score2 * 10 - score3 * 50 - score4 * 1000 - score5 * 100;

% Helper function
function WEEKDAYS: weekday(DAYS: day) = 
    let {
        int: temp = (enum2int(day) - enum2int(C(1)) + enum2int(MONTH_START)) mod 7
    } in
    if (temp == 0) then Sun else to_enum(WEEKDAYS, temp) endif;

function array[int] of ReqDuties: req_duties(array[int, int] of int: input) = 
    [(to_enum(STAFFS, input[i,1]), 
      to_enum(DAYS, input[i,2]), 
      to_enum(DUTIES, input[i,3])) | i in 1..length(col(input,1))];

function string: format_shift(set of STAFFS: staffs) =
    join("",[show(card(staffs intersect GRADE_STAFFS[grade])) | grade in GRADES]);

function var int: max_diff_shifts(array[int] of var int: input) = max(input) - min(input); 

% Verify data input and derived parameters
output ["Whole calendar: "] ++ [show(i) ++ " " | i in DAYS] ++ ["\n"];
output ["Whole calendar: "] ++ [show(DAY_WEEKDAYS)] ++ ["\n"];
output ["Available weekends: "] ++ [show(weekends)] ++ ["\n"];
output ["Available APN/RN1/RN2/RN3s: "] ++ [show(card(GRADE_STAFFS[i])) ++ " " | i in GRADES] ++ ["\n"];
output ["Index sets of MIN_WARD: "] ++ [show(index_set_1of2(MIN_WARD)) ++ "\t" ++ show(index_set_2of2(MIN_WARD))] ++ ["\n"];
output ["Min staffs/APNs/RN1s/RN2s/RN3s in N/A/P: \n"] ++ [show2d(MIN_WARD)] ++ ["\n"];
output ["Index sets of GRADE_MAXS: "] ++ [show(index_set_1of2(GRADE_MAXS)) ++ "\t" ++ show(index_set_2of2(GRADE_MAXS))] ++ ["\n"];
output ["Max Ns/Ps/As/Offs in APN/RN1/RN2/RN3: \n"] ++ [show2d(GRADE_MAXS)] ++ ["\n"];
output ["STAFF_REQ_DUTIES: \n"] ++ [show(STAFF_REQ_DUTIES)] ++ ["\n"];
output ["WARD_REQ_DUTIES: \n"] ++ [show(WARD_REQ_DUTIES)] ++ ["\n"];
output ["special_mask of APN(1): \n"] ++ [show(row(special_mask,APN(1)))] ++ ["\n"];
output ["special_mask of RN1(2): \n"] ++ [show(row(special_mask,RN1(2)))] ++ ["\n"];
output ["special_mask of RN3(1): \n"] ++ [show(row(special_mask,RN3(1)))] ++ ["\n"];

% Result printing
output["\t" ++ join(" ",[if i in {C(1),X(1)} then "1" elseif i == C(mthStartAt) then show(mthStartAt) elseif i == X(nNextMthDays) then show(nNextMthDays) else " " endif | i in DAYS]) ++ "\n"];
output["\t" ++ join(" ",[if i in weekends then "S" else " " endif | i in DAYS]) ++ "\t" ++ join("\t",[show(i) | i in DUTIES]) ++ "\n"];
output[show(i) ++ "\t" ++ join(" ",[show(roster[i,j]) | j in DAYS]) ++ "\t" ++ join("\t",[show(staff_duty_counts[i,j]) | j in DUTIES]) ++ "\n" | i in STAFFS];
output["# of PAs= " ++ show(score1) ++ "\t# of NPs= " ++ show(score2) ++ "\t# of POAs= " ++ show(score3) ++ "\t# of re-duty non-fulfillments= " ++ show(score4) ++ "\n"];
output["Total # of max shift diffs= " ++ show(score5) ++ "\n"];
