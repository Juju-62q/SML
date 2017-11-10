type student = {Name:string, University:string, School:string, Grade:int};

val st1 = {Name = "Ichiro", University = "Nagoya", School = "Engineering", Grade = 2};
val st2 = {Name = "Jiro", University = "Nagoya", School = "Science", Grade = 3};
val st3 = {Name = "Saburo", University = "Nagoya", School = "Engineering", Grade = 3};
val st4 = {Name = "Shiro", University = "Tokyo", School = "Engineering", Grade = 4};
val st5 = {Name = "Goro", University = "Tokyo", School = "Science", Grade = 2};
val st6 = {Name = "Rokuro", University = "Osaka", School = "Engineering", Grade = 1};
val st7 = {Name = "Shichiro", University = "Osaka", School = "Engineering", Grade = 3};

fun getSchool ({School, ...}:student) = School;

fun lower2 ({Grade, ...}:student) = Grade <= 2;

fun sameUnivGrade ({University = univx, Grade = gradex, ...}:student) ({University = univy, Grade = gradey, ...}:student) =
  if univx = univy andalso gradex = gradey then
    true
  else
    false;

