if #"?" < #"$" then
  if #"$" < #"*" then
    (str #"?") ^ (str #"$") ^ (str #"*")
  else if #"?" < #"*" then
    (str #"?") ^ (str #"*") ^ (str #"$")
  else (str #"*") ^ (str #"?") ^ (str #"$")
else if #"?" < #"*" then
  (str #"$") ^ (str #"?") ^ (str #"*")
else if #"$" < #"*" then
  (str #"$") ^ (str #"*") ^ (str #"?")
else (str #"*") ^ (str #"$") ^ (str #"?")
