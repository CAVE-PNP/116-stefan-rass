theory SavingInterpretation
imports Main
begin

locale A begin
  lemma one_is_one: "1=1" ..
end

locale B
begin
  sublocale A done
end

context B begin
  thm one_is_one
end

end