# Approximately, what’s the probability that in a room filled with 23 people at least one pair of people have the same birthday?
birthdays = iid(Int, i->discreteuniform(1,366),30)
function same_birthday(birthdays)
  bday = false
  for i = 1:length(birthdays), j = 1:length(birthdays)
    if i != j
      bday |= (birthdays[i] == birthdays[j])
    end
  end
  bday
end

rand(same_birthday(birthdays))

prob_sampled(same_birthday(birthdays))