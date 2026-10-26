import NewObligations
namespace CollatzResearch

theorem targeted_trace_0 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3] 1015021595 732466883 := by
  exact ⟨1522532393, by decide, ⟨1141899295, by decide, ⟨1712848943, by decide, ⟨2569273415, by decide, ⟨3853910123, by decide, ⟨5780865185, by decide, ⟨4335648889, by decide, ⟨3251736667, by decide, ⟨4877605001, by decide, ⟨3658203751, by decide, ⟨5487305627, by decide, ⟨8230958441, by decide, ⟨6173218831, by decide, ⟨9259828247, by decide, ⟨13889742371, by decide, ⟨20834613557, by decide, ⟨1953245021, by decide, ⟨732466883, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_0 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3] (1015021595 + q * 2 ^ 30) endpoint ∧ endpoint < 1015021595 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3] targeted_trace_0 (by decide) (by decide) (by decide) q
#print axioms targeted_class_0

theorem targeted_trace_1 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4] 478150683 172523197 := by
  exact ⟨717226025, by decide, ⟨537919519, by decide, ⟨806879279, by decide, ⟨1210318919, by decide, ⟨1815478379, by decide, ⟨2723217569, by decide, ⟨2042413177, by decide, ⟨1531809883, by decide, ⟨2297714825, by decide, ⟨1723286119, by decide, ⟨2584929179, by decide, ⟨3877393769, by decide, ⟨2908045327, by decide, ⟨4362067991, by decide, ⟨6543101987, by decide, ⟨9814652981, by decide, ⟨920123717, by decide, ⟨172523197, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_1 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4] (478150683 + q * 2 ^ 31) endpoint ∧ endpoint < 478150683 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4] targeted_trace_1 (by decide) (by decide) (by decide) q
#print axioms targeted_class_1

theorem targeted_trace_2 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4] 287309851 207330517 := by
  exact ⟨430964777, by decide, ⟨323223583, by decide, ⟨484835375, by decide, ⟨727253063, by decide, ⟨1090879595, by decide, ⟨1636319393, by decide, ⟨1227239545, by decide, ⟨920429659, by decide, ⟨1380644489, by decide, ⟨1035483367, by decide, ⟨1553225051, by decide, ⟨2329837577, by decide, ⟨1747378183, by decide, ⟨2621067275, by decide, ⟨3931600913, by decide, ⟨2948700685, by decide, ⟨1105762757, by decide, ⟨207330517, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_2 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4] (287309851 + q * 2 ^ 30) endpoint ∧ endpoint < 287309851 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4] targeted_trace_2 (by decide) (by decide) (by decide) q
#print axioms targeted_class_2

theorem targeted_trace_3 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3] 522190875 376826981 := by
  exact ⟨783286313, by decide, ⟨587464735, by decide, ⟨881197103, by decide, ⟨1321795655, by decide, ⟨1982693483, by decide, ⟨2974040225, by decide, ⟨2230530169, by decide, ⟨1672897627, by decide, ⟨2509346441, by decide, ⟨1882009831, by decide, ⟨2823014747, by decide, ⟨4234522121, by decide, ⟨3175891591, by decide, ⟨4763837387, by decide, ⟨7145756081, by decide, ⟨5359317061, by decide, ⟨1004871949, by decide, ⟨376826981, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_3 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3] (522190875 + q * 2 ^ 30) endpoint ∧ endpoint < 522190875 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3] targeted_trace_3 (by decide) (by decide) (by decide) q
#print axioms targeted_class_3

theorem targeted_trace_4 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5] 824180763 297375503 := by
  exact ⟨1236271145, by decide, ⟨927203359, by decide, ⟨1390805039, by decide, ⟨2086207559, by decide, ⟨3129311339, by decide, ⟨4693967009, by decide, ⟨3520475257, by decide, ⟨2640356443, by decide, ⟨3960534665, by decide, ⟨2970400999, by decide, ⟨4455601499, by decide, ⟨6683402249, by decide, ⟨5012551687, by decide, ⟨7518827531, by decide, ⟨11278241297, by decide, ⟨8458680973, by decide, ⟨3172005365, by decide, ⟨297375503, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_4 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5] (824180763 + q * 2 ^ 31) endpoint ∧ endpoint < 824180763 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5] targeted_trace_4 (by decide) (by decide) (by decide) q
#print axioms targeted_class_4

theorem targeted_trace_5 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4] 375390235 270891691 := by
  exact ⟨563085353, by decide, ⟨422314015, by decide, ⟨633471023, by decide, ⟨950206535, by decide, ⟨1425309803, by decide, ⟨2137964705, by decide, ⟨1603473529, by decide, ⟨1202605147, by decide, ⟨1803907721, by decide, ⟨1352930791, by decide, ⟨2029396187, by decide, ⟨3044094281, by decide, ⟨2283070711, by decide, ⟨3424606067, by decide, ⟨5136909101, by decide, ⟨1926340913, by decide, ⟨1444755685, by decide, ⟨270891691, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_5 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4] (375390235 + q * 2 ^ 30) endpoint ∧ endpoint < 375390235 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4] targeted_trace_5 (by decide) (by decide) (by decide) q
#print axioms targeted_class_5

theorem targeted_trace_6 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5] 1986002971 716576579 := by
  exact ⟨2979004457, by decide, ⟨2234253343, by decide, ⟨3351380015, by decide, ⟨5027070023, by decide, ⟨7540605035, by decide, ⟨11310907553, by decide, ⟨8483180665, by decide, ⟨6362385499, by decide, ⟨9543578249, by decide, ⟨7157683687, by decide, ⟨10736525531, by decide, ⟨16104788297, by decide, ⟨12078591223, by decide, ⟨18117886835, by decide, ⟨27176830253, by decide, ⟨10191311345, by decide, ⟨7643483509, by decide, ⟨716576579, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_6 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5] (1986002971 + q * 2 ^ 31) endpoint ∧ endpoint < 1986002971 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5] targeted_trace_6 (by decide) (by decide) (by decide) q
#print axioms targeted_class_6

theorem targeted_trace_7 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 6] 31457307 20178169 := by
  exact ⟨47185961, by decide, ⟨35389471, by decide, ⟨53084207, by decide, ⟨79626311, by decide, ⟨119439467, by decide, ⟨179159201, by decide, ⟨134369401, by decide, ⟨100777051, by decide, ⟨151165577, by decide, ⟨113374183, by decide, ⟨170061275, by decide, ⟨255091913, by decide, ⟨191318935, by decide, ⟨286978403, by decide, ⟨430467605, by decide, ⟨20178169, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_7 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 6] (31457307 + q * 2 ^ 27) endpoint ∧ endpoint < 31457307 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 6] targeted_trace_7 (by decide) (by decide) (by decide) q
#print axioms targeted_class_7

theorem targeted_trace_8 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3] 2430599195 1315489313 := by
  exact ⟨3645898793, by decide, ⟨2734424095, by decide, ⟨4101636143, by decide, ⟨6152454215, by decide, ⟨9228681323, by decide, ⟨13843021985, by decide, ⟨10382266489, by decide, ⟨7786699867, by decide, ⟨11680049801, by decide, ⟨8760037351, by decide, ⟨13140056027, by decide, ⟨19710084041, by decide, ⟨14782563031, by decide, ⟨22173844547, by decide, ⟨33260766821, by decide, ⟨6236393779, by decide, ⟨9354590669, by decide, ⟨3507971501, by decide, ⟨1315489313, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_8 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3] (2430599195 + q * 2 ^ 32) endpoint ∧ endpoint < 2430599195 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3] targeted_trace_8 (by decide) (by decide) (by decide) q
#print axioms targeted_class_8

theorem targeted_trace_9 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4] 685768731 371151871 := by
  exact ⟨1028653097, by decide, ⟨771489823, by decide, ⟨1157234735, by decide, ⟨1735852103, by decide, ⟨2603778155, by decide, ⟨3905667233, by decide, ⟨2929250425, by decide, ⟨2196937819, by decide, ⟨3295406729, by decide, ⟨2471555047, by decide, ⟨3707332571, by decide, ⟨5560998857, by decide, ⟨4170749143, by decide, ⟨6256123715, by decide, ⟨9384185573, by decide, ⟨1759534795, by decide, ⟨2639302193, by decide, ⟨1979476645, by decide, ⟨371151871, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_9 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4] (685768731 + q * 2 ^ 32) endpoint ∧ endpoint < 685768731 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4] targeted_trace_9 (by decide) (by decide) (by decide) q
#print axioms targeted_class_9

theorem targeted_trace_10 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5] 1960837147 1061244617 := by
  exact ⟨2941255721, by decide, ⟨2205941791, by decide, ⟨3308912687, by decide, ⟨4963369031, by decide, ⟨7445053547, by decide, ⟨11167580321, by decide, ⟨8375685241, by decide, ⟨6281763931, by decide, ⟨9422645897, by decide, ⟨7066984423, by decide, ⟨10600476635, by decide, ⟨15900714953, by decide, ⟨11925536215, by decide, ⟨17888304323, by decide, ⟨26832456485, by decide, ⟨5031085591, by decide, ⟨7546628387, by decide, ⟨11319942581, by decide, ⟨1061244617, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_10 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5] (1960837147 + q * 2 ^ 32) endpoint ∧ endpoint < 1960837147 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5] targeted_trace_10 (by decide) (by decide) (by decide) q
#print axioms targeted_class_10

theorem targeted_trace_11 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4] 920649755 498274219 := by
  exact ⟨1380974633, by decide, ⟨1035730975, by decide, ⟨1553596463, by decide, ⟨2330394695, by decide, ⟨3495592043, by decide, ⟨5243388065, by decide, ⟨3932541049, by decide, ⟨2949405787, by decide, ⟨4424108681, by decide, ⟨3318081511, by decide, ⟨4977122267, by decide, ⟨7465683401, by decide, ⟨5599262551, by decide, ⟨8398893827, by decide, ⟨12598340741, by decide, ⟨2362188889, by decide, ⟨1771641667, by decide, ⟨2657462501, by decide, ⟨498274219, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_11 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4] (920649755 + q * 2 ^ 32) endpoint ∧ endpoint < 920649755 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4] targeted_trace_11 (by decide) (by decide) (by decide) q
#print axioms targeted_class_11

theorem targeted_trace_12 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3] 2665480219 1442611661 := by
  exact ⟨3998220329, by decide, ⟨2998665247, by decide, ⟨4497997871, by decide, ⟨6746996807, by decide, ⟨10120495211, by decide, ⟨15180742817, by decide, ⟨11385557113, by decide, ⟨8539167835, by decide, ⟨12808751753, by decide, ⟨9606563815, by decide, ⟨14409845723, by decide, ⟨21614768585, by decide, ⟨16211076439, by decide, ⟨24316614659, by decide, ⟨36474921989, by decide, ⟨6839047873, by decide, ⟨5129285905, by decide, ⟨3846964429, by decide, ⟨1442611661, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_12 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3] (2665480219 + q * 2 ^ 32) endpoint ∧ endpoint < 2665480219 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3] targeted_trace_12 (by decide) (by decide) (by decide) q
#print axioms targeted_class_12

theorem targeted_trace_13 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5] 1041235995 751383899 := by
  exact ⟨1561853993, by decide, ⟨1171390495, by decide, ⟨1757085743, by decide, ⟨2635628615, by decide, ⟨3953442923, by decide, ⟨5930164385, by decide, ⟨4447623289, by decide, ⟨3335717467, by decide, ⟨5003576201, by decide, ⟨3752682151, by decide, ⟨5629023227, by decide, ⟨8443534841, by decide, ⟨6332651131, by decide, ⟨9498976697, by decide, ⟨7124232523, by decide, ⟨10686348785, by decide, ⟨8014761589, by decide, ⟨751383899, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_13 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5] (1041235995 + q * 2 ^ 30) endpoint ∧ endpoint < 1041235995 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5] targeted_trace_13 (by decide) (by decide) (by decide) q
#print axioms targeted_class_13

theorem targeted_trace_14 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3] 319815707 230787617 := by
  exact ⟨479723561, by decide, ⟨359792671, by decide, ⟨539689007, by decide, ⟨809533511, by decide, ⟨1214300267, by decide, ⟨1821450401, by decide, ⟨1366087801, by decide, ⟨1024565851, by decide, ⟨1536848777, by decide, ⟨1152636583, by decide, ⟨1728954875, by decide, ⟨2593432313, by decide, ⟨1945074235, by decide, ⟨2917611353, by decide, ⟨2188208515, by decide, ⟨3282312773, by decide, ⟨615433645, by decide, ⟨230787617, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_14 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3] (319815707 + q * 2 ^ 30) endpoint ∧ endpoint < 319815707 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3] targeted_trace_14 (by decide) (by decide) (by decide) q
#print axioms targeted_class_14

theorem targeted_trace_15 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6] 504365083 181981705 := by
  exact ⟨756547625, by decide, ⟨567410719, by decide, ⟨851116079, by decide, ⟨1276674119, by decide, ⟨1915011179, by decide, ⟨2872516769, by decide, ⟨2154387577, by decide, ⟨1615790683, by decide, ⟨2423686025, by decide, ⟨1817764519, by decide, ⟨2726646779, by decide, ⟨4089970169, by decide, ⟨3067477627, by decide, ⟨4601216441, by decide, ⟨3450912331, by decide, ⟨5176368497, by decide, ⟨3882276373, by decide, ⟨181981705, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_15 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6] (504365083 + q * 2 ^ 31) endpoint ∧ endpoint < 504365083 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6] targeted_trace_15 (by decide) (by decide) (by decide) q
#print axioms targeted_class_15

theorem targeted_trace_16 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6] 982515739 709009783 := by
  exact ⟨1473773609, by decide, ⟨1105330207, by decide, ⟨1657995311, by decide, ⟨2486992967, by decide, ⟨3730489451, by decide, ⟨5595734177, by decide, ⟨4196800633, by decide, ⟨3147600475, by decide, ⟨4721400713, by decide, ⟨3541050535, by decide, ⟨5311575803, by decide, ⟨7967363705, by decide, ⟨5975522779, by decide, ⟨8963284169, by decide, ⟨6722463127, by decide, ⟨10083694691, by decide, ⟨15125542037, by decide, ⟨709009783, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_16 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6] (982515739 + q * 2 ^ 30) endpoint ∧ endpoint < 982515739 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6] targeted_trace_16 (by decide) (by decide) (by decide) q
#print axioms targeted_class_16

theorem targeted_trace_17 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7] 445644827 160794647 := by
  exact ⟨668467241, by decide, ⟨501350431, by decide, ⟨752025647, by decide, ⟨1128038471, by decide, ⟨1692057707, by decide, ⟨2538086561, by decide, ⟨1903564921, by decide, ⟨1427673691, by decide, ⟨2141510537, by decide, ⟨1606132903, by decide, ⟨2409199355, by decide, ⟨3613799033, by decide, ⟨2710349275, by decide, ⟨4065523913, by decide, ⟨3049142935, by decide, ⟨4573714403, by decide, ⟨6860571605, by decide, ⟨160794647, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_17 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7] (445644827 + q * 2 ^ 31) endpoint ∧ endpoint < 445644827 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7] targeted_trace_17 (by decide) (by decide) (by decide) q
#print axioms targeted_class_17

theorem targeted_trace_18 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3] 407896091 294348791 := by
  exact ⟨611844137, by decide, ⟨458883103, by decide, ⟨688324655, by decide, ⟨1032486983, by decide, ⟨1548730475, by decide, ⟨2323095713, by decide, ⟨1742321785, by decide, ⟨1306741339, by decide, ⟨1960112009, by decide, ⟨1470084007, by decide, ⟨2205126011, by decide, ⟨3307689017, by decide, ⟨2480766763, by decide, ⟨3721150145, by decide, ⟨2790862609, by decide, ⟨2093146957, by decide, ⟨784930109, by decide, ⟨294348791, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_18 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3] (407896091 + q * 2 ^ 30) endpoint ∧ endpoint < 407896091 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3] targeted_trace_18 (by decide) (by decide) (by decide) q
#print axioms targeted_class_18

theorem targeted_trace_19 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4] 2018508827 728305129 := by
  exact ⟨3027763241, by decide, ⟨2270822431, by decide, ⟨3406233647, by decide, ⟨5109350471, by decide, ⟨7664025707, by decide, ⟨11496038561, by decide, ⟨8622028921, by decide, ⟨6466521691, by decide, ⟨9699782537, by decide, ⟨7274836903, by decide, ⟨10912255355, by decide, ⟨16368383033, by decide, ⟨12276287275, by decide, ⟨18414430913, by decide, ⟨13810823185, by decide, ⟨10358117389, by decide, ⟨3884294021, by decide, ⟨728305129, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_19 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4] (2018508827 + q * 2 ^ 31) endpoint ∧ endpoint < 2018508827 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4] targeted_trace_19 (by decide) (by decide) (by decide) q
#print axioms targeted_class_19

theorem targeted_trace_20 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 5] 97517595 62552285 := by
  exact ⟨146276393, by decide, ⟨109707295, by decide, ⟨164560943, by decide, ⟨246841415, by decide, ⟨370262123, by decide, ⟨555393185, by decide, ⟨416544889, by decide, ⟨312408667, by decide, ⟨468613001, by decide, ⟨351459751, by decide, ⟨527189627, by decide, ⟨790784441, by decide, ⟨593088331, by decide, ⟨889632497, by decide, ⟨667224373, by decide, ⟨62552285, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_20 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 5] (97517595 + q * 2 ^ 27) endpoint ∧ endpoint < 97517595 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 5] targeted_trace_20 (by decide) (by decide) (by decide) q
#print axioms targeted_class_20

theorem targeted_trace_21 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4] 349175835 251974675 := by
  exact ⟨523763753, by decide, ⟨392822815, by decide, ⟨589234223, by decide, ⟨883851335, by decide, ⟨1325777003, by decide, ⟨1988665505, by decide, ⟨1491499129, by decide, ⟨1118624347, by decide, ⟨1677936521, by decide, ⟨1258452391, by decide, ⟨1887678587, by decide, ⟨2831517881, by decide, ⟨2123638411, by decide, ⟨3185457617, by decide, ⟨2389093213, by decide, ⟨895909955, by decide, ⟨1343864933, by decide, ⟨251974675, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_21 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4] (349175835 + q * 2 ^ 30) endpoint ∧ endpoint < 349175835 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4] targeted_trace_21 (by decide) (by decide) (by decide) q
#print axioms targeted_class_21

theorem targeted_trace_22 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3] 936378395 675715835 := by
  exact ⟨1404567593, by decide, ⟨1053425695, by decide, ⟨1580138543, by decide, ⟨2370207815, by decide, ⟨3555311723, by decide, ⟨5332967585, by decide, ⟨3999725689, by decide, ⟨2999794267, by decide, ⟨4499691401, by decide, ⟨3374768551, by decide, ⟨5062152827, by decide, ⟨7593229241, by decide, ⟨5694921931, by decide, ⟨8542382897, by decide, ⟨6406787173, by decide, ⟨1201272595, by decide, ⟨1801908893, by decide, ⟨675715835, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_22 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3] (936378395 + q * 2 ^ 30) endpoint ∧ endpoint < 936378395 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3] targeted_trace_22 (by decide) (by decide) (by decide) q
#print axioms targeted_class_22

theorem targeted_trace_23 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5] 1959788571 707118071 := by
  exact ⟨2939682857, by decide, ⟨2204762143, by decide, ⟨3307143215, by decide, ⟨4960714823, by decide, ⟨7441072235, by decide, ⟨11161608353, by decide, ⟨8371206265, by decide, ⟨6278404699, by decide, ⟨9417607049, by decide, ⟨7063205287, by decide, ⟨10594807931, by decide, ⟨15892211897, by decide, ⟨11919158923, by decide, ⟨17878738385, by decide, ⟨13409053789, by decide, ⟨5028395171, by decide, ⟨7542592757, by decide, ⟨707118071, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_23 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5] (1959788571 + q * 2 ^ 31) endpoint ∧ endpoint < 1959788571 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5] targeted_trace_23 (by decide) (by decide) (by decide) q
#print axioms targeted_class_23

theorem targeted_trace_24 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4] 399507483 144147673 := by
  exact ⟨599261225, by decide, ⟨449445919, by decide, ⟨674168879, by decide, ⟨1011253319, by decide, ⟨1516879979, by decide, ⟨2275319969, by decide, ⟨1706489977, by decide, ⟨1279867483, by decide, ⟨1919801225, by decide, ⟨1439850919, by decide, ⟨2159776379, by decide, ⟨3239664569, by decide, ⟨2429748427, by decide, ⟨3644622641, by decide, ⟨2733466981, by decide, ⟨512525059, by decide, ⟨768787589, by decide, ⟨144147673, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_24 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4] (399507483 + q * 2 ^ 31) endpoint ∧ endpoint < 399507483 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4] targeted_trace_24 (by decide) (by decide) (by decide) q
#print axioms targeted_class_24

theorem targeted_trace_25 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5] 3905945627 2113976561 := by
  exact ⟨5858918441, by decide, ⟨4394188831, by decide, ⟨6591283247, by decide, ⟨9886924871, by decide, ⟨14830387307, by decide, ⟨22245580961, by decide, ⟨16684185721, by decide, ⟨12513139291, by decide, ⟨18769708937, by decide, ⟨14077281703, by decide, ⟨21115922555, by decide, ⟨31673883833, by decide, ⟨23755412875, by decide, ⟨35633119313, by decide, ⟨26724839485, by decide, ⟨10021814807, by decide, ⟨15032722211, by decide, ⟨22549083317, by decide, ⟨2113976561, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_25 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5] (3905945627 + q * 2 ^ 32) endpoint ∧ endpoint < 3905945627 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5] targeted_trace_25 (by decide) (by decide) (by decide) q
#print axioms targeted_class_25

theorem targeted_trace_26 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6] 886046747 159848791 := by
  exact ⟨1329070121, by decide, ⟨996802591, by decide, ⟨1495203887, by decide, ⟨2242805831, by decide, ⟨3364208747, by decide, ⟨5046313121, by decide, ⟨3784734841, by decide, ⟨2838551131, by decide, ⟨4257826697, by decide, ⟨3193370023, by decide, ⟨4790055035, by decide, ⟨7185082553, by decide, ⟨5388811915, by decide, ⟨8083217873, by decide, ⟨6062413405, by decide, ⟨2273405027, by decide, ⟨3410107541, by decide, ⟨159848791, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_26 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6] (886046747 + q * 2 ^ 32) endpoint ∧ endpoint < 886046747 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6] targeted_trace_26 (by decide) (by decide) (by decide) q
#print axioms targeted_class_26

theorem targeted_trace_27 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4] 2630877211 1423883815 := by
  exact ⟨3946315817, by decide, ⟨2959736863, by decide, ⟨4439605295, by decide, ⟨6659407943, by decide, ⟨9989111915, by decide, ⟨14983667873, by decide, ⟨11237750905, by decide, ⟨8428313179, by decide, ⟨12642469769, by decide, ⟨9481852327, by decide, ⟨14222778491, by decide, ⟨21334167737, by decide, ⟨16000625803, by decide, ⟨24000938705, by decide, ⟨18000704029, by decide, ⟨6750264011, by decide, ⟨10125396017, by decide, ⟨7594047013, by decide, ⟨1423883815, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_27 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4] (2630877211 + q * 2 ^ 32) endpoint ∧ endpoint < 2630877211 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4] targeted_trace_27 (by decide) (by decide) (by decide) q
#print axioms targeted_class_27

theorem targeted_trace_28 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3] 315621403 170820671 := by
  exact ⟨473432105, by decide, ⟨355074079, by decide, ⟨532611119, by decide, ⟨798916679, by decide, ⟨1198375019, by decide, ⟨1797562529, by decide, ⟨1348171897, by decide, ⟨1011128923, by decide, ⟨1516693385, by decide, ⟨1137520039, by decide, ⟨1706280059, by decide, ⟨2559420089, by decide, ⟨1919565067, by decide, ⟨2879347601, by decide, ⟨2159510701, by decide, ⟨809816513, by decide, ⟨607362385, by decide, ⟨455521789, by decide, ⟨170820671, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_28 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3] (315621403 + q * 2 ^ 32) endpoint ∧ endpoint < 315621403 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3] targeted_trace_28 (by decide) (by decide) (by decide) q
#print axioms targeted_class_28

theorem targeted_trace_29 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4] 2865758235 1551006163 := by
  exact ⟨4298637353, by decide, ⟨3223978015, by decide, ⟨4835967023, by decide, ⟨7253950535, by decide, ⟨10880925803, by decide, ⟨16321388705, by decide, ⟨12241041529, by decide, ⟨9180781147, by decide, ⟨13771171721, by decide, ⟨10328378791, by decide, ⟨15492568187, by decide, ⟨23238852281, by decide, ⟨17429139211, by decide, ⟨26143708817, by decide, ⟨19607781613, by decide, ⟨7352918105, by decide, ⟨5514688579, by decide, ⟨8272032869, by decide, ⟨1551006163, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_29 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4] (2865758235 + q * 2 ^ 32) endpoint ∧ endpoint < 2865758235 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4] targeted_trace_29 (by decide) (by decide) (by decide) q
#print axioms targeted_class_29

theorem targeted_trace_30 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4] 842006555 607614577 := by
  exact ⟨1263009833, by decide, ⟨947257375, by decide, ⟨1420886063, by decide, ⟨2131329095, by decide, ⟨3196993643, by decide, ⟨4795490465, by decide, ⟨3596617849, by decide, ⟨2697463387, by decide, ⟨4046195081, by decide, ⟨3034646311, by decide, ⟨4551969467, by decide, ⟨6827954201, by decide, ⟨5120965651, by decide, ⟨7681448477, by decide, ⟨2880543179, by decide, ⟨4320814769, by decide, ⟨3240611077, by decide, ⟨607614577, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_30 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4] (842006555 + q * 2 ^ 30) endpoint ∧ endpoint < 842006555 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4] targeted_trace_30 (by decide) (by decide) (by decide) q
#print axioms targeted_class_30

theorem targeted_trace_31 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5] 1378877467 497517533 := by
  exact ⟨2068316201, by decide, ⟨1551237151, by decide, ⟨2326855727, by decide, ⟨3490283591, by decide, ⟨5235425387, by decide, ⟨7853138081, by decide, ⟨5889853561, by decide, ⟨4417390171, by decide, ⟨6626085257, by decide, ⟨4969563943, by decide, ⟨7454345915, by decide, ⟨11181518873, by decide, ⟨8386139155, by decide, ⟨12579208733, by decide, ⟨4717203275, by decide, ⟨7075804913, by decide, ⟨5306853685, by decide, ⟨497517533, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_31 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5] (1378877467 + q * 2 ^ 31) endpoint ∧ endpoint < 1378877467 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5] targeted_trace_31 (by decide) (by decide) (by decide) q
#print axioms targeted_class_31

theorem targeted_trace_32 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 4] 95420443 61207075 := by
  exact ⟨143130665, by decide, ⟨107347999, by decide, ⟨161021999, by decide, ⟨241532999, by decide, ⟨362299499, by decide, ⟨543449249, by decide, ⟨407586937, by decide, ⟨305690203, by decide, ⟨458535305, by decide, ⟨343901479, by decide, ⟨515852219, by decide, ⟨773778329, by decide, ⟨580333747, by decide, ⟨870500621, by decide, ⟨326437733, by decide, ⟨61207075, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_32 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 4] (95420443 + q * 2 ^ 27) endpoint ∧ endpoint < 95420443 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 4] targeted_trace_32 (by decide) (by decide) (by decide) q
#print axioms targeted_class_32

theorem targeted_trace_33 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4] 1018167323 734736925 := by
  exact ⟨1527250985, by decide, ⟨1145438239, by decide, ⟨1718157359, by decide, ⟨2577236039, by decide, ⟨3865854059, by decide, ⟨5798781089, by decide, ⟨4349085817, by decide, ⟨3261814363, by decide, ⟨4892721545, by decide, ⟨3669541159, by decide, ⟨5504311739, by decide, ⟨8256467609, by decide, ⟨6192350707, by decide, ⟨9288526061, by decide, ⟨3483197273, by decide, ⟨2612397955, by decide, ⟨3918596933, by decide, ⟨734736925, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_33 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4] (1018167323 + q * 2 ^ 30) endpoint ∧ endpoint < 1018167323 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4] targeted_trace_33 (by decide) (by decide) (by decide) q
#print axioms targeted_class_33

theorem targeted_trace_34 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3] 531628059 383637107 := by
  exact ⟨797442089, by decide, ⟨598081567, by decide, ⟨897122351, by decide, ⟨1345683527, by decide, ⟨2018525291, by decide, ⟨3027787937, by decide, ⟨2270840953, by decide, ⟨1703130715, by decide, ⟨2554696073, by decide, ⟨1916022055, by decide, ⟨2874033083, by decide, ⟨4311049625, by decide, ⟨3233287219, by decide, ⟨4849930829, by decide, ⟨1818724061, by decide, ⟨682021523, by decide, ⟨1023032285, by decide, ⟨383637107, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_34 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3] (531628059 + q * 2 ^ 30) endpoint ∧ endpoint < 531628059 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3] targeted_trace_34 (by decide) (by decide) (by decide) q
#print axioms targeted_class_34

theorem targeted_trace_35 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5] 1555038235 561078707 := by
  exact ⟨2332557353, by decide, ⟨1749418015, by decide, ⟨2624127023, by decide, ⟨3936190535, by decide, ⟨5904285803, by decide, ⟨8856428705, by decide, ⟨6642321529, by decide, ⟨4981741147, by decide, ⟨7472611721, by decide, ⟨5604458791, by decide, ⟨8406688187, by decide, ⟨12610032281, by decide, ⟨9457524211, by decide, ⟨14186286317, by decide, ⟨5319857369, by decide, ⟨3989893027, by decide, ⟨5984839541, by decide, ⟨561078707, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_35 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5] (1555038235 + q * 2 ^ 31) endpoint ∧ endpoint < 1555038235 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5] targeted_trace_35 (by decide) (by decide) (by decide) q
#print axioms targeted_class_35

theorem targeted_trace_36 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4] 2142240795 772949287 := by
  exact ⟨3213361193, by decide, ⟨2410020895, by decide, ⟨3615031343, by decide, ⟨5422547015, by decide, ⟨8133820523, by decide, ⟨12200730785, by decide, ⟨9150548089, by decide, ⟨6862911067, by decide, ⟨10294366601, by decide, ⟨7720774951, by decide, ⟨11581162427, by decide, ⟨17371743641, by decide, ⟨13028807731, by decide, ⟨19543211597, by decide, ⟨7328704349, by decide, ⟨2748264131, by decide, ⟨4122396197, by decide, ⟨772949287, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_36 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4] (2142240795 + q * 2 ^ 31) endpoint ∧ endpoint < 2142240795 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4] targeted_trace_36 (by decide) (by decide) (by decide) q
#print axioms targeted_class_36

theorem targeted_trace_37 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5] 3501195291 1894917515 := by
  exact ⟨5251792937, by decide, ⟨3938844703, by decide, ⟨5908267055, by decide, ⟨8862400583, by decide, ⟨13293600875, by decide, ⟨19940401313, by decide, ⟨14955300985, by decide, ⟨11216475739, by decide, ⟨16824713609, by decide, ⟨12618535207, by decide, ⟨18927802811, by decide, ⟨28391704217, by decide, ⟨21293778163, by decide, ⟨31940667245, by decide, ⟨11977750217, by decide, ⟨8983312663, by decide, ⟨13474968995, by decide, ⟨20212453493, by decide, ⟨1894917515, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_37 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5] (3501195291 + q * 2 ^ 32) endpoint ∧ endpoint < 3501195291 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5] targeted_trace_37 (by decide) (by decide) (by decide) q
#print axioms targeted_class_37

theorem targeted_trace_38 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3] 3970957339 2149162211 := by
  exact ⟨5956436009, by decide, ⟨4467327007, by decide, ⟨6700990511, by decide, ⟨10051485767, by decide, ⟨15077228651, by decide, ⟨22615842977, by decide, ⟨16961882233, by decide, ⟨12721411675, by decide, ⟨19082117513, by decide, ⟨14311588135, by decide, ⟨21467382203, by decide, ⟨32201073305, by decide, ⟨24150804979, by decide, ⟨36226207469, by decide, ⟨13584827801, by decide, ⟨10188620851, by decide, ⟨15282931277, by decide, ⟨5731099229, by decide, ⟨2149162211, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_38 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3] (3970957339 + q * 2 ^ 32) endpoint ∧ endpoint < 3970957339 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3] targeted_trace_38 (by decide) (by decide) (by decide) q
#print axioms targeted_class_38

theorem targeted_trace_39 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6] 481296411 86829109 := by
  exact ⟨721944617, by decide, ⟨541458463, by decide, ⟨812187695, by decide, ⟨1218281543, by decide, ⟨1827422315, by decide, ⟨2741133473, by decide, ⟨2055850105, by decide, ⟨1541887579, by decide, ⟨2312831369, by decide, ⟨1734623527, by decide, ⟨2601935291, by decide, ⟨3902902937, by decide, ⟨2927177203, by decide, ⟨4390765805, by decide, ⟨1646537177, by decide, ⟨1234902883, by decide, ⟨1852354325, by decide, ⟨86829109, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_39 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6] (481296411 + q * 2 ^ 32) endpoint ∧ endpoint < 481296411 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6] targeted_trace_39 (by decide) (by decide) (by decide) q
#print axioms targeted_class_39

theorem targeted_trace_40 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4] 2461007899 1331947117 := by
  exact ⟨3691511849, by decide, ⟨2768633887, by decide, ⟨4152950831, by decide, ⟨6229426247, by decide, ⟨9344139371, by decide, ⟨14016209057, by decide, ⟨10512156793, by decide, ⟨7884117595, by decide, ⟨11826176393, by decide, ⟨8869632295, by decide, ⟨13304448443, by decide, ⟨19956672665, by decide, ⟨14967504499, by decide, ⟨22451256749, by decide, ⟨8419221281, by decide, ⟨6314415961, by decide, ⟨4735811971, by decide, ⟨7103717957, by decide, ⟨1331947117, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_40 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4] (2461007899 + q * 2 ^ 32) endpoint ∧ endpoint < 2461007899 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4] targeted_trace_40 (by decide) (by decide) (by decide) q
#print axioms targeted_class_40

theorem targeted_trace_41 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 3] 91226139 58516655 := by
  exact ⟨136839209, by decide, ⟨102629407, by decide, ⟨153944111, by decide, ⟨230916167, by decide, ⟨346374251, by decide, ⟨519561377, by decide, ⟨389671033, by decide, ⟨292253275, by decide, ⟨438379913, by decide, ⟨328784935, by decide, ⟨493177403, by decide, ⟨739766105, by decide, ⟨554824579, by decide, ⟨832236869, by decide, ⟨156044413, by decide, ⟨58516655, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_41 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 3] (91226139 + q * 2 ^ 27) endpoint ∧ endpoint < 91226139 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 3] targeted_trace_41 (by decide) (by decide) (by decide) q
#print axioms targeted_class_41

theorem targeted_trace_42 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3] 443547675 320075933 := by
  exact ⟨665321513, by decide, ⟨498991135, by decide, ⟨748486703, by decide, ⟨1122730055, by decide, ⟨1684095083, by decide, ⟨2526142625, by decide, ⟨1894606969, by decide, ⟨1420955227, by decide, ⟨2131432841, by decide, ⟨1598574631, by decide, ⟨2397861947, by decide, ⟨3596792921, by decide, ⟨2697594691, by decide, ⟨4046392037, by decide, ⟨758698507, by decide, ⟨1138047761, by decide, ⟨853535821, by decide, ⟨320075933, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_42 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3] (443547675 + q * 2 ^ 30) endpoint ∧ endpoint < 443547675 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3] targeted_trace_42 (by decide) (by decide) (by decide) q
#print axioms targeted_class_42

theorem targeted_trace_43 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4] 980418587 353748211 := by
  exact ⟨1470627881, by decide, ⟨1102970911, by decide, ⟨1654456367, by decide, ⟨2481684551, by decide, ⟨3722526827, by decide, ⟨5583790241, by decide, ⟨4187842681, by decide, ⟨3140882011, by decide, ⟨4711323017, by decide, ⟨3533492263, by decide, ⟨5300238395, by decide, ⟨7950357593, by decide, ⟨5962768195, by decide, ⟨8944152293, by decide, ⟨1677028555, by decide, ⟨2515542833, by decide, ⟨1886657125, by decide, ⟨353748211, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_43 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4] (980418587 + q * 2 ^ 31) endpoint ∧ endpoint < 980418587 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4] targeted_trace_43 (by decide) (by decide) (by decide) q
#print axioms targeted_class_43

theorem targeted_trace_44 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5] 2691694619 1456799423 := by
  exact ⟨4037541929, by decide, ⟨3028156447, by decide, ⟨4542234671, by decide, ⟨6813352007, by decide, ⟨10220028011, by decide, ⟨15330042017, by decide, ⟨11497531513, by decide, ⟨8623148635, by decide, ⟨12934722953, by decide, ⟨9701042215, by decide, ⟨14551563323, by decide, ⟨21827344985, by decide, ⟨16370508739, by decide, ⟨24555763109, by decide, ⟨4604205583, by decide, ⟨6906308375, by decide, ⟨10359462563, by decide, ⟨15539193845, by decide, ⟨1456799423, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_44 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5] (2691694619 + q * 2 ^ 32) endpoint ∧ endpoint < 2691694619 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5] targeted_trace_44 (by decide) (by decide) (by decide) q
#print axioms targeted_class_44

theorem targeted_trace_45 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4] 1416626203 766706677 := by
  exact ⟨2124939305, by decide, ⟨1593704479, by decide, ⟨2390556719, by decide, ⟨3585835079, by decide, ⟨5378752619, by decide, ⟨8068128929, by decide, ⟨6051096697, by decide, ⟨4538322523, by decide, ⟨6807483785, by decide, ⟨5105612839, by decide, ⟨7658419259, by decide, ⟨11487628889, by decide, ⟨8615721667, by decide, ⟨12923582501, by decide, ⟨2423171719, by decide, ⟨3634757579, by decide, ⟨5452136369, by decide, ⟨4089102277, by decide, ⟨766706677, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_45 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4] (1416626203 + q * 2 ^ 32) endpoint ∧ endpoint < 1416626203 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4] targeted_trace_45 (by decide) (by decide) (by decide) q
#print axioms targeted_class_45

theorem targeted_trace_46 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3] 3161456667 1711044119 := by
  exact ⟨4742185001, by decide, ⟨3556638751, by decide, ⟨5334958127, by decide, ⟨8002437191, by decide, ⟨12003655787, by decide, ⟨18005483681, by decide, ⟨13504112761, by decide, ⟨10128084571, by decide, ⟨15192126857, by decide, ⟨11394095143, by decide, ⟨17091142715, by decide, ⟨25636714073, by decide, ⟨19227535555, by decide, ⟨28841303333, by decide, ⟨5407744375, by decide, ⟨8111616563, by decide, ⟨12167424845, by decide, ⟨4562784317, by decide, ⟨1711044119, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_46 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3] (3161456667 + q * 2 ^ 32) endpoint ∧ endpoint < 3161456667 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3] targeted_trace_46 (by decide) (by decide) (by decide) q
#print axioms targeted_class_46

theorem targeted_trace_47 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4] 1651507227 893829025 := by
  exact ⟨2477260841, by decide, ⟨1857945631, by decide, ⟨2786918447, by decide, ⟨4180377671, by decide, ⟨6270566507, by decide, ⟨9405849761, by decide, ⟨7054387321, by decide, ⟨5290790491, by decide, ⟨7936185737, by decide, ⟨5952139303, by decide, ⟨8928208955, by decide, ⟨13392313433, by decide, ⟨10044235075, by decide, ⟨15066352613, by decide, ⟨2824941115, by decide, ⟨4237411673, by decide, ⟨3178058755, by decide, ⟨4767088133, by decide, ⟨893829025, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_47 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4] (1651507227 + q * 2 ^ 32) endpoint ∧ endpoint < 1651507227 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4] targeted_trace_47 (by decide) (by decide) (by decide) q
#print axioms targeted_class_47

theorem targeted_trace_48 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3] 3396337691 1838166467 := by
  exact ⟨5094506537, by decide, ⟨3820879903, by decide, ⟨5731319855, by decide, ⟨8596979783, by decide, ⟨12895469675, by decide, ⟨19343204513, by decide, ⟨14507403385, by decide, ⟨10880552539, by decide, ⟨16320828809, by decide, ⟨12240621607, by decide, ⟨18360932411, by decide, ⟨27541398617, by decide, ⟨20656048963, by decide, ⟨30984073445, by decide, ⟨5809513771, by decide, ⟨8714270657, by decide, ⟨6535702993, by decide, ⟨4901777245, by decide, ⟨1838166467, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_48 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3] (3396337691 + q * 2 ^ 32) endpoint ∧ endpoint < 3396337691 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3] targeted_trace_48 (by decide) (by decide) (by decide) q
#print axioms targeted_class_48

theorem targeted_trace_49 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 3] 113770523 72977663 := by
  exact ⟨170655785, by decide, ⟨127991839, by decide, ⟨191987759, by decide, ⟨287981639, by decide, ⟨431972459, by decide, ⟨647958689, by decide, ⟨485969017, by decide, ⟨364476763, by decide, ⟨546715145, by decide, ⟨410036359, by decide, ⟨615054539, by decide, ⟨922581809, by decide, ⟨691936357, by decide, ⟨129738067, by decide, ⟨194607101, by decide, ⟨72977663, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_49 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 3] (113770523 + q * 2 ^ 27) endpoint ∧ endpoint < 113770523 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 3] targeted_trace_49 (by decide) (by decide) (by decide) q
#print axioms targeted_class_49

theorem targeted_trace_50 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3] 818413595 590589263 := by
  exact ⟨1227620393, by decide, ⟨920715295, by decide, ⟨1381072943, by decide, ⟨2071609415, by decide, ⟨3107414123, by decide, ⟨4661121185, by decide, ⟨3495840889, by decide, ⟨2621880667, by decide, ⟨3932821001, by decide, ⟨2949615751, by decide, ⟨4424423627, by decide, ⟨6636635441, by decide, ⟨4977476581, by decide, ⟨933276859, by decide, ⟨1399915289, by decide, ⟨1049936467, by decide, ⟨1574904701, by decide, ⟨590589263, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_50 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3] (818413595 + q * 2 ^ 30) endpoint ∧ endpoint < 818413595 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3] targeted_trace_50 (by decide) (by decide) (by decide) q
#print axioms targeted_class_50

theorem targeted_trace_51 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3] 466092059 336344567 := by
  exact ⟨699138089, by decide, ⟨524353567, by decide, ⟨786530351, by decide, ⟨1179795527, by decide, ⟨1769693291, by decide, ⟨2654539937, by decide, ⟨1990904953, by decide, ⟨1493178715, by decide, ⟨2239768073, by decide, ⟨1679826055, by decide, ⟨2519739083, by decide, ⟨3779608625, by decide, ⟨2834706469, by decide, ⟨531507463, by decide, ⟨797261195, by decide, ⟨1195891793, by decide, ⟨896918845, by decide, ⟨336344567, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_51 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3] (466092059 + q * 2 ^ 30) endpoint ∧ endpoint < 466092059 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3] targeted_trace_51 (by decide) (by decide) (by decide) q
#print axioms targeted_class_51

theorem targeted_trace_52 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4] 281542683 101584387 := by
  exact ⟨422314025, by decide, ⟨316735519, by decide, ⟨475103279, by decide, ⟨712654919, by decide, ⟨1068982379, by decide, ⟨1603473569, by decide, ⟨1202605177, by decide, ⟨901953883, by decide, ⟨1352930825, by decide, ⟨1014698119, by decide, ⟨1522047179, by decide, ⟨2283070769, by decide, ⟨1712303077, by decide, ⟨321056827, by decide, ⟨481585241, by decide, ⟨361188931, by decide, ⟨541783397, by decide, ⟨101584387, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_52 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4] (281542683 + q * 2 ^ 31) endpoint ∧ endpoint < 281542683 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4] targeted_trace_52 (by decide) (by decide) (by decide) q
#print axioms targeted_class_52

theorem targeted_trace_53 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4] 2076704795 749303017 := by
  exact ⟨3115057193, by decide, ⟨2336292895, by decide, ⟨3504439343, by decide, ⟨5256659015, by decide, ⟨7884988523, by decide, ⟨11827482785, by decide, ⟨8870612089, by decide, ⟨6652959067, by decide, ⟨9979438601, by decide, ⟨7484578951, by decide, ⟨11226868427, by decide, ⟨16840302641, by decide, ⟨12630226981, by decide, ⟨2368167559, by decide, ⟨3552251339, by decide, ⟨5328377009, by decide, ⟨3996282757, by decide, ⟨749303017, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_53 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4] (2076704795 + q * 2 ^ 31) endpoint ∧ endpoint < 2076704795 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4] targeted_trace_53 (by decide) (by decide) (by decide) q
#print axioms targeted_class_53

theorem targeted_trace_54 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3] 2697461787 1459920731 := by
  exact ⟨4046192681, by decide, ⟨3034644511, by decide, ⟨4551966767, by decide, ⟨6827950151, by decide, ⟨10241925227, by decide, ⟨15362887841, by decide, ⟨11522165881, by decide, ⟨8641624411, by decide, ⟨12962436617, by decide, ⟨9721827463, by decide, ⟨14582741195, by decide, ⟨21874111793, by decide, ⟨16405583845, by decide, ⟨3076046971, by decide, ⟨4614070457, by decide, ⟨3460552843, by decide, ⟨5190829265, by decide, ⟨3893121949, by decide, ⟨1459920731, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_54 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3] (2697461787 + q * 2 ^ 32) endpoint ∧ endpoint < 2697461787 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3] targeted_trace_54 (by decide) (by decide) (by decide) q
#print axioms targeted_class_54

theorem targeted_trace_55 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5] 3502768155 631922927 := by
  exact ⟨5254152233, by decide, ⟨3940614175, by decide, ⟨5910921263, by decide, ⟨8866381895, by decide, ⟨13299572843, by decide, ⟨19949359265, by decide, ⟨14962019449, by decide, ⟨11221514587, by decide, ⟨16832271881, by decide, ⟨12624203911, by decide, ⟨18936305867, by decide, ⟨28404458801, by decide, ⟨21303344101, by decide, ⟨3994377019, by decide, ⟨5991565529, by decide, ⟨4493674147, by decide, ⟨6740511221, by decide, ⟨631922927, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_55 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5] (3502768155 + q * 2 ^ 32) endpoint ∧ endpoint < 3502768155 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5] targeted_trace_55 (by decide) (by decide) (by decide) q
#print axioms targeted_class_55

theorem targeted_trace_56 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4] 952631323 515583289 := by
  exact ⟨1428946985, by decide, ⟨1071710239, by decide, ⟨1607565359, by decide, ⟨2411348039, by decide, ⟨3617022059, by decide, ⟨5425533089, by decide, ⟨4069149817, by decide, ⟨3051862363, by decide, ⟨4577793545, by decide, ⟨3433345159, by decide, ⟨5150017739, by decide, ⟨7725026609, by decide, ⟨5793769957, by decide, ⟨1086331867, by decide, ⟨1629497801, by decide, ⟨1222123351, by decide, ⟨1833185027, by decide, ⟨2749777541, by decide, ⟨515583289, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_56 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4] (952631323 + q * 2 ^ 32) endpoint ∧ endpoint < 952631323 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4] targeted_trace_56 (by decide) (by decide) (by decide) q
#print axioms targeted_class_56

theorem targeted_trace_57 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5] 1640497179 887870165 := by
  exact ⟨2460745769, by decide, ⟨1845559327, by decide, ⟨2768338991, by decide, ⟨4152508487, by decide, ⟨6228762731, by decide, ⟨9343144097, by decide, ⟨7007358073, by decide, ⟨5255518555, by decide, ⟨7883277833, by decide, ⟨5912458375, by decide, ⟨8868687563, by decide, ⟨13303031345, by decide, ⟨9977273509, by decide, ⟨1870738783, by decide, ⟨2806108175, by decide, ⟨4209162263, by decide, ⟨6313743395, by decide, ⟨9470615093, by decide, ⟨887870165, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_57 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5] (1640497179 + q * 2 ^ 32) endpoint ∧ endpoint < 1640497179 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5] targeted_trace_57 (by decide) (by decide) (by decide) q
#print axioms targeted_class_57

theorem targeted_trace_58 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4] 365428763 197777419 := by
  exact ⟨548143145, by decide, ⟨411107359, by decide, ⟨616661039, by decide, ⟨924991559, by decide, ⟨1387487339, by decide, ⟨2081231009, by decide, ⟨1560923257, by decide, ⟨1170692443, by decide, ⟨1756038665, by decide, ⟨1317028999, by decide, ⟨1975543499, by decide, ⟨2963315249, by decide, ⟨2222486437, by decide, ⟨416716207, by decide, ⟨625074311, by decide, ⟨937611467, by decide, ⟨1406417201, by decide, ⟨1054812901, by decide, ⟨197777419, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_58 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4] (365428763 + q * 2 ^ 32) endpoint ∧ endpoint < 365428763 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4] targeted_trace_58 (by decide) (by decide) (by decide) q
#print axioms targeted_class_58

theorem targeted_trace_59 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 3] 120061979 77013293 := by
  exact ⟨180092969, by decide, ⟨135069727, by decide, ⟨202604591, by decide, ⟨303906887, by decide, ⟨455860331, by decide, ⟨683790497, by decide, ⟨512842873, by decide, ⟨384632155, by decide, ⟨576948233, by decide, ⟨432711175, by decide, ⟨649066763, by decide, ⟨973600145, by decide, ⟨730200109, by decide, ⟨273825041, by decide, ⟨205368781, by decide, ⟨77013293, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_59 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 3] (120061979 + q * 2 ^ 27) endpoint ∧ endpoint < 120061979 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 3] targeted_trace_59 (by decide) (by decide) (by decide) q
#print axioms targeted_class_59

theorem targeted_trace_60 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4] 371720219 268243309 := by
  exact ⟨557580329, by decide, ⟨418185247, by decide, ⟨627277871, by decide, ⟨940916807, by decide, ⟨1411375211, by decide, ⟨2117062817, by decide, ⟨1587797113, by decide, ⟨1190847835, by decide, ⟨1786271753, by decide, ⟨1339703815, by decide, ⟨2009555723, by decide, ⟨3014333585, by decide, ⟨2260750189, by decide, ⟨847781321, by decide, ⟨635835991, by decide, ⟨953753987, by decide, ⟨1430630981, by decide, ⟨268243309, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_60 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4] (371720219 + q * 2 ^ 30) endpoint ∧ endpoint < 371720219 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4] targeted_trace_60 (by decide) (by decide) (by decide) q
#print axioms targeted_class_60

theorem targeted_trace_61 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3] 958922779 691984469 := by
  exact ⟨1438384169, by decide, ⟨1078788127, by decide, ⟨1618182191, by decide, ⟨2427273287, by decide, ⟨3640909931, by decide, ⟨5461364897, by decide, ⟨4096023673, by decide, ⟨3072017755, by decide, ⟨4608026633, by decide, ⟨3456019975, by decide, ⟨5184029963, by decide, ⟨7776044945, by decide, ⟨5832033709, by decide, ⟨2187012641, by decide, ⟨1640259481, by decide, ⟨1230194611, by decide, ⟨1845291917, by decide, ⟨691984469, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_61 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3] (958922779 + q * 2 ^ 30) endpoint ∧ endpoint < 958922779 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3] targeted_trace_61 (by decide) (by decide) (by decide) q
#print axioms targeted_class_61

theorem targeted_trace_62 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5] 908591131 327831899 := by
  exact ⟨1362886697, by decide, ⟨1022165023, by decide, ⟨1533247535, by decide, ⟨2299871303, by decide, ⟨3449806955, by decide, ⟨5174710433, by decide, ⟨3881032825, by decide, ⟨2910774619, by decide, ⟨4366161929, by decide, ⟨3274621447, by decide, ⟨4911932171, by decide, ⟨7367898257, by decide, ⟨5525923693, by decide, ⟨2072221385, by decide, ⟨1554166039, by decide, ⟨2331249059, by decide, ⟨3496873589, by decide, ⟨327831899, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_62 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5] (908591131 + q * 2 ^ 31) endpoint ∧ endpoint < 908591131 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5] targeted_trace_62 (by decide) (by decide) (by decide) q
#print axioms targeted_class_62

theorem targeted_trace_63 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4] 1495793691 539702479 := by
  exact ⟨2243690537, by decide, ⟨1682767903, by decide, ⟨2524151855, by decide, ⟨3786227783, by decide, ⟨5679341675, by decide, ⟨8519012513, by decide, ⟨6389259385, by decide, ⟨4791944539, by decide, ⟨7187916809, by decide, ⟨5390937607, by decide, ⟨8086406411, by decide, ⟨12129609617, by decide, ⟨9097207213, by decide, ⟨3411452705, by decide, ⟨2558589529, by decide, ⟨1918942147, by decide, ⟨2878413221, by decide, ⟨539702479, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_63 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4] (1495793691 + q * 2 ^ 31) endpoint ∧ endpoint < 1495793691 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4] targeted_trace_63 (by decide) (by decide) (by decide) q
#print axioms targeted_class_63

theorem targeted_trace_64 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3] 3559391259 1926414347 := by
  exact ⟨5339086889, by decide, ⟨4004315167, by decide, ⟨6006472751, by decide, ⟨9009709127, by decide, ⟨13514563691, by decide, ⟨20271845537, by decide, ⟨15203884153, by decide, ⟨11402913115, by decide, ⟨17104369673, by decide, ⟨12828277255, by decide, ⟨19242415883, by decide, ⟨28863623825, by decide, ⟨21647717869, by decide, ⟨8117894201, by decide, ⟨6088420651, by decide, ⟨9132630977, by decide, ⟨6849473233, by decide, ⟨5137104925, by decide, ⟨1926414347, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_64 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3] (3559391259 + q * 2 ^ 32) endpoint ∧ endpoint < 3559391259 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3] targeted_trace_64 (by decide) (by decide) (by decide) q
#print axioms targeted_class_64

theorem targeted_trace_65 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4] 1814560795 982076905 := by
  exact ⟨2721841193, by decide, ⟨2041380895, by decide, ⟨3062071343, by decide, ⟨4593107015, by decide, ⟨6889660523, by decide, ⟨10334490785, by decide, ⟨7750868089, by decide, ⟨5813151067, by decide, ⟨8719726601, by decide, ⟨6539794951, by decide, ⟨9809692427, by decide, ⟨14714538641, by decide, ⟨11035903981, by decide, ⟨4138463993, by decide, ⟨3103847995, by decide, ⟨4655771993, by decide, ⟨3491828995, by decide, ⟨5237743493, by decide, ⟨982076905, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_65 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4] (1814560795 + q * 2 ^ 32) endpoint ∧ endpoint < 1814560795 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4] targeted_trace_65 (by decide) (by decide) (by decide) q
#print axioms targeted_class_65

theorem targeted_trace_66 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5] 2854748187 1545047303 := by
  exact ⟨4282122281, by decide, ⟨3211591711, by decide, ⟨4817387567, by decide, ⟨7226081351, by decide, ⟨10839122027, by decide, ⟨16258683041, by decide, ⟨12194012281, by decide, ⟨9145509211, by decide, ⟨13718263817, by decide, ⟨10288697863, by decide, ⟨15433046795, by decide, ⟨23149570193, by decide, ⟨17362177645, by decide, ⟨6510816617, by decide, ⟨4883112463, by decide, ⟨7324668695, by decide, ⟨10987003043, by decide, ⟨16480504565, by decide, ⟨1545047303, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_66 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5] (2854748187 + q * 2 ^ 32) endpoint ∧ endpoint < 2854748187 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5] targeted_trace_66 (by decide) (by decide) (by decide) q
#print axioms targeted_class_66

theorem targeted_trace_67 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3] 3324510235 1799291999 := by
  exact ⟨4986765353, by decide, ⟨3740074015, by decide, ⟨5610111023, by decide, ⟨8415166535, by decide, ⟨12622749803, by decide, ⟨18934124705, by decide, ⟨14200593529, by decide, ⟨10650445147, by decide, ⟨15975667721, by decide, ⟨11981750791, by decide, ⟨17972626187, by decide, ⟨26958939281, by decide, ⟨20219204461, by decide, ⟨7582201673, by decide, ⟨5686651255, by decide, ⟨8529976883, by decide, ⟨12794965325, by decide, ⟨4798111997, by decide, ⟨1799291999, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_67 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3] (3324510235 + q * 2 ^ 32) endpoint ∧ endpoint < 3324510235 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3] targeted_trace_67 (by decide) (by decide) (by decide) q
#print axioms targeted_class_67

theorem targeted_trace_68 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6] 4129816603 745046683 := by
  exact ⟨6194724905, by decide, ⟨4646043679, by decide, ⟨6969065519, by decide, ⟨10453598279, by decide, ⟨15680397419, by decide, ⟨23520596129, by decide, ⟨17640447097, by decide, ⟨13230335323, by decide, ⟨19845502985, by decide, ⟨14884127239, by decide, ⟨22326190859, by decide, ⟨33489286289, by decide, ⟨25116964717, by decide, ⟨9418861769, by decide, ⟨7064146327, by decide, ⟨10596219491, by decide, ⟨15894329237, by decide, ⟨745046683, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_68 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6] (4129816603 + q * 2 ^ 32) endpoint ∧ endpoint < 4129816603 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6] targeted_trace_68 (by decide) (by decide) (by decide) q
#print axioms targeted_class_68

theorem targeted_trace_69 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4] 1579679771 854954557 := by
  exact ⟨2369519657, by decide, ⟨1777139743, by decide, ⟨2665709615, by decide, ⟨3998564423, by decide, ⟨5997846635, by decide, ⟨8996769953, by decide, ⟨6747577465, by decide, ⟨5060683099, by decide, ⟨7591024649, by decide, ⟨5693268487, by decide, ⟨8539902731, by decide, ⟨12809854097, by decide, ⟨9607390573, by decide, ⟨3602771465, by decide, ⟨2702078599, by decide, ⟨4053117899, by decide, ⟨6079676849, by decide, ⟨4559757637, by decide, ⟨854954557, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_69 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4] (1579679771 + q * 2 ^ 32) endpoint ∧ endpoint < 1579679771 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4] targeted_trace_69 (by decide) (by decide) (by decide) q
#print axioms targeted_class_69

theorem targeted_trace_70 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 4] 124256283 79703713 := by
  exact ⟨186384425, by decide, ⟨139788319, by decide, ⟨209682479, by decide, ⟨314523719, by decide, ⟨471785579, by decide, ⟨707678369, by decide, ⟨530758777, by decide, ⟨398069083, by decide, ⟨597103625, by decide, ⟨447827719, by decide, ⟨671741579, by decide, ⟨1007612369, by decide, ⟨755709277, by decide, ⟨283390979, by decide, ⟨425086469, by decide, ⟨79703713, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_70 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 4] (124256283 + q * 2 ^ 27) endpoint ∧ endpoint < 124256283 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 4] targeted_trace_70 (by decide) (by decide) (by decide) q
#print axioms targeted_class_70

theorem targeted_trace_71 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3] 342360091 247056251 := by
  exact ⟨513540137, by decide, ⟨385155103, by decide, ⟨577732655, by decide, ⟨866598983, by decide, ⟨1299898475, by decide, ⟨1949847713, by decide, ⟨1462385785, by decide, ⟨1096789339, by decide, ⟨1645184009, by decide, ⟨1233888007, by decide, ⟨1850832011, by decide, ⟨2776248017, by decide, ⟨2082186013, by decide, ⟨780819755, by decide, ⟨1171229633, by decide, ⟨878422225, by decide, ⟨658816669, by decide, ⟨247056251, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_71 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3] (342360091 + q * 2 ^ 30) endpoint ∧ endpoint < 342360091 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3] targeted_trace_71 (by decide) (by decide) (by decide) q
#print axioms targeted_class_71

theorem targeted_trace_72 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4] 1952972827 704658859 := by
  exact ⟨2929459241, by decide, ⟨2197094431, by decide, ⟨3295641647, by decide, ⟨4943462471, by decide, ⟨7415193707, by decide, ⟨11122790561, by decide, ⟨8342092921, by decide, ⟨6256569691, by decide, ⟨9384854537, by decide, ⟨7038640903, by decide, ⟨10557961355, by decide, ⟨15836942033, by decide, ⟨11877706525, by decide, ⟨4454139947, by decide, ⟨6681209921, by decide, ⟨5010907441, by decide, ⟨3758180581, by decide, ⟨704658859, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_72 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4] (1952972827 + q * 2 ^ 31) endpoint ∧ endpoint < 1952972827 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4] targeted_trace_72 (by decide) (by decide) (by decide) q
#print axioms targeted_class_72

theorem targeted_trace_73 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5] 879231003 158619185 := by
  exact ⟨1318846505, by decide, ⟨989134879, by decide, ⟨1483702319, by decide, ⟨2225553479, by decide, ⟨3338330219, by decide, ⟨5007495329, by decide, ⟨3755621497, by decide, ⟨2816716123, by decide, ⟨4225074185, by decide, ⟨3168805639, by decide, ⟨4753208459, by decide, ⟨7129812689, by decide, ⟨5347359517, by decide, ⟨2005259819, by decide, ⟨3007889729, by decide, ⟨2255917297, by decide, ⟨1691937973, by decide, ⟨158619185, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_73 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5] (879231003 + q * 2 ^ 32) endpoint ∧ endpoint < 879231003 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5] targeted_trace_73 (by decide) (by decide) (by decide) q
#print axioms targeted_class_73

theorem targeted_trace_74 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4] 2624061467 1420194997 := by
  exact ⟨3936092201, by decide, ⟨2952069151, by decide, ⟨4428103727, by decide, ⟨6642155591, by decide, ⟨9963233387, by decide, ⟨14944850081, by decide, ⟨11208637561, by decide, ⟨8406478171, by decide, ⟨12609717257, by decide, ⟨9457287943, by decide, ⟨14185931915, by decide, ⟨21278897873, by decide, ⟨15959173405, by decide, ⟨5984690027, by decide, ⟨8977035041, by decide, ⟨6732776281, by decide, ⟨5049582211, by decide, ⟨7574373317, by decide, ⟨1420194997, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_74 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4] (2624061467 + q * 2 ^ 32) endpoint ∧ endpoint < 2624061467 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4] targeted_trace_74 (by decide) (by decide) (by decide) q
#print axioms targeted_class_74

theorem targeted_trace_75 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5] 3664248859 1983165395 := by
  exact ⟨5496373289, by decide, ⟨4122279967, by decide, ⟨6183419951, by decide, ⟨9275129927, by decide, ⟨13912694891, by decide, ⟨20869042337, by decide, ⟨15651781753, by decide, ⟨11738836315, by decide, ⟨17608254473, by decide, ⟨13206190855, by decide, ⟨19809286283, by decide, ⟨29713929425, by decide, ⟨22285447069, by decide, ⟨8357042651, by decide, ⟨12535563977, by decide, ⟨9401672983, by decide, ⟨14102509475, by decide, ⟨21153764213, by decide, ⟨1983165395, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_75 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5] (3664248859 + q * 2 ^ 32) endpoint ∧ endpoint < 3664248859 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5] targeted_trace_75 (by decide) (by decide) (by decide) q
#print axioms targeted_class_75

theorem targeted_trace_76 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3] 4134010907 2237410091 := by
  exact ⟨6201016361, by decide, ⟨4650762271, by decide, ⟨6976143407, by decide, ⟨10464215111, by decide, ⟨15696322667, by decide, ⟨23544484001, by decide, ⟨17658363001, by decide, ⟨13243772251, by decide, ⟨19865658377, by decide, ⟨14899243783, by decide, ⟨22348865675, by decide, ⟨33523298513, by decide, ⟨25142473885, by decide, ⟨9428427707, by decide, ⟨14142641561, by decide, ⟨10606981171, by decide, ⟨15910471757, by decide, ⟨5966426909, by decide, ⟨2237410091, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_76 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3] (4134010907 + q * 2 ^ 32) endpoint ∧ endpoint < 4134010907 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3] targeted_trace_76 (by decide) (by decide) (by decide) q
#print axioms targeted_class_76

theorem targeted_trace_77 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5] 887619611 640530185 := by
  exact ⟨1331429417, by decide, ⟨998572063, by decide, ⟨1497858095, by decide, ⟨2246787143, by decide, ⟨3370180715, by decide, ⟨5055271073, by decide, ⟨3791453305, by decide, ⟨2843589979, by decide, ⟨4265384969, by decide, ⟨3199038727, by decide, ⟨4798558091, by decide, ⟨7197837137, by decide, ⟨5398377853, by decide, ⟨2024391695, by decide, ⟨3036587543, by decide, ⟨4554881315, by decide, ⟨6832321973, by decide, ⟨640530185, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_77 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5] (887619611 + q * 2 ^ 30) endpoint ∧ endpoint < 887619611 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5] targeted_trace_77 (by decide) (by decide) (by decide) q
#print axioms targeted_class_77

theorem targeted_trace_78 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4] 1005060123 725278417 := by
  exact ⟨1507590185, by decide, ⟨1130692639, by decide, ⟨1696038959, by decide, ⟨2544058439, by decide, ⟨3816087659, by decide, ⟨5724131489, by decide, ⟨4293098617, by decide, ⟨3219823963, by decide, ⟨4829735945, by decide, ⟨3622301959, by decide, ⟨5433452939, by decide, ⟨8150179409, by decide, ⟨6112634557, by decide, ⟨2292237959, by decide, ⟨3438356939, by decide, ⟨5157535409, by decide, ⟨3868151557, by decide, ⟨725278417, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_78 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4] (1005060123 + q * 2 ^ 30) endpoint ∧ endpoint < 1005060123 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4] targeted_trace_78 (by decide) (by decide) (by decide) q
#print axioms targeted_class_78

theorem targeted_trace_79 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6] 1424490523 513975337 := by
  exact ⟨2136735785, by decide, ⟨1602551839, by decide, ⟨2403827759, by decide, ⟨3605741639, by decide, ⟨5408612459, by decide, ⟨8112918689, by decide, ⟨6084689017, by decide, ⟨4563516763, by decide, ⟨6845275145, by decide, ⟨5133956359, by decide, ⟨7700934539, by decide, ⟨11551401809, by decide, ⟨8663551357, by decide, ⟨3248831759, by decide, ⟨4873247639, by decide, ⟨7309871459, by decide, ⟨10964807189, by decide, ⟨513975337, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_79 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6] (1424490523 + q * 2 ^ 31) endpoint ∧ endpoint < 1424490523 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6] targeted_trace_79 (by decide) (by decide) (by decide) q
#print axioms targeted_class_79

theorem targeted_trace_80 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5] 1541931035 556349453 := by
  exact ⟨2312896553, by decide, ⟨1734672415, by decide, ⟨2602008623, by decide, ⟨3903012935, by decide, ⟨5854519403, by decide, ⟨8781779105, by decide, ⟨6586334329, by decide, ⟨4939750747, by decide, ⟨7409626121, by decide, ⟨5557219591, by decide, ⟨8335829387, by decide, ⟨12503744081, by decide, ⟨9377808061, by decide, ⟨3516678023, by decide, ⟨5275017035, by decide, ⟨7912525553, by decide, ⟨5934394165, by decide, ⟨556349453, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_80 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5] (1541931035 + q * 2 ^ 31) endpoint ∧ endpoint < 1541931035 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5] targeted_trace_80 (by decide) (by decide) (by decide) q
#print axioms targeted_class_80

theorem targeted_trace_81 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5] 421003291 303807299 := by
  exact ⟨631504937, by decide, ⟨473628703, by decide, ⟨710443055, by decide, ⟨1065664583, by decide, ⟨1598496875, by decide, ⟨2397745313, by decide, ⟨1798308985, by decide, ⟨1348731739, by decide, ⟨2023097609, by decide, ⟨1517323207, by decide, ⟨2275984811, by decide, ⟨3413977217, by decide, ⟨2560482913, by decide, ⟨1920362185, by decide, ⟨1440271639, by decide, ⟨2160407459, by decide, ⟨3240611189, by decide, ⟨303807299, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_81 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5] (421003291 + q * 2 ^ 30) endpoint ∧ endpoint < 421003291 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5] targeted_trace_81 (by decide) (by decide) (by decide) q
#print axioms targeted_class_81

theorem targeted_trace_82 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6] 2031616027 733034383 := by
  exact ⟨3047424041, by decide, ⟨2285568031, by decide, ⟨3428352047, by decide, ⟨5142528071, by decide, ⟨7713792107, by decide, ⟨11570688161, by decide, ⟨8678016121, by decide, ⟨6508512091, by decide, ⟨9762768137, by decide, ⟨7322076103, by decide, ⟨10983114155, by decide, ⟨16474671233, by decide, ⟨12356003425, by decide, ⟨9267002569, by decide, ⟨6950251927, by decide, ⟨10425377891, by decide, ⟨15638066837, by decide, ⟨733034383, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_82 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6] (2031616027 + q * 2 ^ 31) endpoint ∧ endpoint < 2031616027 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6] targeted_trace_82 (by decide) (by decide) (by decide) q
#print axioms targeted_class_82

theorem targeted_trace_83 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 4] 60293147 38674807 := by
  exact ⟨90439721, by decide, ⟨67829791, by decide, ⟨101744687, by decide, ⟨152617031, by decide, ⟨228925547, by decide, ⟨343388321, by decide, ⟨257541241, by decide, ⟨193155931, by decide, ⟨289733897, by decide, ⟨217300423, by decide, ⟨325950635, by decide, ⟨488925953, by decide, ⟨366694465, by decide, ⟨275020849, by decide, ⟨206265637, by decide, ⟨38674807, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_83 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 4] (60293147 + q * 2 ^ 27) endpoint ∧ endpoint < 60293147 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 4] targeted_trace_83 (by decide) (by decide) (by decide) q
#print axioms targeted_class_83

theorem targeted_trace_84 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3] 949485595 685174343 := by
  exact ⟨1424228393, by decide, ⟨1068171295, by decide, ⟨1602256943, by decide, ⟨2403385415, by decide, ⟨3605078123, by decide, ⟨5407617185, by decide, ⟨4055712889, by decide, ⟨3041784667, by decide, ⟨4562677001, by decide, ⟨3422007751, by decide, ⟨5133011627, by decide, ⟨7699517441, by decide, ⟨5774638081, by decide, ⟨4330978561, by decide, ⟨3248233921, by decide, ⟨2436175441, by decide, ⟨1827131581, by decide, ⟨685174343, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_84 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3] (949485595 + q * 2 ^ 30) endpoint ∧ endpoint < 949485595 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3] targeted_trace_84 (by decide) (by decide) (by decide) q
#print axioms targeted_class_84

theorem targeted_trace_85 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4] 412614683 148876927 := by
  exact ⟨618922025, by decide, ⟨464191519, by decide, ⟨696287279, by decide, ⟨1044430919, by decide, ⟨1566646379, by decide, ⟨2349969569, by decide, ⟨1762477177, by decide, ⟨1321857883, by decide, ⟨1982786825, by decide, ⟨1487090119, by decide, ⟨2230635179, by decide, ⟨3345952769, by decide, ⟨2509464577, by decide, ⟨1882098433, by decide, ⟨1411573825, by decide, ⟨1058680369, by decide, ⟨794010277, by decide, ⟨148876927, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_85 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4] (412614683 + q * 2 ^ 31) endpoint ∧ endpoint < 412614683 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4] targeted_trace_85 (by decide) (by decide) (by decide) q
#print axioms targeted_class_85

theorem targeted_trace_86 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4] 1083703323 586522099 := by
  exact ⟨1625554985, by decide, ⟨1219166239, by decide, ⟨1828749359, by decide, ⟨2743124039, by decide, ⟨4114686059, by decide, ⟨6172029089, by decide, ⟨4629021817, by decide, ⟨3471766363, by decide, ⟨5207649545, by decide, ⟨3905737159, by decide, ⟨5858605739, by decide, ⟨8787908609, by decide, ⟨6590931457, by decide, ⟨4943198593, by decide, ⟨3707398945, by decide, ⟨2780549209, by decide, ⟨2085411907, by decide, ⟨3128117861, by decide, ⟨586522099, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_86 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4] (1083703323 + q * 2 ^ 32) endpoint ∧ endpoint < 1083703323 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4] targeted_trace_86 (by decide) (by decide) (by decide) q
#print axioms targeted_class_86

theorem targeted_trace_87 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3] 2828533787 1530859541 := by
  exact ⟨4242800681, by decide, ⟨3182100511, by decide, ⟨4773150767, by decide, ⟨7159726151, by decide, ⟨10739589227, by decide, ⟨16109383841, by decide, ⟨12082037881, by decide, ⟨9061528411, by decide, ⟨13592292617, by decide, ⟨10194219463, by decide, ⟨15291329195, by decide, ⟨22936993793, by decide, ⟨17202745345, by decide, ⟨12902059009, by decide, ⟨9676544257, by decide, ⟨7257408193, by decide, ⟨5443056145, by decide, ⟨4082292109, by decide, ⟨1530859541, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_87 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3] (2828533787 + q * 2 ^ 32) endpoint ∧ endpoint < 2828533787 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3] targeted_trace_87 (by decide) (by decide) (by decide) q
#print axioms targeted_class_87

theorem targeted_trace_88 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5] 3633840155 655569197 := by
  exact ⟨5450760233, by decide, ⟨4088070175, by decide, ⟨6132105263, by decide, ⟨9198157895, by decide, ⟨13797236843, by decide, ⟨20695855265, by decide, ⟨15521891449, by decide, ⟨11641418587, by decide, ⟨17462127881, by decide, ⟨13096595911, by decide, ⟨19644893867, by decide, ⟨29467340801, by decide, ⟨22100505601, by decide, ⟨16575379201, by decide, ⟨12431534401, by decide, ⟨9323650801, by decide, ⟨6992738101, by decide, ⟨655569197, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_88 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5] (3633840155 + q * 2 ^ 32) endpoint ∧ endpoint < 3633840155 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5] targeted_trace_88 (by decide) (by decide) (by decide) q
#print axioms targeted_class_88

theorem targeted_trace_89 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4] 848822299 459399751 := by
  exact ⟨1273233449, by decide, ⟨954925087, by decide, ⟨1432387631, by decide, ⟨2148581447, by decide, ⟨3222872171, by decide, ⟨4834308257, by decide, ⟨3625731193, by decide, ⟨2719298395, by decide, ⟨4078947593, by decide, ⟨3059210695, by decide, ⟨4588816043, by decide, ⟨6883224065, by decide, ⟨5162418049, by decide, ⟨3871813537, by decide, ⟨2903860153, by decide, ⟨2177895115, by decide, ⟨3266842673, by decide, ⟨2450132005, by decide, ⟨459399751, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_89 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4] (848822299 + q * 2 ^ 32) endpoint ∧ endpoint < 848822299 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4] targeted_trace_89 (by decide) (by decide) (by decide) q
#print axioms targeted_class_89

theorem targeted_trace_90 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3] 2593652763 1403737193 := by
  exact ⟨3890479145, by decide, ⟨2917859359, by decide, ⟨4376789039, by decide, ⟨6565183559, by decide, ⟨9847775339, by decide, ⟨14771663009, by decide, ⟨11078747257, by decide, ⟨8309060443, by decide, ⟨12463590665, by decide, ⟨9347692999, by decide, ⟨14021539499, by decide, ⟨21032309249, by decide, ⟨15774231937, by decide, ⟨11830673953, by decide, ⟨8873005465, by decide, ⟨6654754099, by decide, ⟨9982131149, by decide, ⟨3743299181, by decide, ⟨1403737193, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_90 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3] (2593652763 + q * 2 ^ 32) endpoint ∧ endpoint < 2593652763 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3] targeted_trace_90 (by decide) (by decide) (by decide) q
#print axioms targeted_class_90

theorem targeted_trace_91 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 3] 56098843 35984387 := by
  exact ⟨84148265, by decide, ⟨63111199, by decide, ⟨94666799, by decide, ⟨142000199, by decide, ⟨213000299, by decide, ⟨319500449, by decide, ⟨239625337, by decide, ⟨179719003, by decide, ⟨269578505, by decide, ⟨202183879, by decide, ⟨303275819, by decide, ⟨454913729, by decide, ⟨341185297, by decide, ⟨255888973, by decide, ⟨95958365, by decide, ⟨35984387, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_91 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 3] (56098843 + q * 2 ^ 27) endpoint ∧ endpoint < 56098843 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 3] targeted_trace_91 (by decide) (by decide) (by decide) q
#print axioms targeted_class_91

theorem targeted_trace_92 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4] 978845723 706361401 := by
  exact ⟨1468268585, by decide, ⟨1101201439, by decide, ⟨1651802159, by decide, ⟨2477703239, by decide, ⟨3716554859, by decide, ⟨5574832289, by decide, ⟨4181124217, by decide, ⟨3135843163, by decide, ⟨4703764745, by decide, ⟨3527823559, by decide, ⟨5291735339, by decide, ⟨7937603009, by decide, ⟨5953202257, by decide, ⟨4464901693, by decide, ⟨1674338135, by decide, ⟨2511507203, by decide, ⟨3767260805, by decide, ⟨706361401, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_92 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4] (978845723 + q * 2 ^ 30) endpoint ∧ endpoint < 978845723 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4] targeted_trace_92 (by decide) (by decide) (by decide) q
#print axioms targeted_class_92

theorem targeted_trace_93 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3] 492306459 355261583 := by
  exact ⟨738459689, by decide, ⟨553844767, by decide, ⟨830767151, by decide, ⟨1246150727, by decide, ⟨1869226091, by decide, ⟨2803839137, by decide, ⟨2102879353, by decide, ⟨1577159515, by decide, ⟨2365739273, by decide, ⟨1774304455, by decide, ⟨2661456683, by decide, ⟨3992185025, by decide, ⟨2994138769, by decide, ⟨2245604077, by decide, ⟨842101529, by decide, ⟨631576147, by decide, ⟨947364221, by decide, ⟨355261583, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_93 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3] (492306459 + q * 2 ^ 30) endpoint ∧ endpoint < 492306459 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3] targeted_trace_93 (by decide) (by decide) (by decide) q
#print axioms targeted_class_93

theorem targeted_trace_94 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5] 1515716635 546890945 := by
  exact ⟨2273574953, by decide, ⟨1705181215, by decide, ⟨2557771823, by decide, ⟨3836657735, by decide, ⟨5754986603, by decide, ⟨8632479905, by decide, ⟨6474359929, by decide, ⟨4855769947, by decide, ⟨7283654921, by decide, ⟨5462741191, by decide, ⟨8194111787, by decide, ⟨12291167681, by decide, ⟨9218375761, by decide, ⟨6913781821, by decide, ⟨2592668183, by decide, ⟨3889002275, by decide, ⟨5833503413, by decide, ⟨546890945, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_94 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5] (1515716635 + q * 2 ^ 31) endpoint ∧ endpoint < 1515716635 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5] targeted_trace_94 (by decide) (by decide) (by decide) q
#print axioms targeted_class_94

theorem targeted_trace_95 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4] 2102919195 758761525 := by
  exact ⟨3154378793, by decide, ⟨2365784095, by decide, ⟨3548676143, by decide, ⟨5323014215, by decide, ⟨7984521323, by decide, ⟨11976781985, by decide, ⟨8982586489, by decide, ⟨6736939867, by decide, ⟨10105409801, by decide, ⟨7579057351, by decide, ⟨11368586027, by decide, ⟨17052879041, by decide, ⟨12789659281, by decide, ⟨9592244461, by decide, ⟨3597091673, by decide, ⟨2697818755, by decide, ⟨4046728133, by decide, ⟨758761525, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_95 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4] (2102919195 + q * 2 ^ 31) endpoint ∧ endpoint < 2102919195 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4] targeted_trace_95 (by decide) (by decide) (by decide) q
#print axioms targeted_class_95

theorem targeted_trace_96 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4] 274202651 148404007 := by
  exact ⟨411303977, by decide, ⟨308477983, by decide, ⟨462716975, by decide, ⟨694075463, by decide, ⟨1041113195, by decide, ⟨1561669793, by decide, ⟨1171252345, by decide, ⟨878439259, by decide, ⟨1317658889, by decide, ⟨988244167, by decide, ⟨1482366251, by decide, ⟨2223549377, by decide, ⟨1667662033, by decide, ⟨1250746525, by decide, ⟨469029947, by decide, ⟨703544921, by decide, ⟨527658691, by decide, ⟨791488037, by decide, ⟨148404007, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_96 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4] (274202651 + q * 2 ^ 32) endpoint ∧ endpoint < 274202651 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4] targeted_trace_96 (by decide) (by decide) (by decide) q
#print axioms targeted_class_96

theorem targeted_trace_97 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3] 2019033115 1092741449 := by
  exact ⟨3028549673, by decide, ⟨2271412255, by decide, ⟨3407118383, by decide, ⟨5110677575, by decide, ⟨7666016363, by decide, ⟨11499024545, by decide, ⟨8624268409, by decide, ⟨6468201307, by decide, ⟨9702301961, by decide, ⟨7276726471, by decide, ⟨10915089707, by decide, ⟨16372634561, by decide, ⟨12279475921, by decide, ⟨9209606941, by decide, ⟨3453602603, by decide, ⟨5180403905, by decide, ⟨3885302929, by decide, ⟨2913977197, by decide, ⟨1092741449, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_97 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3] (2019033115 + q * 2 ^ 32) endpoint ∧ endpoint < 2019033115 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3] targeted_trace_97 (by decide) (by decide) (by decide) q
#print axioms targeted_class_97

theorem targeted_trace_98 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3] 1784152091 965619101 := by
  exact ⟨2676228137, by decide, ⟨2007171103, by decide, ⟨3010756655, by decide, ⟨4516134983, by decide, ⟨6774202475, by decide, ⟨10161303713, by decide, ⟨7620977785, by decide, ⟨5715733339, by decide, ⟨8573600009, by decide, ⟨6430200007, by decide, ⟨9645300011, by decide, ⟨14467950017, by decide, ⟨10850962513, by decide, ⟨8138221885, by decide, ⟨3051833207, by decide, ⟨4577749811, by decide, ⟨6866624717, by decide, ⟨2574984269, by decide, ⟨965619101, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_98 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3] (1784152091 + q * 2 ^ 32) endpoint ∧ endpoint < 1784152091 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3] targeted_trace_98 (by decide) (by decide) (by decide) q
#print axioms targeted_class_98

theorem targeted_trace_99 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6] 2589458459 467155717 := by
  exact ⟨3884187689, by decide, ⟨2913140767, by decide, ⟨4369711151, by decide, ⟨6554566727, by decide, ⟨9831850091, by decide, ⟨14747775137, by decide, ⟨11060831353, by decide, ⟨8295623515, by decide, ⟨12443435273, by decide, ⟨9332576455, by decide, ⟨13998864683, by decide, ⟨20998297025, by decide, ⟨15748722769, by decide, ⟨11811542077, by decide, ⟨4429328279, by decide, ⟨6643992419, by decide, ⟨9965988629, by decide, ⟨467155717, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_99 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6] (2589458459 + q * 2 ^ 32) endpoint ∧ endpoint < 2589458459 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6] targeted_trace_99 (by decide) (by decide) (by decide) q
#print axioms targeted_class_99

theorem targeted_trace_100 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5] 1314390043 711374405 := by
  exact ⟨1971585065, by decide, ⟨1478688799, by decide, ⟨2218033199, by decide, ⟨3327049799, by decide, ⟨4990574699, by decide, ⟨7485862049, by decide, ⟨5614396537, by decide, ⟨4210797403, by decide, ⟨6316196105, by decide, ⟨4737147079, by decide, ⟨7105720619, by decide, ⟨10658580929, by decide, ⟨7993935697, by decide, ⟨5995451773, by decide, ⟨2248294415, by decide, ⟨3372441623, by decide, ⟨5058662435, by decide, ⟨7587993653, by decide, ⟨711374405, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_100 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5] (1314390043 + q * 2 ^ 32) endpoint ∧ endpoint < 1314390043 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5] targeted_trace_100 (by decide) (by decide) (by decide) q
#print axioms targeted_class_100

theorem targeted_trace_101 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4] 943194139 680634259 := by
  exact ⟨1414791209, by decide, ⟨1061093407, by decide, ⟨1591640111, by decide, ⟨2387460167, by decide, ⟨3581190251, by decide, ⟨5371785377, by decide, ⟨4028839033, by decide, ⟨3021629275, by decide, ⟨4532443913, by decide, ⟨3399332935, by decide, ⟨5098999403, by decide, ⟨7648499105, by decide, ⟨5736374329, by decide, ⟨4302280747, by decide, ⟨6453421121, by decide, ⟨4840065841, by decide, ⟨3630049381, by decide, ⟨680634259, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_101 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4] (943194139 + q * 2 ^ 30) endpoint ∧ endpoint < 943194139 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4] targeted_trace_101 (by decide) (by decide) (by decide) q
#print axioms targeted_class_101

theorem targeted_trace_102 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5] 825753627 595886027 := by
  exact ⟨1238630441, by decide, ⟨928972831, by decide, ⟨1393459247, by decide, ⟨2090188871, by decide, ⟨3135283307, by decide, ⟨4702924961, by decide, ⟨3527193721, by decide, ⟨2645395291, by decide, ⟨3968092937, by decide, ⟨2976069703, by decide, ⟨4464104555, by decide, ⟨6696156833, by decide, ⟨5022117625, by decide, ⟨3766588219, by decide, ⟨5649882329, by decide, ⟨4237411747, by decide, ⟨6356117621, by decide, ⟨595886027, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_102 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5] (825753627 + q * 2 ^ 30) endpoint ∧ endpoint < 825753627 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5] targeted_trace_102 (by decide) (by decide) (by decide) q
#print axioms targeted_class_102

theorem targeted_trace_103 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5] 406323227 146606885 := by
  exact ⟨609484841, by decide, ⟨457113631, by decide, ⟨685670447, by decide, ⟨1028505671, by decide, ⟨1542758507, by decide, ⟨2314137761, by decide, ⟨1735603321, by decide, ⟨1301702491, by decide, ⟨1952553737, by decide, ⟨1464415303, by decide, ⟨2196622955, by decide, ⟨3294934433, by decide, ⟨2471200825, by decide, ⟨1853400619, by decide, ⟨2780100929, by decide, ⟨2085075697, by decide, ⟨1563806773, by decide, ⟨146606885, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_103 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5] (406323227 + q * 2 ^ 31) endpoint ∧ endpoint < 406323227 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5] targeted_trace_103 (by decide) (by decide) (by decide) q
#print axioms targeted_class_103

theorem targeted_trace_104 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6] 288882715 104232769 := by
  exact ⟨433324073, by decide, ⟨324993055, by decide, ⟨487489583, by decide, ⟨731234375, by decide, ⟨1096851563, by decide, ⟨1645277345, by decide, ⟨1233958009, by decide, ⟨925468507, by decide, ⟨1388202761, by decide, ⟨1041152071, by decide, ⟨1561728107, by decide, ⟨2342592161, by decide, ⟨1756944121, by decide, ⟨1317708091, by decide, ⟨1976562137, by decide, ⟨1482421603, by decide, ⟨2223632405, by decide, ⟨104232769, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_104 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6] (288882715 + q * 2 ^ 31) endpoint ∧ endpoint < 288882715 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6] targeted_trace_104 (by decide) (by decide) (by decide) q
#print axioms targeted_class_104

theorem targeted_trace_105 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 5] 62390299 40020017 := by
  exact ⟨93585449, by decide, ⟨70189087, by decide, ⟨105283631, by decide, ⟨157925447, by decide, ⟨236888171, by decide, ⟨355332257, by decide, ⟨266499193, by decide, ⟨199874395, by decide, ⟨299811593, by decide, ⟨224858695, by decide, ⟨337288043, by decide, ⟨505932065, by decide, ⟨379449049, by decide, ⟨284586787, by decide, ⟨426880181, by decide, ⟨40020017, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_105 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 5] (62390299 + q * 2 ^ 27) endpoint ∧ endpoint < 62390299 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 5] targeted_trace_105 (by decide) (by decide) (by decide) q
#print axioms targeted_class_105

theorem targeted_trace_106 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3] 280494107 202412093 := by
  exact ⟨420741161, by decide, ⟨315555871, by decide, ⟨473333807, by decide, ⟨710000711, by decide, ⟨1065001067, by decide, ⟨1597501601, by decide, ⟨1198126201, by decide, ⟨898594651, by decide, ⟨1347891977, by decide, ⟨1010918983, by decide, ⟨1516378475, by decide, ⟨2274567713, by decide, ⟨1705925785, by decide, ⟨1279444339, by decide, ⟨1919166509, by decide, ⟨719687441, by decide, ⟨539765581, by decide, ⟨202412093, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_106 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3] (280494107 + q * 2 ^ 30) endpoint ∧ endpoint < 280494107 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3] targeted_trace_106 (by decide) (by decide) (by decide) q
#print axioms targeted_class_106

theorem targeted_trace_107 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4] 817365019 294916291 := by
  exact ⟨1226047529, by decide, ⟨919535647, by decide, ⟨1379303471, by decide, ⟨2068955207, by decide, ⟨3103432811, by decide, ⟨4655149217, by decide, ⟨3491361913, by decide, ⟨2618521435, by decide, ⟨3927782153, by decide, ⟨2945836615, by decide, ⟨4418754923, by decide, ⟨6628132385, by decide, ⟨4971099289, by decide, ⟨3728324467, by decide, ⟨5592486701, by decide, ⟨2097182513, by decide, ⟨1572886885, by decide, ⟨294916291, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_107 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4] (817365019 + q * 2 ^ 31) endpoint ∧ endpoint < 817365019 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4] targeted_trace_107 (by decide) (by decide) (by decide) q
#print axioms targeted_class_107

theorem targeted_trace_108 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3] 3233284123 1749918587 := by
  exact ⟨4849926185, by decide, ⟨3637444639, by decide, ⟨5456166959, by decide, ⟨8184250439, by decide, ⟨12276375659, by decide, ⟨18414563489, by decide, ⟨13810922617, by decide, ⟨10358191963, by decide, ⟨15537287945, by decide, ⟨11652965959, by decide, ⟨17479448939, by decide, ⟨26219173409, by decide, ⟨19664380057, by decide, ⟨14748285043, by decide, ⟨22122427565, by decide, ⟨8295910337, by decide, ⟨6221932753, by decide, ⟨4666449565, by decide, ⟨1749918587, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_108 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3] (3233284123 + q * 2 ^ 32) endpoint ∧ endpoint < 3233284123 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3] targeted_trace_108 (by decide) (by decide) (by decide) q
#print axioms targeted_class_108

theorem targeted_trace_109 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5] 4038590491 728588879 := by
  exact ⟨6057885737, by decide, ⟨4543414303, by decide, ⟨6815121455, by decide, ⟨10222682183, by decide, ⟨15334023275, by decide, ⟨23001034913, by decide, ⟨17250776185, by decide, ⟨12938082139, by decide, ⟨19407123209, by decide, ⟨14555342407, by decide, ⟨21833013611, by decide, ⟨32749520417, by decide, ⟨24562140313, by decide, ⟨18421605235, by decide, ⟨27632407853, by decide, ⟨10362152945, by decide, ⟨7771614709, by decide, ⟨728588879, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_109 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5] (4038590491 + q * 2 ^ 32) endpoint ∧ endpoint < 4038590491 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5] targeted_trace_109 (by decide) (by decide) (by decide) q
#print axioms targeted_class_109

theorem targeted_trace_110 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4] 1488453659 805581145 := by
  exact ⟨2232680489, by decide, ⟨1674510367, by decide, ⟨2511765551, by decide, ⟨3767648327, by decide, ⟨5651472491, by decide, ⟨8477208737, by decide, ⟨6357906553, by decide, ⟨4768429915, by decide, ⟨7152644873, by decide, ⟨5364483655, by decide, ⟨8046725483, by decide, ⟨12070088225, by decide, ⟨9052566169, by decide, ⟨6789424627, by decide, ⟨10184136941, by decide, ⟨3819051353, by decide, ⟨2864288515, by decide, ⟨4296432773, by decide, ⟨805581145, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_110 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4] (1488453659 + q * 2 ^ 32) endpoint ∧ endpoint < 1488453659 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4] targeted_trace_110 (by decide) (by decide) (by decide) q
#print axioms targeted_class_110

theorem targeted_trace_111 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3] 2998403099 1622796239 := by
  exact ⟨4497604649, by decide, ⟨3373203487, by decide, ⟨5059805231, by decide, ⟨7589707847, by decide, ⟨11384561771, by decide, ⟨17076842657, by decide, ⟨12807631993, by decide, ⟨9605723995, by decide, ⟨14408585993, by decide, ⟨10806439495, by decide, ⟨16209659243, by decide, ⟨24314488865, by decide, ⟨18235866649, by decide, ⟨13676899987, by decide, ⟨20515349981, by decide, ⟨7693256243, by decide, ⟨11539884365, by decide, ⟨4327456637, by decide, ⟨1622796239, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_111 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3] (2998403099 + q * 2 ^ 32) endpoint ∧ endpoint < 2998403099 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3] targeted_trace_111 (by decide) (by decide) (by decide) q
#print axioms targeted_class_111

theorem targeted_trace_112 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4] 1253572635 678458797 := by
  exact ⟨1880358953, by decide, ⟨1410269215, by decide, ⟨2115403823, by decide, ⟨3173105735, by decide, ⟨4759658603, by decide, ⟨7139487905, by decide, ⟨5354615929, by decide, ⟨4015961947, by decide, ⟨6023942921, by decide, ⟨4517957191, by decide, ⟨6776935787, by decide, ⟨10165403681, by decide, ⟨7624052761, by decide, ⟨5718039571, by decide, ⟨8577059357, by decide, ⟨3216397259, by decide, ⟨4824595889, by decide, ⟨3618446917, by decide, ⟨678458797, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_112 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4] (1253572635 + q * 2 ^ 32) endpoint ∧ endpoint < 1253572635 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4] targeted_trace_112 (by decide) (by decide) (by decide) q
#print axioms targeted_class_112

theorem targeted_trace_113 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5] 2528641051 1368551543 := by
  exact ⟨3792961577, by decide, ⟨2844721183, by decide, ⟨4267081775, by decide, ⟨6400622663, by decide, ⟨9600933995, by decide, ⟨14401400993, by decide, ⟨10801050745, by decide, ⟨8100788059, by decide, ⟨12151182089, by decide, ⟨9113386567, by decide, ⟨13670079851, by decide, ⟨20505119777, by decide, ⟨15378839833, by decide, ⟨11534129875, by decide, ⟨17301194813, by decide, ⟨6487948055, by decide, ⟨9731922083, by decide, ⟨14597883125, by decide, ⟨1368551543, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_113 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5] (2528641051 + q * 2 ^ 32) endpoint ∧ endpoint < 2528641051 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5] targeted_trace_113 (by decide) (by decide) (by decide) q
#print axioms targeted_class_113

theorem targeted_trace_114 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4] 855113755 617073085 := by
  exact ⟨1282670633, by decide, ⟨962002975, by decide, ⟨1443004463, by decide, ⟨2164506695, by decide, ⟨3246760043, by decide, ⟨4870140065, by decide, ⟨3652605049, by decide, ⟨2739453787, by decide, ⟨4109180681, by decide, ⟨3081885511, by decide, ⟨4622828267, by decide, ⟨6934242401, by decide, ⟨5200681801, by decide, ⟨3900511351, by decide, ⟨5850767027, by decide, ⟨8776150541, by decide, ⟨3291056453, by decide, ⟨617073085, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_114 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4] (855113755 + q * 2 ^ 30) endpoint ∧ endpoint < 855113755 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4] targeted_trace_114 (by decide) (by decide) (by decide) q
#print axioms targeted_class_114

theorem targeted_trace_115 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5] 1391984667 502246787 := by
  exact ⟨2087977001, by decide, ⟨1565982751, by decide, ⟨2348974127, by decide, ⟨3523461191, by decide, ⟨5285191787, by decide, ⟨7927787681, by decide, ⟨5945840761, by decide, ⟨4459380571, by decide, ⟨6689070857, by decide, ⟨5016803143, by decide, ⟨7525204715, by decide, ⟨11287807073, by decide, ⟨8465855305, by decide, ⟨6349391479, by decide, ⟨9524087219, by decide, ⟨14286130829, by decide, ⟨5357299061, by decide, ⟨502246787, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_115 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5] (1391984667 + q * 2 ^ 31) endpoint ∧ endpoint < 1391984667 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5] targeted_trace_115 (by decide) (by decide) (by decide) q
#print axioms targeted_class_115

theorem targeted_trace_116 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3] 1040449563 750816389 := by
  exact ⟨1560674345, by decide, ⟨1170505759, by decide, ⟨1755758639, by decide, ⟨2633637959, by decide, ⟨3950456939, by decide, ⟨5925685409, by decide, ⟨4444264057, by decide, ⟨3333198043, by decide, ⟨4999797065, by decide, ⟨3749847799, by decide, ⟨5624771699, by decide, ⟨8437157549, by decide, ⟨3163934081, by decide, ⟨2372950561, by decide, ⟨1779712921, by decide, ⟨1334784691, by decide, ⟨2002177037, by decide, ⟨750816389, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_116 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3] (1040449563 + q * 2 ^ 30) endpoint ∧ endpoint < 1040449563 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3] targeted_trace_116 (by decide) (by decide) (by decide) q
#print axioms targeted_class_116

theorem targeted_trace_117 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4] 453247003 327075229 := by
  exact ⟨679870505, by decide, ⟨509902879, by decide, ⟨764854319, by decide, ⟨1147281479, by decide, ⟨1720922219, by decide, ⟨2581383329, by decide, ⟨1936037497, by decide, ⟨1452028123, by decide, ⟨2178042185, by decide, ⟨1633531639, by decide, ⟨2450297459, by decide, ⟨3675446189, by decide, ⟨1378292321, by decide, ⟨1033719241, by decide, ⟨775289431, by decide, ⟨1162934147, by decide, ⟨1744401221, by decide, ⟨327075229, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_117 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4] (453247003 + q * 2 ^ 30) endpoint ∧ endpoint < 453247003 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4] targeted_trace_117 (by decide) (by decide) (by decide) q
#print axioms targeted_class_117

theorem targeted_trace_118 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4] 1577320475 569118439 := by
  exact ⟨2365980713, by decide, ⟨1774485535, by decide, ⟨2661728303, by decide, ⟨3992592455, by decide, ⟨5988888683, by decide, ⟨8983333025, by decide, ⟨6737499769, by decide, ⟨5053124827, by decide, ⟨7579687241, by decide, ⟨5684765431, by decide, ⟨8527148147, by decide, ⟨12790722221, by decide, ⟨4796520833, by decide, ⟨3597390625, by decide, ⟨2698042969, by decide, ⟨2023532227, by decide, ⟨3035298341, by decide, ⟨569118439, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_118 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4] (1577320475 + q * 2 ^ 31) endpoint ∧ endpoint < 1577320475 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4] targeted_trace_118 (by decide) (by decide) (by decide) q
#print axioms targeted_class_118

theorem targeted_trace_119 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5] 990117915 357247859 := by
  exact ⟨1485176873, by decide, ⟨1113882655, by decide, ⟨1670823983, by decide, ⟨2506235975, by decide, ⟨3759353963, by decide, ⟨5639030945, by decide, ⟨4229273209, by decide, ⟨3171954907, by decide, ⟨4757932361, by decide, ⟨3568449271, by decide, ⟨5352673907, by decide, ⟨8029010861, by decide, ⟨3010879073, by decide, ⟨2258159305, by decide, ⟨1693619479, by decide, ⟨2540429219, by decide, ⟨3810643829, by decide, ⟨357247859, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_119 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5] (990117915 + q * 2 ^ 31) endpoint ∧ endpoint < 990117915 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5] targeted_trace_119 (by decide) (by decide) (by decide) q
#print axioms targeted_class_119

theorem targeted_trace_120 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3] 3993239579 2161221809 := by
  exact ⟨5989859369, by decide, ⟨4492394527, by decide, ⟨6738591791, by decide, ⟨10107887687, by decide, ⟨15161831531, by decide, ⟨22742747297, by decide, ⟨17057060473, by decide, ⟨12792795355, by decide, ⟨19189193033, by decide, ⟨14391894775, by decide, ⟨21587842163, by decide, ⟨32381763245, by decide, ⟨12143161217, by decide, ⟨9107370913, by decide, ⟨6830528185, by decide, ⟨5122896139, by decide, ⟨7684344209, by decide, ⟨5763258157, by decide, ⟨2161221809, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_120 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3] (3993239579 + q * 2 ^ 32) endpoint ∧ endpoint < 3993239579 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3] targeted_trace_120 (by decide) (by decide) (by decide) q
#print axioms targeted_class_120

theorem targeted_trace_121 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5] 503578651 90848975 := by
  exact ⟨755367977, by decide, ⟨566525983, by decide, ⟨849788975, by decide, ⟨1274683463, by decide, ⟨1912025195, by decide, ⟨2868037793, by decide, ⟨2151028345, by decide, ⟨1613271259, by decide, ⟨2419906889, by decide, ⟨1814930167, by decide, ⟨2722395251, by decide, ⟨4083592877, by decide, ⟨1531347329, by decide, ⟨1148510497, by decide, ⟨861382873, by decide, ⟨646037155, by decide, ⟨969055733, by decide, ⟨90848975, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_121 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5] (503578651 + q * 2 ^ 32) endpoint ∧ endpoint < 503578651 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5] targeted_trace_121 (by decide) (by decide) (by decide) q
#print axioms targeted_class_121

theorem targeted_trace_122 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4] 1896087579 1026200845 := by
  exact ⟨2844131369, by decide, ⟨2133098527, by decide, ⟨3199647791, by decide, ⟨4799471687, by decide, ⟨7199207531, by decide, ⟨10798811297, by decide, ⟨8099108473, by decide, ⟨6074331355, by decide, ⟨9111497033, by decide, ⟨6833622775, by decide, ⟨10250434163, by decide, ⟨15375651245, by decide, ⟨5765869217, by decide, ⟨4324401913, by decide, ⟨3243301435, by decide, ⟨4864952153, by decide, ⟨3648714115, by decide, ⟨5473071173, by decide, ⟨1026200845, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_122 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4] (1896087579 + q * 2 ^ 32) endpoint ∧ endpoint < 1896087579 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4] targeted_trace_122 (by decide) (by decide) (by decide) q
#print axioms targeted_class_122

theorem targeted_trace_123 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3] 3640918043 1970538287 := by
  exact ⟨5461377065, by decide, ⟨4096032799, by decide, ⟨6144049199, by decide, ⟨9216073799, by decide, ⟨13824110699, by decide, ⟨20736166049, by decide, ⟨15552124537, by decide, ⟨11664093403, by decide, ⟨17496140105, by decide, ⟨13122105079, by decide, ⟨19683157619, by decide, ⟨29524736429, by decide, ⟨11071776161, by decide, ⟨8303832121, by decide, ⟨6227874091, by decide, ⟨9341811137, by decide, ⟨7006358353, by decide, ⟨5254768765, by decide, ⟨1970538287, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_123 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3] (3640918043 + q * 2 ^ 32) endpoint ∧ endpoint < 3640918043 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3] targeted_trace_123 (by decide) (by decide) (by decide) q
#print axioms targeted_class_123

theorem targeted_trace_124 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4] 1661206555 899078497 := by
  exact ⟨2491809833, by decide, ⟨1868857375, by decide, ⟨2803286063, by decide, ⟨4204929095, by decide, ⟨6307393643, by decide, ⟨9461090465, by decide, ⟨7095817849, by decide, ⟨5321863387, by decide, ⟨7982795081, by decide, ⟨5987096311, by decide, ⟨8980644467, by decide, ⟨13470966701, by decide, ⟨5051612513, by decide, ⟨3788709385, by decide, ⟨2841532039, by decide, ⟨4262298059, by decide, ⟨6393447089, by decide, ⟨4795085317, by decide, ⟨899078497, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_124 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4] (1661206555 + q * 2 ^ 32) endpoint ∧ endpoint < 1661206555 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4] targeted_trace_124 (by decide) (by decide) (by decide) q
#print axioms targeted_class_124

theorem targeted_trace_125 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3] 3406037019 1843415939 := by
  exact ⟨5109055529, by decide, ⟨3831791647, by decide, ⟨5747687471, by decide, ⟨8621531207, by decide, ⟨12932296811, by decide, ⟨19398445217, by decide, ⟨14548833913, by decide, ⟨10911625435, by decide, ⟨16367438153, by decide, ⟨12275578615, by decide, ⟨18413367923, by decide, ⟨27620051885, by decide, ⟨10357519457, by decide, ⟨7768139593, by decide, ⟨5826104695, by decide, ⟨8739157043, by decide, ⟨13108735565, by decide, ⟨4915775837, by decide, ⟨1843415939, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_125 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3] (3406037019 + q * 2 ^ 32) endpoint ∧ endpoint < 3406037019 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3] targeted_trace_125 (by decide) (by decide) (by decide) q
#print axioms targeted_class_125

theorem targeted_trace_126 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6] 4211343387 759754663 := by
  exact ⟨6317015081, by decide, ⟨4737761311, by decide, ⟨7106641967, by decide, ⟨10659962951, by decide, ⟨15989944427, by decide, ⟨23984916641, by decide, ⟨17988687481, by decide, ⟨13491515611, by decide, ⟨20237273417, by decide, ⟨15177955063, by decide, ⟨22766932595, by decide, ⟨34150398893, by decide, ⟨12806399585, by decide, ⟨9604799689, by decide, ⟨7203599767, by decide, ⟨10805399651, by decide, ⟨16208099477, by decide, ⟨759754663, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_126 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6] (4211343387 + q * 2 ^ 32) endpoint ∧ endpoint < 4211343387 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6] targeted_trace_126 (by decide) (by decide) (by decide) q
#print axioms targeted_class_126

theorem targeted_trace_127 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3] 423886875 305888171 := by
  exact ⟨635830313, by decide, ⟨476872735, by decide, ⟨715309103, by decide, ⟨1072963655, by decide, ⟨1609445483, by decide, ⟨2414168225, by decide, ⟨1810626169, by decide, ⟨1357969627, by decide, ⟨2036954441, by decide, ⟨1527715831, by decide, ⟨2291573747, by decide, ⟨3437360621, by decide, ⟨1289010233, by decide, ⟨966757675, by decide, ⟨1450136513, by decide, ⟨1087602385, by decide, ⟨815701789, by decide, ⟨305888171, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_127 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3] (423886875 + q * 2 ^ 30) endpoint ∧ endpoint < 423886875 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3] targeted_trace_127 (by decide) (by decide) (by decide) q
#print axioms targeted_class_127

theorem targeted_trace_128 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4] 2034499611 734074819 := by
  exact ⟨3051749417, by decide, ⟨2288812063, by decide, ⟨3433218095, by decide, ⟨5149827143, by decide, ⟨7724740715, by decide, ⟨11587111073, by decide, ⟨8690333305, by decide, ⟨6517749979, by decide, ⟨9776624969, by decide, ⟨7332468727, by decide, ⟨10998703091, by decide, ⟨16498054637, by decide, ⟨6186770489, by decide, ⟨4640077867, by decide, ⟨6960116801, by decide, ⟨5220087601, by decide, ⟨3915065701, by decide, ⟨734074819, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_128 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4] (2034499611 + q * 2 ^ 31) endpoint ∧ endpoint < 2034499611 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4] targeted_trace_128 (by decide) (by decide) (by decide) q
#print axioms targeted_class_128

theorem targeted_trace_129 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4] 3057909787 1655002459 := by
  exact ⟨4586864681, by decide, ⟨3440148511, by decide, ⟨5160222767, by decide, ⟨7740334151, by decide, ⟨11610501227, by decide, ⟨17415751841, by decide, ⟨13061813881, by decide, ⟨9796360411, by decide, ⟨14694540617, by decide, ⟨11020905463, by decide, ⟨16531358195, by decide, ⟨24797037293, by decide, ⟨9298888985, by decide, ⟨6974166739, by decide, ⟨10461250109, by decide, ⟨3922968791, by decide, ⟨5884453187, by decide, ⟨8826679781, by decide, ⟨1655002459, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_129 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4] (3057909787 + q * 2 ^ 32) endpoint ∧ endpoint < 3057909787 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4] targeted_trace_129 (by decide) (by decide) (by decide) q
#print axioms targeted_class_129

theorem targeted_trace_130 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3] 507772955 274816967 := by
  exact ⟨761659433, by decide, ⟨571244575, by decide, ⟨856866863, by decide, ⟨1285300295, by decide, ⟨1927950443, by decide, ⟨2891925665, by decide, ⟨2168944249, by decide, ⟨1626708187, by decide, ⟨2440062281, by decide, ⟨1830046711, by decide, ⟨2745070067, by decide, ⟨4117605101, by decide, ⟨1544101913, by decide, ⟨1158076435, by decide, ⟨1737114653, by decide, ⟨651417995, by decide, ⟨977126993, by decide, ⟨732845245, by decide, ⟨274816967, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_130 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3] (507772955 + q * 2 ^ 32) endpoint ∧ endpoint < 507772955 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3] targeted_trace_130 (by decide) (by decide) (by decide) q
#print axioms targeted_class_130

theorem targeted_trace_131 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4] 2705588251 1464318937 := by
  exact ⟨4058382377, by decide, ⟨3043786783, by decide, ⟨4565680175, by decide, ⟨6848520263, by decide, ⟨10272780395, by decide, ⟨15409170593, by decide, ⟨11556877945, by decide, ⟨8667658459, by decide, ⟨13001487689, by decide, ⟨9751115767, by decide, ⟨14626673651, by decide, ⟨21940010477, by decide, ⟨8227503929, by decide, ⟨6170627947, by decide, ⟨9255941921, by decide, ⟨6941956441, by decide, ⟨5206467331, by decide, ⟨7809700997, by decide, ⟨1464318937, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_131 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4] (2705588251 + q * 2 ^ 32) endpoint ∧ endpoint < 2705588251 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4] targeted_trace_131 (by decide) (by decide) (by decide) q
#print axioms targeted_class_131

theorem targeted_trace_132 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5] 960757787 173327165 := by
  exact ⟨1441136681, by decide, ⟨1080852511, by decide, ⟨1621278767, by decide, ⟨2431918151, by decide, ⟨3647877227, by decide, ⟨5471815841, by decide, ⟨4103861881, by decide, ⟨3077896411, by decide, ⟨4616844617, by decide, ⟨3462633463, by decide, ⟨5193950195, by decide, ⟨7790925293, by decide, ⟨2921596985, by decide, ⟨2191197739, by decide, ⟨3286796609, by decide, ⟨2465097457, by decide, ⟨1848823093, by decide, ⟨173327165, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_132 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5] (960757787 + q * 2 ^ 32) endpoint ∧ endpoint < 960757787 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5] targeted_trace_132 (by decide) (by decide) (by decide) q
#print axioms targeted_class_132

theorem targeted_trace_133 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4] 2470707227 1337196589 := by
  exact ⟨3706060841, by decide, ⟨2779545631, by decide, ⟨4169318447, by decide, ⟨6253977671, by decide, ⟨9380966507, by decide, ⟨14071449761, by decide, ⟨10553587321, by decide, ⟨7915190491, by decide, ⟨11872785737, by decide, ⟨8904589303, by decide, ⟨13356883955, by decide, ⟨20035325933, by decide, ⟨7513247225, by decide, ⟨5634935419, by decide, ⟨8452403129, by decide, ⟨6339302347, by decide, ⟨9508953521, by decide, ⟨7131715141, by decide, ⟨1337196589, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_133 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4] (2470707227 + q * 2 ^ 32) endpoint ∧ endpoint < 2470707227 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4] targeted_trace_133 (by decide) (by decide) (by decide) q
#print axioms targeted_class_133

theorem targeted_trace_134 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3] 4215537691 2281534031 := by
  exact ⟨6323306537, by decide, ⟨4742479903, by decide, ⟨7113719855, by decide, ⟨10670579783, by decide, ⟨16005869675, by decide, ⟨24008804513, by decide, ⟨18006603385, by decide, ⟨13504952539, by decide, ⟨20257428809, by decide, ⟨15193071607, by decide, ⟨22789607411, by decide, ⟨34184411117, by decide, ⟨12819154169, by decide, ⟨9614365627, by decide, ⟨14421548441, by decide, ⟨10816161331, by decide, ⟨16224241997, by decide, ⟨6084090749, by decide, ⟨2281534031, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_134 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3] (4215537691 + q * 2 ^ 32) endpoint ∧ endpoint < 4215537691 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3] targeted_trace_134 (by decide) (by decide) (by decide) q
#print axioms targeted_class_134

theorem targeted_trace_135 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5] 969146395 699362105 := by
  exact ⟨1453719593, by decide, ⟨1090289695, by decide, ⟨1635434543, by decide, ⟨2453151815, by decide, ⟨3679727723, by decide, ⟨5519591585, by decide, ⟨4139693689, by decide, ⟨3104770267, by decide, ⟨4657155401, by decide, ⟨3492866551, by decide, ⟨5239299827, by decide, ⟨7858949741, by decide, ⟨2947106153, by decide, ⟨2210329615, by decide, ⟨3315494423, by decide, ⟨4973241635, by decide, ⟨7459862453, by decide, ⟨699362105, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_135 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5] (969146395 + q * 2 ^ 30) endpoint ∧ endpoint < 969146395 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5] targeted_trace_135 (by decide) (by decide) (by decide) q
#print axioms targeted_class_135

theorem targeted_trace_136 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6] 1506017307 543391297 := by
  exact ⟨2259025961, by decide, ⟨1694269471, by decide, ⟨2541404207, by decide, ⟨3812106311, by decide, ⟨5718159467, by decide, ⟨8577239201, by decide, ⟨6432929401, by decide, ⟨4824697051, by decide, ⟨7237045577, by decide, ⟨5427784183, by decide, ⟨8141676275, by decide, ⟨12212514413, by decide, ⟨4579692905, by decide, ⟨3434769679, by decide, ⟨5152154519, by decide, ⟨7728231779, by decide, ⟨11592347669, by decide, ⟨543391297, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_136 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6] (1506017307 + q * 2 ^ 31) endpoint ∧ endpoint < 1506017307 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6] targeted_trace_136 (by decide) (by decide) (by decide) q
#print axioms targeted_class_136

theorem targeted_trace_137 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 3] 61079579 39179261 := by
  exact ⟨91619369, by decide, ⟨68714527, by decide, ⟨103071791, by decide, ⟨154607687, by decide, ⟨231911531, by decide, ⟨347867297, by decide, ⟨260900473, by decide, ⟨195675355, by decide, ⟨293513033, by decide, ⟨220134775, by decide, ⟨330202163, by decide, ⟨495303245, by decide, ⟨185738717, by decide, ⟨69652019, by decide, ⟨104478029, by decide, ⟨39179261, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_137 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 3] (61079579 + q * 2 ^ 27) endpoint ∧ endpoint < 61079579 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 3] targeted_trace_137 (by decide) (by decide) (by decide) q
#print axioms targeted_class_137

theorem targeted_trace_138 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4] 312737819 225680023 := by
  exact ⟨469106729, by decide, ⟨351830047, by decide, ⟨527745071, by decide, ⟨791617607, by decide, ⟨1187426411, by decide, ⟨1781139617, by decide, ⟨1335854713, by decide, ⟨1001891035, by decide, ⟨1502836553, by decide, ⟨1127127415, by decide, ⟨1690691123, by decide, ⟨2536036685, by decide, ⟨951013757, by decide, ⟨356630159, by decide, ⟨534945239, by decide, ⟨802417859, by decide, ⟨1203626789, by decide, ⟨225680023, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_138 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4] (312737819 + q * 2 ^ 30) endpoint ∧ endpoint < 312737819 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4] targeted_trace_138 (by decide) (by decide) (by decide) q
#print axioms targeted_class_138

theorem targeted_trace_139 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3] 899940379 649421183 := by
  exact ⟨1349910569, by decide, ⟨1012432927, by decide, ⟨1518649391, by decide, ⟨2277974087, by decide, ⟨3416961131, by decide, ⟨5125441697, by decide, ⟨3844081273, by decide, ⟨2883060955, by decide, ⟨4324591433, by decide, ⟨3243443575, by decide, ⟨4865165363, by decide, ⟨7297748045, by decide, ⟨2736655517, by decide, ⟨1026245819, by decide, ⟨1539368729, by decide, ⟨1154526547, by decide, ⟨1731789821, by decide, ⟨649421183, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_139 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3] (899940379 + q * 2 ^ 30) endpoint ∧ endpoint < 899940379 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3] targeted_trace_139 (by decide) (by decide) (by decide) q
#print axioms targeted_class_139

theorem targeted_trace_140 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5] 1923350555 693970745 := by
  exact ⟨2885025833, by decide, ⟨2163769375, by decide, ⟨3245654063, by decide, ⟨4868481095, by decide, ⟨7302721643, by decide, ⟨10954082465, by decide, ⟨8215561849, by decide, ⟨6161671387, by decide, ⟨9242507081, by decide, ⟨6931880311, by decide, ⟨10397820467, by decide, ⟨15596730701, by decide, ⟨5848774013, by decide, ⟨2193290255, by decide, ⟨3289935383, by decide, ⟨4934903075, by decide, ⟨7402354613, by decide, ⟨693970745, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_140 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5] (1923350555 + q * 2 ^ 31) endpoint ∧ endpoint < 1923350555 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5] targeted_trace_140 (by decide) (by decide) (by decide) q
#print axioms targeted_class_140

theorem targeted_trace_141 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4] 363069467 131000347 := by
  exact ⟨544604201, by decide, ⟨408453151, by decide, ⟨612679727, by decide, ⟨919019591, by decide, ⟨1378529387, by decide, ⟨2067794081, by decide, ⟨1550845561, by decide, ⟨1163134171, by decide, ⟨1744701257, by decide, ⟨1308525943, by decide, ⟨1962788915, by decide, ⟨2944183373, by decide, ⟨1104068765, by decide, ⟨414025787, by decide, ⟨621038681, by decide, ⟨465779011, by decide, ⟨698668517, by decide, ⟨131000347, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_141 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4] (363069467 + q * 2 ^ 31) endpoint ∧ endpoint < 363069467 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4] targeted_trace_141 (by decide) (by decide) (by decide) q
#print axioms targeted_class_141

theorem targeted_trace_142 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3] 2426667035 1313361149 := by
  exact ⟨3640000553, by decide, ⟨2730000415, by decide, ⟨4095000623, by decide, ⟨6142500935, by decide, ⟨9213751403, by decide, ⟨13820627105, by decide, ⟨10365470329, by decide, ⟨7774102747, by decide, ⟨11661154121, by decide, ⟨8745865591, by decide, ⟨13118798387, by decide, ⟨19678197581, by decide, ⟨7379324093, by decide, ⟨2767246535, by decide, ⟨4150869803, by decide, ⟨6226304705, by decide, ⟨4669728529, by decide, ⟨3502296397, by decide, ⟨1313361149, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_142 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3] (2426667035 + q * 2 ^ 32) endpoint ∧ endpoint < 2426667035 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3] targeted_trace_142 (by decide) (by decide) (by decide) q
#print axioms targeted_class_142

theorem targeted_trace_143 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4] 681836571 369023707 := by
  exact ⟨1022754857, by decide, ⟨767066143, by decide, ⟨1150599215, by decide, ⟨1725898823, by decide, ⟨2588848235, by decide, ⟨3883272353, by decide, ⟨2912454265, by decide, ⟨2184340699, by decide, ⟨3276511049, by decide, ⟨2457383287, by decide, ⟨3686074931, by decide, ⟨5529112397, by decide, ⟨2073417149, by decide, ⟨777531431, by decide, ⟨1166297147, by decide, ⟨1749445721, by decide, ⟨1312084291, by decide, ⟨1968126437, by decide, ⟨369023707, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_143 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4] (681836571 + q * 2 ^ 32) endpoint ∧ endpoint < 681836571 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4] targeted_trace_143 (by decide) (by decide) (by decide) q
#print axioms targeted_class_143

theorem targeted_trace_144 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6] 2997092379 540695617 := by
  exact ⟨4495638569, by decide, ⟨3371728927, by decide, ⟨5057593391, by decide, ⟨7586390087, by decide, ⟨11379585131, by decide, ⟨17069377697, by decide, ⟨12802033273, by decide, ⟨9601524955, by decide, ⟨14402287433, by decide, ⟨10801715575, by decide, ⟨16202573363, by decide, ⟨24303860045, by decide, ⟨9113947517, by decide, ⟨3417730319, by decide, ⟨5126595479, by decide, ⟨7689893219, by decide, ⟨11534839829, by decide, ⟨540695617, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_144 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6] (2997092379 + q * 2 ^ 32) endpoint ∧ endpoint < 2997092379 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6] targeted_trace_144 (by decide) (by decide) (by decide) q
#print axioms targeted_class_144

theorem targeted_trace_145 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4] 446955547 241901359 := by
  exact ⟨670433321, by decide, ⟨502824991, by decide, ⟨754237487, by decide, ⟨1131356231, by decide, ⟨1697034347, by decide, ⟨2545551521, by decide, ⟨1909163641, by decide, ⟨1431872731, by decide, ⟨2147809097, by decide, ⟨1610856823, by decide, ⟨2416285235, by decide, ⟨3624427853, by decide, ⟨1359160445, by decide, ⟨509685167, by decide, ⟨764527751, by decide, ⟨1146791627, by decide, ⟨1720187441, by decide, ⟨1290140581, by decide, ⟨241901359, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_145 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4] (446955547 + q * 2 ^ 32) endpoint ∧ endpoint < 446955547 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4] targeted_trace_145 (by decide) (by decide) (by decide) q
#print axioms targeted_class_145

theorem targeted_trace_146 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5] 1722023963 931994105 := by
  exact ⟨2583035945, by decide, ⟨1937276959, by decide, ⟨2905915439, by decide, ⟨4358873159, by decide, ⟨6538309739, by decide, ⟨9807464609, by decide, ⟨7355598457, by decide, ⟨5516698843, by decide, ⟨8275048265, by decide, ⟨6206286199, by decide, ⟨9309429299, by decide, ⟨13964143949, by decide, ⟨5236553981, by decide, ⟨1963707743, by decide, ⟨2945561615, by decide, ⟨4418342423, by decide, ⟨6627513635, by decide, ⟨9941270453, by decide, ⟨931994105, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_146 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5] (1722023963 + q * 2 ^ 32) endpoint ∧ endpoint < 1722023963 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5] targeted_trace_146 (by decide) (by decide) (by decide) q
#print axioms targeted_class_146

theorem targeted_trace_147 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5] 907280411 654717947 := by
  exact ⟨1360920617, by decide, ⟨1020690463, by decide, ⟨1531035695, by decide, ⟨2296553543, by decide, ⟨3444830315, by decide, ⟨5167245473, by decide, ⟨3875434105, by decide, ⟨2906575579, by decide, ⟨4359863369, by decide, ⟨3269897527, by decide, ⟨4904846291, by decide, ⟨7357269437, by decide, ⟨2758976039, by decide, ⟨4138464059, by decide, ⟨6207696089, by decide, ⟨4655772067, by decide, ⟨6983658101, by decide, ⟨654717947, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_147 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5] (907280411 + q * 2 ^ 30) endpoint ∧ endpoint < 907280411 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5] targeted_trace_147 (by decide) (by decide) (by decide) q
#print axioms targeted_class_147

theorem targeted_trace_148 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4] 1024720923 739466179 := by
  exact ⟨1537081385, by decide, ⟨1152811039, by decide, ⟨1729216559, by decide, ⟨2593824839, by decide, ⟨3890737259, by decide, ⟨5836105889, by decide, ⟨4377079417, by decide, ⟨3282809563, by decide, ⟨4924214345, by decide, ⟨3693160759, by decide, ⟨5539741139, by decide, ⟨8309611709, by decide, ⟨3116104391, by decide, ⟨4674156587, by decide, ⟨7011234881, by decide, ⟨5258426161, by decide, ⟨3943819621, by decide, ⟨739466179, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_148 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4] (1024720923 + q * 2 ^ 30) endpoint ∧ endpoint < 1024720923 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4] targeted_trace_148 (by decide) (by decide) (by decide) q
#print axioms targeted_class_148

theorem targeted_trace_149 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6] 370409499 133648729 := by
  exact ⟨555614249, by decide, ⟨416710687, by decide, ⟨625066031, by decide, ⟨937599047, by decide, ⟨1406398571, by decide, ⟨2109597857, by decide, ⟨1582198393, by decide, ⟨1186648795, by decide, ⟨1779973193, by decide, ⟨1334979895, by decide, ⟨2002469843, by decide, ⟨3003704765, by decide, ⟨1126389287, by decide, ⟨1689583931, by decide, ⟨2534375897, by decide, ⟨1900781923, by decide, ⟨2851172885, by decide, ⟨133648729, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_149 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6] (370409499 + q * 2 ^ 31) endpoint ∧ endpoint < 370409499 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6] targeted_trace_149 (by decide) (by decide) (by decide) q
#print axioms targeted_class_149

theorem targeted_trace_150 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3] 362020891 261244013 := by
  exact ⟨543031337, by decide, ⟨407273503, by decide, ⟨610910255, by decide, ⟨916365383, by decide, ⟨1374548075, by decide, ⟨2061822113, by decide, ⟨1546366585, by decide, ⟨1159774939, by decide, ⟨1739662409, by decide, ⟨1304746807, by decide, ⟨1957120211, by decide, ⟨2935680317, by decide, ⟨1100880119, by decide, ⟨1651320179, by decide, ⟨2476980269, by decide, ⟨928867601, by decide, ⟨696650701, by decide, ⟨261244013, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_150 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3] (362020891 + q * 2 ^ 30) endpoint ∧ endpoint < 362020891 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3] targeted_trace_150 (by decide) (by decide) (by decide) q
#print axioms targeted_class_150

theorem targeted_trace_151 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4] 898891803 324332251 := by
  exact ⟨1348337705, by decide, ⟨1011253279, by decide, ⟨1516879919, by decide, ⟨2275319879, by decide, ⟨3412979819, by decide, ⟨5119469729, by decide, ⟨3839602297, by decide, ⟨2879701723, by decide, ⟨4319552585, by decide, ⟨3239664439, by decide, ⟨4859496659, by decide, ⟨7289244989, by decide, ⟨2733466871, by decide, ⟨4100200307, by decide, ⟨6150300461, by decide, ⟨2306362673, by decide, ⟨1729772005, by decide, ⟨324332251, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_151 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4] (898891803 + q * 2 ^ 31) endpoint ∧ endpoint < 898891803 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4] targeted_trace_151 (by decide) (by decide) (by decide) q
#print axioms targeted_class_151

theorem targeted_trace_152 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4] 1922301979 1040388607 := by
  exact ⟨2883452969, by decide, ⟨2162589727, by decide, ⟨3243884591, by decide, ⟨4865826887, by decide, ⟨7298740331, by decide, ⟨10948110497, by decide, ⟨8211082873, by decide, ⟨6158312155, by decide, ⟨9237468233, by decide, ⟨6928101175, by decide, ⟨10392151763, by decide, ⟨15588227645, by decide, ⟨5845585367, by decide, ⟨8768378051, by decide, ⟨13152567077, by decide, ⟨2466106327, by decide, ⟨3699159491, by decide, ⟨5548739237, by decide, ⟨1040388607, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_152 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4] (1922301979 + q * 2 ^ 32) endpoint ∧ endpoint < 1922301979 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4] targeted_trace_152 (by decide) (by decide) (by decide) q
#print axioms targeted_class_152

theorem targeted_trace_153 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3] 3667132443 1984726049 := by
  exact ⟨5500698665, by decide, ⟨4125523999, by decide, ⟨6188285999, by decide, ⟨9282428999, by decide, ⟨13923643499, by decide, ⟨20885465249, by decide, ⟨15664098937, by decide, ⟨11748074203, by decide, ⟨17622111305, by decide, ⟨13216583479, by decide, ⟨19824875219, by decide, ⟨29737312829, by decide, ⟨11151492311, by decide, ⟨16727238467, by decide, ⟨25090857701, by decide, ⟨4704535819, by decide, ⟨7056803729, by decide, ⟨5292602797, by decide, ⟨1984726049, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_153 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3] (3667132443 + q * 2 ^ 32) endpoint ∧ endpoint < 3667132443 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3] targeted_trace_153 (by decide) (by decide) (by decide) q
#print axioms targeted_class_153

theorem targeted_trace_154 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3] 3314810907 1794042527 := by
  exact ⟨4972216361, by decide, ⟨3729162271, by decide, ⟨5593743407, by decide, ⟨8390615111, by decide, ⟨12585922667, by decide, ⟨18878884001, by decide, ⟨14159163001, by decide, ⟨10619372251, by decide, ⟨15929058377, by decide, ⟨11946793783, by decide, ⟨17920190675, by decide, ⟨26880286013, by decide, ⟨10080107255, by decide, ⟨15120160883, by decide, ⟨22680241325, by decide, ⟨8505090497, by decide, ⟨6378817873, by decide, ⟨4784113405, by decide, ⟨1794042527, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_154 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3] (3314810907 + q * 2 ^ 32) endpoint ∧ endpoint < 3314810907 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3] targeted_trace_154 (by decide) (by decide) (by decide) q
#print axioms targeted_class_154

theorem targeted_trace_155 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5] 4120117275 743296859 := by
  exact ⟨6180175913, by decide, ⟨4635131935, by decide, ⟨6952697903, by decide, ⟨10429046855, by decide, ⟨15643570283, by decide, ⟨23465355425, by decide, ⟨17599016569, by decide, ⟨13199262427, by decide, ⟨19798893641, by decide, ⟨14849170231, by decide, ⟨22273755347, by decide, ⟨33410633021, by decide, ⟨12528987383, by decide, ⟨18793481075, by decide, ⟨28190221613, by decide, ⟨10571333105, by decide, ⟨7928499829, by decide, ⟨743296859, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_155 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5] (4120117275 + q * 2 ^ 32) endpoint ∧ endpoint < 4120117275 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5] targeted_trace_155 (by decide) (by decide) (by decide) q
#print axioms targeted_class_155

theorem targeted_trace_156 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4] 1569980443 849705085 := by
  exact ⟨2354970665, by decide, ⟨1766227999, by decide, ⟨2649341999, by decide, ⟨3974012999, by decide, ⟨5961019499, by decide, ⟨8941529249, by decide, ⟨6706146937, by decide, ⟨5029610203, by decide, ⟨7544415305, by decide, ⟨5658311479, by decide, ⟨8487467219, by decide, ⟨12731200829, by decide, ⟨4774200311, by decide, ⟨7161300467, by decide, ⟨10741950701, by decide, ⟨4028231513, by decide, ⟨3021173635, by decide, ⟨4531760453, by decide, ⟨849705085, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_156 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4] (1569980443 + q * 2 ^ 32) endpoint ∧ endpoint < 1569980443 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4] targeted_trace_156 (by decide) (by decide) (by decide) q
#print axioms targeted_class_156

theorem targeted_trace_157 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5] 2610167835 1412675483 := by
  exact ⟨3915251753, by decide, ⟨2936438815, by decide, ⟨4404658223, by decide, ⟨6606987335, by decide, ⟨9910481003, by decide, ⟨14865721505, by decide, ⟨11149291129, by decide, ⟨8361968347, by decide, ⟨12542952521, by decide, ⟨9407214391, by decide, ⟨14110821587, by decide, ⟨21166232381, by decide, ⟨7937337143, by decide, ⟨11906005715, by decide, ⟨17859008573, by decide, ⟨6697128215, by decide, ⟨10045692323, by decide, ⟨15068538485, by decide, ⟨1412675483, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_157 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5] (2610167835 + q * 2 ^ 32) endpoint ∧ endpoint < 2610167835 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5] targeted_trace_157 (by decide) (by decide) (by decide) q
#print axioms targeted_class_157

theorem targeted_trace_158 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5] 819200027 591156773 := by
  exact ⟨1228800041, by decide, ⟨921600031, by decide, ⟨1382400047, by decide, ⟨2073600071, by decide, ⟨3110400107, by decide, ⟨4665600161, by decide, ⟨3499200121, by decide, ⟨2624400091, by decide, ⟨3936600137, by decide, ⟨2952450103, by decide, ⟨4428675155, by decide, ⟨6643012733, by decide, ⟨2491129775, by decide, ⟨3736694663, by decide, ⟨5605041995, by decide, ⟨8407562993, by decide, ⟨6305672245, by decide, ⟨591156773, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_158 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5] (819200027 + q * 2 ^ 30) endpoint ∧ endpoint < 819200027 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5] targeted_trace_158 (by decide) (by decide) (by decide) q
#print axioms targeted_class_158

theorem targeted_trace_159 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4] 936640539 675905005 := by
  exact ⟨1404960809, by decide, ⟨1053720607, by decide, ⟨1580580911, by decide, ⟨2370871367, by decide, ⟨3556307051, by decide, ⟨5334460577, by decide, ⟨4000845433, by decide, ⟨3000634075, by decide, ⟨4500951113, by decide, ⟨3375713335, by decide, ⟨5063570003, by decide, ⟨7595355005, by decide, ⟨2848258127, by decide, ⟨4272387191, by decide, ⟨6408580787, by decide, ⟨9612871181, by decide, ⟨3604826693, by decide, ⟨675905005, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_159 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4] (936640539 + q * 2 ^ 30) endpoint ∧ endpoint < 936640539 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4] targeted_trace_159 (by decide) (by decide) (by decide) q
#print axioms targeted_class_159

theorem targeted_trace_160 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6] 1356070939 489288631 := by
  exact ⟨2034106409, by decide, ⟨1525579807, by decide, ⟨2288369711, by decide, ⟨3432554567, by decide, ⟨5148831851, by decide, ⟨7723247777, by decide, ⟨5792435833, by decide, ⟨4344326875, by decide, ⟨6516490313, by decide, ⟨4887367735, by decide, ⟨7331051603, by decide, ⟨10996577405, by decide, ⟨4123716527, by decide, ⟨6185574791, by decide, ⟨9278362187, by decide, ⟨13917543281, by decide, ⟨10438157461, by decide, ⟨489288631, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_160 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6] (1356070939 + q * 2 ^ 31) endpoint ∧ endpoint < 1356070939 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6] targeted_trace_160 (by decide) (by decide) (by decide) q
#print axioms targeted_class_160

theorem targeted_trace_161 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4] 1060372507 765193321 := by
  exact ⟨1590558761, by decide, ⟨1192919071, by decide, ⟨1789378607, by decide, ⟨2684067911, by decide, ⟨4026101867, by decide, ⟨6039152801, by decide, ⟨4529364601, by decide, ⟨3397023451, by decide, ⟨5095535177, by decide, ⟨3821651383, by decide, ⟨5732477075, by decide, ⟨8598715613, by decide, ⟨3224518355, by decide, ⟨4836777533, by decide, ⟨1813791575, by decide, ⟨2720687363, by decide, ⟨4081031045, by decide, ⟨765193321, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_161 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4] (1060372507 + q * 2 ^ 30) endpoint ∧ endpoint < 1060372507 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4] targeted_trace_161 (by decide) (by decide) (by decide) q
#print axioms targeted_class_161

theorem targeted_trace_162 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5] 1597243419 576306905 := by
  exact ⟨2395865129, by decide, ⟨1796898847, by decide, ⟨2695348271, by decide, ⟨4043022407, by decide, ⟨6064533611, by decide, ⟨9096800417, by decide, ⟨6822600313, by decide, ⟨5116950235, by decide, ⟨7675425353, by decide, ⟨5756569015, by decide, ⟨8634853523, by decide, ⟨12952280285, by decide, ⟨4857105107, by decide, ⟨7285657661, by decide, ⟨2732121623, by decide, ⟨4098182435, by decide, ⟨6147273653, by decide, ⟨576306905, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_162 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5] (1597243419 + q * 2 ^ 31) endpoint ∧ endpoint < 1597243419 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5] targeted_trace_162 (by decide) (by decide) (by decide) q
#print axioms targeted_class_162

theorem targeted_trace_163 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3] 2452881435 1327548911 := by
  exact ⟨3679322153, by decide, ⟨2759491615, by decide, ⟨4139237423, by decide, ⟨6208856135, by decide, ⟨9313284203, by decide, ⟨13969926305, by decide, ⟨10477444729, by decide, ⟨7858083547, by decide, ⟨11787125321, by decide, ⟨8840343991, by decide, ⟨13260515987, by decide, ⟨19890773981, by decide, ⟨7459040243, by decide, ⟨11188560365, by decide, ⟨4195710137, by decide, ⟨3146782603, by decide, ⟨4720173905, by decide, ⟨3540130429, by decide, ⟨1327548911, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_163 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3] (2452881435 + q * 2 ^ 32) endpoint ∧ endpoint < 2452881435 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3] targeted_trace_163 (by decide) (by decide) (by decide) q
#print axioms targeted_class_163

theorem targeted_trace_164 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4] 708050971 383211469 := by
  exact ⟨1062076457, by decide, ⟨796557343, by decide, ⟨1194836015, by decide, ⟨1792254023, by decide, ⟨2688381035, by decide, ⟨4032571553, by decide, ⟨3024428665, by decide, ⟨2268321499, by decide, ⟨3402482249, by decide, ⟨2551861687, by decide, ⟨3827792531, by decide, ⟨5741688797, by decide, ⟨2153133299, by decide, ⟨3229699949, by decide, ⟨1211137481, by decide, ⟨908353111, by decide, ⟨1362529667, by decide, ⟨2043794501, by decide, ⟨383211469, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_164 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4] (708050971 + q * 2 ^ 32) endpoint ∧ endpoint < 708050971 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4] targeted_trace_164 (by decide) (by decide) (by decide) q
#print axioms targeted_class_164

theorem targeted_trace_165 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4] 355729435 192527947 := by
  exact ⟨533594153, by decide, ⟨400195615, by decide, ⟨600293423, by decide, ⟨900440135, by decide, ⟨1350660203, by decide, ⟨2025990305, by decide, ⟨1519492729, by decide, ⟨1139619547, by decide, ⟨1709429321, by decide, ⟨1282071991, by decide, ⟨1923107987, by decide, ⟨2884661981, by decide, ⟨1081748243, by decide, ⟨1622622365, by decide, ⟨608483387, by decide, ⟨912725081, by decide, ⟨684543811, by decide, ⟨1026815717, by decide, ⟨192527947, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_165 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4] (355729435 + q * 2 ^ 32) endpoint ∧ endpoint < 355729435 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4] targeted_trace_165 (by decide) (by decide) (by decide) q
#print axioms targeted_class_165

theorem targeted_trace_166 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3] 2100559899 1136865389 := by
  exact ⟨3150839849, by decide, ⟨2363129887, by decide, ⟨3544694831, by decide, ⟨5317042247, by decide, ⟨7975563371, by decide, ⟨11963345057, by decide, ⟨8972508793, by decide, ⟨6729381595, by decide, ⟨10094072393, by decide, ⟨7570554295, by decide, ⟨11355831443, by decide, ⟨17033747165, by decide, ⟨6387655187, by decide, ⟨9581482781, by decide, ⟨3593056043, by decide, ⟨5389584065, by decide, ⟨4042188049, by decide, ⟨3031641037, by decide, ⟨1136865389, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_166 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3] (2100559899 + q * 2 ^ 32) endpoint ∧ endpoint < 2100559899 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3] targeted_trace_166 (by decide) (by decide) (by decide) q
#print axioms targeted_class_166

theorem targeted_trace_167 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5] 1395916827 755498345 := by
  exact ⟨2093875241, by decide, ⟨1570406431, by decide, ⟨2355609647, by decide, ⟨3533414471, by decide, ⟨5300121707, by decide, ⟨7950182561, by decide, ⟨5962636921, by decide, ⟨4471977691, by decide, ⟨6707966537, by decide, ⟨5030974903, by decide, ⟨7546462355, by decide, ⟨11319693533, by decide, ⟨4244885075, by decide, ⟨6367327613, by decide, ⟨2387747855, by decide, ⟨3581621783, by decide, ⟨5372432675, by decide, ⟨8058649013, by decide, ⟨755498345, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_167 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5] (1395916827 + q * 2 ^ 32) endpoint ∧ endpoint < 1395916827 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5] targeted_trace_167 (by decide) (by decide) (by decide) q
#print axioms targeted_class_167

theorem targeted_trace_168 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3] 309592091 223409981 := by
  exact ⟨464388137, by decide, ⟨348291103, by decide, ⟨522436655, by decide, ⟨783654983, by decide, ⟨1175482475, by decide, ⟨1763223713, by decide, ⟨1322417785, by decide, ⟨991813339, by decide, ⟨1487720009, by decide, ⟨1115790007, by decide, ⟨1673685011, by decide, ⟨2510527517, by decide, ⟨941447819, by decide, ⟨1412171729, by decide, ⟨1059128797, by decide, ⟨397173299, by decide, ⟨595759949, by decide, ⟨223409981, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_168 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3] (309592091 + q * 2 ^ 30) endpoint ∧ endpoint < 309592091 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3] targeted_trace_168 (by decide) (by decide) (by decide) q
#print axioms targeted_class_168

theorem targeted_trace_169 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3] 1031012379 744006263 := by
  exact ⟨1546518569, by decide, ⟨1159888927, by decide, ⟨1739833391, by decide, ⟨2609750087, by decide, ⟨3914625131, by decide, ⟨5871937697, by decide, ⟨4403953273, by decide, ⟨3302964955, by decide, ⟨4954447433, by decide, ⟨3715835575, by decide, ⟨5573753363, by decide, ⟨8360630045, by decide, ⟨3135236267, by decide, ⟨4702854401, by decide, ⟨3527140801, by decide, ⟨2645355601, by decide, ⟨1984016701, by decide, ⟨744006263, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_169 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3] (1031012379 + q * 2 ^ 30) endpoint ∧ endpoint < 1031012379 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3] targeted_trace_169 (by decide) (by decide) (by decide) q
#print axioms targeted_class_169

theorem targeted_trace_170 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4] 846463003 305415235 := by
  exact ⟨1269694505, by decide, ⟨952270879, by decide, ⟨1428406319, by decide, ⟨2142609479, by decide, ⟨3213914219, by decide, ⟨4820871329, by decide, ⟨3615653497, by decide, ⟨2711740123, by decide, ⟨4067610185, by decide, ⟨3050707639, by decide, ⟨4576061459, by decide, ⟨6864092189, by decide, ⟨2574034571, by decide, ⟨3861051857, by decide, ⟨2895788893, by decide, ⟨1085920835, by decide, ⟨1628881253, by decide, ⟨305415235, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_170 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4] (846463003 + q * 2 ^ 31) endpoint ∧ endpoint < 846463003 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4] targeted_trace_170 (by decide) (by decide) (by decide) q
#print axioms targeted_class_170

theorem targeted_trace_171 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4] 494141467 178292887 := by
  exact ⟨741212201, by decide, ⟨555909151, by decide, ⟨833863727, by decide, ⟨1250795591, by decide, ⟨1876193387, by decide, ⟨2814290081, by decide, ⟨2110717561, by decide, ⟨1583038171, by decide, ⟨2374557257, by decide, ⟨1780917943, by decide, ⟨2671376915, by decide, ⟨4007065373, by decide, ⟨1502649515, by decide, ⟨2253974273, by decide, ⟨1690480705, by decide, ⟨1267860529, by decide, ⟨950895397, by decide, ⟨178292887, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_171 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4] (494141467 + q * 2 ^ 31) endpoint ∧ endpoint < 494141467 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4] targeted_trace_171 (by decide) (by decide) (by decide) q
#print axioms targeted_class_171

theorem targeted_trace_172 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3] 3262382107 1765667003 := by
  exact ⟨4893573161, by decide, ⟨3670179871, by decide, ⟨5505269807, by decide, ⟨8257904711, by decide, ⟨12386857067, by decide, ⟨18580285601, by decide, ⟨13935214201, by decide, ⟨10451410651, by decide, ⟨15677115977, by decide, ⟨11757836983, by decide, ⟨17636755475, by decide, ⟨26455133213, by decide, ⟨9920674955, by decide, ⟨14881012433, by decide, ⟨11160759325, by decide, ⟨4185284747, by decide, ⟨6277927121, by decide, ⟨4708445341, by decide, ⟨1765667003, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_172 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3] (3262382107 + q * 2 ^ 32) endpoint ∧ endpoint < 3262382107 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3] targeted_trace_172 (by decide) (by decide) (by decide) q
#print axioms targeted_class_172

theorem targeted_trace_173 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5] 4067688475 733838351 := by
  exact ⟨6101532713, by decide, ⟨4576149535, by decide, ⟨6864224303, by decide, ⟨10296336455, by decide, ⟨15444504683, by decide, ⟨23166757025, by decide, ⟨17375067769, by decide, ⟨13031300827, by decide, ⟨19546951241, by decide, ⟨14660213431, by decide, ⟨21990320147, by decide, ⟨32985480221, by decide, ⟨12369555083, by decide, ⟨18554332625, by decide, ⟨13915749469, by decide, ⟨5218406051, by decide, ⟨7827609077, by decide, ⟨733838351, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_173 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5] (4067688475 + q * 2 ^ 32) endpoint ∧ endpoint < 4067688475 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5] targeted_trace_173 (by decide) (by decide) (by decide) q
#print axioms targeted_class_173

theorem targeted_trace_174 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4] 1517551643 821329561 := by
  exact ⟨2276327465, by decide, ⟨1707245599, by decide, ⟨2560868399, by decide, ⟨3841302599, by decide, ⟨5761953899, by decide, ⟨8642930849, by decide, ⟨6482198137, by decide, ⟨4861648603, by decide, ⟨7292472905, by decide, ⟨5469354679, by decide, ⟨8204032019, by decide, ⟨12306048029, by decide, ⟨4614768011, by decide, ⟨6922152017, by decide, ⟨5191614013, by decide, ⟨1946855255, by decide, ⟨2920282883, by decide, ⟨4380424325, by decide, ⟨821329561, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_174 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4] (1517551643 + q * 2 ^ 32) endpoint ∧ endpoint < 1517551643 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4] targeted_trace_174 (by decide) (by decide) (by decide) q
#print axioms targeted_class_174

theorem targeted_trace_175 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4] 1165230107 630646039 := by
  exact ⟨1747845161, by decide, ⟨1310883871, by decide, ⟨1966325807, by decide, ⟨2949488711, by decide, ⟨4424233067, by decide, ⟨6636349601, by decide, ⟨4977262201, by decide, ⟨3732946651, by decide, ⟨5599419977, by decide, ⟨4199564983, by decide, ⟨6299347475, by decide, ⟨9449021213, by decide, ⟨3543382955, by decide, ⟨5315074433, by decide, ⟨3986305825, by decide, ⟨2989729369, by decide, ⟨2242297027, by decide, ⟨3363445541, by decide, ⟨630646039, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_175 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4] (1165230107 + q * 2 ^ 32) endpoint ∧ endpoint < 1165230107 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4] targeted_trace_175 (by decide) (by decide) (by decide) q
#print axioms targeted_class_175

theorem targeted_trace_176 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3] 2910060571 1574983481 := by
  exact ⟨4365090857, by decide, ⟨3273818143, by decide, ⟨4910727215, by decide, ⟨7366090823, by decide, ⟨11049136235, by decide, ⟨16573704353, by decide, ⟨12430278265, by decide, ⟨9322708699, by decide, ⟨13984063049, by decide, ⟨10488047287, by decide, ⟨15732070931, by decide, ⟨23598106397, by decide, ⟨8849289899, by decide, ⟨13273934849, by decide, ⟨9955451137, by decide, ⟨7466588353, by decide, ⟨5599941265, by decide, ⟨4199955949, by decide, ⟨1574983481, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_176 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3] (2910060571 + q * 2 ^ 32) endpoint ∧ endpoint < 2910060571 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3] targeted_trace_176 (by decide) (by decide) (by decide) q
#print axioms targeted_class_176

theorem targeted_trace_177 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5] 3715366939 670277177 := by
  exact ⟨5573050409, by decide, ⟨4179787807, by decide, ⟨6269681711, by decide, ⟨9404522567, by decide, ⟨14106783851, by decide, ⟨21160175777, by decide, ⟨15870131833, by decide, ⟨11902598875, by decide, ⟨17853898313, by decide, ⟨13390423735, by decide, ⟨20085635603, by decide, ⟨30128453405, by decide, ⟨11298170027, by decide, ⟨16947255041, by decide, ⟨12710441281, by decide, ⟨9532830961, by decide, ⟨7149623221, by decide, ⟨670277177, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_177 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5] (3715366939 + q * 2 ^ 32) endpoint ∧ endpoint < 3715366939 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5] targeted_trace_177 (by decide) (by decide) (by decide) q
#print axioms targeted_class_177

theorem targeted_trace_178 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3] 854851611 616883915 := by
  exact ⟨1282277417, by decide, ⟨961708063, by decide, ⟨1442562095, by decide, ⟨2163843143, by decide, ⟨3245764715, by decide, ⟨4868647073, by decide, ⟨3651485305, by decide, ⟨2738613979, by decide, ⟨4107920969, by decide, ⟨3080940727, by decide, ⟨4621411091, by decide, ⟨6932116637, by decide, ⟨2599543739, by decide, ⟨3899315609, by decide, ⟨2924486707, by decide, ⟨4386730061, by decide, ⟨1645023773, by decide, ⟨616883915, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_178 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3] (854851611 + q * 2 ^ 30) endpoint ∧ endpoint < 854851611 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3] targeted_trace_178 (by decide) (by decide) (by decide) q
#print axioms targeted_class_178

theorem targeted_trace_179 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5] 502530075 362639219 := by
  exact ⟨753795113, by decide, ⟨565346335, by decide, ⟨848019503, by decide, ⟨1272029255, by decide, ⟨1908043883, by decide, ⟨2862065825, by decide, ⟨2146549369, by decide, ⟨1609912027, by decide, ⟨2414868041, by decide, ⟨1811151031, by decide, ⟨2716726547, by decide, ⟨4075089821, by decide, ⟨1528158683, by decide, ⟨2292238025, by decide, ⟨1719178519, by decide, ⟨2578767779, by decide, ⟨3868151669, by decide, ⟨362639219, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_179 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5] (502530075 + q * 2 ^ 30) endpoint ∧ endpoint < 502530075 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5] targeted_trace_179 (by decide) (by decide) (by decide) q
#print axioms targeted_class_179

theorem targeted_trace_180 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4] 317980699 114731713 := by
  exact ⟨476971049, by decide, ⟨357728287, by decide, ⟨536592431, by decide, ⟨804888647, by decide, ⟨1207332971, by decide, ⟨1810999457, by decide, ⟨1358249593, by decide, ⟨1018687195, by decide, ⟨1528030793, by decide, ⟨1146023095, by decide, ⟨1719034643, by decide, ⟨2578551965, by decide, ⟨966956987, by decide, ⟨1450435481, by decide, ⟨1087826611, by decide, ⟨1631739917, by decide, ⟨611902469, by decide, ⟨114731713, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_180 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4] (317980699 + q * 2 ^ 31) endpoint ∧ endpoint < 317980699 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4] targeted_trace_180 (by decide) (by decide) (by decide) q
#print axioms targeted_class_180

theorem targeted_trace_181 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6] 2113142811 762450343 := by
  exact ⟨3169714217, by decide, ⟨2377285663, by decide, ⟨3565928495, by decide, ⟨5348892743, by decide, ⟨8023339115, by decide, ⟨12035008673, by decide, ⟨9026256505, by decide, ⟨6769692379, by decide, ⟨10154538569, by decide, ⟨7615903927, by decide, ⟨11423855891, by decide, ⟨17135783837, by decide, ⟨6425918939, by decide, ⟨9638878409, by decide, ⟨7229158807, by decide, ⟨10843738211, by decide, ⟨16265607317, by decide, ⟨762450343, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_181 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6] (2113142811 + q * 2 ^ 31) endpoint ∧ endpoint < 2113142811 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6] targeted_trace_181 (by decide) (by decide) (by decide) q
#print axioms targeted_class_181

theorem targeted_trace_182 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 3] 89915419 57675899 := by
  exact ⟨134873129, by decide, ⟨101154847, by decide, ⟨151732271, by decide, ⟨227598407, by decide, ⟨341397611, by decide, ⟨512096417, by decide, ⟨384072313, by decide, ⟨288054235, by decide, ⟨432081353, by decide, ⟨324061015, by decide, ⟨486091523, by decide, ⟨729137285, by decide, ⟨136713241, by decide, ⟨102534931, by decide, ⟨153802397, by decide, ⟨57675899, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_182 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 3] (89915419 + q * 2 ^ 27) endpoint ∧ endpoint < 89915419 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 3] targeted_trace_182 (by decide) (by decide) (by decide) q
#print axioms targeted_class_182

theorem targeted_trace_183 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4] 475791387 343343863 := by
  exact ⟨713687081, by decide, ⟨535265311, by decide, ⟨802897967, by decide, ⟨1204346951, by decide, ⟨1806520427, by decide, ⟨2709780641, by decide, ⟨2032335481, by decide, ⟨1524251611, by decide, ⟨2286377417, by decide, ⟨1714783063, by decide, ⟨2572174595, by decide, ⟨3858261893, by decide, ⟨723424105, by decide, ⟨542568079, by decide, ⟨813852119, by decide, ⟨1220778179, by decide, ⟨1831167269, by decide, ⟨343343863, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_183 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4] (475791387 + q * 2 ^ 30) endpoint ∧ endpoint < 475791387 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4] targeted_trace_183 (by decide) (by decide) (by decide) q
#print axioms targeted_class_183

theorem targeted_trace_184 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3] 1062993947 767085023 := by
  exact ⟨1594490921, by decide, ⟨1195868191, by decide, ⟨1793802287, by decide, ⟨2690703431, by decide, ⟨4036055147, by decide, ⟨6054082721, by decide, ⟨4540562041, by decide, ⟨3405421531, by decide, ⟨5108132297, by decide, ⟨3831099223, by decide, ⟨5746648835, by decide, ⟨8619973253, by decide, ⟨1616244985, by decide, ⟨1212183739, by decide, ⟨1818275609, by decide, ⟨1363706707, by decide, ⟨2045560061, by decide, ⟨767085023, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_184 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3] (1062993947 + q * 2 ^ 30) endpoint ∧ endpoint < 1062993947 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3] targeted_trace_184 (by decide) (by decide) (by decide) q
#print axioms targeted_class_184

theorem targeted_trace_185 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5] 2086404123 752802665 := by
  exact ⟨3129606185, by decide, ⟨2347204639, by decide, ⟨3520806959, by decide, ⟨5281210439, by decide, ⟨7921815659, by decide, ⟨11882723489, by decide, ⟨8912042617, by decide, ⟨6684031963, by decide, ⟨10026047945, by decide, ⟨7519535959, by decide, ⟨11279303939, by decide, ⟨16918955909, by decide, ⟨3172304233, by decide, ⟨2379228175, by decide, ⟨3568842263, by decide, ⟨5353263395, by decide, ⟨8029895093, by decide, ⟨752802665, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_185 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5] (2086404123 + q * 2 ^ 31) endpoint ∧ endpoint < 2086404123 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5] targeted_trace_185 (by decide) (by decide) (by decide) q
#print axioms targeted_class_185

theorem targeted_trace_186 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4] 526123035 189832267 := by
  exact ⟨789184553, by decide, ⟨591888415, by decide, ⟨887832623, by decide, ⟨1331748935, by decide, ⟨1997623403, by decide, ⟨2996435105, by decide, ⟨2247326329, by decide, ⟨1685494747, by decide, ⟨2528242121, by decide, ⟨1896181591, by decide, ⟨2844272387, by decide, ⟨4266408581, by decide, ⟨799951609, by decide, ⟨599963707, by decide, ⟨899945561, by decide, ⟨674959171, by decide, ⟨1012438757, by decide, ⟨189832267, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_186 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4] (526123035 + q * 2 ^ 31) endpoint ∧ endpoint < 526123035 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4] targeted_trace_186 (by decide) (by decide) (by decide) q
#print axioms targeted_class_186

theorem targeted_trace_187 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5] 1885077531 1020241985 := by
  exact ⟨2827616297, by decide, ⟨2120712223, by decide, ⟨3181068335, by decide, ⟨4771602503, by decide, ⟨7157403755, by decide, ⟨10736105633, by decide, ⟨8052079225, by decide, ⟨6039059419, by decide, ⟨9058589129, by decide, ⟨6793941847, by decide, ⟨10190912771, by decide, ⟨15286369157, by decide, ⟨2866194217, by decide, ⟨2149645663, by decide, ⟨3224468495, by decide, ⟨4836702743, by decide, ⟨7255054115, by decide, ⟨10882581173, by decide, ⟨1020241985, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_187 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5] (1885077531 + q * 2 ^ 32) endpoint ∧ endpoint < 1885077531 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5] targeted_trace_187 (by decide) (by decide) (by decide) q
#print axioms targeted_class_187

theorem targeted_trace_188 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4] 610009115 330149239 := by
  exact ⟨915013673, by decide, ⟨686260255, by decide, ⟨1029390383, by decide, ⟨1544085575, by decide, ⟨2316128363, by decide, ⟨3474192545, by decide, ⟨2605644409, by decide, ⟨1954233307, by decide, ⟨2931349961, by decide, ⟨2198512471, by decide, ⟨3297768707, by decide, ⟨4946653061, by decide, ⟨927497449, by decide, ⟨695623087, by decide, ⟨1043434631, by decide, ⟨1565151947, by decide, ⟨2347727921, by decide, ⟨1760795941, by decide, ⟨330149239, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_188 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4] (610009115 + q * 2 ^ 32) endpoint ∧ endpoint < 610009115 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4] targeted_trace_188 (by decide) (by decide) (by decide) q
#print axioms targeted_class_188

theorem targeted_trace_189 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6] 3160145947 570111577 := by
  exact ⟨4740218921, by decide, ⟨3555164191, by decide, ⟨5332746287, by decide, ⟨7999119431, by decide, ⟨11998679147, by decide, ⟨17998018721, by decide, ⟨13498514041, by decide, ⟨10123885531, by decide, ⟨15185828297, by decide, ⟨11389371223, by decide, ⟨17084056835, by decide, ⟨25626085253, by decide, ⟨4804890985, by decide, ⟨3603668239, by decide, ⟨5405502359, by decide, ⟨8108253539, by decide, ⟨12162380309, by decide, ⟨570111577, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_189 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6] (3160145947 + q * 2 ^ 32) endpoint ∧ endpoint < 3160145947 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6] targeted_trace_189 (by decide) (by decide) (by decide) q
#print axioms targeted_class_189

theorem targeted_trace_190 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4] 844890139 457271587 := by
  exact ⟨1267335209, by decide, ⟨950501407, by decide, ⟨1425752111, by decide, ⟨2138628167, by decide, ⟨3207942251, by decide, ⟨4811913377, by decide, ⟨3608935033, by decide, ⟨2706701275, by decide, ⟨4060051913, by decide, ⟨3045038935, by decide, ⟨4567558403, by decide, ⟨6851337605, by decide, ⟨1284625801, by decide, ⟨963469351, by decide, ⟨1445204027, by decide, ⟨2167806041, by decide, ⟨1625854531, by decide, ⟨2438781797, by decide, ⟨457271587, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_190 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4] (844890139 + q * 2 ^ 32) endpoint ∧ endpoint < 844890139 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4] targeted_trace_190 (by decide) (by decide) (by decide) q
#print axioms targeted_class_190

theorem targeted_trace_191 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3] 2589720603 1401609029 := by
  exact ⟨3884580905, by decide, ⟨2913435679, by decide, ⟨4370153519, by decide, ⟨6555230279, by decide, ⟨9832845419, by decide, ⟨14749268129, by decide, ⟨11061951097, by decide, ⟨8296463323, by decide, ⟨12444694985, by decide, ⟨9333521239, by decide, ⟨14000281859, by decide, ⟨21000422789, by decide, ⟨3937579273, by decide, ⟨2953184455, by decide, ⟨4429776683, by decide, ⟨6644665025, by decide, ⟨4983498769, by decide, ⟨3737624077, by decide, ⟨1401609029, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_191 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3] (2589720603 + q * 2 ^ 32) endpoint ∧ endpoint < 2589720603 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3] targeted_trace_191 (by decide) (by decide) (by decide) q
#print axioms targeted_class_191

theorem targeted_trace_192 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 3] 96206875 61711529 := by
  exact ⟨144310313, by decide, ⟨108232735, by decide, ⟨162349103, by decide, ⟨243523655, by decide, ⟨365285483, by decide, ⟨547928225, by decide, ⟨410946169, by decide, ⟨308209627, by decide, ⟨462314441, by decide, ⟨346735831, by decide, ⟨520103747, by decide, ⟨780155621, by decide, ⟨146279179, by decide, ⟨219418769, by decide, ⟨164564077, by decide, ⟨61711529, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_192 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 3] (96206875 + q * 2 ^ 27) endpoint ∧ endpoint < 96206875 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 3] targeted_trace_192 (by decide) (by decide) (by decide) q
#print axioms targeted_class_192

theorem targeted_trace_193 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3] 851181595 614235533 := by
  exact ⟨1276772393, by decide, ⟨957579295, by decide, ⟨1436368943, by decide, ⟨2154553415, by decide, ⟨3231830123, by decide, ⟨4847745185, by decide, ⟨3635808889, by decide, ⟨2726856667, by decide, ⟨4090285001, by decide, ⟨3067713751, by decide, ⟨4601570627, by decide, ⟨6902355941, by decide, ⟨1294191739, by decide, ⟨1941287609, by decide, ⟨1455965707, by decide, ⟨2183948561, by decide, ⟨1637961421, by decide, ⟨614235533, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_193 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3] (851181595 + q * 2 ^ 30) endpoint ∧ endpoint < 851181595 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3] targeted_trace_193 (by decide) (by decide) (by decide) q
#print axioms targeted_class_193

theorem targeted_trace_194 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4] 1388052507 500828011 := by
  exact ⟨2082078761, by decide, ⟨1561559071, by decide, ⟨2342338607, by decide, ⟨3513507911, by decide, ⟨5270261867, by decide, ⟨7905392801, by decide, ⟨5929044601, by decide, ⟨4446783451, by decide, ⟨6670175177, by decide, ⟨5002631383, by decide, ⟨7503947075, by decide, ⟨11255920613, by decide, ⟨2110485115, by decide, ⟨3165727673, by decide, ⟨2374295755, by decide, ⟨3561443633, by decide, ⟨2671082725, by decide, ⟨500828011, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_194 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4] (1388052507 + q * 2 ^ 31) endpoint ∧ endpoint < 1388052507 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4] targeted_trace_194 (by decide) (by decide) (by decide) q
#print axioms targeted_class_194

theorem targeted_trace_195 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5] 3099328539 1677419123 := by
  exact ⟨4648992809, by decide, ⟨3486744607, by decide, ⟨5230116911, by decide, ⟨7845175367, by decide, ⟨11767763051, by decide, ⟨17651644577, by decide, ⟨13238733433, by decide, ⟨9929050075, by decide, ⟨14893575113, by decide, ⟨11170181335, by decide, ⟨16755272003, by decide, ⟨25132908005, by decide, ⟨4712420251, by decide, ⟨7068630377, by decide, ⟨5301472783, by decide, ⟨7952209175, by decide, ⟨11928313763, by decide, ⟨17892470645, by decide, ⟨1677419123, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_195 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5] (3099328539 + q * 2 ^ 32) endpoint ∧ endpoint < 3099328539 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5] targeted_trace_195 (by decide) (by decide) (by decide) q
#print axioms targeted_class_195

theorem targeted_trace_196 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3] 3569090587 1931663819 := by
  exact ⟨5353635881, by decide, ⟨4015226911, by decide, ⟨6022840367, by decide, ⟨9034260551, by decide, ⟨13551390827, by decide, ⟨20327086241, by decide, ⟨15245314681, by decide, ⟨11433986011, by decide, ⟨17150979017, by decide, ⟨12863234263, by decide, ⟨19294851395, by decide, ⟨28942277093, by decide, ⟨5426676955, by decide, ⟨8140015433, by decide, ⟨6105011575, by decide, ⟨9157517363, by decide, ⟨13736276045, by decide, ⟨5151103517, by decide, ⟨1931663819, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_196 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3] (3569090587 + q * 2 ^ 32) endpoint ∧ endpoint < 3569090587 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3] targeted_trace_196 (by decide) (by decide) (by decide) q
#print axioms targeted_class_196

theorem targeted_trace_197 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4] 1824260123 987326377 := by
  exact ⟨2736390185, by decide, ⟨2052292639, by decide, ⟨3078438959, by decide, ⟨4617658439, by decide, ⟨6926487659, by decide, ⟨10389731489, by decide, ⟨7792298617, by decide, ⟨5844223963, by decide, ⟨8766335945, by decide, ⟨6574751959, by decide, ⟨9862127939, by decide, ⟨14793191909, by decide, ⟨2773723483, by decide, ⟨4160585225, by decide, ⟨3120438919, by decide, ⟨4680658379, by decide, ⟨7020987569, by decide, ⟨5265740677, by decide, ⟨987326377, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_197 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4] (1824260123 + q * 2 ^ 32) endpoint ∧ endpoint < 1824260123 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4] targeted_trace_197 (by decide) (by decide) (by decide) q
#print axioms targeted_class_197

theorem targeted_trace_198 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3] 3803971611 2058786167 := by
  exact ⟨5705957417, by decide, ⟨4279468063, by decide, ⟨6419202095, by decide, ⟨9628803143, by decide, ⟨14443204715, by decide, ⟨21664807073, by decide, ⟨16248605305, by decide, ⟨12186453979, by decide, ⟨18279680969, by decide, ⟨13709760727, by decide, ⟨20564641091, by decide, ⟨30846961637, by decide, ⟨5783805307, by decide, ⟨8675707961, by decide, ⟨6506780971, by decide, ⟨9760171457, by decide, ⟨7320128593, by decide, ⟨5490096445, by decide, ⟨2058786167, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_198 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3] (3803971611 + q * 2 ^ 32) endpoint ∧ endpoint < 3803971611 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3] targeted_trace_198 (by decide) (by decide) (by decide) q
#print axioms targeted_class_198

theorem targeted_trace_199 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5] 314310683 56703761 := by
  exact ⟨471466025, by decide, ⟨353599519, by decide, ⟨530399279, by decide, ⟨795598919, by decide, ⟨1193398379, by decide, ⟨1790097569, by decide, ⟨1342573177, by decide, ⟨1006929883, by decide, ⟨1510394825, by decide, ⟨1132796119, by decide, ⟨1699194179, by decide, ⟨2548791269, by decide, ⟨477898363, by decide, ⟨716847545, by decide, ⟨537635659, by decide, ⟨806453489, by decide, ⟨604840117, by decide, ⟨56703761, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_199 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5] (314310683 + q * 2 ^ 32) endpoint ∧ endpoint < 314310683 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5] targeted_trace_199 (by decide) (by decide) (by decide) q
#print axioms targeted_class_199

theorem targeted_trace_200 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3] 410779675 296429663 := by
  exact ⟨616169513, by decide, ⟨462127135, by decide, ⟨693190703, by decide, ⟨1039786055, by decide, ⟨1559679083, by decide, ⟨2339518625, by decide, ⟨1754638969, by decide, ⟨1315979227, by decide, ⟨1973968841, by decide, ⟨1480476631, by decide, ⟨2220714947, by decide, ⟨3331072421, by decide, ⟨624576079, by decide, ⟨936864119, by decide, ⟨1405296179, by decide, ⟨2107944269, by decide, ⟨790479101, by decide, ⟨296429663, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_200 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3] (410779675 + q * 2 ^ 30) endpoint ∧ endpoint < 410779675 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3] targeted_trace_200 (by decide) (by decide) (by decide) q
#print axioms targeted_class_200

theorem targeted_trace_201 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4] 2021392411 729345565 := by
  exact ⟨3032088617, by decide, ⟨2274066463, by decide, ⟨3411099695, by decide, ⟨5116649543, by decide, ⟨7674974315, by decide, ⟨11512461473, by decide, ⟨8634346105, by decide, ⟨6475759579, by decide, ⟨9713639369, by decide, ⟨7285229527, by decide, ⟨10927844291, by decide, ⟨16391766437, by decide, ⟨3073456207, by decide, ⟨4610184311, by decide, ⟨6915276467, by decide, ⟨10372914701, by decide, ⟨3889843013, by decide, ⟨729345565, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_201 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4] (2021392411 + q * 2 ^ 31) endpoint ∧ endpoint < 2021392411 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4] targeted_trace_201 (by decide) (by decide) (by decide) q
#print axioms targeted_class_201

theorem targeted_trace_202 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 4] 100401179 64401949 := by
  exact ⟨150601769, by decide, ⟨112951327, by decide, ⟨169426991, by decide, ⟨254140487, by decide, ⟨381210731, by decide, ⟨571816097, by decide, ⟨428862073, by decide, ⟨321646555, by decide, ⟨482469833, by decide, ⟨361852375, by decide, ⟨542778563, by decide, ⟨814167845, by decide, ⟨152656471, by decide, ⟨228984707, by decide, ⟨343477061, by decide, ⟨64401949, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_202 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 4] (100401179 + q * 2 ^ 27) endpoint ∧ endpoint < 100401179 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 4] targeted_trace_202 (by decide) (by decide) (by decide) q
#print axioms targeted_class_202

theorem targeted_trace_203 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4] 352059419 254055547 := by
  exact ⟨528089129, by decide, ⟨396066847, by decide, ⟨594100271, by decide, ⟨891150407, by decide, ⟨1336725611, by decide, ⟨2005088417, by decide, ⟨1503816313, by decide, ⟨1127862235, by decide, ⟨1691793353, by decide, ⟨1268845015, by decide, ⟨1903267523, by decide, ⟨2854901285, by decide, ⟨535293991, by decide, ⟨802940987, by decide, ⟨1204411481, by decide, ⟨903308611, by decide, ⟨1354962917, by decide, ⟨254055547, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_203 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4] (352059419 + q * 2 ^ 30) endpoint ∧ endpoint < 352059419 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4] targeted_trace_203 (by decide) (by decide) (by decide) q
#print axioms targeted_class_203

theorem targeted_trace_204 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3] 939261979 677796707 := by
  exact ⟨1408892969, by decide, ⟨1056669727, by decide, ⟨1585004591, by decide, ⟨2377506887, by decide, ⟨3566260331, by decide, ⟨5349390497, by decide, ⟨4012042873, by decide, ⟨3009032155, by decide, ⟨4513548233, by decide, ⟨3385161175, by decide, ⟨5077741763, by decide, ⟨7616612645, by decide, ⟨1428114871, by decide, ⟨2142172307, by decide, ⟨3213258461, by decide, ⟨1204971923, by decide, ⟨1807457885, by decide, ⟨677796707, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_204 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3] (939261979 + q * 2 ^ 30) endpoint ∧ endpoint < 939261979 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3] targeted_trace_204 (by decide) (by decide) (by decide) q
#print axioms targeted_class_204

theorem targeted_trace_205 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5] 1962672155 708158507 := by
  exact ⟨2944008233, by decide, ⟨2208006175, by decide, ⟨3312009263, by decide, ⟨4968013895, by decide, ⟨7452020843, by decide, ⟨11178031265, by decide, ⟨8383523449, by decide, ⟨6287642587, by decide, ⟨9431463881, by decide, ⟨7073597911, by decide, ⟨10610396867, by decide, ⟨15915595301, by decide, ⟨2984174119, by decide, ⟨4476261179, by decide, ⟨6714391769, by decide, ⟨5035793827, by decide, ⟨7553690741, by decide, ⟨708158507, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_205 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5] (1962672155 + q * 2 ^ 31) endpoint ∧ endpoint < 1962672155 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5] targeted_trace_205 (by decide) (by decide) (by decide) q
#print axioms targeted_class_205

theorem targeted_trace_206 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4] 402391067 145188109 := by
  exact ⟨603586601, by decide, ⟨452689951, by decide, ⟨679034927, by decide, ⟨1018552391, by decide, ⟨1527828587, by decide, ⟨2291742881, by decide, ⟨1718807161, by decide, ⟨1289105371, by decide, ⟨1933658057, by decide, ⟨1450243543, by decide, ⟨2175365315, by decide, ⟨3263047973, by decide, ⟨611821495, by decide, ⟨917732243, by decide, ⟨1376598365, by decide, ⟨516224387, by decide, ⟨774336581, by decide, ⟨145188109, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_206 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4] (402391067 + q * 2 ^ 31) endpoint ∧ endpoint < 402391067 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4] targeted_trace_206 (by decide) (by decide) (by decide) q
#print axioms targeted_class_206

theorem targeted_trace_207 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5] 3908829211 2115537215 := by
  exact ⟨5863243817, by decide, ⟨4397432863, by decide, ⟨6596149295, by decide, ⟨9894223943, by decide, ⟨14841335915, by decide, ⟨22262003873, by decide, ⟨16696502905, by decide, ⟨12522377179, by decide, ⟨18783565769, by decide, ⟨14087674327, by decide, ⟨21131511491, by decide, ⟨31697267237, by decide, ⟨5943237607, by decide, ⟨8914856411, by decide, ⟨13372284617, by decide, ⟨10029213463, by decide, ⟨15043820195, by decide, ⟨22565730293, by decide, ⟨2115537215, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_207 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5] (3908829211 + q * 2 ^ 32) endpoint ∧ endpoint < 3908829211 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5] targeted_trace_207 (by decide) (by decide) (by decide) q
#print axioms targeted_class_207

theorem targeted_trace_208 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6] 888930331 160369009 := by
  exact ⟨1333395497, by decide, ⟨1000046623, by decide, ⟨1500069935, by decide, ⟨2250104903, by decide, ⟨3375157355, by decide, ⟨5062736033, by decide, ⟨3797052025, by decide, ⟨2847789019, by decide, ⟨4271683529, by decide, ⟨3203762647, by decide, ⟨4805643971, by decide, ⟨7208465957, by decide, ⟨1351587367, by decide, ⟨2027381051, by decide, ⟨3041071577, by decide, ⟨2280803683, by decide, ⟨3421205525, by decide, ⟨160369009, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_208 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6] (888930331 + q * 2 ^ 32) endpoint ∧ endpoint < 888930331 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6] targeted_trace_208 (by decide) (by decide) (by decide) q
#print axioms targeted_class_208

theorem targeted_trace_209 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4] 2633760795 1425444469 := by
  exact ⟨3950641193, by decide, ⟨2962980895, by decide, ⟨4444471343, by decide, ⟨6666707015, by decide, ⟨10000060523, by decide, ⟨15000090785, by decide, ⟨11250068089, by decide, ⟨8437551067, by decide, ⟨12656326601, by decide, ⟨9492244951, by decide, ⟨14238367427, by decide, ⟨21357551141, by decide, ⟨4004540839, by decide, ⟨6006811259, by decide, ⟨9010216889, by decide, ⟨6757662667, by decide, ⟨10136494001, by decide, ⟨7602370501, by decide, ⟨1425444469, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_209 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4] (2633760795 + q * 2 ^ 32) endpoint ∧ endpoint < 2633760795 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4] targeted_trace_209 (by decide) (by decide) (by decide) q
#print axioms targeted_class_209

theorem targeted_trace_210 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3] 318504987 172381325 := by
  exact ⟨477757481, by decide, ⟨358318111, by decide, ⟨537477167, by decide, ⟨806215751, by decide, ⟨1209323627, by decide, ⟨1813985441, by decide, ⟨1360489081, by decide, ⟨1020366811, by decide, ⟨1530550217, by decide, ⟨1147912663, by decide, ⟨1721868995, by decide, ⟨2582803493, by decide, ⟨484275655, by decide, ⟨726413483, by decide, ⟨1089620225, by decide, ⟨817215169, by decide, ⟨612911377, by decide, ⟨459683533, by decide, ⟨172381325, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_210 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3] (318504987 + q * 2 ^ 32) endpoint ∧ endpoint < 318504987 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3] targeted_trace_210 (by decide) (by decide) (by decide) q
#print axioms targeted_class_210

theorem targeted_trace_211 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4] 2868641819 1552566817 := by
  exact ⟨4302962729, by decide, ⟨3227222047, by decide, ⟨4840833071, by decide, ⟨7261249607, by decide, ⟨10891874411, by decide, ⟨16337811617, by decide, ⟨12253358713, by decide, ⟨9190019035, by decide, ⟨13785028553, by decide, ⟨10338771415, by decide, ⟨15508157123, by decide, ⟨23262235685, by decide, ⟨4361669191, by decide, ⟨6542503787, by decide, ⟨9813755681, by decide, ⟨7360316761, by decide, ⟨5520237571, by decide, ⟨8280356357, by decide, ⟨1552566817, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_211 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4] (2868641819 + q * 2 ^ 32) endpoint ∧ endpoint < 2868641819 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4] targeted_trace_211 (by decide) (by decide) (by decide) q
#print axioms targeted_class_211

theorem targeted_trace_212 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 3] 50462747 32369135 := by
  exact ⟨75694121, by decide, ⟨56770591, by decide, ⟨85155887, by decide, ⟨127733831, by decide, ⟨191600747, by decide, ⟨287401121, by decide, ⟨215550841, by decide, ⟨161663131, by decide, ⟨242494697, by decide, ⟨181871023, by decide, ⟨272806535, by decide, ⟨409209803, by decide, ⟨613814705, by decide, ⟨460361029, by decide, ⟨86317693, by decide, ⟨32369135, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_212 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 3] (50462747 + q * 2 ^ 27) endpoint ∧ endpoint < 50462747 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 3] targeted_trace_212 (by decide) (by decide) (by decide) q
#print axioms targeted_class_212

theorem targeted_trace_213 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3] 402784283 290659973 := by
  exact ⟨604176425, by decide, ⟨453132319, by decide, ⟨679698479, by decide, ⟨1019547719, by decide, ⟨1529321579, by decide, ⟨2293982369, by decide, ⟨1720486777, by decide, ⟨1290365083, by decide, ⟨1935547625, by decide, ⟨1451660719, by decide, ⟨2177491079, by decide, ⟨3266236619, by decide, ⟨4899354929, by decide, ⟨3674516197, by decide, ⟨688971787, by decide, ⟨1033457681, by decide, ⟨775093261, by decide, ⟨290659973, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_213 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3] (402784283 + q * 2 ^ 30) endpoint ∧ endpoint < 402784283 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3] targeted_trace_213 (by decide) (by decide) (by decide) q
#print axioms targeted_class_213

theorem targeted_trace_214 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4] 939655195 339040231 := by
  exact ⟨1409482793, by decide, ⟨1057112095, by decide, ⟨1585668143, by decide, ⟨2378502215, by decide, ⟨3567753323, by decide, ⟨5351629985, by decide, ⟨4013722489, by decide, ⟨3010291867, by decide, ⟨4515437801, by decide, ⟨3386578351, by decide, ⟨5079867527, by decide, ⟨7619801291, by decide, ⟨11429701937, by decide, ⟨8572276453, by decide, ⟨1607301835, by decide, ⟨2410952753, by decide, ⟨1808214565, by decide, ⟨339040231, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_214 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4] (939655195 + q * 2 ^ 31) endpoint ∧ endpoint < 939655195 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4] targeted_trace_214 (by decide) (by decide) (by decide) q
#print axioms targeted_class_214

theorem targeted_trace_215 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4] 1610743835 871767055 := by
  exact ⟨2416115753, by decide, ⟨1812086815, by decide, ⟨2718130223, by decide, ⟨4077195335, by decide, ⟨6115793003, by decide, ⟨9173689505, by decide, ⟨6880267129, by decide, ⟨5160200347, by decide, ⟨7740300521, by decide, ⟨5805225391, by decide, ⟨8707838087, by decide, ⟨13061757131, by decide, ⟨19592635697, by decide, ⟨14694476773, by decide, ⟨2755214395, by decide, ⟨4132821593, by decide, ⟨3099616195, by decide, ⟨4649424293, by decide, ⟨871767055, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_215 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4] (1610743835 + q * 2 ^ 32) endpoint ∧ endpoint < 1610743835 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4] targeted_trace_215 (by decide) (by decide) (by decide) q
#print axioms targeted_class_215

theorem targeted_trace_216 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3] 3355574299 1816104497 := by
  exact ⟨5033361449, by decide, ⟨3775021087, by decide, ⟨5662531631, by decide, ⟨8493797447, by decide, ⟨12740696171, by decide, ⟨19111044257, by decide, ⟨14333283193, by decide, ⟨10749962395, by decide, ⟨16124943593, by decide, ⟨12093707695, by decide, ⟨18140561543, by decide, ⟨27210842315, by decide, ⟨40816263473, by decide, ⟨30612197605, by decide, ⟨5739787051, by decide, ⟨8609680577, by decide, ⟨6457260433, by decide, ⟨4842945325, by decide, ⟨1816104497, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_216 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3] (3355574299 + q * 2 ^ 32) endpoint ∧ endpoint < 3355574299 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3] targeted_trace_216 (by decide) (by decide) (by decide) q
#print axioms targeted_class_216

theorem targeted_trace_217 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5] 4160880667 750650849 := by
  exact ⟨6241321001, by decide, ⟨4680990751, by decide, ⟨7021486127, by decide, ⟨10532229191, by decide, ⟨15798343787, by decide, ⟨23697515681, by decide, ⟨17773136761, by decide, ⟨13329852571, by decide, ⟨19994778857, by decide, ⟨14996084143, by decide, ⟨22494126215, by decide, ⟨33741189323, by decide, ⟨50611783985, by decide, ⟨37958837989, by decide, ⟨7117282123, by decide, ⟨10675923185, by decide, ⟨8006942389, by decide, ⟨750650849, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_217 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5] (4160880667 + q * 2 ^ 32) endpoint ∧ endpoint < 4160880667 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5] targeted_trace_217 (by decide) (by decide) (by decide) q
#print axioms targeted_class_217

theorem targeted_trace_218 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4] 1375862811 744644707 := by
  exact ⟨2063794217, by decide, ⟨1547845663, by decide, ⟨2321768495, by decide, ⟨3482652743, by decide, ⟨5223979115, by decide, ⟨7835968673, by decide, ⟨5876976505, by decide, ⟨4407732379, by decide, ⟨6611598569, by decide, ⟨4958698927, by decide, ⟨7438048391, by decide, ⟨11157072587, by decide, ⟨16735608881, by decide, ⟨12551706661, by decide, ⟨2353444999, by decide, ⟨3530167499, by decide, ⟨5295251249, by decide, ⟨3971438437, by decide, ⟨744644707, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_218 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4] (1375862811 + q * 2 ^ 32) endpoint ∧ endpoint < 1375862811 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4] targeted_trace_218 (by decide) (by decide) (by decide) q
#print axioms targeted_class_218

theorem targeted_trace_219 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3] 3120693275 1688982149 := by
  exact ⟨4681039913, by decide, ⟨3510779935, by decide, ⟨5266169903, by decide, ⟨7899254855, by decide, ⟨11848882283, by decide, ⟨17773323425, by decide, ⟨13329992569, by decide, ⟨9997494427, by decide, ⟨14996241641, by decide, ⟨11247181231, by decide, ⟨16870771847, by decide, ⟨25306157771, by decide, ⟨37959236657, by decide, ⟨28469427493, by decide, ⟨5338017655, by decide, ⟨8007026483, by decide, ⟨12010539725, by decide, ⟨4503952397, by decide, ⟨1688982149, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_219 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3] (3120693275 + q * 2 ^ 32) endpoint ∧ endpoint < 3120693275 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3] targeted_trace_219 (by decide) (by decide) (by decide) q
#print axioms targeted_class_219

theorem targeted_trace_220 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5] 2650931227 1434737453 := by
  exact ⟨3976396841, by decide, ⟨2982297631, by decide, ⟨4473446447, by decide, ⟨6710169671, by decide, ⟨10065254507, by decide, ⟨15097881761, by decide, ⟨11323411321, by decide, ⟨8492558491, by decide, ⟨12738837737, by decide, ⟨9554128303, by decide, ⟨14331192455, by decide, ⟨21496788683, by decide, ⟨32245183025, by decide, ⟨24183887269, by decide, ⟨4534478863, by decide, ⟨6801718295, by decide, ⟨10202577443, by decide, ⟨15303866165, by decide, ⟨1434737453, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_220 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5] (2650931227 + q * 2 ^ 32) endpoint ∧ endpoint < 2650931227 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5] targeted_trace_220 (by decide) (by decide) (by decide) q
#print axioms targeted_class_220

theorem targeted_trace_221 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 4] 54657051 35059555 := by
  exact ⟨81985577, by decide, ⟨61489183, by decide, ⟨92233775, by decide, ⟨138350663, by decide, ⟨207525995, by decide, ⟨311288993, by decide, ⟨233466745, by decide, ⟨175100059, by decide, ⟨262650089, by decide, ⟨196987567, by decide, ⟨295481351, by decide, ⟨443222027, by decide, ⟨664833041, by decide, ⟨498624781, by decide, ⟨186984293, by decide, ⟨35059555, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_221 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 4] (54657051 + q * 2 ^ 27) endpoint ∧ endpoint < 54657051 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 4] targeted_trace_221 (by decide) (by decide) (by decide) q
#print axioms targeted_class_221

theorem targeted_trace_222 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4] 977403931 705320965 := by
  exact ⟨1466105897, by decide, ⟨1099579423, by decide, ⟨1649369135, by decide, ⟨2474053703, by decide, ⟨3711080555, by decide, ⟨5566620833, by decide, ⟨4174965625, by decide, ⟨3131224219, by decide, ⟨4696836329, by decide, ⟨3522627247, by decide, ⟨5283940871, by decide, ⟨7925911307, by decide, ⟨11888866961, by decide, ⟨8916650221, by decide, ⟨3343743833, by decide, ⟨2507807875, by decide, ⟨3761711813, by decide, ⟨705320965, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_222 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4] (977403931 + q * 2 ^ 30) endpoint ∧ endpoint < 977403931 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4] targeted_trace_222 (by decide) (by decide) (by decide) q
#print axioms targeted_class_222

theorem targeted_trace_223 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3] 490864667 354221147 := by
  exact ⟨736297001, by decide, ⟨552222751, by decide, ⟨828334127, by decide, ⟨1242501191, by decide, ⟨1863751787, by decide, ⟨2795627681, by decide, ⟨2096720761, by decide, ⟨1572540571, by decide, ⟨2358810857, by decide, ⟨1769108143, by decide, ⟨2653662215, by decide, ⟨3980493323, by decide, ⟨5970739985, by decide, ⟨4478054989, by decide, ⟨1679270621, by decide, ⟨629726483, by decide, ⟨944589725, by decide, ⟨354221147, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_223 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3] (490864667 + q * 2 ^ 30) endpoint ∧ endpoint < 490864667 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3] targeted_trace_223 (by decide) (by decide) (by decide) q
#print axioms targeted_class_223

theorem targeted_trace_224 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5] 1514274843 546370727 := by
  exact ⟨2271412265, by decide, ⟨1703559199, by decide, ⟨2555338799, by decide, ⟨3833008199, by decide, ⟨5749512299, by decide, ⟨8624268449, by decide, ⟨6468201337, by decide, ⟨4851151003, by decide, ⟨7276726505, by decide, ⟨5457544879, by decide, ⟨8186317319, by decide, ⟨12279475979, by decide, ⟨18419213969, by decide, ⟨13814410477, by decide, ⟨5180403929, by decide, ⟨3885302947, by decide, ⟨5827954421, by decide, ⟨546370727, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_224 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5] (1514274843 + q * 2 ^ 31) endpoint ∧ endpoint < 1514274843 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5] targeted_trace_224 (by decide) (by decide) (by decide) q
#print axioms targeted_class_224

theorem targeted_trace_225 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4] 2101477403 758241307 := by
  exact ⟨3152216105, by decide, ⟨2364162079, by decide, ⟨3546243119, by decide, ⟨5319364679, by decide, ⟨7979047019, by decide, ⟨11968570529, by decide, ⟨8976427897, by decide, ⟨6732320923, by decide, ⟨10098481385, by decide, ⟨7573861039, by decide, ⟨11360791559, by decide, ⟨17041187339, by decide, ⟨25561781009, by decide, ⟨19171335757, by decide, ⟨7189250909, by decide, ⟨2695969091, by decide, ⟨4043953637, by decide, ⟨758241307, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_225 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4] (2101477403 + q * 2 ^ 31) endpoint ∧ endpoint < 2101477403 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4] targeted_trace_225 (by decide) (by decide) (by decide) q
#print axioms targeted_class_225

theorem targeted_trace_226 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4] 2420244507 1309885147 := by
  exact ⟨3630366761, by decide, ⟨2722775071, by decide, ⟨4084162607, by decide, ⟨6126243911, by decide, ⟨9189365867, by decide, ⟨13784048801, by decide, ⟨10338036601, by decide, ⟨7753527451, by decide, ⟨11630291177, by decide, ⟨8722718383, by decide, ⟨13084077575, by decide, ⟨19626116363, by decide, ⟨29439174545, by decide, ⟨22079380909, by decide, ⟨8279767841, by decide, ⟨6209825881, by decide, ⟨4657369411, by decide, ⟨6986054117, by decide, ⟨1309885147, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_226 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4] (2420244507 + q * 2 ^ 32) endpoint ∧ endpoint < 2420244507 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4] targeted_trace_226 (by decide) (by decide) (by decide) q
#print axioms targeted_class_226

theorem targeted_trace_227 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3] 4165074971 2254222589 := by
  exact ⟨6247612457, by decide, ⟨4685709343, by decide, ⟨7028564015, by decide, ⟨10542846023, by decide, ⟨15814269035, by decide, ⟨23721403553, by decide, ⟨17791052665, by decide, ⟨13343289499, by decide, ⟨20014934249, by decide, ⟨15011200687, by decide, ⟨22516801031, by decide, ⟨33775201547, by decide, ⟨50662802321, by decide, ⟨37997101741, by decide, ⟨14248913153, by decide, ⟨10686684865, by decide, ⟨8015013649, by decide, ⟨6011260237, by decide, ⟨2254222589, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_227 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3] (4165074971 + q * 2 ^ 32) endpoint ∧ endpoint < 4165074971 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3] targeted_trace_227 (by decide) (by decide) (by decide) q
#print axioms targeted_class_227

theorem targeted_trace_228 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3] 3930193947 2127100241 := by
  exact ⟨5895290921, by decide, ⟨4421468191, by decide, ⟨6632202287, by decide, ⟨9948303431, by decide, ⟨14922455147, by decide, ⟨22383682721, by decide, ⟨16787762041, by decide, ⟨12590821531, by decide, ⟨18886232297, by decide, ⟨14164674223, by decide, ⟨21247011335, by decide, ⟨31870517003, by decide, ⟨47805775505, by decide, ⟨35854331629, by decide, ⟨13445374361, by decide, ⟨10084030771, by decide, ⟨15126046157, by decide, ⟨5672267309, by decide, ⟨2127100241, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_228 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3] (3930193947 + q * 2 ^ 32) endpoint ∧ endpoint < 3930193947 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3] targeted_trace_228 (by decide) (by decide) (by decide) q
#print axioms targeted_class_228

theorem targeted_trace_229 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6] 440533019 79475119 := by
  exact ⟨660799529, by decide, ⟨495599647, by decide, ⟨743399471, by decide, ⟨1115099207, by decide, ⟨1672648811, by decide, ⟨2508973217, by decide, ⟨1881729913, by decide, ⟨1411297435, by decide, ⟨2116946153, by decide, ⟨1587709615, by decide, ⟨2381564423, by decide, ⟨3572346635, by decide, ⟨5358519953, by decide, ⟨4018889965, by decide, ⟨1507083737, by decide, ⟨1130312803, by decide, ⟨1695469205, by decide, ⟨79475119, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_229 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6] (440533019 + q * 2 ^ 32) endpoint ∧ endpoint < 440533019 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6] targeted_trace_229 (by decide) (by decide) (by decide) q
#print axioms targeted_class_229

theorem targeted_trace_230 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5] 3460431899 1872855545 := by
  exact ⟨5190647849, by decide, ⟨3892985887, by decide, ⟨5839478831, by decide, ⟨8759218247, by decide, ⟨13138827371, by decide, ⟨19708241057, by decide, ⟨14781180793, by decide, ⟨11085885595, by decide, ⟨16628828393, by decide, ⟨12471621295, by decide, ⟨18707431943, by decide, ⟨28061147915, by decide, ⟨42091721873, by decide, ⟨31568791405, by decide, ⟨11838296777, by decide, ⟨8878722583, by decide, ⟨13318083875, by decide, ⟨19977125813, by decide, ⟨1872855545, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_230 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5] (3460431899 + q * 2 ^ 32) endpoint ∧ endpoint < 3460431899 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5] targeted_trace_230 (by decide) (by decide) (by decide) q
#print axioms targeted_class_230

theorem targeted_trace_231 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3] 1036124187 747695081 := by
  exact ⟨1554186281, by decide, ⟨1165639711, by decide, ⟨1748459567, by decide, ⟨2622689351, by decide, ⟨3934034027, by decide, ⟨5901051041, by decide, ⟨4425788281, by decide, ⟨3319341211, by decide, ⟨4979011817, by decide, ⟨3734258863, by decide, ⟨5601388295, by decide, ⟨8402082443, by decide, ⟨12603123665, by decide, ⟨9452342749, by decide, ⟨3544628531, by decide, ⟨5316942797, by decide, ⟨1993853549, by decide, ⟨747695081, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_231 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3] (1036124187 + q * 2 ^ 30) endpoint ∧ endpoint < 1036124187 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3] targeted_trace_231 (by decide) (by decide) (by decide) q
#print axioms targeted_class_231

theorem targeted_trace_232 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4] 1572995099 567557785 := by
  exact ⟨2359492649, by decide, ⟨1769619487, by decide, ⟨2654429231, by decide, ⟨3981643847, by decide, ⟨5972465771, by decide, ⟨8958698657, by decide, ⟨6719023993, by decide, ⟨5039267995, by decide, ⟨7558901993, by decide, ⟨5669176495, by decide, ⟨8503764743, by decide, ⟨12755647115, by decide, ⟨19133470673, by decide, ⟨14350103005, by decide, ⟨5381288627, by decide, ⟨8071932941, by decide, ⟨3026974853, by decide, ⟨567557785, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_232 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4] (1572995099 + q * 2 ^ 31) endpoint ∧ endpoint < 1572995099 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4] targeted_trace_232 (by decide) (by decide) (by decide) q
#print axioms targeted_class_232

theorem targeted_trace_233 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6] 941752347 679593823 := by
  exact ⟨1412628521, by decide, ⟨1059471391, by decide, ⟨1589207087, by decide, ⟨2383810631, by decide, ⟨3575715947, by decide, ⟨5363573921, by decide, ⟨4022680441, by decide, ⟨3017010331, by decide, ⟨4525515497, by decide, ⟨3394136623, by decide, ⟨5091204935, by decide, ⟨7636807403, by decide, ⟨11455211105, by decide, ⟨8591408329, by decide, ⟨6443556247, by decide, ⟨9665334371, by decide, ⟨14498001557, by decide, ⟨679593823, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_233 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6] (941752347 + q * 2 ^ 30) endpoint ∧ endpoint < 941752347 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6] targeted_trace_233 (by decide) (by decide) (by decide) q
#print axioms targeted_class_233

theorem targeted_trace_234 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7] 404881435 146086667 := by
  exact ⟨607322153, by decide, ⟨455491615, by decide, ⟨683237423, by decide, ⟨1024856135, by decide, ⟨1537284203, by decide, ⟨2305926305, by decide, ⟨1729444729, by decide, ⟨1297083547, by decide, ⟨1945625321, by decide, ⟨1459218991, by decide, ⟨2188828487, by decide, ⟨3283242731, by decide, ⟨4924864097, by decide, ⟨3693648073, by decide, ⟨2770236055, by decide, ⟨4155354083, by decide, ⟨6233031125, by decide, ⟨146086667, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_234 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7] (404881435 + q * 2 ^ 31) endpoint ∧ endpoint < 404881435 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7] targeted_trace_234 (by decide) (by decide) (by decide) q
#print axioms targeted_class_234

theorem targeted_trace_235 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3] 279052315 201371657 := by
  exact ⟨418578473, by decide, ⟨313933855, by decide, ⟨470900783, by decide, ⟨706351175, by decide, ⟨1059526763, by decide, ⟨1589290145, by decide, ⟨1191967609, by decide, ⟨893975707, by decide, ⟨1340963561, by decide, ⟨1005722671, by decide, ⟨1508584007, by decide, ⟨2262876011, by decide, ⟨3394314017, by decide, ⟨2545735513, by decide, ⟨1909301635, by decide, ⟨2863952453, by decide, ⟨536991085, by decide, ⟨201371657, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_235 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3] (279052315 + q * 2 ^ 30) endpoint ∧ endpoint < 279052315 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3] targeted_trace_235 (by decide) (by decide) (by decide) q
#print axioms targeted_class_235

theorem targeted_trace_236 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5] 1000472603 721967939 := by
  exact ⟨1500708905, by decide, ⟨1125531679, by decide, ⟨1688297519, by decide, ⟨2532446279, by decide, ⟨3798669419, by decide, ⟨5698004129, by decide, ⟨4273503097, by decide, ⟨3205127323, by decide, ⟨4807690985, by decide, ⟨3605768239, by decide, ⟨5408652359, by decide, ⟨8112978539, by decide, ⟨12169467809, by decide, ⟨9127100857, by decide, ⟨6845325643, by decide, ⟨10267988465, by decide, ⟨7700991349, by decide, ⟨721967939, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_236 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5] (1000472603 + q * 2 ^ 30) endpoint ∧ endpoint < 1000472603 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5] targeted_trace_236 (by decide) (by decide) (by decide) q
#print axioms targeted_class_236

theorem targeted_trace_237 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4] 815923227 294396073 := by
  exact ⟨1223884841, by decide, ⟨917913631, by decide, ⟨1376870447, by decide, ⟨2065305671, by decide, ⟨3097958507, by decide, ⟨4646937761, by decide, ⟨3485203321, by decide, ⟨2613902491, by decide, ⟨3920853737, by decide, ⟨2940640303, by decide, ⟨4410960455, by decide, ⟨6616440683, by decide, ⟨9924661025, by decide, ⟨7443495769, by decide, ⟨5582621827, by decide, ⟨8373932741, by decide, ⟨1570112389, by decide, ⟨294396073, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_237 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4] (815923227 + q * 2 ^ 31) endpoint ∧ endpoint < 815923227 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4] targeted_trace_237 (by decide) (by decide) (by decide) q
#print axioms targeted_class_237

theorem targeted_trace_238 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6] 463601691 167273725 := by
  exact ⟨695402537, by decide, ⟨521551903, by decide, ⟨782327855, by decide, ⟨1173491783, by decide, ⟨1760237675, by decide, ⟨2640356513, by decide, ⟨1980267385, by decide, ⟨1485200539, by decide, ⟨2227800809, by decide, ⟨1670850607, by decide, ⟨2506275911, by decide, ⟨3759413867, by decide, ⟨5639120801, by decide, ⟨4229340601, by decide, ⟨3172005451, by decide, ⟨4758008177, by decide, ⟨3568506133, by decide, ⟨167273725, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_238 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6] (463601691 + q * 2 ^ 31) endpoint ∧ endpoint < 463601691 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6] targeted_trace_238 (by decide) (by decide) (by decide) q
#print axioms targeted_class_238

theorem targeted_trace_239 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 5] 56754203 36404765 := by
  exact ⟨85131305, by decide, ⟨63848479, by decide, ⟨95772719, by decide, ⟨143659079, by decide, ⟨215488619, by decide, ⟨323232929, by decide, ⟨242424697, by decide, ⟨181818523, by decide, ⟨272727785, by decide, ⟨204545839, by decide, ⟨306818759, by decide, ⟨460228139, by decide, ⟨690342209, by decide, ⟨517756657, by decide, ⟨388317493, by decide, ⟨36404765, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_239 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 5] (56754203 + q * 2 ^ 27) endpoint ∧ endpoint < 56754203 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 5] targeted_trace_239 (by decide) (by decide) (by decide) q
#print axioms targeted_class_239

theorem targeted_trace_240 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4] 308412443 222558715 := by
  exact ⟨462618665, by decide, ⟨346963999, by decide, ⟨520445999, by decide, ⟨780668999, by decide, ⟨1171003499, by decide, ⟨1756505249, by decide, ⟨1317378937, by decide, ⟨988034203, by decide, ⟨1482051305, by decide, ⟨1111538479, by decide, ⟨1667307719, by decide, ⟨2500961579, by decide, ⟨3751442369, by decide, ⟨2813581777, by decide, ⟨2110186333, by decide, ⟨791319875, by decide, ⟨1186979813, by decide, ⟨222558715, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_240 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4] (308412443 + q * 2 ^ 30) endpoint ∧ endpoint < 308412443 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4] targeted_trace_240 (by decide) (by decide) (by decide) q
#print axioms targeted_class_240

theorem targeted_trace_241 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3] 895615003 646299875 := by
  exact ⟨1343422505, by decide, ⟨1007566879, by decide, ⟨1511350319, by decide, ⟨2267025479, by decide, ⟨3400538219, by decide, ⟨5100807329, by decide, ⟨3825605497, by decide, ⟨2869204123, by decide, ⟨4303806185, by decide, ⟨3227854639, by decide, ⟨4841781959, by decide, ⟨7262672939, by decide, ⟨10894009409, by decide, ⟨8170507057, by decide, ⟨6127880293, by decide, ⟨1148977555, by decide, ⟨1723466333, by decide, ⟨646299875, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_241 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3] (895615003 + q * 2 ^ 30) endpoint ∧ endpoint < 895615003 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3] targeted_trace_241 (by decide) (by decide) (by decide) q
#print axioms targeted_class_241

theorem targeted_trace_242 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5] 1919025179 692410091 := by
  exact ⟨2878537769, by decide, ⟨2158903327, by decide, ⟨3238354991, by decide, ⟨4857532487, by decide, ⟨7286298731, by decide, ⟨10929448097, by decide, ⟨8197086073, by decide, ⟨6147814555, by decide, ⟨9221721833, by decide, ⟨6916291375, by decide, ⟨10374437063, by decide, ⟨15561655595, by decide, ⟨23342483393, by decide, ⟨17506862545, by decide, ⟨13130146909, by decide, ⟨4923805091, by decide, ⟨7385707637, by decide, ⟨692410091, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_242 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5] (1919025179 + q * 2 ^ 31) endpoint ∧ endpoint < 1919025179 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5] targeted_trace_242 (by decide) (by decide) (by decide) q
#print axioms targeted_class_242

theorem targeted_trace_243 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4] 358744091 129439693 := by
  exact ⟨538116137, by decide, ⟨403587103, by decide, ⟨605380655, by decide, ⟨908070983, by decide, ⟨1362106475, by decide, ⟨2043159713, by decide, ⟨1532369785, by decide, ⟨1149277339, by decide, ⟨1723916009, by decide, ⟨1292937007, by decide, ⟨1939405511, by decide, ⟨2909108267, by decide, ⟨4363662401, by decide, ⟨3272746801, by decide, ⟨2454560101, by decide, ⟨460230019, by decide, ⟨690345029, by decide, ⟨129439693, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_243 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4] (358744091 + q * 2 ^ 31) endpoint ∧ endpoint < 358744091 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4] targeted_trace_243 (by decide) (by decide) (by decide) q
#print axioms targeted_class_243

theorem targeted_trace_244 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3] 274858011 148758701 := by
  exact ⟨412287017, by decide, ⟨309215263, by decide, ⟨463822895, by decide, ⟨695734343, by decide, ⟨1043601515, by decide, ⟨1565402273, by decide, ⟨1174051705, by decide, ⟨880538779, by decide, ⟨1320808169, by decide, ⟨990606127, by decide, ⟨1485909191, by decide, ⟨2228863787, by decide, ⟨3343295681, by decide, ⟨2507471761, by decide, ⟨1880603821, by decide, ⟨705226433, by decide, ⟨528919825, by decide, ⟨396689869, by decide, ⟨148758701, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_244 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3] (274858011 + q * 2 ^ 32) endpoint ∧ endpoint < 274858011 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3] targeted_trace_244 (by decide) (by decide) (by decide) q
#print axioms targeted_class_244

theorem targeted_trace_245 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4] 2824994843 1528944193 := by
  exact ⟨4237492265, by decide, ⟨3178119199, by decide, ⟨4767178799, by decide, ⟨7150768199, by decide, ⟨10726152299, by decide, ⟨16089228449, by decide, ⟨12066921337, by decide, ⟨9050191003, by decide, ⟨13575286505, by decide, ⟨10181464879, by decide, ⟨15272197319, by decide, ⟨22908295979, by decide, ⟨34362443969, by decide, ⟨25771832977, by decide, ⟨19328874733, by decide, ⟨7248328025, by decide, ⟨5436246019, by decide, ⟨8154369029, by decide, ⟨1528944193, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_245 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4] (2824994843 + q * 2 ^ 32) endpoint ∧ endpoint < 2824994843 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4] targeted_trace_245 (by decide) (by decide) (by decide) q
#print axioms targeted_class_245

theorem targeted_trace_246 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6] 845283355 152494801 := by
  exact ⟨1267925033, by decide, ⟨950943775, by decide, ⟨1426415663, by decide, ⟨2139623495, by decide, ⟨3209435243, by decide, ⟨4814152865, by decide, ⟨3610614649, by decide, ⟨2707960987, by decide, ⟨4061941481, by decide, ⟨3046456111, by decide, ⟨4569684167, by decide, ⟨6854526251, by decide, ⟨10281789377, by decide, ⟨7711342033, by decide, ⟨5783506525, by decide, ⟨2168814947, by decide, ⟨3253222421, by decide, ⟨152494801, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_246 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6] (845283355 + q * 2 ^ 32) endpoint ∧ endpoint < 845283355 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6] targeted_trace_246 (by decide) (by decide) (by decide) q
#print axioms targeted_class_246

theorem targeted_trace_247 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4] 2590113819 1401821845 := by
  exact ⟨3885170729, by decide, ⟨2913878047, by decide, ⟨4370817071, by decide, ⟨6556225607, by decide, ⟨9834338411, by decide, ⟨14751507617, by decide, ⟨11063630713, by decide, ⟨8297723035, by decide, ⟨12446584553, by decide, ⟨9334938415, by decide, ⟨14002407623, by decide, ⟨21003611435, by decide, ⟨31505417153, by decide, ⟨23629062865, by decide, ⟨17721797149, by decide, ⟨6645673931, by decide, ⟨9968510897, by decide, ⟨7476383173, by decide, ⟨1401821845, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_247 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4] (2590113819 + q * 2 ^ 32) endpoint ∧ endpoint < 2590113819 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4] targeted_trace_247 (by decide) (by decide) (by decide) q
#print axioms targeted_class_247

theorem targeted_trace_248 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5] 3865182235 2091914591 := by
  exact ⟨5797773353, by decide, ⟨4348330015, by decide, ⟨6522495023, by decide, ⟨9783742535, by decide, ⟨14675613803, by decide, ⟨22013420705, by decide, ⟨16510065529, by decide, ⟨12382549147, by decide, ⟨18573823721, by decide, ⟨13930367791, by decide, ⟨20895551687, by decide, ⟨31343327531, by decide, ⟨47014991297, by decide, ⟨35261243473, by decide, ⟨26445932605, by decide, ⟨9917224727, by decide, ⟨14875837091, by decide, ⟨22313755637, by decide, ⟨2091914591, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_248 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5] (3865182235 + q * 2 ^ 32) endpoint ∧ endpoint < 3865182235 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5] targeted_trace_248 (by decide) (by decide) (by decide) q
#print axioms targeted_class_248

theorem targeted_trace_249 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3] 367132699 264932831 := by
  exact ⟨550699049, by decide, ⟨413024287, by decide, ⟨619536431, by decide, ⟨929304647, by decide, ⟨1393956971, by decide, ⟨2090935457, by decide, ⟨1568201593, by decide, ⟨1176151195, by decide, ⟨1764226793, by decide, ⟨1323170095, by decide, ⟨1984755143, by decide, ⟨2977132715, by decide, ⟨4465699073, by decide, ⟨3349274305, by decide, ⟨2511955729, by decide, ⟨1883966797, by decide, ⟨706487549, by decide, ⟨264932831, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_249 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3] (367132699 + q * 2 ^ 30) endpoint ∧ endpoint < 367132699 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3] targeted_trace_249 (by decide) (by decide) (by decide) q
#print axioms targeted_class_249

theorem targeted_trace_250 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4] 1977745435 713597149 := by
  exact ⟨2966618153, by decide, ⟨2224963615, by decide, ⟨3337445423, by decide, ⟨5006168135, by decide, ⟨7509252203, by decide, ⟨11263878305, by decide, ⟨8447908729, by decide, ⟨6335931547, by decide, ⟨9503897321, by decide, ⟨7127922991, by decide, ⟨10691884487, by decide, ⟨16037826731, by decide, ⟨24056740097, by decide, ⟨18042555073, by decide, ⟨13531916305, by decide, ⟨10148937229, by decide, ⟨3805851461, by decide, ⟨713597149, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_250 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4] (1977745435 + q * 2 ^ 31) endpoint ∧ endpoint < 1977745435 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4] targeted_trace_250 (by decide) (by decide) (by decide) q
#print axioms targeted_class_250

theorem targeted_trace_251 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3] 974258203 703050923 := by
  exact ⟨1461387305, by decide, ⟨1096040479, by decide, ⟨1644060719, by decide, ⟨2466091079, by decide, ⟨3699136619, by decide, ⟨5548704929, by decide, ⟨4161528697, by decide, ⟨3121146523, by decide, ⟨4681719785, by decide, ⟨3511289839, by decide, ⟨5266934759, by decide, ⟨7900402139, by decide, ⟨11850603209, by decide, ⟨8887952407, by decide, ⟨13331928611, by decide, ⟨19997892917, by decide, ⟨1874802461, by decide, ⟨703050923, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_251 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3] (974258203 + q * 2 ^ 30) endpoint ∧ endpoint < 974258203 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3] targeted_trace_251 (by decide) (by decide) (by decide) q
#print axioms targeted_class_251

theorem targeted_trace_252 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4] 437387291 157815217 := by
  exact ⟨656080937, by decide, ⟨492060703, by decide, ⟨738091055, by decide, ⟨1107136583, by decide, ⟨1660704875, by decide, ⟨2491057313, by decide, ⟨1868292985, by decide, ⟨1401219739, by decide, ⟨2101829609, by decide, ⟨1576372207, by decide, ⟨2364558311, by decide, ⟨3546837467, by decide, ⟨5320256201, by decide, ⟨3990192151, by decide, ⟨5985288227, by decide, ⟨8977932341, by decide, ⟨841681157, by decide, ⟨157815217, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_252 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4] (437387291 + q * 2 ^ 31) endpoint ∧ endpoint < 437387291 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4] targeted_trace_252 (by decide) (by decide) (by decide) q
#print axioms targeted_class_252

theorem targeted_trace_253 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7] 533856283 385245053 := by
  exact ⟨800784425, by decide, ⟨600588319, by decide, ⟨900882479, by decide, ⟨1351323719, by decide, ⟨2026985579, by decide, ⟨3040478369, by decide, ⟨2280358777, by decide, ⟨1710269083, by decide, ⟨2565403625, by decide, ⟨1924052719, by decide, ⟨2886079079, by decide, ⟨4329118619, by decide, ⟨6493677929, by decide, ⟨4870258447, by decide, ⟨7305387671, by decide, ⟨10958081507, by decide, ⟨16437122261, by decide, ⟨385245053, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_253 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7] (533856283 + q * 2 ^ 30) endpoint ∧ endpoint < 533856283 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7] targeted_trace_253 (by decide) (by decide) (by decide) q
#print axioms targeted_class_253

theorem targeted_trace_254 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3] 481427483 347411021 := by
  exact ⟨722141225, by decide, ⟨541605919, by decide, ⟨812408879, by decide, ⟨1218613319, by decide, ⟨1827919979, by decide, ⟨2741879969, by decide, ⟨2056409977, by decide, ⟨1542307483, by decide, ⟨2313461225, by decide, ⟨1735095919, by decide, ⟨2602643879, by decide, ⟨3903965819, by decide, ⟨5855948729, by decide, ⟨4391961547, by decide, ⟨6587942321, by decide, ⟨4940956741, by decide, ⟨926429389, by decide, ⟨347411021, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_254 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3] (481427483 + q * 2 ^ 30) endpoint ∧ endpoint < 481427483 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3] targeted_trace_254 (by decide) (by decide) (by decide) q
#print axioms targeted_class_254

theorem targeted_trace_255 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4] 1018298395 367415755 := by
  exact ⟨1527447593, by decide, ⟨1145585695, by decide, ⟨1718378543, by decide, ⟨2577567815, by decide, ⟨3866351723, by decide, ⟨5799527585, by decide, ⟨4349645689, by decide, ⟨3262234267, by decide, ⟨4893351401, by decide, ⟨3670013551, by decide, ⟨5505020327, by decide, ⟨8257530491, by decide, ⟨12386295737, by decide, ⟨9289721803, by decide, ⟨13934582705, by decide, ⟨10450937029, by decide, ⟨1959550693, by decide, ⟨367415755, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_255 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4] (1018298395 + q * 2 ^ 31) endpoint ∧ endpoint < 1018298395 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4] targeted_trace_255 (by decide) (by decide) (by decide) q
#print axioms targeted_class_255

theorem targeted_trace_256 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 6] 124911643 80124091 := by
  exact ⟨187367465, by decide, ⟨140525599, by decide, ⟨210788399, by decide, ⟨316182599, by decide, ⟨474273899, by decide, ⟨711410849, by decide, ⟨533558137, by decide, ⟨400168603, by decide, ⟨600252905, by decide, ⟨450189679, by decide, ⟨675284519, by decide, ⟨1012926779, by decide, ⟨1519390169, by decide, ⟨1139542627, by decide, ⟨1709313941, by decide, ⟨80124091, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_256 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 6] (124911643 + q * 2 ^ 27) endpoint ∧ endpoint < 124911643 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 6] targeted_trace_256 (by decide) (by decide) (by decide) q
#print axioms targeted_class_256

theorem targeted_trace_257 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4] 510787611 368598079 := by
  exact ⟨766181417, by decide, ⟨574636063, by decide, ⟨861954095, by decide, ⟨1292931143, by decide, ⟨1939396715, by decide, ⟨2909095073, by decide, ⟨2181821305, by decide, ⟨1636365979, by decide, ⟨2454548969, by decide, ⟨1840911727, by decide, ⟨2761367591, by decide, ⟨4142051387, by decide, ⟨6213077081, by decide, ⟨4659807811, by decide, ⟨6989711717, by decide, ⟨1310570947, by decide, ⟨1965856421, by decide, ⟨368598079, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_257 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4] (510787611 + q * 2 ^ 30) endpoint ∧ endpoint < 510787611 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4] targeted_trace_257 (by decide) (by decide) (by decide) q
#print axioms targeted_class_257

theorem targeted_trace_258 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5] 2121400347 765429773 := by
  exact ⟨3182100521, by decide, ⟨2386575391, by decide, ⟨3579863087, by decide, ⟨5369794631, by decide, ⟨8054691947, by decide, ⟨12082037921, by decide, ⟨9061528441, by decide, ⟨6796146331, by decide, ⟨10194219497, by decide, ⟨7645664623, by decide, ⟨11468496935, by decide, ⟨17202745403, by decide, ⟨25804118105, by decide, ⟨19353088579, by decide, ⟨29029632869, by decide, ⟨5443056163, by decide, ⟨8164584245, by decide, ⟨765429773, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_258 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5] (2121400347 + q * 2 ^ 31) endpoint ∧ endpoint < 2121400347 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5] targeted_trace_258 (by decide) (by decide) (by decide) q
#print axioms targeted_class_258

theorem targeted_trace_259 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4] 879886363 476212249 := by
  exact ⟨1319829545, by decide, ⟨989872159, by decide, ⟨1484808239, by decide, ⟨2227212359, by decide, ⟨3340818539, by decide, ⟨5011227809, by decide, ⟨3758420857, by decide, ⟨2818815643, by decide, ⟨4228223465, by decide, ⟨3171167599, by decide, ⟨4756751399, by decide, ⟨7135127099, by decide, ⟨10702690649, by decide, ⟨8027017987, by decide, ⟨12040526981, by decide, ⟨2257598809, by decide, ⟨1693199107, by decide, ⟨2539798661, by decide, ⟨476212249, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_259 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4] (879886363 + q * 2 ^ 32) endpoint ∧ endpoint < 879886363 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4] targeted_trace_259 (by decide) (by decide) (by decide) q
#print axioms targeted_class_259

theorem targeted_trace_260 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3] 2624716827 1420549691 := by
  exact ⟨3937075241, by decide, ⟨2952806431, by decide, ⟨4429209647, by decide, ⟨6643814471, by decide, ⟨9965721707, by decide, ⟨14948582561, by decide, ⟨11211436921, by decide, ⟨8408577691, by decide, ⟨12612866537, by decide, ⟨9459649903, by decide, ⟨14189474855, by decide, ⟨21284212283, by decide, ⟨31926318425, by decide, ⟨23944738819, by decide, ⟨35917108229, by decide, ⟨6734457793, by decide, ⟨5050843345, by decide, ⟨3788132509, by decide, ⟨1420549691, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_260 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3] (2624716827 + q * 2 ^ 32) endpoint ∧ endpoint < 2624716827 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3] targeted_trace_260 (by decide) (by decide) (by decide) q
#print axioms targeted_class_260

theorem targeted_trace_261 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5] 1920073755 1039182647 := by
  exact ⟨2880110633, by decide, ⟨2160082975, by decide, ⟨3240124463, by decide, ⟨4860186695, by decide, ⟨7290280043, by decide, ⟨10935420065, by decide, ⟨8201565049, by decide, ⟨6151173787, by decide, ⟨9226760681, by decide, ⟨6920070511, by decide, ⟨10380105767, by decide, ⟨15570158651, by decide, ⟨23355237977, by decide, ⟨17516428483, by decide, ⟨26274642725, by decide, ⟨4926495511, by decide, ⟨7389743267, by decide, ⟨11084614901, by decide, ⟨1039182647, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_261 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5] (1920073755 + q * 2 ^ 32) endpoint ∧ endpoint < 1920073755 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5] targeted_trace_261 (by decide) (by decide) (by decide) q
#print axioms targeted_class_261

theorem targeted_trace_262 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4] 645005339 349089901 := by
  exact ⟨967508009, by decide, ⟨725631007, by decide, ⟨1088446511, by decide, ⟨1632669767, by decide, ⟨2449004651, by decide, ⟨3673506977, by decide, ⟨2755130233, by decide, ⟨2066347675, by decide, ⟨3099521513, by decide, ⟨2324641135, by decide, ⟨3486961703, by decide, ⟨5230442555, by decide, ⟨7845663833, by decide, ⟨5884247875, by decide, ⟨8826371813, by decide, ⟨1654944715, by decide, ⟨2482417073, by decide, ⟨1861812805, by decide, ⟨349089901, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_262 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4] (645005339 + q * 2 ^ 32) endpoint ∧ endpoint < 645005339 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4] targeted_trace_262 (by decide) (by decide) (by decide) q
#print axioms targeted_class_262

theorem targeted_trace_263 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6] 3195142171 576425131 := by
  exact ⟨4792713257, by decide, ⟨3594534943, by decide, ⟨5391802415, by decide, ⟨8087703623, by decide, ⟨12131555435, by decide, ⟨18197333153, by decide, ⟨13647999865, by decide, ⟨10235999899, by decide, ⟨15353999849, by decide, ⟨11515499887, by decide, ⟨17273249831, by decide, ⟨25909874747, by decide, ⟨38864812121, by decide, ⟨29148609091, by decide, ⟨43722913637, by decide, ⟨8198046307, by decide, ⟨12297069461, by decide, ⟨576425131, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_263 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6] (3195142171 + q * 2 ^ 32) endpoint ∧ endpoint < 3195142171 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6] targeted_trace_263 (by decide) (by decide) (by decide) q
#print axioms targeted_class_263

theorem targeted_trace_264 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4] 334626843 241475731 := by
  exact ⟨501940265, by decide, ⟨376455199, by decide, ⟨564682799, by decide, ⟨847024199, by decide, ⟨1270536299, by decide, ⟨1905804449, by decide, ⟨1429353337, by decide, ⟨1072015003, by decide, ⟨1608022505, by decide, ⟨1206016879, by decide, ⟨1809025319, by decide, ⟨2713537979, by decide, ⟨4070306969, by decide, ⟨3052730227, by decide, ⟨4579095341, by decide, ⟨1717160753, by decide, ⟨1287870565, by decide, ⟨241475731, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_264 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4] (334626843 + q * 2 ^ 30) endpoint ∧ endpoint < 334626843 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4] targeted_trace_264 (by decide) (by decide) (by decide) q
#print axioms targeted_class_264

theorem targeted_trace_265 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5] 1945239579 701868599 := by
  exact ⟨2917859369, by decide, ⟨2188394527, by decide, ⟨3282591791, by decide, ⟨4923887687, by decide, ⟨7385831531, by decide, ⟨11078747297, by decide, ⟨8309060473, by decide, ⟨6231795355, by decide, ⟨9347693033, by decide, ⟨7010769775, by decide, ⟨10516154663, by decide, ⟨15774231995, by decide, ⟨23661347993, by decide, ⟨17746010995, by decide, ⟨26619016493, by decide, ⟨9982131185, by decide, ⟨7486598389, by decide, ⟨701868599, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_265 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5] (1945239579 + q * 2 ^ 31) endpoint ∧ endpoint < 1945239579 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5] targeted_trace_265 (by decide) (by decide) (by decide) q
#print axioms targeted_class_265

theorem targeted_trace_266 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4] 814350363 587657125 := by
  exact ⟨1221525545, by decide, ⟨916144159, by decide, ⟨1374216239, by decide, ⟨2061324359, by decide, ⟨3091986539, by decide, ⟨4637979809, by decide, ⟨3478484857, by decide, ⟨2608863643, by decide, ⟨3913295465, by decide, ⟨2934971599, by decide, ⟨4402457399, by decide, ⟨6603686099, by decide, ⟨9905529149, by decide, ⟨3714573431, by decide, ⟨5571860147, by decide, ⟨8357790221, by decide, ⟨3134171333, by decide, ⟨587657125, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_266 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4] (814350363 + q * 2 ^ 30) endpoint ∧ endpoint < 814350363 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4] targeted_trace_266 (by decide) (by decide) (by decide) q
#print axioms targeted_class_266

theorem targeted_trace_267 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3] 1049231387 757153589 := by
  exact ⟨1573847081, by decide, ⟨1180385311, by decide, ⟨1770577967, by decide, ⟨2655866951, by decide, ⟨3983800427, by decide, ⟨5975700641, by decide, ⟨4481775481, by decide, ⟨3361331611, by decide, ⟨5041997417, by decide, ⟨3781498063, by decide, ⟨5672247095, by decide, ⟨8508370643, by decide, ⟨12762555965, by decide, ⟨4785958487, by decide, ⟨7178937731, by decide, ⟨10768406597, by decide, ⟨2019076237, by decide, ⟨757153589, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_267 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3] (1049231387 + q * 2 ^ 30) endpoint ∧ endpoint < 1049231387 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3] targeted_trace_267 (by decide) (by decide) (by decide) q
#print axioms targeted_class_267

theorem targeted_trace_268 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5] 1351221275 487538807 := by
  exact ⟨2026831913, by decide, ⟨1520123935, by decide, ⟨2280185903, by decide, ⟨3420278855, by decide, ⟨5130418283, by decide, ⟨7695627425, by decide, ⟨5771720569, by decide, ⟨4328790427, by decide, ⟨6493185641, by decide, ⟨4869889231, by decide, ⟨7304833847, by decide, ⟨10957250771, by decide, ⟨16435876157, by decide, ⟨6163453559, by decide, ⟨9245180339, by decide, ⟨13867770509, by decide, ⟨5200413941, by decide, ⟨487538807, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_268 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5] (1351221275 + q * 2 ^ 31) endpoint ∧ endpoint < 1351221275 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5] targeted_trace_268 (by decide) (by decide) (by decide) q
#print axioms targeted_class_268

theorem targeted_trace_269 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4] 1586102299 572287039 := by
  exact ⟨2379153449, by decide, ⟨1784365087, by decide, ⟨2676547631, by decide, ⟨4014821447, by decide, ⟨6022232171, by decide, ⟨9033348257, by decide, ⟨6775011193, by decide, ⟨5081258395, by decide, ⟨7621887593, by decide, ⟨5716415695, by decide, ⟨8574623543, by decide, ⟨12861935315, by decide, ⟨19292902973, by decide, ⟨7234838615, by decide, ⟨10852257923, by decide, ⟨16278386885, by decide, ⟨3052197541, by decide, ⟨572287039, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_269 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4] (1586102299 + q * 2 ^ 31) endpoint ∧ endpoint < 1586102299 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4] targeted_trace_269 (by decide) (by decide) (by decide) q
#print axioms targeted_class_269

theorem targeted_trace_270 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 5] 21626907 13872497 := by
  exact ⟨32440361, by decide, ⟨24330271, by decide, ⟨36495407, by decide, ⟨54743111, by decide, ⟨82114667, by decide, ⟨123172001, by decide, ⟨92379001, by decide, ⟨69284251, by decide, ⟨103926377, by decide, ⟨77944783, by decide, ⟨116917175, by decide, ⟨175375763, by decide, ⟨263063645, by decide, ⟨98648867, by decide, ⟨147973301, by decide, ⟨13872497, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_270 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 5] (21626907 + q * 2 ^ 27) endpoint ∧ endpoint < 21626907 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 5] targeted_trace_270 (by decide) (by decide) (by decide) q
#print axioms targeted_class_270

theorem targeted_trace_271 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3] 2957639707 1600734269 := by
  exact ⟨4436459561, by decide, ⟨3327344671, by decide, ⟨4991017007, by decide, ⟨7486525511, by decide, ⟨11229788267, by decide, ⟨16844682401, by decide, ⟨12633511801, by decide, ⟨9475133851, by decide, ⟨14212700777, by decide, ⟨10659525583, by decide, ⟨15989288375, by decide, ⟨23983932563, by decide, ⟨35975898845, by decide, ⟨13490962067, by decide, ⟨20236443101, by decide, ⟨7588666163, by decide, ⟨11382999245, by decide, ⟨4268624717, by decide, ⟨1600734269, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_271 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3] (2957639707 + q * 2 ^ 32) endpoint ∧ endpoint < 2957639707 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3] targeted_trace_271 (by decide) (by decide) (by decide) q
#print axioms targeted_class_271

theorem targeted_trace_272 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4] 1212809243 656396827 := by
  exact ⟨1819213865, by decide, ⟨1364410399, by decide, ⟨2046615599, by decide, ⟨3069923399, by decide, ⟨4604885099, by decide, ⟨6907327649, by decide, ⟨5180495737, by decide, ⟨3885371803, by decide, ⟨5828057705, by decide, ⟨4371043279, by decide, ⟨6556564919, by decide, ⟨9834847379, by decide, ⟨14752271069, by decide, ⟨5532101651, by decide, ⟨8298152477, by decide, ⟨3111807179, by decide, ⟨4667710769, by decide, ⟨3500783077, by decide, ⟨656396827, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_272 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4] (1212809243 + q * 2 ^ 32) endpoint ∧ endpoint < 1212809243 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4] targeted_trace_272 (by decide) (by decide) (by decide) q
#print axioms targeted_class_272

theorem targeted_trace_273 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5] 2487877659 1346489573 := by
  exact ⟨3731816489, by decide, ⟨2798862367, by decide, ⟨4198293551, by decide, ⟨6297440327, by decide, ⟨9446160491, by decide, ⟨14169240737, by decide, ⟨10626930553, by decide, ⟨7970197915, by decide, ⟨11955296873, by decide, ⟨8966472655, by decide, ⟨13449708983, by decide, ⟨20174563475, by decide, ⟨30261845213, by decide, ⟨11348191955, by decide, ⟨17022287933, by decide, ⟨6383357975, by decide, ⟨9575036963, by decide, ⟨14362555445, by decide, ⟨1346489573, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_273 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5] (2487877659 + q * 2 ^ 32) endpoint ∧ endpoint < 2487877659 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5] targeted_trace_273 (by decide) (by decide) (by decide) q
#print axioms targeted_class_273

theorem targeted_trace_274 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4] 1447690267 783519175 := by
  exact ⟨2171535401, by decide, ⟨1628651551, by decide, ⟨2442977327, by decide, ⟨3664465991, by decide, ⟨5496698987, by decide, ⟨8245048481, by decide, ⟨6183786361, by decide, ⟨4637839771, by decide, ⟨6956759657, by decide, ⟨5217569743, by decide, ⟨7826354615, by decide, ⟨11739531923, by decide, ⟨17609297885, by decide, ⟨6603486707, by decide, ⟨9905230061, by decide, ⟨3714461273, by decide, ⟨2785845955, by decide, ⟨4178768933, by decide, ⟨783519175, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_274 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4] (1447690267 + q * 2 ^ 32) endpoint ∧ endpoint < 1447690267 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4] targeted_trace_274 (by decide) (by decide) (by decide) q
#print axioms targeted_class_274

theorem targeted_trace_275 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3] 3192520731 1727856617 := by
  exact ⟨4788781097, by decide, ⟨3591585823, by decide, ⟨5387378735, by decide, ⟨8081068103, by decide, ⟨12121602155, by decide, ⟨18182403233, by decide, ⟨13636802425, by decide, ⟨10227601819, by decide, ⟨15341402729, by decide, ⟨11506052047, by decide, ⟨17259078071, by decide, ⟨25888617107, by decide, ⟨38832925661, by decide, ⟨14562347123, by decide, ⟨21843520685, by decide, ⟨8191320257, by decide, ⟨6143490193, by decide, ⟨4607617645, by decide, ⟨1727856617, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_275 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3] (3192520731 + q * 2 ^ 32) endpoint ∧ endpoint < 3192520731 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3] targeted_trace_275 (by decide) (by decide) (by decide) q
#print axioms targeted_class_275

theorem targeted_trace_276 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3] 3544842267 1918540139 := by
  exact ⟨5317263401, by decide, ⟨3987947551, by decide, ⟨5981921327, by decide, ⟨8972881991, by decide, ⟨13459322987, by decide, ⟨20188984481, by decide, ⟨15141738361, by decide, ⟨11356303771, by decide, ⟨17034455657, by decide, ⟨12775841743, by decide, ⟨19163762615, by decide, ⟨28745643923, by decide, ⟨43118465885, by decide, ⟨16169424707, by decide, ⟨24254137061, by decide, ⟨4547650699, by decide, ⟨6821476049, by decide, ⟨5116107037, by decide, ⟨1918540139, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_276 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3] (3544842267 + q * 2 ^ 32) endpoint ∧ endpoint < 3544842267 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3] targeted_trace_276 (by decide) (by decide) (by decide) q
#print axioms targeted_class_276

theorem targeted_trace_277 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4] 902430747 651218299 := by
  exact ⟨1353646121, by decide, ⟨1015234591, by decide, ⟨1522851887, by decide, ⟨2284277831, by decide, ⟨3426416747, by decide, ⟨5139625121, by decide, ⟨3854718841, by decide, ⟨2891039131, by decide, ⟨4336558697, by decide, ⟨3252419023, by decide, ⟨4878628535, by decide, ⟨7317942803, by decide, ⟨10976914205, by decide, ⟨4116342827, by decide, ⟨6174514241, by decide, ⟨4630885681, by decide, ⟨3473164261, by decide, ⟨651218299, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_277 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4] (902430747 + q * 2 ^ 30) endpoint ∧ endpoint < 902430747 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4] targeted_trace_277 (by decide) (by decide) (by decide) q
#print axioms targeted_class_277

theorem targeted_trace_278 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5] 365559835 131898905 := by
  exact ⟨548339753, by decide, ⟨411254815, by decide, ⟨616882223, by decide, ⟨925323335, by decide, ⟨1387985003, by decide, ⟨2081977505, by decide, ⟨1561483129, by decide, ⟨1171112347, by decide, ⟨1756668521, by decide, ⟨1317501391, by decide, ⟨1976252087, by decide, ⟨2964378131, by decide, ⟨4446567197, by decide, ⟨1667462699, by decide, ⟨2501194049, by decide, ⟨1875895537, by decide, ⟨1406921653, by decide, ⟨131898905, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_278 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5] (365559835 + q * 2 ^ 31) endpoint ∧ endpoint < 365559835 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5] targeted_trace_278 (by decide) (by decide) (by decide) q
#print axioms targeted_class_278

theorem targeted_trace_279 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 4] 19529755 12527287 := by
  exact ⟨29294633, by decide, ⟨21970975, by decide, ⟨32956463, by decide, ⟨49434695, by decide, ⟨74152043, by decide, ⟨111228065, by decide, ⟨83421049, by decide, ⟨62565787, by decide, ⟨93848681, by decide, ⟨70386511, by decide, ⟨105579767, by decide, ⟨158369651, by decide, ⟨237554477, by decide, ⟨89082929, by decide, ⟨66812197, by decide, ⟨12527287, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_279 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 4] (19529755 + q * 2 ^ 27) endpoint ∧ endpoint < 19529755 + q * 2 ^ 27 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 4] targeted_trace_279 (by decide) (by decide) (by decide) q
#print axioms targeted_class_279

theorem targeted_trace_280 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3] 908722203 655758383 := by
  exact ⟨1363083305, by decide, ⟨1022312479, by decide, ⟨1533468719, by decide, ⟨2300203079, by decide, ⟨3450304619, by decide, ⟨5175456929, by decide, ⟨3881592697, by decide, ⟨2911194523, by decide, ⟨4366791785, by decide, ⟨3275093839, by decide, ⟨4912640759, by decide, ⟨7368961139, by decide, ⟨11053441709, by decide, ⟨4145040641, by decide, ⟨3108780481, by decide, ⟨2331585361, by decide, ⟨1748689021, by decide, ⟨655758383, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_280 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3] (908722203 + q * 2 ^ 30) endpoint ∧ endpoint < 908722203 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3] targeted_trace_280 (by decide) (by decide) (by decide) q
#print axioms targeted_class_280

theorem targeted_trace_281 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4] 371851291 134168947 := by
  exact ⟨557776937, by decide, ⟨418332703, by decide, ⟨627499055, by decide, ⟨941248583, by decide, ⟨1411872875, by decide, ⟨2117809313, by decide, ⟨1588356985, by decide, ⟨1191267739, by decide, ⟨1786901609, by decide, ⟨1340176207, by decide, ⟨2010264311, by decide, ⟨3015396467, by decide, ⟨4523094701, by decide, ⟨1696160513, by decide, ⟨1272120385, by decide, ⟨954090289, by decide, ⟨715567717, by decide, ⟨134168947, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_281 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4] (371851291 + q * 2 ^ 31) endpoint ∧ endpoint < 371851291 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4] targeted_trace_281 (by decide) (by decide) (by decide) q
#print axioms targeted_class_281

theorem targeted_trace_282 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4] 808058907 437337781 := by
  exact ⟨1212088361, by decide, ⟨909066271, by decide, ⟨1363599407, by decide, ⟨2045399111, by decide, ⟨3068098667, by decide, ⟨4602148001, by decide, ⟨3451611001, by decide, ⟨2588708251, by decide, ⟨3883062377, by decide, ⟨2912296783, by decide, ⟨4368445175, by decide, ⟨6552667763, by decide, ⟨9829001645, by decide, ⟨3685875617, by decide, ⟨2764406713, by decide, ⟨2073305035, by decide, ⟨3109957553, by decide, ⟨2332468165, by decide, ⟨437337781, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_282 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4] (808058907 + q * 2 ^ 32) endpoint ∧ endpoint < 808058907 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4] targeted_trace_282 (by decide) (by decide) (by decide) q
#print axioms targeted_class_282

theorem targeted_trace_283 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3] 2552889371 1381675223 := by
  exact ⟨3829334057, by decide, ⟨2872000543, by decide, ⟨4308000815, by decide, ⟨6462001223, by decide, ⟨9693001835, by decide, ⟨14539502753, by decide, ⟨10904627065, by decide, ⟨8178470299, by decide, ⟨12267705449, by decide, ⟨9200779087, by decide, ⟨13801168631, by decide, ⟨20701752947, by decide, ⟨31052629421, by decide, ⟨11644736033, by decide, ⟨8733552025, by decide, ⟨6550164019, by decide, ⟨9825246029, by decide, ⟨3684467261, by decide, ⟨1381675223, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_283 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3] (2552889371 + q * 2 ^ 32) endpoint ∧ endpoint < 2552889371 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3] targeted_trace_283 (by decide) (by decide) (by decide) q
#print axioms targeted_class_283

theorem targeted_trace_284 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5] 2083127323 1127430527 := by
  exact ⟨3124690985, by decide, ⟨2343518239, by decide, ⟨3515277359, by decide, ⟨5272916039, by decide, ⟨7909374059, by decide, ⟨11864061089, by decide, ⟨8898045817, by decide, ⟨6673534363, by decide, ⟨10010301545, by decide, ⟨7507726159, by decide, ⟨11261589239, by decide, ⟨16892383859, by decide, ⟨25338575789, by decide, ⟨9501965921, by decide, ⟨7126474441, by decide, ⟨5344855831, by decide, ⟨8017283747, by decide, ⟨12025925621, by decide, ⟨1127430527, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_284 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5] (2083127323 + q * 2 ^ 32) endpoint ∧ endpoint < 2083127323 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5] targeted_trace_284 (by decide) (by decide) (by decide) q
#print axioms targeted_class_284

theorem targeted_trace_285 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3] 2787770395 1508797571 := by
  exact ⟨4181655593, by decide, ⟨3136241695, by decide, ⟨4704362543, by decide, ⟨7056543815, by decide, ⟨10584815723, by decide, ⟨15877223585, by decide, ⟨11907917689, by decide, ⟨8930938267, by decide, ⟨13396407401, by decide, ⟨10047305551, by decide, ⟨15070958327, by decide, ⟨22606437491, by decide, ⟨33909656237, by decide, ⟨12716121089, by decide, ⟨9537090817, by decide, ⟨7152818113, by decide, ⟨5364613585, by decide, ⟨4023460189, by decide, ⟨1508797571, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_285 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3] (2787770395 + q * 2 ^ 32) endpoint ∧ endpoint < 2787770395 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3] targeted_trace_285 (by decide) (by decide) (by decide) q
#print axioms targeted_class_285

theorem targeted_trace_286 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5] 3593076763 648215207 := by
  exact ⟨5389615145, by decide, ⟨4042211359, by decide, ⟨6063317039, by decide, ⟨9094975559, by decide, ⟨13642463339, by decide, ⟨20463695009, by decide, ⟨15347771257, by decide, ⟨11510828443, by decide, ⟨17266242665, by decide, ⟨12949681999, by decide, ⟨19424522999, by decide, ⟨29136784499, by decide, ⟨43705176749, by decide, ⟨16389441281, by decide, ⟨12292080961, by decide, ⟨9219060721, by decide, ⟨6914295541, by decide, ⟨648215207, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_286 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5] (3593076763 + q * 2 ^ 32) endpoint ∧ endpoint < 3593076763 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5] targeted_trace_286 (by decide) (by decide) (by decide) q
#print axioms targeted_class_286

theorem targeted_trace_287 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4] 1042939931 564460129 := by
  exact ⟨1564409897, by decide, ⟨1173307423, by decide, ⟨1759961135, by decide, ⟨2639941703, by decide, ⟨3959912555, by decide, ⟨5939868833, by decide, ⟨4454901625, by decide, ⟨3341176219, by decide, ⟨5011764329, by decide, ⟨3758823247, by decide, ⟨5638234871, by decide, ⟨8457352307, by decide, ⟨12686028461, by decide, ⟨4757260673, by decide, ⟨3567945505, by decide, ⟨2675959129, by decide, ⟨2006969347, by decide, ⟨3010454021, by decide, ⟨564460129, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_287 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4] (1042939931 + q * 2 ^ 32) endpoint ∧ endpoint < 1042939931 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4] targeted_trace_287 (by decide) (by decide) (by decide) q
#print axioms targeted_class_287

theorem targeted_trace_288 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5] 380239899 274391339 := by
  exact ⟨570359849, by decide, ⟨427769887, by decide, ⟨641654831, by decide, ⟨962482247, by decide, ⟨1443723371, by decide, ⟨2165585057, by decide, ⟨1624188793, by decide, ⟨1218141595, by decide, ⟨1827212393, by decide, ⟨1370409295, by decide, ⟨2055613943, by decide, ⟨3083420915, by decide, ⟨4625131373, by decide, ⟨1734424265, by decide, ⟨1300818199, by decide, ⟨1951227299, by decide, ⟨2926840949, by decide, ⟨274391339, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_288 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5] (380239899 + q * 2 ^ 30) endpoint ∧ endpoint < 380239899 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5] targeted_trace_288 (by decide) (by decide) (by decide) q
#print axioms targeted_class_288

theorem targeted_trace_289 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4] 497680411 359139571 := by
  exact ⟨746520617, by decide, ⟨559890463, by decide, ⟨839835695, by decide, ⟨1259753543, by decide, ⟨1889630315, by decide, ⟨2834445473, by decide, ⟨2125834105, by decide, ⟨1594375579, by decide, ⟨2391563369, by decide, ⟨1793672527, by decide, ⟨2690508791, by decide, ⟨4035763187, by decide, ⟨6053644781, by decide, ⟨2270116793, by decide, ⟨1702587595, by decide, ⟨2553881393, by decide, ⟨1915411045, by decide, ⟨359139571, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_289 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4] (497680411 + q * 2 ^ 30) endpoint ∧ endpoint < 497680411 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4] targeted_trace_289 (by decide) (by decide) (by decide) q
#print axioms targeted_class_289

theorem targeted_trace_290 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6] 1990852635 718326403 := by
  exact ⟨2986278953, by decide, ⟨2239709215, by decide, ⟨3359563823, by decide, ⟨5039345735, by decide, ⟨7559018603, by decide, ⟨11338527905, by decide, ⟨8503895929, by decide, ⟨6377921947, by decide, ⟨9566882921, by decide, ⟨7175162191, by decide, ⟨10762743287, by decide, ⟨16144114931, by decide, ⟨24216172397, by decide, ⟨9081064649, by decide, ⟨6810798487, by decide, ⟨10216197731, by decide, ⟨15324296597, by decide, ⟨718326403, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_290 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6] (1990852635 + q * 2 ^ 31) endpoint ∧ endpoint < 1990852635 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6] targeted_trace_290 (by decide) (by decide) (by decide) q
#print axioms targeted_class_290

theorem targeted_trace_291 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3] 451543067 325845623 := by
  exact ⟨677314601, by decide, ⟨507985951, by decide, ⟨761978927, by decide, ⟨1142968391, by decide, ⟨1714452587, by decide, ⟨2571678881, by decide, ⟨1928759161, by decide, ⟨1446569371, by decide, ⟨2169854057, by decide, ⟨1627390543, by decide, ⟨2441085815, by decide, ⟨3661628723, by decide, ⟨5492443085, by decide, ⟨2059666157, by decide, ⟨772374809, by decide, ⟨579281107, by decide, ⟨868921661, by decide, ⟨325845623, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_291 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3] (451543067 + q * 2 ^ 30) endpoint ∧ endpoint < 451543067 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3] targeted_trace_291 (by decide) (by decide) (by decide) q
#print axioms targeted_class_291

theorem targeted_trace_292 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4] 938082331 676945441 := by
  exact ⟨1407123497, by decide, ⟨1055342623, by decide, ⟨1583013935, by decide, ⟨2374520903, by decide, ⟨3561781355, by decide, ⟨5342672033, by decide, ⟨4007004025, by decide, ⟨3005253019, by decide, ⟨4507879529, by decide, ⟨3380909647, by decide, ⟨5071364471, by decide, ⟨7607046707, by decide, ⟨11410570061, by decide, ⟨4278963773, by decide, ⟨1604611415, by decide, ⟨2406917123, by decide, ⟨3610375685, by decide, ⟨676945441, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_292 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4] (938082331 + q * 2 ^ 30) endpoint ∧ endpoint < 938082331 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4] targeted_trace_292 (by decide) (by decide) (by decide) q
#print axioms targeted_class_292

theorem targeted_trace_293 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4] 2062155803 744053545 := by
  exact ⟨3093233705, by decide, ⟨2319925279, by decide, ⟨3479887919, by decide, ⟨5219831879, by decide, ⟨7829747819, by decide, ⟨11744621729, by decide, ⟨8808466297, by decide, ⟨6606349723, by decide, ⟨9909524585, by decide, ⟨7432143439, by decide, ⟨11148215159, by decide, ⟨16722322739, by decide, ⟨25083484109, by decide, ⟨9406306541, by decide, ⟨3527364953, by decide, ⟨2645523715, by decide, ⟨3968285573, by decide, ⟨744053545, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_293 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4] (2062155803 + q * 2 ^ 31) endpoint ∧ endpoint < 2062155803 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4] targeted_trace_293 (by decide) (by decide) (by decide) q
#print axioms targeted_class_293

theorem targeted_trace_294 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5] 1474953243 532182965 := by
  exact ⟨2212429865, by decide, ⟨1659322399, by decide, ⟨2488983599, by decide, ⟨3733475399, by decide, ⟨5600213099, by decide, ⟨8400319649, by decide, ⟨6300239737, by decide, ⟨4725179803, by decide, ⟨7087769705, by decide, ⟨5315827279, by decide, ⟨7973740919, by decide, ⟨11960611379, by decide, ⟨17940917069, by decide, ⟨6727843901, by decide, ⟨2522941463, by decide, ⟨3784412195, by decide, ⟨5676618293, by decide, ⟨532182965, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_294 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5] (1474953243 + q * 2 ^ 31) endpoint ∧ endpoint < 1474953243 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5] targeted_trace_294 (by decide) (by decide) (by decide) q
#print axioms targeted_class_294

theorem targeted_trace_295 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4] 585760795 317025559 := by
  exact ⟨878641193, by decide, ⟨658980895, by decide, ⟨988471343, by decide, ⟨1482707015, by decide, ⟨2224060523, by decide, ⟨3336090785, by decide, ⟨2502068089, by decide, ⟨1876551067, by decide, ⟨2814826601, by decide, ⟨2111119951, by decide, ⟨3166679927, by decide, ⟨4750019891, by decide, ⟨7125029837, by decide, ⟨2671886189, by decide, ⟨1001957321, by decide, ⟨751467991, by decide, ⟨1127201987, by decide, ⟨1690802981, by decide, ⟨317025559, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_295 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4] (585760795 + q * 2 ^ 32) endpoint ∧ endpoint < 585760795 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4] targeted_trace_295 (by decide) (by decide) (by decide) q
#print axioms targeted_class_295

theorem targeted_trace_296 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5] 3135897627 565737017 := by
  exact ⟨4703846441, by decide, ⟨3527884831, by decide, ⟨5291827247, by decide, ⟨7937740871, by decide, ⟨11906611307, by decide, ⟨17859916961, by decide, ⟨13394937721, by decide, ⟨10046203291, by decide, ⟨15069304937, by decide, ⟨11301978703, by decide, ⟨16952968055, by decide, ⟨25429452083, by decide, ⟨38144178125, by decide, ⟨14304066797, by decide, ⟨5364025049, by decide, ⟨4023018787, by decide, ⟨6034528181, by decide, ⟨565737017, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_296 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5] (3135897627 + q * 2 ^ 32) endpoint ∧ endpoint < 3135897627 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5] targeted_trace_296 (by decide) (by decide) (by decide) q
#print axioms targeted_class_296

theorem targeted_trace_297 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3] 1978269723 1070679479 := by
  exact ⟨2967404585, by decide, ⟨2225553439, by decide, ⟨3338330159, by decide, ⟨5007495239, by decide, ⟨7511242859, by decide, ⟨11266864289, by decide, ⟨8450148217, by decide, ⟨6337611163, by decide, ⟨9506416745, by decide, ⟨7129812559, by decide, ⟨10694718839, by decide, ⟨16042078259, by decide, ⟨24063117389, by decide, ⟨9023669021, by decide, ⟨3383875883, by decide, ⟨5075813825, by decide, ⟨3806860369, by decide, ⟨2855145277, by decide, ⟨1070679479, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_297 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3] (1978269723 + q * 2 ^ 32) endpoint ∧ endpoint < 1978269723 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3] targeted_trace_297 (by decide) (by decide) (by decide) q
#print axioms targeted_class_297

theorem targeted_trace_298 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5] 1273626651 689312435 := by
  exact ⟨1910439977, by decide, ⟨1432829983, by decide, ⟨2149244975, by decide, ⟨3223867463, by decide, ⟨4835801195, by decide, ⟨7253701793, by decide, ⟨5440276345, by decide, ⟨4080207259, by decide, ⟨6120310889, by decide, ⟨4590233167, by decide, ⟨6885349751, by decide, ⟨10328024627, by decide, ⟨15492036941, by decide, ⟨5809513853, by decide, ⟨2178567695, by decide, ⟨3267851543, by decide, ⟨4901777315, by decide, ⟨7352665973, by decide, ⟨689312435, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_298 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5] (1273626651 + q * 2 ^ 32) endpoint ∧ endpoint < 1273626651 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5] targeted_trace_298 (by decide) (by decide) (by decide) q
#print axioms targeted_class_298

theorem targeted_trace_299 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3] 425328667 306928607 := by
  exact ⟨637993001, by decide, ⟨478494751, by decide, ⟨717742127, by decide, ⟨1076613191, by decide, ⟨1614919787, by decide, ⟨2422379681, by decide, ⟨1816784761, by decide, ⟨1362588571, by decide, ⟨2043882857, by decide, ⟨1532912143, by decide, ⟨2299368215, by decide, ⟨3449052323, by decide, ⟨5173578485, by decide, ⟨485022983, by decide, ⟨727534475, by decide, ⟨1091301713, by decide, ⟨818476285, by decide, ⟨306928607, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_299 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3] (425328667 + q * 2 ^ 30) endpoint ∧ endpoint < 425328667 + q * 2 ^ 30 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3] targeted_trace_299 (by decide) (by decide) (by decide) q
#print axioms targeted_class_299

theorem targeted_trace_300 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4] 2035941403 734595037 := by
  exact ⟨3053912105, by decide, ⟨2290434079, by decide, ⟨3435651119, by decide, ⟨5153476679, by decide, ⟨7730215019, by decide, ⟨11595322529, by decide, ⟨8696491897, by decide, ⟨6522368923, by decide, ⟨9783553385, by decide, ⟨7337665039, by decide, ⟨11006497559, by decide, ⟨16509746339, by decide, ⟨24764619509, by decide, ⟨2321683079, by decide, ⟨3482524619, by decide, ⟨5223786929, by decide, ⟨3917840197, by decide, ⟨734595037, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_300 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4] (2035941403 + q * 2 ^ 31) endpoint ∧ endpoint < 2035941403 + q * 2 ^ 31 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4] targeted_trace_300 (by decide) (by decide) (by decide) q
#print axioms targeted_class_300

theorem targeted_trace_301 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4] 911867931 493521319 := by
  exact ⟨1367801897, by decide, ⟨1025851423, by decide, ⟨1538777135, by decide, ⟨2308165703, by decide, ⟨3462248555, by decide, ⟨5193372833, by decide, ⟨3895029625, by decide, ⟨2921272219, by decide, ⟨4381908329, by decide, ⟨3286431247, by decide, ⟨4929646871, by decide, ⟨7394470307, by decide, ⟨11091705461, by decide, ⟨1039847387, by decide, ⟨1559771081, by decide, ⟨1169828311, by decide, ⟨1754742467, by decide, ⟨2632113701, by decide, ⟨493521319, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_301 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4] (911867931 + q * 2 ^ 32) endpoint ∧ endpoint < 911867931 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4] targeted_trace_301 (by decide) (by decide) (by decide) q
#print axioms targeted_class_301

theorem targeted_trace_302 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3] 2656698395 1437858761 := by
  exact ⟨3985047593, by decide, ⟨2988785695, by decide, ⟨4483178543, by decide, ⟨6724767815, by decide, ⟨10087151723, by decide, ⟨15130727585, by decide, ⟨11348045689, by decide, ⟨8511034267, by decide, ⟨12766551401, by decide, ⟨9574913551, by decide, ⟨14362370327, by decide, ⟨21543555491, by decide, ⟨32315333237, by decide, ⟨3029562491, by decide, ⟨4544343737, by decide, ⟨3408257803, by decide, ⟨5112386705, by decide, ⟨3834290029, by decide, ⟨1437858761, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_302 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3] (2656698395 + q * 2 ^ 32) endpoint ∧ endpoint < 2656698395 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3] targeted_trace_302 (by decide) (by decide) (by decide) q
#print axioms targeted_class_302

theorem targeted_trace_303 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4] 559546395 302837797 := by
  exact ⟨839319593, by decide, ⟨629489695, by decide, ⟨944234543, by decide, ⟨1416351815, by decide, ⟨2124527723, by decide, ⟨3186791585, by decide, ⟨2390093689, by decide, ⟨1792570267, by decide, ⟨2688855401, by decide, ⟨2016641551, by decide, ⟨3024962327, by decide, ⟨4537443491, by decide, ⟨6806165237, by decide, ⟨638077991, by decide, ⟨957116987, by decide, ⟨1435675481, by decide, ⟨1076756611, by decide, ⟨1615134917, by decide, ⟨302837797, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_303 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4] (559546395 + q * 2 ^ 32) endpoint ∧ endpoint < 559546395 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4] targeted_trace_303 (by decide) (by decide) (by decide) q
#print axioms targeted_class_303

theorem targeted_trace_304 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5] 3109683227 561007763 := by
  exact ⟨4664524841, by decide, ⟨3498393631, by decide, ⟨5247590447, by decide, ⟨7871385671, by decide, ⟨11807078507, by decide, ⟨17710617761, by decide, ⟨13282963321, by decide, ⟨9962222491, by decide, ⟨14943333737, by decide, ⟨11207500303, by decide, ⟨16811250455, by decide, ⟨25216875683, by decide, ⟨37825313525, by decide, ⟨3546123143, by decide, ⟨5319184715, by decide, ⟨7978777073, by decide, ⟨5984082805, by decide, ⟨561007763, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_304 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5] (3109683227 + q * 2 ^ 32) endpoint ∧ endpoint < 3109683227 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5] targeted_trace_304 (by decide) (by decide) (by decide) q
#print axioms targeted_class_304

theorem targeted_trace_305 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4] 324665371 175715449 := by
  exact ⟨486998057, by decide, ⟨365248543, by decide, ⟨547872815, by decide, ⟨821809223, by decide, ⟨1232713835, by decide, ⟨1849070753, by decide, ⟨1386803065, by decide, ⟨1040102299, by decide, ⟨1560153449, by decide, ⟨1170115087, by decide, ⟨1755172631, by decide, ⟨2632758947, by decide, ⟨3949138421, by decide, ⟨370231727, by decide, ⟨555347591, by decide, ⟨833021387, by decide, ⟨1249532081, by decide, ⟨937149061, by decide, ⟨175715449, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_305 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4] (324665371 + q * 2 ^ 32) endpoint ∧ endpoint < 324665371 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4] targeted_trace_305 (by decide) (by decide) (by decide) q
#print axioms targeted_class_305

theorem targeted_trace_306 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3] 2069495835 1120052891 := by
  exact ⟨3104243753, by decide, ⟨2328182815, by decide, ⟨3492274223, by decide, ⟨5238411335, by decide, ⟨7857617003, by decide, ⟨11786425505, by decide, ⟨8839819129, by decide, ⟨6629864347, by decide, ⟨9944796521, by decide, ⟨7458597391, by decide, ⟨11187896087, by decide, ⟨16781844131, by decide, ⟨25172766197, by decide, ⟨2359946831, by decide, ⟨3539920247, by decide, ⟨5309880371, by decide, ⟨7964820557, by decide, ⟨2986807709, by decide, ⟨1120052891, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem targeted_class_306 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3] (2069495835 + q * 2 ^ 32) endpoint ∧ endpoint < 2069495835 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3] targeted_trace_306 (by decide) (by decide) (by decide) q
#print axioms targeted_class_306

theorem fixed_point_trace : WordTrace [2] 1 1 := by
  exact ⟨1, by decide, rfl⟩
theorem fixed_point_threshold (q : Nat) (h : 2 ≤ q) : ∃ endpoint, WordTrace [2] (1 + q * 2 ^ 3) endpoint ∧ endpoint < 1 + q * 2 ^ 3 := by
  exact threshold_family_descends [2] fixed_point_trace (by decide) (by decide) h
#print axioms fixed_point_threshold
end CollatzResearch
