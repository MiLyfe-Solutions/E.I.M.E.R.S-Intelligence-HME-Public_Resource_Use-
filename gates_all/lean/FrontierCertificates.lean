import FamilyDescent
namespace CollatzResearch

theorem frontier_trace_0 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6] 51589939227 47117557789 := by
  exact ⟨77384908841, by decide, ⟨58038681631, by decide, ⟨87058022447, by decide, ⟨130587033671, by decide, ⟨195880550507, by decide, ⟨293820825761, by decide, ⟨220365619321, by decide, ⟨165274214491, by decide, ⟨247911321737, by decide, ⟨185933491303, by decide, ⟨278900236955, by decide, ⟨418350355433, by decide, ⟨313762766575, by decide, ⟨470644149863, by decide, ⟨705966224795, by decide, ⟨1058949337193, by decide, ⟨794212002895, by decide, ⟨1191318004343, by decide, ⟨1786977006515, by decide, ⟨2680465509773, by decide, ⟨1005174566165, by decide, ⟨47117557789, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_0 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6] (51589939227 + q * 2 ^ 36) endpoint ∧ endpoint < 51589939227 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6] frontier_trace_0 (by decide) (by decide) (by decide) q
#print axioms frontier_class_0

theorem frontier_trace_1 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7] 85949677595 39249308699 := by
  exact ⟨128924516393, by decide, ⟨96693387295, by decide, ⟨145040080943, by decide, ⟨217560121415, by decide, ⟨326340182123, by decide, ⟨489510273185, by decide, ⟨367132704889, by decide, ⟨275349528667, by decide, ⟨413024293001, by decide, ⟨309768219751, by decide, ⟨464652329627, by decide, ⟨696978494441, by decide, ⟨522733870831, by decide, ⟨784100806247, by decide, ⟨1176151209371, by decide, ⟨1764226814057, by decide, ⟨1323170110543, by decide, ⟨1984755165815, by decide, ⟨2977132748723, by decide, ⟨4465699123085, by decide, ⟨1674637171157, by decide, ⟨39249308699, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_1 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7] (85949677595 + q * 2 ^ 37) endpoint ∧ endpoint < 85949677595 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7] frontier_trace_1 (by decide) (by decide) (by decide) q
#print axioms frontier_class_1

theorem frontier_trace_2 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3] 240568500251 164785039229 := by
  exact ⟨360852750377, by decide, ⟨270639562783, by decide, ⟨405959344175, by decide, ⟨608939016263, by decide, ⟨913408524395, by decide, ⟨1370112786593, by decide, ⟨1027584589945, by decide, ⟨770688442459, by decide, ⟨1156032663689, by decide, ⟨867024497767, by decide, ⟨1300536746651, by decide, ⟨1950805119977, by decide, ⟨1463103839983, by decide, ⟨2194655759975, by decide, ⟨3291983639963, by decide, ⟨4937975459945, by decide, ⟨3703481594959, by decide, ⟨5555222392439, by decide, ⟨8332833588659, by decide, ⟨12499250382989, by decide, ⟨4687218893621, by decide, ⟨439426771277, by decide, ⟨164785039229, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_2 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3] (240568500251 + q * 2 ^ 38) endpoint ∧ endpoint < 240568500251 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3] frontier_trace_2 (by decide) (by decide) (by decide) q
#print axioms frontier_class_2

theorem frontier_trace_3 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 8] 17230200859 3934124545 := by
  exact ⟨25845301289, by decide, ⟨19383975967, by decide, ⟨29075963951, by decide, ⟨43613945927, by decide, ⟨65420918891, by decide, ⟨98131378337, by decide, ⟨73598533753, by decide, ⟨55198900315, by decide, ⟨82798350473, by decide, ⟨62098762855, by decide, ⟨93148144283, by decide, ⟨139722216425, by decide, ⟨104791662319, by decide, ⟨157187493479, by decide, ⟨235781240219, by decide, ⟨353671860329, by decide, ⟨265253895247, by decide, ⟨397880842871, by decide, ⟨596821264307, by decide, ⟨895231896461, by decide, ⟨335711961173, by decide, ⟨3934124545, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_3 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 8] (17230200859 + q * 2 ^ 38) endpoint ∧ endpoint < 17230200859 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 8] frontier_trace_3 (by decide) (by decide) (by decide) q
#print axioms frontier_class_3

theorem frontier_trace_4 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4] 266338304027 182436885259 := by
  exact ⟨399507456041, by decide, ⟨299630592031, by decide, ⟨449445888047, by decide, ⟨674168832071, by decide, ⟨1011253248107, by decide, ⟨1516879872161, by decide, ⟨1137659904121, by decide, ⟨853244928091, by decide, ⟨1279867392137, by decide, ⟨959900544103, by decide, ⟨1439850816155, by decide, ⟨2159776224233, by decide, ⟨1619832168175, by decide, ⟨2429748252263, by decide, ⟨3644622378395, by decide, ⟨5466933567593, by decide, ⟨4100200175695, by decide, ⟨6150300263543, by decide, ⟨9225450395315, by decide, ⟨13838175592973, by decide, ⟨5189315847365, by decide, ⟨972996721381, by decide, ⟨182436885259, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_4 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4] (266338304027 + q * 2 ^ 38) endpoint ∧ endpoint < 266338304027 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4] frontier_trace_4 (by decide) (by decide) (by decide) q
#print axioms frontier_class_4

theorem frontier_trace_5 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5] 141784252443 97119629447 := by
  exact ⟨212676378665, by decide, ⟨159507283999, by decide, ⟨239260925999, by decide, ⟨358891388999, by decide, ⟨538337083499, by decide, ⟨807505625249, by decide, ⟨605629218937, by decide, ⟨454221914203, by decide, ⟨681332871305, by decide, ⟨510999653479, by decide, ⟨766499480219, by decide, ⟨1149749220329, by decide, ⟨862311915247, by decide, ⟨1293467872871, by decide, ⟨1940201809307, by decide, ⟨2910302713961, by decide, ⟨2182727035471, by decide, ⟨3274090553207, by decide, ⟨4911135829811, by decide, ⟨7366703744717, by decide, ⟨2762513904269, by decide, ⟨1035942714101, by decide, ⟨97119629447, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_5 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5] (141784252443 + q * 2 ^ 38) endpoint ∧ endpoint < 141784252443 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5] frontier_trace_5 (by decide) (by decide) (by decide) q
#print axioms frontier_class_5

theorem frontier_trace_6 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3] 15292432411 9311144495 := by
  exact ⟨22938648617, by decide, ⟨17203986463, by decide, ⟨25805979695, by decide, ⟨38708969543, by decide, ⟨58063454315, by decide, ⟨87095181473, by decide, ⟨65321386105, by decide, ⟨48991039579, by decide, ⟨73486559369, by decide, ⟨55114919527, by decide, ⟨82672379291, by decide, ⟨124008568937, by decide, ⟨93006426703, by decide, ⟨139509640055, by decide, ⟨209264460083, by decide, ⟨313896690125, by decide, ⟨117711258797, by decide, ⟨44141722049, by decide, ⟨33106291537, by decide, ⟨24829718653, by decide, ⟨9311144495, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_6 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3] (15292432411 + q * 2 ^ 35) endpoint ∧ endpoint < 15292432411 + q * 2 ^ 35 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3] frontier_trace_6 (by decide) (by decide) (by decide) q
#print axioms frontier_class_6

theorem frontier_trace_7 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3] 62537072667 57115673705 := by
  exact ⟨93805609001, by decide, ⟨70354206751, by decide, ⟨105531310127, by decide, ⟨158296965191, by decide, ⟨237445447787, by decide, ⟨356168171681, by decide, ⟨267126128761, by decide, ⟨200344596571, by decide, ⟨300516894857, by decide, ⟨225387671143, by decide, ⟨338081506715, by decide, ⟨507122260073, by decide, ⟨380341695055, by decide, ⟨570512542583, by decide, ⟨855768813875, by decide, ⟨1283653220813, by decide, ⟨481369957805, by decide, ⟨180513734177, by decide, ⟨135385300633, by decide, ⟨101538975475, by decide, ⟨152308463213, by decide, ⟨57115673705, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_7 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3] (62537072667 + q * 2 ^ 36) endpoint ∧ endpoint < 62537072667 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3] frontier_trace_7 (by decide) (by decide) (by decide) q
#print axioms frontier_class_7

theorem frontier_trace_8 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2] 23882367003 21811981645 := by
  exact ⟨35823550505, by decide, ⟨26867662879, by decide, ⟨40301494319, by decide, ⟨60452241479, by decide, ⟨90678362219, by decide, ⟨136017543329, by decide, ⟨102013157497, by decide, ⟨76509868123, by decide, ⟨114764802185, by decide, ⟨86073601639, by decide, ⟨129110402459, by decide, ⟨193665603689, by decide, ⟨145249202767, by decide, ⟨217873804151, by decide, ⟨326810706227, by decide, ⟨490216059341, by decide, ⟨183831022253, by decide, ⟨68936633345, by decide, ⟨51702475009, by decide, ⟨38776856257, by decide, ⟨29082642193, by decide, ⟨21811981645, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_8 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2] (23882367003 + q * 2 ^ 36) endpoint ∧ endpoint < 23882367003 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2] frontier_trace_8 (by decide) (by decide) (by decide) q
#print axioms frontier_class_8

theorem frontier_trace_9 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4] 32472301595 9885748849 := by
  exact ⟨48708452393, by decide, ⟨36531339295, by decide, ⟨54797008943, by decide, ⟨82195513415, by decide, ⟨123293270123, by decide, ⟨184939905185, by decide, ⟨138704928889, by decide, ⟨104028696667, by decide, ⟨156043045001, by decide, ⟨117032283751, by decide, ⟨175548425627, by decide, ⟨263322638441, by decide, ⟨197491978831, by decide, ⟨296237968247, by decide, ⟨444356952371, by decide, ⟨666535428557, by decide, ⟨249950785709, by decide, ⟨93731544641, by decide, ⟨70298658481, by decide, ⟨52723993861, by decide, ⟨9885748849, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_9 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4] (32472301595 + q * 2 ^ 36) endpoint ∧ endpoint < 32472301595 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4] frontier_trace_9 (by decide) (by decide) (by decide) q
#print axioms frontier_class_9

theorem frontier_trace_10 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4] 96896811035 44248366657 := by
  exact ⟨145345216553, by decide, ⟨109008912415, by decide, ⟨163513368623, by decide, ⟨245270052935, by decide, ⟨367905079403, by decide, ⟨551857619105, by decide, ⟨413893214329, by decide, ⟨310419910747, by decide, ⟨465629866121, by decide, ⟨349222399591, by decide, ⟨523833599387, by decide, ⟨785750399081, by decide, ⟨589312799311, by decide, ⟨883969198967, by decide, ⟨1325953798451, by decide, ⟨1988930697677, by decide, ⟨745849011629, by decide, ⟨279693379361, by decide, ⟨209770034521, by decide, ⟨157327525891, by decide, ⟨235991288837, by decide, ⟨44248366657, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_10 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4] (96896811035 + q * 2 ^ 37) endpoint ∧ endpoint < 96896811035 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4] frontier_trace_10 (by decide) (by decide) (by decide) q
#print axioms frontier_class_10

theorem frontier_trace_11 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3] 58242105371 26596520627 := by
  exact ⟨87363158057, by decide, ⟨65522368543, by decide, ⟨98283552815, by decide, ⟨147425329223, by decide, ⟨221137993835, by decide, ⟨331706990753, by decide, ⟨248780243065, by decide, ⟨186585182299, by decide, ⟨279877773449, by decide, ⟨209908330087, by decide, ⟨314862495131, by decide, ⟨472293742697, by decide, ⟨354220307023, by decide, ⟨531330460535, by decide, ⟨796995690803, by decide, ⟨1195493536205, by decide, ⟨448310076077, by decide, ⟨168116278529, by decide, ⟨126087208897, by decide, ⟨94565406673, by decide, ⟨70924055005, by decide, ⟨26596520627, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_11 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3] (58242105371 + q * 2 ^ 37) endpoint ∧ endpoint < 58242105371 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3] frontier_trace_11 (by decide) (by decide) (by decide) q
#print axioms frontier_class_11

theorem frontier_trace_12 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 5] 135551516699 20633404229 := by
  exact ⟨203327275049, by decide, ⟨152495456287, by decide, ⟨228743184431, by decide, ⟨343114776647, by decide, ⟨514672164971, by decide, ⟨772008247457, by decide, ⟨579006185593, by decide, ⟨434254639195, by decide, ⟨651381958793, by decide, ⟨488536469095, by decide, ⟨732804703643, by decide, ⟨1099207055465, by decide, ⟨824405291599, by decide, ⟨1236607937399, by decide, ⟨1854911906099, by decide, ⟨2782367859149, by decide, ⟨1043387947181, by decide, ⟨391270480193, by decide, ⟨293452860145, by decide, ⟨220089645109, by decide, ⟨20633404229, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_12 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 5] (135551516699 + q * 2 ^ 37) endpoint ∧ endpoint < 135551516699 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 5] frontier_trace_12 (by decide) (by decide) (by decide) q
#print axioms frontier_class_12

theorem frontier_trace_13 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4] 139846483995 95792293369 := by
  exact ⟨209769725993, by decide, ⟨157327294495, by decide, ⟨235990941743, by decide, ⟨353986412615, by decide, ⟨530979618923, by decide, ⟨796469428385, by decide, ⟨597352071289, by decide, ⟨448014053467, by decide, ⟨672021080201, by decide, ⟨504015810151, by decide, ⟨756023715227, by decide, ⟨1134035572841, by decide, ⟨850526679631, by decide, ⟨1275790019447, by decide, ⟨1913685029171, by decide, ⟨2870527543757, by decide, ⟨1076447828909, by decide, ⟨403667935841, by decide, ⟨302750951881, by decide, ⟨227063213911, by decide, ⟨340594820867, by decide, ⟨510892231301, by decide, ⟨95792293369, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_13 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4] (139846483995 + q * 2 ^ 38) endpoint ∧ endpoint < 139846483995 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4] frontier_trace_13 (by decide) (by decide) (by decide) q
#print axioms frontier_class_13

theorem frontier_trace_14 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3] 114076680219 78140447339 := by
  exact ⟨171115020329, by decide, ⟨128336265247, by decide, ⟨192504397871, by decide, ⟨288756596807, by decide, ⟨433134895211, by decide, ⟨649702342817, by decide, ⟨487276757113, by decide, ⟨365457567835, by decide, ⟨548186351753, by decide, ⟨411139763815, by decide, ⟨616709645723, by decide, ⟨925064468585, by decide, ⟨693798351439, by decide, ⟨1040697527159, by decide, ⟨1561046290739, by decide, ⟨2341569436109, by decide, ⟨878088538541, by decide, ⟨329283201953, by decide, ⟨246962401465, by decide, ⟨185221801099, by decide, ⟨277832701649, by decide, ⟨208374526237, by decide, ⟨78140447339, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_14 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3] (114076680219 + q * 2 ^ 38) endpoint ∧ endpoint < 114076680219 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3] frontier_trace_14 (by decide) (by decide) (by decide) q
#print axioms frontier_class_14

theorem frontier_trace_15 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 5] 165616287771 37814713133 := by
  exact ⟨248424431657, by decide, ⟨186318323743, by decide, ⟨279477485615, by decide, ⟨419216228423, by decide, ⟨628824342635, by decide, ⟨943236513953, by decide, ⟨707427385465, by decide, ⟨530570539099, by decide, ⟨795855808649, by decide, ⟨596891856487, by decide, ⟨895337784731, by decide, ⟨1343006677097, by decide, ⟨1007255007823, by decide, ⟨1510882511735, by decide, ⟨2266323767603, by decide, ⟨3399485651405, by decide, ⟨1274807119277, by decide, ⟨478052669729, by decide, ⟨358539502297, by decide, ⟨268904626723, by decide, ⟨403356940085, by decide, ⟨37814713133, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_15 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 5] (165616287771 + q * 2 ^ 38) endpoint ∧ endpoint < 165616287771 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 5] frontier_trace_15 (by decide) (by decide) (by decide) q
#print axioms frontier_class_15

theorem frontier_trace_16 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3] 212860928027 145805857121 := by
  exact ⟨319291392041, by decide, ⟨239468544031, by decide, ⟨359202816047, by decide, ⟨538804224071, by decide, ⟨808206336107, by decide, ⟨1212309504161, by decide, ⟨909232128121, by decide, ⟨681924096091, by decide, ⟨1022886144137, by decide, ⟨767164608103, by decide, ⟨1150746912155, by decide, ⟨1726120368233, by decide, ⟨1294590276175, by decide, ⟨1941885414263, by decide, ⟨2912828121395, by decide, ⟨4369242182093, by decide, ⟨1638465818285, by decide, ⟨614424681857, by decide, ⟨460818511393, by decide, ⟨345613883545, by decide, ⟨259210412659, by decide, ⟨388815618989, by decide, ⟨145805857121, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_16 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3] (212860928027 + q * 2 ^ 38) endpoint ∧ endpoint < 212860928027 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3] frontier_trace_16 (by decide) (by decide) (by decide) q
#print axioms frontier_class_16

theorem frontier_trace_17 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 4] 264400535579 60369849727 := by
  exact ⟨396600803369, by decide, ⟨297450602527, by decide, ⟨446175903791, by decide, ⟨669263855687, by decide, ⟨1003895783531, by decide, ⟨1505843675297, by decide, ⟨1129382756473, by decide, ⟨847037067355, by decide, ⟨1270555601033, by decide, ⟨952916700775, by decide, ⟨1429375051163, by decide, ⟨2144062576745, by decide, ⟨1608046932559, by decide, ⟨2412070398839, by decide, ⟨3618105598259, by decide, ⟨5427158397389, by decide, ⟨2035184399021, by decide, ⟨763194149633, by decide, ⟨572395612225, by decide, ⟨429296709169, by decide, ⟨321972531877, by decide, ⟨60369849727, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_17 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 4] (264400535579 + q * 2 ^ 38) endpoint ∧ endpoint < 264400535579 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 4] frontier_trace_17 (by decide) (by decide) (by decide) q
#print axioms frontier_class_17

theorem frontier_trace_18 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 6] 66832039963 5086525513 := by
  exact ⟨100248059945, by decide, ⟨75186044959, by decide, ⟨112779067439, by decide, ⟨169168601159, by decide, ⟨253752901739, by decide, ⟨380629352609, by decide, ⟨285472014457, by decide, ⟨214104010843, by decide, ⟨321156016265, by decide, ⟨240867012199, by decide, ⟨361300518299, by decide, ⟨541950777449, by decide, ⟨406463083087, by decide, ⟨609694624631, by decide, ⟨914541936947, by decide, ⟨1371812905421, by decide, ⟨514429839533, by decide, ⟨192911189825, by decide, ⟨144683392369, by decide, ⟨108512544277, by decide, ⟨5086525513, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_18 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 6] (66832039963 + q * 2 ^ 38) endpoint ∧ endpoint < 66832039963 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 6] frontier_trace_18 (by decide) (by decide) (by decide) q
#print axioms frontier_class_18

theorem frontier_trace_19 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5] 2407530523 824557271 := by
  exact ⟨3611295785, by decide, ⟨2708471839, by decide, ⟨4062707759, by decide, ⟨6094061639, by decide, ⟨9141092459, by decide, ⟨13711638689, by decide, ⟨10283729017, by decide, ⟨7712796763, by decide, ⟨11569195145, by decide, ⟨8676896359, by decide, ⟨13015344539, by decide, ⟨19523016809, by decide, ⟨14642262607, by decide, ⟨21963393911, by decide, ⟨32945090867, by decide, ⟨49417636301, by decide, ⟨18531613613, by decide, ⟨6949355105, by decide, ⟨5212016329, by decide, ⟨3909012247, by decide, ⟨5863518371, by decide, ⟨8795277557, by decide, ⟨824557271, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_19 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5] (2407530523 + q * 2 ^ 39) endpoint ∧ endpoint < 2407530523 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5] frontier_trace_19 (by decide) (by decide) (by decide) q
#print axioms frontier_class_19

theorem frontier_trace_20 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4] 251515633691 86141813083 := by
  exact ⟨377273450537, by decide, ⟨282955087903, by decide, ⟨424432631855, by decide, ⟨636648947783, by decide, ⟨954973421675, by decide, ⟨1432460132513, by decide, ⟨1074345099385, by decide, ⟨805758824539, by decide, ⟨1208638236809, by decide, ⟨906478677607, by decide, ⟨1359718016411, by decide, ⟨2039577024617, by decide, ⟨1529682768463, by decide, ⟨2294524152695, by decide, ⟨3441786229043, by decide, ⟨5162679343565, by decide, ⟨1936004753837, by decide, ⟨726001782689, by decide, ⟨544501337017, by decide, ⟨408376002763, by decide, ⟨612564004145, by decide, ⟨459423003109, by decide, ⟨86141813083, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_20 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4] (251515633691 + q * 2 ^ 39) endpoint ∧ endpoint < 251515633691 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4] frontier_trace_20 (by decide) (by decide) (by decide) q
#print axioms frontier_class_20

theorem frontier_trace_21 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 6] 303055241243 34597886371 := by
  exact ⟨454582861865, by decide, ⟨340937146399, by decide, ⟨511405719599, by decide, ⟨767108579399, by decide, ⟨1150662869099, by decide, ⟨1725994303649, by decide, ⟨1294495727737, by decide, ⟨970871795803, by decide, ⟨1456307693705, by decide, ⟨1092230770279, by decide, ⟨1638346155419, by decide, ⟨2457519233129, by decide, ⟨1843139424847, by decide, ⟨2764709137271, by decide, ⟨4147063705907, by decide, ⟨6220595558861, by decide, ⟨2332723334573, by decide, ⟨874771250465, by decide, ⟨656078437849, by decide, ⟨492058828387, by decide, ⟨738088242581, by decide, ⟨34597886371, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_21 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 6] (303055241243 + q * 2 ^ 39) endpoint ∧ endpoint < 303055241243 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 6] frontier_trace_21 (by decide) (by decide) (by decide) q
#print axioms frontier_class_21

theorem frontier_trace_22 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4] 75421974555 25831339147 := by
  exact ⟨113132961833, by decide, ⟨84849721375, by decide, ⟨127274582063, by decide, ⟨190911873095, by decide, ⟨286367809643, by decide, ⟨429551714465, by decide, ⟨322163785849, by decide, ⟨241622839387, by decide, ⟨362434259081, by decide, ⟨271825694311, by decide, ⟨407738541467, by decide, ⟨611607812201, by decide, ⟨458705859151, by decide, ⟨688058788727, by decide, ⟨1032088183091, by decide, ⟨1548132274637, by decide, ⟨580549602989, by decide, ⟨217706101121, by decide, ⟨163279575841, by decide, ⟨122459681881, by decide, ⟨91844761411, by decide, ⟨137767142117, by decide, ⟨25831339147, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_22 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4] (75421974555 + q * 2 ^ 39) endpoint ∧ endpoint < 75421974555 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4] frontier_trace_22 (by decide) (by decide) (by decide) q
#print axioms frontier_class_22

theorem frontier_trace_23 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 5] 126961582107 14494395059 := by
  exact ⟨190442373161, by decide, ⟨142831779871, by decide, ⟨214247669807, by decide, ⟨321371504711, by decide, ⟨482057257067, by decide, ⟨723085885601, by decide, ⟨542314414201, by decide, ⟨406735810651, by decide, ⟨610103715977, by decide, ⟨457577786983, by decide, ⟨686366680475, by decide, ⟨1029550020713, by decide, ⟨772162515535, by decide, ⟨1158243773303, by decide, ⟨1737365659955, by decide, ⟨2606048489933, by decide, ⟨977268183725, by decide, ⟨366475568897, by decide, ⟨274856676673, by decide, ⟨206142507505, by decide, ⟨154606880629, by decide, ⟨14494395059, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_23 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 5] (126961582107 + q * 2 ^ 39) endpoint ∧ endpoint < 126961582107 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 5] frontier_trace_23 (by decide) (by decide) (by decide) q
#print axioms frontier_class_23

theorem frontier_trace_24 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 7] 479148900379 18233792561 := by
  exact ⟨718723350569, by decide, ⟨539042512927, by decide, ⟨808563769391, by decide, ⟨1212845654087, by decide, ⟨1819268481131, by decide, ⟨2728902721697, by decide, ⟨2046677041273, by decide, ⟨1535007780955, by decide, ⟨2302511671433, by decide, ⟨1726883753575, by decide, ⟨2590325630363, by decide, ⟨3885488445545, by decide, ⟨2914116334159, by decide, ⟨4371174501239, by decide, ⟨6556761751859, by decide, ⟨9835142627789, by decide, ⟨3688178485421, by decide, ⟨1383066932033, by decide, ⟨1037300199025, by decide, ⟨777975149269, by decide, ⟨18233792561, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_24 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 7] (479148900379 + q * 2 ^ 39) endpoint ∧ endpoint < 479148900379 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 7] frontier_trace_24 (by decide) (by decide) (by decide) q
#print axioms frontier_class_24

theorem frontier_trace_25 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7] 60184068123 54966653387 := by
  exact ⟨90276102185, by decide, ⟨67707076639, by decide, ⟨101560614959, by decide, ⟨152340922439, by decide, ⟨228511383659, by decide, ⟨342767075489, by decide, ⟨257075306617, by decide, ⟨192806479963, by decide, ⟨289209719945, by decide, ⟨216907289959, by decide, ⟨325360934939, by decide, ⟨488041402409, by decide, ⟨366031051807, by decide, ⟨549046577711, by decide, ⟨823569866567, by decide, ⟨1235354799851, by decide, ⟨1853032199777, by decide, ⟨1389774149833, by decide, ⟨1042330612375, by decide, ⟨1563495918563, by decide, ⟨2345243877845, by decide, ⟨54966653387, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_25 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7] (60184068123 + q * 2 ^ 36) endpoint ∧ endpoint < 60184068123 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7] frontier_trace_25 (by decide) (by decide) (by decide) q
#print axioms frontier_class_25

theorem frontier_trace_26 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8] 25824329755 11792796889 := by
  exact ⟨38736494633, by decide, ⟨29052370975, by decide, ⟨43578556463, by decide, ⟨65367834695, by decide, ⟨98051752043, by decide, ⟨147077628065, by decide, ⟨110308221049, by decide, ⟨82731165787, by decide, ⟨124096748681, by decide, ⟨93072561511, by decide, ⟨139608842267, by decide, ⟨209413263401, by decide, ⟨157059947551, by decide, ⟨235589921327, by decide, ⟨353384881991, by decide, ⟨530077322987, by decide, ⟨795115984481, by decide, ⟨596336988361, by decide, ⟨447252741271, by decide, ⟨670879111907, by decide, ⟨1006318667861, by decide, ⟨11792796889, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_26 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8] (25824329755 + q * 2 ^ 37) endpoint ∧ endpoint < 25824329755 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8] frontier_trace_26 (by decide) (by decide) (by decide) q
#print axioms frontier_class_26

theorem frontier_trace_27 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4] 68774002715 47108938717 := by
  exact ⟨103161004073, by decide, ⟨77370753055, by decide, ⟨116056129583, by decide, ⟨174084194375, by decide, ⟨261126291563, by decide, ⟨391689437345, by decide, ⟨293767078009, by decide, ⟨220325308507, by decide, ⟨330487962761, by decide, ⟨247865972071, by decide, ⟨371798958107, by decide, ⟨557698437161, by decide, ⟨418273827871, by decide, ⟨627410741807, by decide, ⟨941116112711, by decide, ⟨1411674169067, by decide, ⟨2117511253601, by decide, ⟨1588133440201, by decide, ⟨1191100080151, by decide, ⟨1786650120227, by decide, ⟨2679975180341, by decide, ⟨251247673157, by decide, ⟨47108938717, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_27 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4] (68774002715 + q * 2 ^ 38) endpoint ∧ endpoint < 68774002715 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4] frontier_trace_27 (by decide) (by decide) (by decide) q
#print axioms frontier_class_27

theorem frontier_trace_28 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3] 43004198939 29457092687 := by
  exact ⟨64506298409, by decide, ⟨48379723807, by decide, ⟨72569585711, by decide, ⟨108854378567, by decide, ⟨163281567851, by decide, ⟨244922351777, by decide, ⟨183691763833, by decide, ⟨137768822875, by decide, ⟨206653234313, by decide, ⟨154989925735, by decide, ⟨232484888603, by decide, ⟨348727332905, by decide, ⟨261545499679, by decide, ⟨392318249519, by decide, ⟨588477374279, by decide, ⟨882716061419, by decide, ⟨1324074092129, by decide, ⟨993055569097, by decide, ⟨744791676823, by decide, ⟨1117187515235, by decide, ⟨1675781272853, by decide, ⟨78552247165, by decide, ⟨29457092687, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_28 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3] (43004198939 + q * 2 ^ 38) endpoint ∧ endpoint < 43004198939 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3] frontier_trace_28 (by decide) (by decide) (by decide) q
#print axioms frontier_class_28

theorem frontier_trace_29 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 9] 94543806491 21586928249 := by
  exact ⟨141815709737, by decide, ⟨106361782303, by decide, ⟨159542673455, by decide, ⟨239314010183, by decide, ⟨358971015275, by decide, ⟨538456522913, by decide, ⟨403842392185, by decide, ⟨302881794139, by decide, ⟨454322691209, by decide, ⟨340742018407, by decide, ⟨511113027611, by decide, ⟨766669541417, by decide, ⟨575002156063, by decide, ⟨862503234095, by decide, ⟨1293754851143, by decide, ⟨1940632276715, by decide, ⟨2910948415073, by decide, ⟨2183211311305, by decide, ⟨1637408483479, by decide, ⟨2456112725219, by decide, ⟨3684169087829, by decide, ⟨21586928249, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_29 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 9] (94543806491 + q * 2 ^ 38) endpoint ∧ endpoint < 94543806491 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 9] frontier_trace_29 (by decide) (by decide) (by decide) q
#print axioms frontier_class_29

theorem frontier_trace_30 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4] 21594374171 13148224741 := by
  exact ⟨32391561257, by decide, ⟨24293670943, by decide, ⟨36440506415, by decide, ⟨54660759623, by decide, ⟨81991139435, by decide, ⟨122986709153, by decide, ⟨92240031865, by decide, ⟨69180023899, by decide, ⟨103770035849, by decide, ⟨77827526887, by decide, ⟨116741290331, by decide, ⟨175111935497, by decide, ⟨131333951623, by decide, ⟨197000927435, by decide, ⟨295501391153, by decide, ⟨221626043365, by decide, ⟨41554883131, by decide, ⟨62332324697, by decide, ⟨46749243523, by decide, ⟨70123865285, by decide, ⟨13148224741, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_30 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4] (21594374171 + q * 2 ^ 35) endpoint ∧ endpoint < 21594374171 + q * 2 ^ 35 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4] frontier_trace_30 (by decide) (by decide) (by decide) q
#print axioms frontier_class_30

theorem frontier_trace_31 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5] 4414504987 1343935769 := by
  exact ⟨6621757481, by decide, ⟨4966318111, by decide, ⟨7449477167, by decide, ⟨11174215751, by decide, ⟨16761323627, by decide, ⟨25141985441, by decide, ⟨18856489081, by decide, ⟨14142366811, by decide, ⟨21213550217, by decide, ⟨15910162663, by decide, ⟨23865243995, by decide, ⟨35797865993, by decide, ⟨26848399495, by decide, ⟨40272599243, by decide, ⟨60408898865, by decide, ⟨45306674149, by decide, ⟨8495001403, by decide, ⟨12742502105, by decide, ⟨9556876579, by decide, ⟨14335314869, by decide, ⟨1343935769, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_31 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5] (4414504987 + q * 2 ^ 36) endpoint ∧ endpoint < 4414504987 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5] frontier_trace_31 (by decide) (by decide) (by decide) q
#print axioms frontier_class_31

theorem frontier_trace_32 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2] 64544047131 58948661623 := by
  exact ⟨96816070697, by decide, ⟨72612053023, by decide, ⟨108918079535, by decide, ⟨163377119303, by decide, ⟨245065678955, by decide, ⟨367598518433, by decide, ⟨275698888825, by decide, ⟨206774166619, by decide, ⟨310161249929, by decide, ⟨232620937447, by decide, ⟨348931406171, by decide, ⟨523397109257, by decide, ⟨392547831943, by decide, ⟨588821747915, by decide, ⟨883232621873, by decide, ⟨662424466405, by decide, ⟨124204587451, by decide, ⟨186306881177, by decide, ⟨139730160883, by decide, ⟨209595241325, by decide, ⟨78598215497, by decide, ⟨58948661623, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_32 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2] (64544047131 + q * 2 ^ 36) endpoint ∧ endpoint < 64544047131 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2] frontier_trace_32 (by decide) (by decide) (by decide) q
#print axioms frontier_class_32

theorem frontier_trace_33 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4] 53806628891 49142080495 := by
  exact ⟨80709943337, by decide, ⟨60532457503, by decide, ⟨90798686255, by decide, ⟨136198029383, by decide, ⟨204297044075, by decide, ⟨306445566113, by decide, ⟨229834174585, by decide, ⟨172375630939, by decide, ⟨258563446409, by decide, ⟨193922584807, by decide, ⟨290883877211, by decide, ⟨436325815817, by decide, ⟨327244361863, by decide, ⟨490866542795, by decide, ⟨736299814193, by decide, ⟨552224860645, by decide, ⟨103542161371, by decide, ⟨155313242057, by decide, ⟨116484931543, by decide, ⟨174727397315, by decide, ⟨262091095973, by decide, ⟨49142080495, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_33 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4] (53806628891 + q * 2 ^ 36) endpoint ∧ endpoint < 53806628891 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4] frontier_trace_33 (by decide) (by decide) (by decide) q
#print axioms frontier_class_33

theorem frontier_trace_34 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 6] 107493720091 16362497689 := by
  exact ⟨161240580137, by decide, ⟨120930435103, by decide, ⟨181395652655, by decide, ⟨272093478983, by decide, ⟨408140218475, by decide, ⟨612210327713, by decide, ⟨459157745785, by decide, ⟨344368309339, by decide, ⟨516552464009, by decide, ⟨387414348007, by decide, ⟨581121522011, by decide, ⟨871682283017, by decide, ⟨653761712263, by decide, ⟨980642568395, by decide, ⟨1470963852593, by decide, ⟨1103222889445, by decide, ⟨206854291771, by decide, ⟨310281437657, by decide, ⟨232711078243, by decide, ⟨349066617365, by decide, ⟨16362497689, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_34 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 6] (107493720091 + q * 2 ^ 37) endpoint ∧ endpoint < 107493720091 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 6] frontier_trace_34 (by decide) (by decide) (by decide) q
#print axioms frontier_class_34

theorem frontier_trace_35 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3] 30184308763 13783801007 := by
  exact ⟨45276463145, by decide, ⟨33957347359, by decide, ⟨50936021039, by decide, ⟨76404031559, by decide, ⟨114606047339, by decide, ⟨171909071009, by decide, ⟨128931803257, by decide, ⟨96698852443, by decide, ⟨145048278665, by decide, ⟨108786208999, by decide, ⟨163179313499, by decide, ⟨244768970249, by decide, ⟨183576727687, by decide, ⟨275365091531, by decide, ⟨413047637297, by decide, ⟨309785727973, by decide, ⟨58084823995, by decide, ⟨87127235993, by decide, ⟨65345426995, by decide, ⟨98018140493, by decide, ⟨36756802685, by decide, ⟨13783801007, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_35 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3] (30184308763 + q * 2 ^ 37) endpoint ∧ endpoint < 30184308763 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3] frontier_trace_35 (by decide) (by decide) (by decide) q
#print axioms frontier_class_35

theorem frontier_trace_36 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5] 19446890523 8880510443 := by
  exact ⟨29170335785, by decide, ⟨21877751839, by decide, ⟨32816627759, by decide, ⟨49224941639, by decide, ⟨73837412459, by decide, ⟨110756118689, by decide, ⟨83067089017, by decide, ⟨62300316763, by decide, ⟨93450475145, by decide, ⟨70087856359, by decide, ⟨105131784539, by decide, ⟨157697676809, by decide, ⟨118273257607, by decide, ⟨177409886411, by decide, ⟨266114829617, by decide, ⟨199586122213, by decide, ⟨37422397915, by decide, ⟨56133596873, by decide, ⟨42100197655, by decide, ⟨63150296483, by decide, ⟨94725444725, by decide, ⟨8880510443, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_36 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5] (19446890523 + q * 2 ^ 37) endpoint ∧ endpoint < 19446890523 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5] frontier_trace_36 (by decide) (by decide) (by decide) q
#print axioms frontier_class_36

theorem frontier_trace_37 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3] 86018883611 58921367909 := by
  exact ⟨129028325417, by decide, ⟨96771244063, by decide, ⟨145156866095, by decide, ⟨217735299143, by decide, ⟨326602948715, by decide, ⟨489904423073, by decide, ⟨367428317305, by decide, ⟨275571237979, by decide, ⟨413356856969, by decide, ⟨310017642727, by decide, ⟨465026464091, by decide, ⟨697539696137, by decide, ⟨523154772103, by decide, ⟨784732158155, by decide, ⟨1177098237233, by decide, ⟨882823677925, by decide, ⟨165529439611, by decide, ⟨248294159417, by decide, ⟨186220619563, by decide, ⟨279330929345, by decide, ⟨209498197009, by decide, ⟨157123647757, by decide, ⟨58921367909, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_37 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3] (86018883611 + q * 2 ^ 38) endpoint ∧ endpoint < 86018883611 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3] frontier_trace_37 (by decide) (by decide) (by decide) q
#print axioms frontier_class_37

theorem frontier_trace_38 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4] 111788687387 76573213939 := by
  exact ⟨167683031081, by decide, ⟨125762273311, by decide, ⟨188643409967, by decide, ⟨282965114951, by decide, ⟨424447672427, by decide, ⟨636671508641, by decide, ⟨477503631481, by decide, ⟨358127723611, by decide, ⟨537191585417, by decide, ⟨402893689063, by decide, ⟨604340533595, by decide, ⟨906510800393, by decide, ⟨679883100295, by decide, ⟨1019824650443, by decide, ⟨1529736975665, by decide, ⟨1147302731749, by decide, ⟨215119262203, by decide, ⟨322678893305, by decide, ⟨242009169979, by decide, ⟨363013754969, by decide, ⟨272260316227, by decide, ⟨408390474341, by decide, ⟨76573213939, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_38 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4] (111788687387 + q * 2 ^ 38) endpoint ∧ endpoint < 111788687387 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4] frontier_trace_38 (by decide) (by decide) (by decide) q
#print axioms frontier_class_38

theorem frontier_trace_39 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 7] 38774243355 2951072243 := by
  exact ⟨58161365033, by decide, ⟨43621023775, by decide, ⟨65431535663, by decide, ⟨98147303495, by decide, ⟨147220955243, by decide, ⟨220831432865, by decide, ⟨165623574649, by decide, ⟨124217680987, by decide, ⟨186326521481, by decide, ⟨139744891111, by decide, ⟨209617336667, by decide, ⟨314426005001, by decide, ⟨235819503751, by decide, ⟨353729255627, by decide, ⟨530593883441, by decide, ⟨397945412581, by decide, ⟨74614764859, by decide, ⟨111922147289, by decide, ⟨83941610467, by decide, ⟨125912415701, by decide, ⟨2951072243, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_39 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 7] (38774243355 + q * 2 ^ 38) endpoint ∧ endpoint < 38774243355 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 7] frontier_trace_39 (by decide) (by decide) (by decide) q
#print axioms frontier_class_39

theorem frontier_trace_40 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3] 184803131419 126586777691 := by
  exact ⟨277204697129, by decide, ⟨207903522847, by decide, ⟨311855284271, by decide, ⟨467782926407, by decide, ⟨701674389611, by decide, ⟨1052511584417, by decide, ⟨789383688313, by decide, ⟨592037766235, by decide, ⟨888056649353, by decide, ⟨666042487015, by decide, ⟨999063730523, by decide, ⟨1498595595785, by decide, ⟨1123946696839, by decide, ⟨1685920045259, by decide, ⟨2528880067889, by decide, ⟨1896660050917, by decide, ⟨355623759547, by decide, ⟨533435639321, by decide, ⟨400076729491, by decide, ⟨600115094237, by decide, ⟨225043160339, by decide, ⟨337564740509, by decide, ⟨126586777691, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_40 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3] (184803131419 + q * 2 ^ 38) endpoint ∧ endpoint < 184803131419 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3] frontier_trace_40 (by decide) (by decide) (by decide) q
#print axioms frontier_class_40

theorem frontier_trace_41 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 4] 236342738971 53963489917 := by
  exact ⟨354514108457, by decide, ⟨265885581343, by decide, ⟨398828372015, by decide, ⟨598242558023, by decide, ⟨897363837035, by decide, ⟨1346045755553, by decide, ⟨1009534316665, by decide, ⟨757150737499, by decide, ⟨1135726106249, by decide, ⟨851794579687, by decide, ⟨1277691869531, by decide, ⟨1916537804297, by decide, ⟨1437403353223, by decide, ⟨2156105029835, by decide, ⟨3234157544753, by decide, ⟨2425618158565, by decide, ⟨454803404731, by decide, ⟨682205107097, by decide, ⟨511653830323, by decide, ⟨767480745485, by decide, ⟨287805279557, by decide, ⟨53963489917, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_41 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 4] (236342738971 + q * 2 ^ 38) endpoint ∧ endpoint < 236342738971 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 4] frontier_trace_41 (by decide) (by decide) (by decide) q
#print axioms frontier_class_41

theorem frontier_trace_42 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3] 174065713179 119231841845 := by
  exact ⟨261098569769, by decide, ⟨195823927327, by decide, ⟨293735890991, by decide, ⟨440603836487, by decide, ⟨660905754731, by decide, ⟨991358632097, by decide, ⟨743518974073, by decide, ⟨557639230555, by decide, ⟨836458845833, by decide, ⟨627344134375, by decide, ⟨941016201563, by decide, ⟨1411524302345, by decide, ⟨1058643226759, by decide, ⟨1587964840139, by decide, ⟨2381947260209, by decide, ⟨1786460445157, by decide, ⟨334961333467, by decide, ⟨502442000201, by decide, ⟨376831500151, by decide, ⟨565247250227, by decide, ⟨847870875341, by decide, ⟨317951578253, by decide, ⟨119231841845, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_42 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3] (174065713179 + q * 2 ^ 38) endpoint ∧ endpoint < 174065713179 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3] frontier_trace_42 (by decide) (by decide) (by decide) q
#print axioms frontier_class_42

theorem frontier_trace_43 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 6] 225605320731 51511844635 := by
  exact ⟨338407981097, by decide, ⟨253805985823, by decide, ⟨380708978735, by decide, ⟨571063468103, by decide, ⟨856595202155, by decide, ⟨1284892803233, by decide, ⟨963669602425, by decide, ⟨722752201819, by decide, ⟨1084128302729, by decide, ⟨813096227047, by decide, ⟨1219644340571, by decide, ⟨1829466510857, by decide, ⟨1372099883143, by decide, ⟨2058149824715, by decide, ⟨3087224737073, by decide, ⟨2315418552805, by decide, ⟨434140978651, by decide, ⟨651211467977, by decide, ⟨488408600983, by decide, ⟨732612901475, by decide, ⟨1098919352213, by decide, ⟨51511844635, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_43 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 6] (225605320731 + q * 2 ^ 38) endpoint ∧ endpoint < 225605320731 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 6] frontier_trace_43 (by decide) (by decide) (by decide) q
#print axioms frontier_class_43

theorem frontier_trace_44 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4] 199835516955 136883687875 := by
  exact ⟨299753275433, by decide, ⟨224814956575, by decide, ⟨337222434863, by decide, ⟨505833652295, by decide, ⟨758750478443, by decide, ⟨1138125717665, by decide, ⟨853594288249, by decide, ⟨640195716187, by decide, ⟨960293574281, by decide, ⟨720220180711, by decide, ⟨1080330271067, by decide, ⟨1620495406601, by decide, ⟨1215371554951, by decide, ⟨1823057332427, by decide, ⟨2734585998641, by decide, ⟨2050939498981, by decide, ⟨384551156059, by decide, ⟨576826734089, by decide, ⟨432620050567, by decide, ⟨648930075851, by decide, ⟨973395113777, by decide, ⟨730046335333, by decide, ⟨136883687875, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_44 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4] (199835516955 + q * 2 ^ 38) endpoint ∧ endpoint < 199835516955 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4] frontier_trace_44 (by decide) (by decide) (by decide) q
#print axioms frontier_class_44

theorem frontier_trace_45 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4] 6503268379 5279550037 := by
  exact ⟨9754902569, by decide, ⟨7316176927, by decide, ⟨10974265391, by decide, ⟨16461398087, by decide, ⟨24692097131, by decide, ⟨37038145697, by decide, ⟨27778609273, by decide, ⟨20833956955, by decide, ⟨31250935433, by decide, ⟨23438201575, by decide, ⟨35157302363, by decide, ⟨52735953545, by decide, ⟨39551965159, by decide, ⟨59327947739, by decide, ⟨88991921609, by decide, ⟨66743941207, by decide, ⟨100115911811, by decide, ⟨150173867717, by decide, ⟨28157600197, by decide, ⟨5279550037, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_45 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4] (6503268379 + q * 2 ^ 33) endpoint ∧ endpoint < 6503268379 + q * 2 ^ 33 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4] frontier_trace_45 (by decide) (by decide) (by decide) q
#print axioms frontier_class_45

theorem frontier_trace_46 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5] 10798235675 4383167219 := by
  exact ⟨16197353513, by decide, ⟨12148015135, by decide, ⟨18222022703, by decide, ⟨27333034055, by decide, ⟨40999551083, by decide, ⟨61499326625, by decide, ⟨46124494969, by decide, ⟨34593371227, by decide, ⟨51890056841, by decide, ⟨38917542631, by decide, ⟨58376313947, by decide, ⟨87564470921, by decide, ⟨65673353191, by decide, ⟨98510029787, by decide, ⟨147765044681, by decide, ⟨110823783511, by decide, ⟨166235675267, by decide, ⟨249353512901, by decide, ⟨46753783669, by decide, ⟨4383167219, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_46 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5] (10798235675 + q * 2 ^ 34) endpoint ∧ endpoint < 10798235675 + q * 2 ^ 34 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5] frontier_trace_46 (by decide) (by decide) (by decide) q
#print axioms frontier_class_46

theorem frontier_trace_47 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3] 12945719323 7882294979 := by
  exact ⟨19418578985, by decide, ⟨14563934239, by decide, ⟨21845901359, by decide, ⟨32768852039, by decide, ⟨49153278059, by decide, ⟨73729917089, by decide, ⟨55297437817, by decide, ⟨41473078363, by decide, ⟨62209617545, by decide, ⟨46657213159, by decide, ⟨69985819739, by decide, ⟨104978729609, by decide, ⟨78734047207, by decide, ⟨118101070811, by decide, ⟨177151606217, by decide, ⟨132863704663, by decide, ⟨199295556995, by decide, ⟨298943335493, by decide, ⟨56051875405, by decide, ⟨21019453277, by decide, ⟨7882294979, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_47 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3] (12945719323 + q * 2 ^ 35) endpoint ∧ endpoint < 12945719323 + q * 2 ^ 35 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3] frontier_trace_47 (by decide) (by decide) (by decide) q
#print axioms frontier_class_47

theorem frontier_trace_48 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6] 2208301083 448191409 := by
  exact ⟨3312451625, by decide, ⟨2484338719, by decide, ⟨3726508079, by decide, ⟨5589762119, by decide, ⟨8384643179, by decide, ⟨12576964769, by decide, ⟨9432723577, by decide, ⟨7074542683, by decide, ⟨10611814025, by decide, ⟨7958860519, by decide, ⟨11938290779, by decide, ⟨17907436169, by decide, ⟨13430577127, by decide, ⟨20145865691, by decide, ⟨30218798537, by decide, ⟨22664098903, by decide, ⟨33996148355, by decide, ⟨50994222533, by decide, ⟨9561416725, by decide, ⟨448191409, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_48 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6] (2208301083 + q * 2 ^ 35) endpoint ∧ endpoint < 2208301083 + q * 2 ^ 35 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6] frontier_trace_48 (by decide) (by decide) (by decide) q
#print axioms frontier_class_48

theorem frontier_trace_49 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3] 60190359579 54972399431 := by
  exact ⟨90285539369, by decide, ⟨67714154527, by decide, ⟨101571231791, by decide, ⟨152356847687, by decide, ⟨228535271531, by decide, ⟨342802907297, by decide, ⟨257102180473, by decide, ⟨192826635355, by decide, ⟨289239953033, by decide, ⟨216929964775, by decide, ⟨325394947163, by decide, ⟨488092420745, by decide, ⟨366069315559, by decide, ⟨549103973339, by decide, ⟨823655960009, by decide, ⟨617741970007, by decide, ⟨926612955011, by decide, ⟨1389919432517, by decide, ⟨260609893597, by decide, ⟨97728710099, by decide, ⟨146593065149, by decide, ⟨54972399431, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_49 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3] (60190359579 + q * 2 ^ 36) endpoint ∧ endpoint < 60190359579 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3] frontier_trace_49 (by decide) (by decide) (by decide) q
#print axioms frontier_class_49

theorem frontier_trace_50 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2] 21535653915 19668707371 := by
  exact ⟨32303480873, by decide, ⟨24227610655, by decide, ⟨36341415983, by decide, ⟨54512123975, by decide, ⟨81768185963, by decide, ⟨122652278945, by decide, ⟨91989209209, by decide, ⟨68991906907, by decide, ⟨103487860361, by decide, ⟨77615895271, by decide, ⟨116423842907, by decide, ⟨174635764361, by decide, ⟨130976823271, by decide, ⟨196465234907, by decide, ⟨294697852361, by decide, ⟨221023389271, by decide, ⟨331535083907, by decide, ⟨497302625861, by decide, ⟨93244242349, by decide, ⟨34966590881, by decide, ⟨26224943161, by decide, ⟨19668707371, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_50 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2] (21535653915 + q * 2 ^ 36) endpoint ∧ endpoint < 21535653915 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2] frontier_trace_50 (by decide) (by decide) (by decide) q
#print axioms frontier_class_50

theorem frontier_trace_51 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4] 30125588507 9171324091 := by
  exact ⟨45188382761, by decide, ⟨33891287071, by decide, ⟨50836930607, by decide, ⟨76255395911, by decide, ⟨114383093867, by decide, ⟨171574640801, by decide, ⟨128680980601, by decide, ⟨96510735451, by decide, ⟨144766103177, by decide, ⟨108574577383, by decide, ⟨162861866075, by decide, ⟨244292799113, by decide, ⟨183219599335, by decide, ⟨274829399003, by decide, ⟨412244098505, by decide, ⟨309183073879, by decide, ⟨463774610819, by decide, ⟨695661916229, by decide, ⟨130436609293, by decide, ⟨48913728485, by decide, ⟨9171324091, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_51 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4] (30125588507 + q * 2 ^ 36) endpoint ∧ endpoint < 30125588507 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4] frontier_trace_51 (by decide) (by decide) (by decide) q
#print axioms frontier_class_51

theorem frontier_trace_52 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 7] 19388170267 1967487905 := by
  exact ⟨29082255401, by decide, ⟨21811691551, by decide, ⟨32717537327, by decide, ⟨49076305991, by decide, ⟨73614458987, by decide, ⟨110421688481, by decide, ⟨82816266361, by decide, ⟨62112199771, by decide, ⟨93168299657, by decide, ⟨69876224743, by decide, ⟨104814337115, by decide, ⟨157221505673, by decide, ⟨117916129255, by decide, ⟨176874193883, by decide, ⟨265311290825, by decide, ⟨198983468119, by decide, ⟨298475202179, by decide, ⟨447712803269, by decide, ⟨83946150613, by decide, ⟨1967487905, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_52 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 7] (19388170267 + q * 2 ^ 36) endpoint ∧ endpoint < 19388170267 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 7] frontier_trace_52 (by decide) (by decide) (by decide) q
#print axioms frontier_class_52

theorem frontier_trace_53 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4] 25830621211 11795669911 := by
  exact ⟨38745931817, by decide, ⟨29059448863, by decide, ⟨43589173295, by decide, ⟨65383759943, by decide, ⟨98075639915, by decide, ⟨147113459873, by decide, ⟨110335094905, by decide, ⟨82751321179, by decide, ⟨124126981769, by decide, ⟨93095236327, by decide, ⟨139642854491, by decide, ⟨209464281737, by decide, ⟨157098211303, by decide, ⟨235647316955, by decide, ⟨353470975433, by decide, ⟨265103231575, by decide, ⟨397654847363, by decide, ⟨596482271045, by decide, ⟨111840425821, by decide, ⟨41940159683, by decide, ⟨62910239525, by decide, ⟨11795669911, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_53 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4] (25830621211 + q * 2 ^ 37) endpoint ∧ endpoint < 25830621211 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4] frontier_trace_53 (by decide) (by decide) (by decide) q
#print axioms frontier_class_53

theorem frontier_trace_54 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3] 124614869019 56905943099 := by
  exact ⟨186922303529, by decide, ⟨140191727647, by decide, ⟨210287591471, by decide, ⟨315431387207, by decide, ⟨473147080811, by decide, ⟨709720621217, by decide, ⟨532290465913, by decide, ⟨399217849435, by decide, ⟨598826774153, by decide, ⟨449120080615, by decide, ⟨673680120923, by decide, ⟨1010520181385, by decide, ⟨757890136039, by decide, ⟨1136835204059, by decide, ⟨1705252806089, by decide, ⟨1278939604567, by decide, ⟨1918409406851, by decide, ⟨2877614110277, by decide, ⟨539552645677, by decide, ⟨202332242129, by decide, ⟨151749181597, by decide, ⟨56905943099, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_54 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3] (124614869019 + q * 2 ^ 37) endpoint ∧ endpoint < 124614869019 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3] frontier_trace_54 (by decide) (by decide) (by decide) q
#print axioms frontier_class_54

theorem frontier_trace_55 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 5] 64485326875 9815838647 := by
  exact ⟨96727990313, by decide, ⟨72545992735, by decide, ⟨108818989103, by decide, ⟨163228483655, by decide, ⟨244842725483, by decide, ⟨367264088225, by decide, ⟨275448066169, by decide, ⟨206586049627, by decide, ⟨309879074441, by decide, ⟨232409305831, by decide, ⟨348613958747, by decide, ⟨522920938121, by decide, ⟨392190703591, by decide, ⟨588286055387, by decide, ⟨882429083081, by decide, ⟨661821812311, by decide, ⟨992732718467, by decide, ⟨1489099077701, by decide, ⟨279206077069, by decide, ⟨104702278901, by decide, ⟨9815838647, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_55 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 5] (64485326875 + q * 2 ^ 37) endpoint ∧ endpoint < 64485326875 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 5] frontier_trace_55 (by decide) (by decide) (by decide) q
#print axioms frontier_class_55

theorem frontier_trace_56 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 8] 53747908635 2727136153 := by
  exact ⟨80621862953, by decide, ⟨60466397215, by decide, ⟨90699595823, by decide, ⟨136049393735, by decide, ⟨204074090603, by decide, ⟨306111135905, by decide, ⟨229583351929, by decide, ⟨172187513947, by decide, ⟨258281270921, by decide, ⟨193710953191, by decide, ⟨290566429787, by decide, ⟨435849644681, by decide, ⟨326887233511, by decide, ⟨490330850267, by decide, ⟨735496275401, by decide, ⟨551622206551, by decide, ⟨827433309827, by decide, ⟨1241149964741, by decide, ⟨232715618389, by decide, ⟨2727136153, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_56 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 8] (53747908635 + q * 2 ^ 37) endpoint ∧ endpoint < 53747908635 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 8] frontier_trace_56 (by decide) (by decide) (by decide) q
#print axioms frontier_class_56

theorem frontier_trace_57 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4] 206219247643 141256427077 := by
  exact ⟨309328871465, by decide, ⟨231996653599, by decide, ⟨347994980399, by decide, ⟨521992470599, by decide, ⟨782988705899, by decide, ⟨1174483058849, by decide, ⟨880862294137, by decide, ⟨660646720603, by decide, ⟨990970080905, by decide, ⟨743227560679, by decide, ⟨1114841341019, by decide, ⟨1672262011529, by decide, ⟨1254196508647, by decide, ⟨1881294762971, by decide, ⟨2821942144457, by decide, ⟨2116456608343, by decide, ⟨3174684912515, by decide, ⟨4762027368773, by decide, ⟨892880131645, by decide, ⟨334830049367, by decide, ⟨502245074051, by decide, ⟨753367611077, by decide, ⟨141256427077, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_57 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4] (206219247643 + q * 2 ^ 38) endpoint ∧ endpoint < 206219247643 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4] frontier_trace_57 (by decide) (by decide) (by decide) q
#print axioms frontier_class_57

theorem frontier_trace_58 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3] 180449443867 123604581047 := by
  exact ⟨270674165801, by decide, ⟨203005624351, by decide, ⟨304508436527, by decide, ⟨456762654791, by decide, ⟨685143982187, by decide, ⟨1027715973281, by decide, ⟨770786979961, by decide, ⟨578090234971, by decide, ⟨867135352457, by decide, ⟨650351514343, by decide, ⟨975527271515, by decide, ⟨1463290907273, by decide, ⟨1097468180455, by decide, ⟨1646202270683, by decide, ⟨2469303406025, by decide, ⟨1851977554519, by decide, ⟨2777966331779, by decide, ⟨4166949497669, by decide, ⟨781303030813, by decide, ⟨292988636555, by decide, ⟨439482954833, by decide, ⟨329612216125, by decide, ⟨123604581047, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_58 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3] (180449443867 + q * 2 ^ 38) endpoint ∧ endpoint < 180449443867 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3] frontier_trace_58 (by decide) (by decide) (by decide) q
#print axioms frontier_class_58

theorem frontier_trace_59 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 5] 231989051419 52969424369 := by
  exact ⟨347983577129, by decide, ⟨260987682847, by decide, ⟨391481524271, by decide, ⟨587222286407, by decide, ⟨880833429611, by decide, ⟨1321250144417, by decide, ⟨990937608313, by decide, ⟨743203206235, by decide, ⟨1114804809353, by decide, ⟨836103607015, by decide, ⟨1254155410523, by decide, ⟨1881233115785, by decide, ⟨1410924836839, by decide, ⟨2116387255259, by decide, ⟨3174580882889, by decide, ⟨2380935662167, by decide, ⟨3571403493251, by decide, ⟨5357105239877, by decide, ⟨1004457232477, by decide, ⟨376671462179, by decide, ⟨565007193269, by decide, ⟨52969424369, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_59 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 5] (231989051419 + q * 2 ^ 38) endpoint ∧ endpoint < 231989051419 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 5] frontier_trace_59 (by decide) (by decide) (by decide) q
#print axioms frontier_class_59

theorem frontier_trace_60 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3] 4355784731 2983633175 := by
  exact ⟨6533677097, by decide, ⟨4900257823, by decide, ⟨7350386735, by decide, ⟨11025580103, by decide, ⟨16538370155, by decide, ⟨24807555233, by decide, ⟨18605666425, by decide, ⟨13954249819, by decide, ⟨20931374729, by decide, ⟨15698531047, by decide, ⟨23547796571, by decide, ⟨35321694857, by decide, ⟨26491271143, by decide, ⟨39736906715, by decide, ⟨59605360073, by decide, ⟨44704020055, by decide, ⟨67056030083, by decide, ⟨100584045125, by decide, ⟨18859508461, by decide, ⟨7072315673, by decide, ⟨5304236755, by decide, ⟨7956355133, by decide, ⟨2983633175, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_60 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3] (4355784731 + q * 2 ^ 38) endpoint ∧ endpoint < 4355784731 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3] frontier_trace_60 (by decide) (by decide) (by decide) q
#print axioms frontier_class_60

theorem frontier_trace_61 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 4] 55895392283 12762441745 := by
  exact ⟨83843088425, by decide, ⟨62882316319, by decide, ⟨94323474479, by decide, ⟨141485211719, by decide, ⟨212227817579, by decide, ⟨318341726369, by decide, ⟨238756294777, by decide, ⟨179067221083, by decide, ⟨268600831625, by decide, ⟨201450623719, by decide, ⟨302175935579, by decide, ⟨453263903369, by decide, ⟨339947927527, by decide, ⟨509921891291, by decide, ⟨764882836937, by decide, ⟨573662127703, by decide, ⟨860493191555, by decide, ⟨1290739787333, by decide, ⟨242013710125, by decide, ⟨90755141297, by decide, ⟨68066355973, by decide, ⟨12762441745, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_61 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 4] (55895392283 + q * 2 ^ 38) endpoint ∧ endpoint < 55895392283 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 4] frontier_trace_61 (by decide) (by decide) (by decide) q
#print axioms frontier_class_61

theorem frontier_trace_62 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 6] 133204803611 10138095925 := by
  exact ⟨199807205417, by decide, ⟨149855404063, by decide, ⟨224783106095, by decide, ⟨337174659143, by decide, ⟨505761988715, by decide, ⟨758642983073, by decide, ⟨568982237305, by decide, ⟨426736677979, by decide, ⟨640105016969, by decide, ⟨480078762727, by decide, ⟨720118144091, by decide, ⟨1080177216137, by decide, ⟨810132912103, by decide, ⟨1215199368155, by decide, ⟨1822799052233, by decide, ⟨1367099289175, by decide, ⟨2050648933763, by decide, ⟨3075973400645, by decide, ⟨576745012621, by decide, ⟨216279379733, by decide, ⟨10138095925, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_62 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 6] (133204803611 + q * 2 ^ 38) endpoint ∧ endpoint < 133204803611 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 6] frontier_trace_62 (by decide) (by decide) (by decide) q
#print axioms frontier_class_62

theorem frontier_trace_63 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 9] 122467385371 3106960277 := by
  exact ⟨183701078057, by decide, ⟨137775808543, by decide, ⟨206663712815, by decide, ⟨309995569223, by decide, ⟨464993353835, by decide, ⟨697490030753, by decide, ⟨523117523065, by decide, ⟨392338142299, by decide, ⟨588507213449, by decide, ⟨441380410087, by decide, ⟨662070615131, by decide, ⟨993105922697, by decide, ⟨744829442023, by decide, ⟨1117244163035, by decide, ⟨1675866244553, by decide, ⟨1256899683415, by decide, ⟨1885349525123, by decide, ⟨2828024287685, by decide, ⟨530254553941, by decide, ⟨3106960277, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_63 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 9] (122467385371 + q * 2 ^ 38) endpoint ∧ endpoint < 122467385371 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 9] frontier_trace_63 (by decide) (by decide) (by decide) q
#print axioms frontier_class_63

theorem frontier_trace_64 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5] 68780294171 23556624125 := by
  exact ⟨103170441257, by decide, ⟨77377830943, by decide, ⟨116066746415, by decide, ⟨174100119623, by decide, ⟨261150179435, by decide, ⟨391725269153, by decide, ⟨293793951865, by decide, ⟨220345463899, by decide, ⟨330518195849, by decide, ⟨247888646887, by decide, ⟨371832970331, by decide, ⟨557749455497, by decide, ⟨418312091623, by decide, ⟨627468137435, by decide, ⟨941202206153, by decide, ⟨705901654615, by decide, ⟨1058852481923, by decide, ⟨1588278722885, by decide, ⟨297802260541, by decide, ⟨111675847703, by decide, ⟨167513771555, by decide, ⟨251270657333, by decide, ⟨23556624125, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_64 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5] (68780294171 + q * 2 ^ 39) endpoint ∧ endpoint < 68780294171 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5] frontier_trace_64 (by decide) (by decide) (by decide) q
#print axioms frontier_class_64

theorem frontier_trace_65 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4] 317888397339 108873879937 := by
  exact ⟨476832596009, by decide, ⟨357624447007, by decide, ⟨536436670511, by decide, ⟨804655005767, by decide, ⟨1206982508651, by decide, ⟨1810473762977, by decide, ⟨1357855322233, by decide, ⟨1018391491675, by decide, ⟨1527587237513, by decide, ⟨1145690428135, by decide, ⟨1718535642203, by decide, ⟨2577803463305, by decide, ⟨1933352597479, by decide, ⟨2900028896219, by decide, ⟨4350043344329, by decide, ⟨3262532508247, by decide, ⟨4893798762371, by decide, ⟨7340698143557, by decide, ⟨1376380901917, by decide, ⟨516142838219, by decide, ⟨774214257329, by decide, ⟨580660692997, by decide, ⟨108873879937, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_65 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4] (317888397339 + q * 2 ^ 39) endpoint ∧ endpoint < 317888397339 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4] frontier_trace_65 (by decide) (by decide) (by decide) q
#print axioms frontier_class_65

theorem frontier_trace_66 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 6] 369428004891 42175241989 := by
  exact ⟨554142007337, by decide, ⟨415606505503, by decide, ⟨623409758255, by decide, ⟨935114637383, by decide, ⟨1402671956075, by decide, ⟨2104007934113, by decide, ⟨1578005950585, by decide, ⟨1183504462939, by decide, ⟨1775256694409, by decide, ⟨1331442520807, by decide, ⟨1997163781211, by decide, ⟨2995745671817, by decide, ⟨2246809253863, by decide, ⟨3370213880795, by decide, ⟨5055320821193, by decide, ⟨3791490615895, by decide, ⟨5687235923843, by decide, ⟨8530853885765, by decide, ⟨1599535103581, by decide, ⟨599825663843, by decide, ⟨899738495765, by decide, ⟨42175241989, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_66 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 6] (369428004891 + q * 2 ^ 39) endpoint ∧ endpoint < 369428004891 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 6] frontier_trace_66 (by decide) (by decide) (by decide) q
#print axioms frontier_class_66

theorem frontier_trace_67 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4] 141794738203 48563406001 := by
  exact ⟨212692107305, by decide, ⟨159519080479, by decide, ⟨239278620719, by decide, ⟨358917931079, by decide, ⟨538376896619, by decide, ⟨807565344929, by decide, ⟨605674008697, by decide, ⟨454255506523, by decide, ⟨681383259785, by decide, ⟨511037444839, by decide, ⟨766556167259, by decide, ⟨1149834250889, by decide, ⟨862375688167, by decide, ⟨1293563532251, by decide, ⟨1940345298377, by decide, ⟨1455258973783, by decide, ⟨2182888460675, by decide, ⟨3274332691013, by decide, ⟨613937379565, by decide, ⟨230226517337, by decide, ⟨172669888003, by decide, ⟨259004832005, by decide, ⟨48563406001, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_67 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4] (141794738203 + q * 2 ^ 39) endpoint ∧ endpoint < 141794738203 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4] frontier_trace_67 (by decide) (by decide) (by decide) q
#print axioms frontier_class_67

theorem frontier_trace_68 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 5] 193334345755 22071750677 := by
  exact ⟨290001518633, by decide, ⟨217501138975, by decide, ⟨326251708463, by decide, ⟨489377562695, by decide, ⟨734066344043, by decide, ⟨1101099516065, by decide, ⟨825824637049, by decide, ⟨619368477787, by decide, ⟨929052716681, by decide, ⟨696789537511, by decide, ⟨1045184306267, by decide, ⟨1567776459401, by decide, ⟨1175832344551, by decide, ⟨1763748516827, by decide, ⟨2645622775241, by decide, ⟨1984217081431, by decide, ⟨2976325622147, by decide, ⟨4464488433221, by decide, ⟨837091581229, by decide, ⟨313909342961, by decide, ⟨235432007221, by decide, ⟨22071750677, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_68 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 5] (193334345755 + q * 2 ^ 39) endpoint ∧ endpoint < 193334345755 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 5] frontier_trace_68 (by decide) (by decide) (by decide) q
#print axioms frontier_class_68

theorem frontier_trace_69 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 7] 545521664027 20759577767 := by
  exact ⟨818282496041, by decide, ⟨613711872031, by decide, ⟨920567808047, by decide, ⟨1380851712071, by decide, ⟨2071277568107, by decide, ⟨3106916352161, by decide, ⟨2330187264121, by decide, ⟨1747640448091, by decide, ⟨2621460672137, by decide, ⟨1966095504103, by decide, ⟨2949143256155, by decide, ⟨4423714884233, by decide, ⟨3317786163175, by decide, ⟨4976679244763, by decide, ⟨7465018867145, by decide, ⟨5598764150359, by decide, ⟨8398146225539, by decide, ⟨12597219338309, by decide, ⟨2361978625933, by decide, ⟨885741984725, by decide, ⟨20759577767, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_69 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 7] (545521664027 + q * 2 ^ 39) endpoint ∧ endpoint < 545521664027 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 7] frontier_trace_69 (by decide) (by decide) (by decide) q
#print axioms frontier_class_69

theorem frontier_trace_70 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 10] 259906338843 3296872339 := by
  exact ⟨389859508265, by decide, ⟨292394631199, by decide, ⟨438591946799, by decide, ⟨657887920199, by decide, ⟨986831880299, by decide, ⟨1480247820449, by decide, ⟨1110185865337, by decide, ⟨832639399003, by decide, ⟨1248959098505, by decide, ⟨936719323879, by decide, ⟨1405078985819, by decide, ⟨2107618478729, by decide, ⟨1580713859047, by decide, ⟨2371070788571, by decide, ⟨3556606182857, by decide, ⟨2667454637143, by decide, ⟨4001181955715, by decide, ⟨6001772933573, by decide, ⟨1125332425045, by decide, ⟨3296872339, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_70 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 10] (259906338843 + q * 2 ^ 39) endpoint ∧ endpoint < 259906338843 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 10] frontier_trace_70 (by decide) (by decide) (by decide) q
#print axioms frontier_class_70

theorem frontier_trace_71 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4] 2539651099 1374510403 := by
  exact ⟨3809476649, by decide, ⟨2857107487, by decide, ⟨4285661231, by decide, ⟨6428491847, by decide, ⟨9642737771, by decide, ⟨14464106657, by decide, ⟨10848079993, by decide, ⟨8136059995, by decide, ⟨12204089993, by decide, ⟨9153067495, by decide, ⟨13729601243, by decide, ⟨20594401865, by decide, ⟨15445801399, by decide, ⟨23168702099, by decide, ⟨34753053149, by decide, ⟨13032394931, by decide, ⟨19548592397, by decide, ⟨7330722149, by decide, ⟨1374510403, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_71 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4] (2539651099 + q * 2 ^ 32) endpoint ∧ endpoint < 2539651099 + q * 2 ^ 32 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4] frontier_trace_71 (by decide) (by decide) (by decide) q
#print axioms frontier_class_71

theorem frontier_trace_72 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5] 4687134747 1268385935 := by
  exact ⟨7030702121, by decide, ⟨5273026591, by decide, ⟨7909539887, by decide, ⟨11864309831, by decide, ⟨17796464747, by decide, ⟨26694697121, by decide, ⟨20021022841, by decide, ⟨15015767131, by decide, ⟨22523650697, by decide, ⟨16892738023, by decide, ⟨25339107035, by decide, ⟨38008660553, by decide, ⟨28506495415, by decide, ⟨42759743123, by decide, ⟨64139614685, by decide, ⟨24052355507, by decide, ⟨36078533261, by decide, ⟨13529449973, by decide, ⟨1268385935, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_72 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5] (4687134747 + q * 2 ^ 33) endpoint ∧ endpoint < 4687134747 + q * 2 ^ 33 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5] frontier_trace_72 (by decide) (by decide) (by decide) q
#print axioms frontier_class_72

theorem frontier_trace_73 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 6] 8982102043 1215323701 := by
  exact ⟨13473153065, by decide, ⟨10104864799, by decide, ⟨15157297199, by decide, ⟨22735945799, by decide, ⟨34103918699, by decide, ⟨51155878049, by decide, ⟨38366908537, by decide, ⟨28775181403, by decide, ⟨43162772105, by decide, ⟨32372079079, by decide, ⟨48558118619, by decide, ⟨72837177929, by decide, ⟨54627883447, by decide, ⟨81941825171, by decide, ⟨122912737757, by decide, ⟨46092276659, by decide, ⟨69138414989, by decide, ⟨25926905621, by decide, ⟨1215323701, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_73 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 6] (8982102043 + q * 2 ^ 34) endpoint ∧ endpoint < 8982102043 + q * 2 ^ 34 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 6] frontier_trace_73 (by decide) (by decide) (by decide) q
#print axioms frontier_class_73

theorem frontier_trace_74 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 7] 392167451 26531117 := by
  exact ⟨588251177, by decide, ⟨441188383, by decide, ⟨661782575, by decide, ⟨992673863, by decide, ⟨1489010795, by decide, ⟨2233516193, by decide, ⟨1675137145, by decide, ⟨1256352859, by decide, ⟨1884529289, by decide, ⟨1413396967, by decide, ⟨2120095451, by decide, ⟨3180143177, by decide, ⟨2385107383, by decide, ⟨3577661075, by decide, ⟨5366491613, by decide, ⟨2012434355, by decide, ⟨3018651533, by decide, ⟨1131994325, by decide, ⟨26531117, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_74 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 7] (392167451 + q * 2 ^ 35) endpoint ∧ endpoint < 392167451 + q * 2 ^ 35 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 7] frontier_trace_74 (by decide) (by decide) (by decide) q
#print axioms frontier_class_74

theorem frontier_trace_75 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 8] 51931775003 1756657759 := by
  exact ⟨77897662505, by decide, ⟨58423246879, by decide, ⟨87634870319, by decide, ⟨131452305479, by decide, ⟨197178458219, by decide, ⟨295767687329, by decide, ⟨221825765497, by decide, ⟨166369324123, by decide, ⟨249553986185, by decide, ⟨187165489639, by decide, ⟨280748234459, by decide, ⟨421122351689, by decide, ⟨315841763767, by decide, ⟨473762645651, by decide, ⟨710643968477, by decide, ⟨266491488179, by decide, ⟨399737232269, by decide, ⟨149901462101, by decide, ⟨1756657759, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_75 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 8] (51931775003 + q * 2 ^ 36) endpoint ∧ endpoint < 51931775003 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 8] frontier_trace_75 (by decide) (by decide) (by decide) q
#print axioms frontier_class_75

theorem frontier_trace_76 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 9] 86291513371 1459459613 := by
  exact ⟨129437270057, by decide, ⟨97077952543, by decide, ⟨145616928815, by decide, ⟨218425393223, by decide, ⟨327638089835, by decide, ⟨491457134753, by decide, ⟨368592851065, by decide, ⟨276444638299, by decide, ⟨414666957449, by decide, ⟨311000218087, by decide, ⟨466500327131, by decide, ⟨699750490697, by decide, ⟨524812868023, by decide, ⟨787219302035, by decide, ⟨1180828953053, by decide, ⟨442810857395, by decide, ⟨664216286093, by decide, ⟨249081107285, by decide, ⟨1459459613, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_76 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 9] (86291513371 + q * 2 ^ 37) endpoint ∧ endpoint < 86291513371 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 9] frontier_trace_76 (by decide) (by decide) (by decide) q
#print axioms frontier_class_76

theorem frontier_trace_77 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 10] 17572036635 148599073 := by
  exact ⟨26358054953, by decide, ⟨19768541215, by decide, ⟨29652811823, by decide, ⟨44479217735, by decide, ⟨66718826603, by decide, ⟨100078239905, by decide, ⟨75058679929, by decide, ⟨56294009947, by decide, ⟨84441014921, by decide, ⟨63330761191, by decide, ⟨94996141787, by decide, ⟨142494212681, by decide, ⟨106870659511, by decide, ⟨160305989267, by decide, ⟨240458983901, by decide, ⟨90172118963, by decide, ⟨135258178445, by decide, ⟨50721816917, by decide, ⟨148599073, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_77 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 10] (17572036635 + q * 2 ^ 38) endpoint ∧ endpoint < 17572036635 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 10] frontier_trace_77 (by decide) (by decide) (by decide) q
#print axioms frontier_class_77

theorem frontier_trace_78 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 11] 429888897051 1817691737 := by
  exact ⟨644833345577, by decide, ⟨483625009183, by decide, ⟨725437513775, by decide, ⟨1088156270663, by decide, ⟨1632234405995, by decide, ⟨2448351608993, by decide, ⟨1836263706745, by decide, ⟨1377197780059, by decide, ⟨2065796670089, by decide, ⟨1549347502567, by decide, ⟨2324021253851, by decide, ⟨3486031880777, by decide, ⟨2614523910583, by decide, ⟨3921785865875, by decide, ⟨5882678798813, by decide, ⟨2206004549555, by decide, ⟨3309006824333, by decide, ⟨1240877559125, by decide, ⟨1817691737, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_78 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 11] (429888897051 + q * 2 ^ 39) endpoint ∧ endpoint < 429888897051 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 11] frontier_trace_78 (by decide) (by decide) (by decide) q
#print axioms frontier_class_78

theorem frontier_trace_79 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2] 2198863899 1785104245 := by
  exact ⟨3298295849, by decide, ⟨2473721887, by decide, ⟨3710582831, by decide, ⟨5565874247, by decide, ⟨8348811371, by decide, ⟨12523217057, by decide, ⟨9392412793, by decide, ⟨7044309595, by decide, ⟨10566464393, by decide, ⟨7924848295, by decide, ⟨11887272443, by decide, ⟨17830908665, by decide, ⟨13373181499, by decide, ⟨20059772249, by decide, ⟨15044829187, by decide, ⟨22567243781, by decide, ⟨4231358209, by decide, ⟨3173518657, by decide, ⟨2380138993, by decide, ⟨1785104245, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_79 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2] (2198863899 + q * 2 ^ 33) endpoint ∧ endpoint < 2198863899 + q * 2 ^ 33 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2] frontier_trace_79 (by decide) (by decide) (by decide) q
#print axioms frontier_class_79

theorem frontier_trace_80 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3] 6493831195 2635944323 := by
  exact ⟨9740746793, by decide, ⟨7305560095, by decide, ⟨10958340143, by decide, ⟨16437510215, by decide, ⟨24656265323, by decide, ⟨36984397985, by decide, ⟨27738298489, by decide, ⟨20803723867, by decide, ⟨31205585801, by decide, ⟨23404189351, by decide, ⟨35106284027, by decide, ⟨52659426041, by decide, ⟨39494569531, by decide, ⟨59241854297, by decide, ⟨44431390723, by decide, ⟨66647086085, by decide, ⟨12496328641, by decide, ⟨9372246481, by decide, ⟨7029184861, by decide, ⟨2635944323, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_80 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3] (6493831195 + q * 2 ^ 34) endpoint ∧ endpoint < 6493831195 + q * 2 ^ 34 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3] frontier_trace_80 (by decide) (by decide) (by decide) q
#print axioms frontier_class_80

theorem frontier_trace_81 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3] 8641314843 5261460635 := by
  exact ⟨12961972265, by decide, ⟨9721479199, by decide, ⟨14582218799, by decide, ⟨21873328199, by decide, ⟨32809992299, by decide, ⟨49214988449, by decide, ⟨36911241337, by decide, ⟨27683431003, by decide, ⟨41525146505, by decide, ⟨31143859879, by decide, ⟨46715789819, by decide, ⟨70073684729, by decide, ⟨52555263547, by decide, ⟨78832895321, by decide, ⟨59124671491, by decide, ⟨88687007237, by decide, ⟨16628813857, by decide, ⟨12471610393, by decide, ⟨9353707795, by decide, ⟨14030561693, by decide, ⟨5261460635, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_81 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3] (8641314843 + q * 2 ^ 35) endpoint ∧ endpoint < 8641314843 + q * 2 ^ 35 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3] frontier_trace_81 (by decide) (by decide) (by decide) q
#print axioms frontier_class_81

theorem frontier_trace_82 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4] 32263634971 6548148763 := by
  exact ⟨48395452457, by decide, ⟨36296589343, by decide, ⟨54444884015, by decide, ⟨81667326023, by decide, ⟨122500989035, by decide, ⟨183751483553, by decide, ⟨137813612665, by decide, ⟨103360209499, by decide, ⟨155040314249, by decide, ⟨116280235687, by decide, ⟨174420353531, by decide, ⟨261630530297, by decide, ⟨196222897723, by decide, ⟨294334346585, by decide, ⟨220750759939, by decide, ⟨331126139909, by decide, ⟨62086151233, by decide, ⟨46564613425, by decide, ⟨34923460069, by decide, ⟨6548148763, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_82 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4] (32263634971 + q * 2 ^ 35) endpoint ∧ endpoint < 32263634971 + q * 2 ^ 35 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4] frontier_trace_82 (by decide) (by decide) (by decide) q
#print axioms frontier_class_82

theorem frontier_trace_83 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 2] 17231249435 15737455855 := by
  exact ⟨25846874153, by decide, ⟨19385155615, by decide, ⟨29077733423, by decide, ⟨43616600135, by decide, ⟨65424900203, by decide, ⟨98137350305, by decide, ⟨73603012729, by decide, ⟨55202259547, by decide, ⟨82803389321, by decide, ⟨62102541991, by decide, ⟨93153812987, by decide, ⟨139730719481, by decide, ⟨104798039611, by decide, ⟨157197059417, by decide, ⟨117897794563, by decide, ⟨176846691845, by decide, ⟨33158754721, by decide, ⟨24869066041, by decide, ⟨18651799531, by decide, ⟨27977699297, by decide, ⟨20983274473, by decide, ⟨15737455855, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_83 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 2] (17231249435 + q * 2 ^ 36) endpoint ∧ endpoint < 17231249435 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 2] frontier_trace_83 (by decide) (by decide) (by decide) q
#print axioms frontier_class_83

theorem frontier_trace_84 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4] 25821184027 7860906919 := by
  exact ⟨38731776041, by decide, ⟨29048832031, by decide, ⟨43573248047, by decide, ⟨65359872071, by decide, ⟨98039808107, by decide, ⟨147059712161, by decide, ⟨110294784121, by decide, ⟨82721088091, by decide, ⟨124081632137, by decide, ⟨93061224103, by decide, ⟨139591836155, by decide, ⟨209387754233, by decide, ⟨157040815675, by decide, ⟨235561223513, by decide, ⟨176670917635, by decide, ⟨265006376453, by decide, ⟨49688695585, by decide, ⟨37266521689, by decide, ⟨27949891267, by decide, ⟨41924836901, by decide, ⟨7860906919, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_84 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4] (25821184027 + q * 2 ^ 36) endpoint ∧ endpoint < 25821184027 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4] frontier_trace_84 (by decide) (by decide) (by decide) q
#print axioms frontier_class_84

theorem frontier_trace_85 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 3] 55885955099 51041147915 := by
  exact ⟨83828932649, by decide, ⟨62871699487, by decide, ⟨94307549231, by decide, ⟨141461323847, by decide, ⟨212191985771, by decide, ⟨318287978657, by decide, ⟨238715983993, by decide, ⟨179036987995, by decide, ⟨268555481993, by decide, ⟨201416611495, by decide, ⟨302124917243, by decide, ⟨453187375865, by decide, ⟨339890531899, by decide, ⟨509835797849, by decide, ⟨382376848387, by decide, ⟨573565272581, by decide, ⟨107543488609, by decide, ⟨80657616457, by decide, ⟨60493212343, by decide, ⟨90739818515, by decide, ⟨136109727773, by decide, ⟨51041147915, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_85 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 3] (55885955099 + q * 2 ^ 36) endpoint ∧ endpoint < 55885955099 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 3] frontier_trace_85 (by decide) (by decide) (by decide) q
#print axioms frontier_class_85

theorem frontier_trace_86 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 5] 15083765787 1530682181 := by
  exact ⟨22625648681, by decide, ⟨16969236511, by decide, ⟨25453854767, by decide, ⟨38180782151, by decide, ⟨57271173227, by decide, ⟨85906759841, by decide, ⟨64430069881, by decide, ⟨48322552411, by decide, ⟨72483828617, by decide, ⟨54362871463, by decide, ⟨81544307195, by decide, ⟨122316460793, by decide, ⟨91737345595, by decide, ⟨137606018393, by decide, ⟨103204513795, by decide, ⟨154806770693, by decide, ⟨29026269505, by decide, ⟨21769702129, by decide, ⟨16327276597, by decide, ⟨1530682181, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_86 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 5] (15083765787 + q * 2 ^ 36) endpoint ∧ endpoint < 15083765787 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 5] frontier_trace_86 (by decide) (by decide) (by decide) q
#print axioms frontier_class_86

theorem frontier_trace_87 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 3] 120310464539 54940317341 := by
  exact ⟨180465696809, by decide, ⟨135349272607, by decide, ⟨203023908911, by decide, ⟨304535863367, by decide, ⟨456803795051, by decide, ⟨685205692577, by decide, ⟨513904269433, by decide, ⟨385428202075, by decide, ⟨578142303113, by decide, ⟨433606727335, by decide, ⟨650410091003, by decide, ⟨975615136505, by decide, ⟨731711352379, by decide, ⟨1097567028569, by decide, ⟨823175271427, by decide, ⟨1234762907141, by decide, ⟨231518045089, by decide, ⟨173638533817, by decide, ⟨130228900363, by decide, ⟨195343350545, by decide, ⟨146507512909, by decide, ⟨54940317341, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_87 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 3] (120310464539 + q * 2 ^ 37) endpoint ∧ endpoint < 120310464539 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 3] frontier_trace_87 (by decide) (by decide) (by decide) q
#print axioms frontier_class_87

theorem frontier_trace_88 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 5] 60180922395 9160630061 := by
  exact ⟨90271383593, by decide, ⟨67703537695, by decide, ⟨101555306543, by decide, ⟨152332959815, by decide, ⟨228499439723, by decide, ⟨342749159585, by decide, ⟨257061869689, by decide, ⟨192796402267, by decide, ⟨289194603401, by decide, ⟨216895952551, by decide, ⟨325343928827, by decide, ⟨488015893241, by decide, ⟨366011919931, by decide, ⟨549017879897, by decide, ⟨411763409923, by decide, ⟨617645114885, by decide, ⟨115808459041, by decide, ⟨86856344281, by decide, ⟨65142258211, by decide, ⟨97713387317, by decide, ⟨9160630061, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_88 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 5] (60180922395 + q * 2 ^ 37) endpoint ∧ endpoint < 60180922395 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 5] frontier_trace_88 (by decide) (by decide) (by decide) q
#print axioms frontier_class_88

theorem frontier_trace_89 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 4] 21526216731 9830044153 := by
  exact ⟨32289325097, by decide, ⟨24216993823, by decide, ⟨36325490735, by decide, ⟨54488236103, by decide, ⟨81732354155, by decide, ⟨122598531233, by decide, ⟨91948898425, by decide, ⟨68961673819, by decide, ⟨103442510729, by decide, ⟨77581883047, by decide, ⟨116372824571, by decide, ⟨174559236857, by decide, ⟨130919427643, by decide, ⟨196379141465, by decide, ⟨147284356099, by decide, ⟨220926534149, by decide, ⟨41423725153, by decide, ⟨31067793865, by decide, ⟨23300845399, by decide, ⟨34951268099, by decide, ⟨52426902149, by decide, ⟨9830044153, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_89 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 4] (21526216731 + q * 2 ^ 37) endpoint ∧ endpoint < 21526216731 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 4] frontier_trace_89 (by decide) (by decide) (by decide) q
#print axioms frontier_class_89

theorem frontier_trace_90 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 6] 49443504155 2508733291 := by
  exact ⟨74165256233, by decide, ⟨55623942175, by decide, ⟨83435913263, by decide, ⟨125153869895, by decide, ⟨187730804843, by decide, ⟨281596207265, by decide, ⟨211197155449, by decide, ⟨158397866587, by decide, ⟨237596799881, by decide, ⟨178197599911, by decide, ⟨267296399867, by decide, ⟨400944599801, by decide, ⟨300708449851, by decide, ⟨451062674777, by decide, ⟨338297006083, by decide, ⟨507445509125, by decide, ⟨95146032961, by decide, ⟨71359524721, by decide, ⟨53519643541, by decide, ⟨2508733291, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_90 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 6] (49443504155 + q * 2 ^ 37) endpoint ∧ endpoint < 49443504155 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 6] frontier_trace_90 (by decide) (by decide) (by decide) q
#print axioms frontier_class_90

theorem frontier_trace_91 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 4] 189029941275 43160688475 := by
  exact ⟨283544911913, by decide, ⟨212658683935, by decide, ⟨318988025903, by decide, ⟨478482038855, by decide, ⟨717723058283, by decide, ⟨1076584587425, by decide, ⟨807438440569, by decide, ⟨605578830427, by decide, ⟨908368245641, by decide, ⟨681276184231, by decide, ⟨1021914276347, by decide, ⟨1532871414521, by decide, ⟨1149653560891, by decide, ⟨1724480341337, by decide, ⟨1293360256003, by decide, ⟨1940040384005, by decide, ⟨363757572001, by decide, ⟨272818179001, by decide, ⟨204613634251, by decide, ⟨306920451377, by decide, ⟨230190338533, by decide, ⟨43160688475, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_91 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 4] (189029941275 + q * 2 ^ 38) endpoint ∧ endpoint < 189029941275 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 4] frontier_trace_91 (by decide) (by decide) (by decide) q
#print axioms frontier_class_91

theorem frontier_trace_92 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 6] 266339352603 20270844835 := by
  exact ⟨399509028905, by decide, ⟨299631771679, by decide, ⟨449447657519, by decide, ⟨674171486279, by decide, ⟨1011257229419, by decide, ⟨1516885844129, by decide, ⟨1137664383097, by decide, ⟨853248287323, by decide, ⟨1279872430985, by decide, ⟨959904323239, by decide, ⟨1439856484859, by decide, ⟨2159784727289, by decide, ⟨1619838545467, by decide, ⟨2429757818201, by decide, ⟨1822318363651, by decide, ⟨2733477545477, by decide, ⟨512527039777, by decide, ⟨384395279833, by decide, ⟨288296459875, by decide, ⟨432444689813, by decide, ⟨20270844835, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_92 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 6] (266339352603 + q * 2 ^ 38) endpoint ∧ endpoint < 266339352603 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 6] frontier_trace_92 (by decide) (by decide) (by decide) q
#print axioms frontier_class_92

theorem frontier_trace_93 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3] 38706085915 26512963583 := by
  exact ⟨58059128873, by decide, ⟨43544346655, by decide, ⟨65316519983, by decide, ⟨97974779975, by decide, ⟨146962169963, by decide, ⟨220443254945, by decide, ⟨165332441209, by decide, ⟨123999330907, by decide, ⟨185998996361, by decide, ⟨139499247271, by decide, ⟨209248870907, by decide, ⟨313873306361, by decide, ⟨235404979771, by decide, ⟨353107469657, by decide, ⟨264830602243, by decide, ⟨397245903365, by decide, ⟨74483606881, by decide, ⟨55862705161, by decide, ⟨41897028871, by decide, ⟨62845543307, by decide, ⟨94268314961, by decide, ⟨70701236221, by decide, ⟨26512963583, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_93 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3] (38706085915 + q * 2 ^ 38) endpoint ∧ endpoint < 38706085915 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3] frontier_trace_93 (by decide) (by decide) (by decide) q
#print axioms frontier_class_93

theorem frontier_trace_94 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 5] 90245693467 20605551881 := by
  exact ⟨135368540201, by decide, ⟨101526405151, by decide, ⟨152289607727, by decide, ⟨228434411591, by decide, ⟨342651617387, by decide, ⟨513977426081, by decide, ⟨385483069561, by decide, ⟨289112302171, by decide, ⟨433668453257, by decide, ⟨325251339943, by decide, ⟨487877009915, by decide, ⟨731815514873, by decide, ⟨548861636155, by decide, ⟨823292454233, by decide, ⟨617469340675, by decide, ⟨926204011013, by decide, ⟨173663252065, by decide, ⟨130247439049, by decide, ⟨97685579287, by decide, ⟨146528368931, by decide, ⟨219792553397, by decide, ⟨20605551881, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_94 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 5] (90245693467 + q * 2 ^ 38) endpoint ∧ endpoint < 90245693467 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 5] frontier_trace_94 (by decide) (by decide) (by decide) q
#print axioms frontier_class_94

theorem frontier_trace_95 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4] 64475889691 44164809613 := by
  exact ⟨96713834537, by decide, ⟨72535375903, by decide, ⟨108803063855, by decide, ⟨163204595783, by decide, ⟨244806893675, by decide, ⟨367210340513, by decide, ⟨275407755385, by decide, ⟨206555816539, by decide, ⟨309833724809, by decide, ⟨232375293607, by decide, ⟨348562940411, by decide, ⟨522844410617, by decide, ⟨392133307963, by decide, ⟨588199961945, by decide, ⟨441149971459, by decide, ⟨661724957189, by decide, ⟨124073429473, by decide, ⟨93055072105, by decide, ⟨69791304079, by decide, ⟨104686956119, by decide, ⟨157030434179, by decide, ⟨235545651269, by decide, ⟨44164809613, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_95 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4] (64475889691 + q * 2 ^ 38) endpoint ∧ endpoint < 64475889691 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4] frontier_trace_95 (by decide) (by decide) (by decide) q
#print axioms frontier_class_95

theorem frontier_trace_96 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 7] 255601934363 6484543247 := by
  exact ⟨383402901545, by decide, ⟨287552176159, by decide, ⟨431328264239, by decide, ⟨646992396359, by decide, ⟨970488594539, by decide, ⟨1455732891809, by decide, ⟨1091799668857, by decide, ⟨818849751643, by decide, ⟨1228274627465, by decide, ⟨921205970599, by decide, ⟨1381808955899, by decide, ⟨2072713433849, by decide, ⟨1554535075387, by decide, ⟨2331802613081, by decide, ⟨1748851959811, by decide, ⟨2623277939717, by decide, ⟨491864613697, by decide, ⟨368898460273, by decide, ⟨276673845205, by decide, ⟨6484543247, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_96 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 7] (255601934363 + q * 2 ^ 38) endpoint ∧ endpoint < 255601934363 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 7] frontier_trace_96 (by decide) (by decide) (by decide) q
#print axioms frontier_class_96

theorem frontier_trace_97 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 5] 51590987803 5889814433 := by
  exact ⟨77386481705, by decide, ⟨58039861279, by decide, ⟨87059791919, by decide, ⟨130589687879, by decide, ⟨195884531819, by decide, ⟨293826797729, by decide, ⟨220370098297, by decide, ⟨165277573723, by decide, ⟨247916360585, by decide, ⟨185937270439, by decide, ⟨278905905659, by decide, ⟨418358858489, by decide, ⟨313769143867, by decide, ⟨470653715801, by decide, ⟨352990286851, by decide, ⟨529485430277, by decide, ⟨99278518177, by decide, ⟨74458888633, by decide, ⟨55844166475, by decide, ⟨83766249713, by decide, ⟨62824687285, by decide, ⟨5889814433, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_97 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 5] (51590987803 + q * 2 ^ 39) endpoint ∧ endpoint < 51590987803 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 5] frontier_trace_97 (by decide) (by decide) (by decide) q
#print axioms frontier_class_97

theorem frontier_trace_98 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 7] 403778306075 15365599019 := by
  exact ⟨605667459113, by decide, ⟨454250594335, by decide, ⟨681375891503, by decide, ⟨1022063837255, by decide, ⟨1533095755883, by decide, ⟨2299643633825, by decide, ⟨1724732725369, by decide, ⟨1293549544027, by decide, ⟨1940324316041, by decide, ⟨1455243237031, by decide, ⟨2182864855547, by decide, ⟨3274297283321, by decide, ⟨2455722962491, by decide, ⟨3683584443737, by decide, ⟨2762688332803, by decide, ⟨4144032499205, by decide, ⟨777006093601, by decide, ⟨582754570201, by decide, ⟨437065927651, by decide, ⟨655598891477, by decide, ⟨15365599019, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_98 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 7] (403778306075 + q * 2 ^ 39) endpoint ∧ endpoint < 403778306075 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 7] frontier_trace_98 (by decide) (by decide) (by decide) q
#print axioms frontier_class_98

theorem frontier_trace_99 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4] 176145039387 60328071205 := by
  exact ⟨264217559081, by decide, ⟨198163169311, by decide, ⟨297244753967, by decide, ⟨445867130951, by decide, ⟨668800696427, by decide, ⟨1003201044641, by decide, ⟨752400783481, by decide, ⟨564300587611, by decide, ⟨846450881417, by decide, ⟨634838161063, by decide, ⟨952257241595, by decide, ⟨1428385862393, by decide, ⟨1071289396795, by decide, ⟨1606934095193, by decide, ⟨1205200571395, by decide, ⟨1807800857093, by decide, ⟨338962660705, by decide, ⟨254221995529, by decide, ⟨190666496647, by decide, ⟨285999744971, by decide, ⟨428999617457, by decide, ⟨321749713093, by decide, ⟨60328071205, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_99 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4] (176145039387 + q * 2 ^ 39) endpoint ∧ endpoint < 176145039387 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4] frontier_trace_99 (by decide) (by decide) (by decide) q
#print axioms frontier_class_99

theorem frontier_trace_100 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 6] 227684646939 25993305745 := by
  exact ⟨341526970409, by decide, ⟨256145227807, by decide, ⟨384217841711, by decide, ⟨576326762567, by decide, ⟨864490143851, by decide, ⟨1296735215777, by decide, ⟨972551411833, by decide, ⟨729413558875, by decide, ⟨1094120338313, by decide, ⟨820590253735, by decide, ⟨1230885380603, by decide, ⟨1846328070905, by decide, ⟨1384746053179, by decide, ⟨2077119079769, by decide, ⟨1557839309827, by decide, ⟨2336758964741, by decide, ⟨438142305889, by decide, ⟨328606729417, by decide, ⟨246455047063, by decide, ⟨369682570595, by decide, ⟨554523855893, by decide, ⟨25993305745, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_100 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 6] (227684646939 + q * 2 ^ 39) endpoint ∧ endpoint < 227684646939 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 6] frontier_trace_100 (by decide) (by decide) (by decide) q
#print axioms frontier_class_100

theorem frontier_trace_101 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5] 476792750107 163297173047 := by
  exact ⟨715189125161, by decide, ⟨536391843871, by decide, ⟨804587765807, by decide, ⟨1206881648711, by decide, ⟨1810322473067, by decide, ⟨2715483709601, by decide, ⟨2036612782201, by decide, ⟨1527459586651, by decide, ⟨2291189379977, by decide, ⟨1718392034983, by decide, ⟨2577588052475, by decide, ⟨3866382078713, by decide, ⟨2899786559035, by decide, ⟨4349679838553, by decide, ⟨3262259878915, by decide, ⟨4893389818373, by decide, ⟨917510590945, by decide, ⟨688132943209, by decide, ⟨516099707407, by decide, ⟨774149561111, by decide, ⟨1161224341667, by decide, ⟨1741836512501, by decide, ⟨163297173047, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_101 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5] (476792750107 + q * 2 ^ 39) endpoint ∧ endpoint < 476792750107 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5] frontier_trace_101 (by decide) (by decide) (by decide) q
#print axioms frontier_class_101

theorem frontier_trace_102 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 8] 118162980891 1498879423 := by
  exact ⟨177244471337, by decide, ⟨132933353503, by decide, ⟨199400030255, by decide, ⟨299100045383, by decide, ⟨448650068075, by decide, ⟨672975102113, by decide, ⟨504731326585, by decide, ⟨378548494939, by decide, ⟨567822742409, by decide, ⟨425867056807, by decide, ⟨638800585211, by decide, ⟨958200877817, by decide, ⟨718650658363, by decide, ⟨1077975987545, by decide, ⟨808481990659, by decide, ⟨1212722985989, by decide, ⟨227385559873, by decide, ⟨170539169905, by decide, ⟨127904377429, by decide, ⟨1498879423, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_102 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 8] (118162980891 + q * 2 ^ 39) endpoint ∧ endpoint < 118162980891 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 8] frontier_trace_102 (by decide) (by decide) (by decide) q
#print axioms frontier_class_102

theorem frontier_trace_103 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4] 32272023579 19649553883 := by
  exact ⟨48408035369, by decide, ⟨36306026527, by decide, ⟨54459039791, by decide, ⟨81688559687, by decide, ⟨122532839531, by decide, ⟨183799259297, by decide, ⟨137849444473, by decide, ⟨103387083355, by decide, ⟨155080625033, by decide, ⟨116310468775, by decide, ⟨174465703163, by decide, ⟨261698554745, by decide, ⟨196273916059, by decide, ⟨294410874089, by decide, ⟨220808155567, by decide, ⟨331212233351, by decide, ⟨496818350027, by decide, ⟨745227525041, by decide, ⟨558920643781, by decide, ⟨104797620709, by decide, ⟨19649553883, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_103 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4] (32272023579 + q * 2 ^ 35) endpoint ∧ endpoint < 32272023579 + q * 2 ^ 35 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4] frontier_trace_103 (by decide) (by decide) (by decide) q
#print axioms frontier_class_103

theorem frontier_trace_104 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 4] 30124539931 27513014599 := by
  exact ⟨45186809897, by decide, ⟨33890107423, by decide, ⟨50835161135, by decide, ⟨76252741703, by decide, ⟨114379112555, by decide, ⟨171568668833, by decide, ⟨128676501625, by decide, ⟨96507376219, by decide, ⟨144761064329, by decide, ⟨108570798247, by decide, ⟨162856197371, by decide, ⟨244284296057, by decide, ⟨183213222043, by decide, ⟨274819833065, by decide, ⟨206114874799, by decide, ⟨309172312199, by decide, ⟨463758468299, by decide, ⟨695637702449, by decide, ⟨521728276837, by decide, ⟨97824051907, by decide, ⟨146736077861, by decide, ⟨27513014599, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_104 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 4] (30124539931 + q * 2 ^ 36) endpoint ∧ endpoint < 30124539931 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 4] frontier_trace_104 (by decide) (by decide) (by decide) q
#print axioms frontier_class_104

theorem frontier_trace_105 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 3] 10797187099 9861168569 := by
  exact ⟨16195780649, by decide, ⟨12146835487, by decide, ⟨18220253231, by decide, ⟨27330379847, by decide, ⟨40995569771, by decide, ⟨61493354657, by decide, ⟨46120015993, by decide, ⟨34590011995, by decide, ⟨51885017993, by decide, ⟨38913763495, by decide, ⟨58370645243, by decide, ⟨87555967865, by decide, ⟨65666975899, by decide, ⟨98500463849, by decide, ⟨73875347887, by decide, ⟨110813021831, by decide, ⟨166219532747, by decide, ⟨249329299121, by decide, ⟨186996974341, by decide, ⟨35061932689, by decide, ⟨26296449517, by decide, ⟨9861168569, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_105 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 3] (10797187099 + q * 2 ^ 36) endpoint ∧ endpoint < 10797187099 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 3] frontier_trace_105 (by decide) (by decide) (by decide) q
#print axioms frontier_class_105

theorem frontier_trace_106 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 2] 40861958171 37319595727 := by
  exact ⟨61292937257, by decide, ⟨45969702943, by decide, ⟨68954554415, by decide, ⟨103431831623, by decide, ⟨155147747435, by decide, ⟨232721621153, by decide, ⟨174541215865, by decide, ⟨130905911899, by decide, ⟨196358867849, by decide, ⟨147269150887, by decide, ⟨220903726331, by decide, ⟨331355589497, by decide, ⟨248516692123, by decide, ⟨372775038185, by decide, ⟨279581278639, by decide, ⟨419371917959, by decide, ⟨629057876939, by decide, ⟨943586815409, by decide, ⟨707690111557, by decide, ⟨132691895917, by decide, ⟨49759460969, by decide, ⟨37319595727, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_106 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 2] (40861958171 + q * 2 ^ 36) endpoint ∧ endpoint < 40861958171 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 2] frontier_trace_106 (by decide) (by decide) (by decide) q
#print axioms frontier_class_106

theorem frontier_trace_107 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5] 49451892763 15054953543 := by
  exact ⟨74177839145, by decide, ⟨55633379359, by decide, ⟨83450069039, by decide, ⟨125175103559, by decide, ⟨187762655339, by decide, ⟨281643983009, by decide, ⟨211232987257, by decide, ⟨158424740443, by decide, ⟨237637110665, by decide, ⟨178227832999, by decide, ⟨267341749499, by decide, ⟨401012624249, by decide, ⟨300759468187, by decide, ⟨451139202281, by decide, ⟨338354401711, by decide, ⟨507531602567, by decide, ⟨761297403851, by decide, ⟨1141946105777, by decide, ⟨856459579333, by decide, ⟨160586171125, by decide, ⟨15054953543, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_107 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5] (49451892763 + q * 2 ^ 36) endpoint ∧ endpoint < 49451892763 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5] frontier_trace_107 (by decide) (by decide) (by decide) q
#print axioms frontier_class_107

theorem frontier_trace_108 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 5] 133203755035 60828096713 := by
  exact ⟨199805632553, by decide, ⟨149854224415, by decide, ⟨224781336623, by decide, ⟨337172004935, by decide, ⟨505758007403, by decide, ⟨758637011105, by decide, ⟨568977758329, by decide, ⟨426733318747, by decide, ⟨640099978121, by decide, ⟨480074983591, by decide, ⟨720112475387, by decide, ⟨1080168713081, by decide, ⟨810126534811, by decide, ⟨1215189802217, by decide, ⟨911392351663, by decide, ⟨1367088527495, by decide, ⟨2050632791243, by decide, ⟨3075949186865, by decide, ⟨2306961890149, by decide, ⟨432555354403, by decide, ⟨648833031605, by decide, ⟨60828096713, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_108 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 5] (133203755035 + q * 2 ^ 37) endpoint ∧ endpoint < 133203755035 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 5] frontier_trace_108 (by decide) (by decide) (by decide) q
#print axioms frontier_class_108

theorem frontier_trace_109 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 4] 45156925467 20621114089 := by
  exact ⟨67735388201, by decide, ⟨50801541151, by decide, ⟨76202311727, by decide, ⟨114303467591, by decide, ⟨171455201387, by decide, ⟨257182802081, by decide, ⟨192887101561, by decide, ⟨144665326171, by decide, ⟨216997989257, by decide, ⟨162748491943, by decide, ⟨244122737915, by decide, ⟨366184106873, by decide, ⟨274638080155, by decide, ⟨411957120233, by decide, ⟨308967840175, by decide, ⟨463451760263, by decide, ⟨695177640395, by decide, ⟨1042766460593, by decide, ⟨782074845445, by decide, ⟨146639033521, by decide, ⟨109979275141, by decide, ⟨20621114089, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_109 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 4] (45156925467 + q * 2 ^ 37) endpoint ∧ endpoint < 45156925467 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 4] frontier_trace_109 (by decide) (by decide) (by decide) q
#print axioms frontier_class_109

theorem frontier_trace_110 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 3] 6502219803 2969268059 := by
  exact ⟨9753329705, by decide, ⟨7314997279, by decide, ⟨10972495919, by decide, ⟨16458743879, by decide, ⟨24688115819, by decide, ⟨37032173729, by decide, ⟨27774130297, by decide, ⟨20830597723, by decide, ⟨31245896585, by decide, ⟨23434422439, by decide, ⟨35151633659, by decide, ⟨52727450489, by decide, ⟨39545587867, by decide, ⟨59318381801, by decide, ⟨44488786351, by decide, ⟨66733179527, by decide, ⟨100099769291, by decide, ⟨150149653937, by decide, ⟨112612240453, by decide, ⟨21114795085, by decide, ⟨7918048157, by decide, ⟨2969268059, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_110 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 3] (6502219803 + q * 2 ^ 37) endpoint ∧ endpoint < 6502219803 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 3] frontier_trace_110 (by decide) (by decide) (by decide) q
#print axioms frontier_class_110

theorem frontier_trace_111 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 6] 83811631131 12757653373 := by
  exact ⟨125717446697, by decide, ⟨94288085023, by decide, ⟨141432127535, by decide, ⟨212148191303, by decide, ⟨318222286955, by decide, ⟨477333430433, by decide, ⟨358000072825, by decide, ⟨268500054619, by decide, ⟨402750081929, by decide, ⟨302062561447, by decide, ⟨453093842171, by decide, ⟨679640763257, by decide, ⟨509730572443, by decide, ⟨764595858665, by decide, ⟨573446893999, by decide, ⟨860170340999, by decide, ⟨1290255511499, by decide, ⟨1935383267249, by decide, ⟨1451537450437, by decide, ⟨272163271957, by decide, ⟨12757653373, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_111 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 6] (83811631131 + q * 2 ^ 37) endpoint ∧ endpoint < 83811631131 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 6] frontier_trace_111 (by decide) (by decide) (by decide) q
#print axioms frontier_class_111

theorem frontier_trace_112 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5] 51599376411 35344632641 := by
  exact ⟨77399064617, by decide, ⟨58049298463, by decide, ⟨87073947695, by decide, ⟨130610921543, by decide, ⟨195916382315, by decide, ⟨293874573473, by decide, ⟨220405930105, by decide, ⟨165304447579, by decide, ⟨247956671369, by decide, ⟨185967503527, by decide, ⟨278951255291, by decide, ⟨418426882937, by decide, ⟨313820162203, by decide, ⟨470730243305, by decide, ⟨353047682479, by decide, ⟨529571523719, by decide, ⟨794357285579, by decide, ⟨1191535928369, by decide, ⟨893651946277, by decide, ⟨167559739927, by decide, ⟨251339609891, by decide, ⟨377009414837, by decide, ⟨35344632641, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_112 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5] (51599376411 + q * 2 ^ 38) endpoint ∧ endpoint < 51599376411 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5] frontier_trace_112 (by decide) (by decide) (by decide) q
#print axioms frontier_class_112

theorem frontier_trace_113 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4] 176153427995 120661888453 := by
  exact ⟨264230141993, by decide, ⟨198172606495, by decide, ⟨297258909743, by decide, ⟨445888364615, by decide, ⟨668832546923, by decide, ⟨1003248820385, by decide, ⟨752436615289, by decide, ⟨564327461467, by decide, ⟨846491192201, by decide, ⟨634868394151, by decide, ⟨952302591227, by decide, ⟨1428453886841, by decide, ⟨1071340415131, by decide, ⟨1607010622697, by decide, ⟨1205257967023, by decide, ⟨1807886950535, by decide, ⟨2711830425803, by decide, ⟨4067745638705, by decide, ⟨3050809229029, by decide, ⟨572026730443, by decide, ⟨858040095665, by decide, ⟨643530071749, by decide, ⟨120661888453, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_113 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4] (176153427995 + q * 2 ^ 38) endpoint ∧ endpoint < 176153427995 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4] frontier_trace_113 (by decide) (by decide) (by decide) q
#print axioms frontier_class_113

theorem frontier_trace_114 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3] 150383624219 103010042423 := by
  exact ⟨225575436329, by decide, ⟨169181577247, by decide, ⟨253772365871, by decide, ⟨380658548807, by decide, ⟨570987823211, by decide, ⟨856481734817, by decide, ⟨642361301113, by decide, ⟨481770975835, by decide, ⟨722656463753, by decide, ⟨541992347815, by decide, ⟨812988521723, by decide, ⟨1219482782585, by decide, ⟨914612086939, by decide, ⟨1371918130409, by decide, ⟨1028938597807, by decide, ⟨1543407896711, by decide, ⟨2315111845067, by decide, ⟨3472667767601, by decide, ⟨2604500825701, by decide, ⟨488343904819, by decide, ⟨732515857229, by decide, ⟨274693446461, by decide, ⟨103010042423, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_114 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3] (150383624219 + q * 2 ^ 38) endpoint ∧ endpoint < 150383624219 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3] frontier_trace_114 (by decide) (by decide) (by decide) q
#print axioms frontier_class_114

theorem frontier_trace_115 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 6] 201923231771 46104578161 := by
  exact ⟨302884847657, by decide, ⟨227163635743, by decide, ⟨340745453615, by decide, ⟨511118180423, by decide, ⟨766677270635, by decide, ⟨1150015905953, by decide, ⟨862511929465, by decide, ⟨646883947099, by decide, ⟨970325920649, by decide, ⟨727744440487, by decide, ⟨1091616660731, by decide, ⟨1637424991097, by decide, ⟨1228068743323, by decide, ⟨1842103114985, by decide, ⟨1381577336239, by decide, ⟨2072366004359, by decide, ⟨3108549006539, by decide, ⟨4662823509809, by decide, ⟨3497117632357, by decide, ⟨655709556067, by decide, ⟨983564334101, by decide, ⟨46104578161, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_115 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 6] (201923231771 + q * 2 ^ 38) endpoint ∧ endpoint < 201923231771 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 6] frontier_trace_115 (by decide) (by decide) (by decide) q
#print axioms frontier_class_115

theorem frontier_trace_116 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4] 15289286683 9309229147 := by
  exact ⟨22933930025, by decide, ⟨17200447519, by decide, ⟨25800671279, by decide, ⟨38701006919, by decide, ⟨58051510379, by decide, ⟨87077265569, by decide, ⟨65307949177, by decide, ⟨48980961883, by decide, ⟨73471442825, by decide, ⟨55103582119, by decide, ⟨82655373179, by decide, ⟨123983059769, by decide, ⟨92987294827, by decide, ⟨139480942241, by decide, ⟨104610706681, by decide, ⟨78458030011, by decide, ⟨117687045017, by decide, ⟨88265283763, by decide, ⟨132397925645, by decide, ⟨49649222117, by decide, ⟨9309229147, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_116 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4] (15289286683 + q * 2 ^ 35) endpoint ∧ endpoint < 15289286683 + q * 2 ^ 35 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4] frontier_trace_116 (by decide) (by decide) (by decide) q
#print axioms frontier_class_116

theorem frontier_trace_117 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 4] 13141803035 12002527495 := by
  exact ⟨19712704553, by decide, ⟨14784528415, by decide, ⟨22176792623, by decide, ⟨33265188935, by decide, ⟨49897783403, by decide, ⟨74846675105, by decide, ⟨56135006329, by decide, ⟨42101254747, by decide, ⟨63151882121, by decide, ⟨47363911591, by decide, ⟨71045867387, by decide, ⟨106568801081, by decide, ⟨79926600811, by decide, ⟨119889901217, by decide, ⟨89917425913, by decide, ⟨67438069435, by decide, ⟨101157104153, by decide, ⟨75867828115, by decide, ⟨113801742173, by decide, ⟨42675653315, by decide, ⟨64013479973, by decide, ⟨12002527495, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_117 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 4] (13141803035 + q * 2 ^ 36) endpoint ∧ endpoint < 13141803035 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 4] frontier_trace_117 (by decide) (by decide) (by decide) q
#print axioms frontier_class_117

theorem frontier_trace_118 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 3] 62533926939 57112800683 := by
  exact ⟨93800890409, by decide, ⟨70350667807, by decide, ⟨105526001711, by decide, ⟨158289002567, by decide, ⟨237433503851, by decide, ⟨356150255777, by decide, ⟨267112691833, by decide, ⟨200334518875, by decide, ⟨300501778313, by decide, ⟨225376333735, by decide, ⟨338064500603, by decide, ⟨507096750905, by decide, ⟨380322563179, by decide, ⟨570483844769, by decide, ⟨427862883577, by decide, ⟨320897162683, by decide, ⟨481345744025, by decide, ⟨361009308019, by decide, ⟨541513962029, by decide, ⟨203067735761, by decide, ⟨152300801821, by decide, ⟨57112800683, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_118 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 3] (62533926939 + q * 2 ^ 36) endpoint ∧ endpoint < 62533926939 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 3] frontier_trace_118 (by decide) (by decide) (by decide) q
#print axioms frontier_class_118

theorem frontier_trace_119 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 2] 23879221275 21809108623 := by
  exact ⟨35818831913, by decide, ⟨26864123935, by decide, ⟨40296185903, by decide, ⟨60444278855, by decide, ⟨90666418283, by decide, ⟨135999627425, by decide, ⟨101999720569, by decide, ⟨76499790427, by decide, ⟨114749685641, by decide, ⟨86062264231, by decide, ⟨129093396347, by decide, ⟨193640094521, by decide, ⟨145230070891, by decide, ⟨217845106337, by decide, ⟨163383829753, by decide, ⟨122537872315, by decide, ⟨183806808473, by decide, ⟨137855106355, by decide, ⟨206782659533, by decide, ⟨77543497325, by decide, ⟨29078811497, by decide, ⟨21809108623, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_119 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 2] (23879221275 + q * 2 ^ 36) endpoint ∧ endpoint < 23879221275 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 2] frontier_trace_119 (by decide) (by decide) (by decide) q
#print axioms frontier_class_119

theorem frontier_trace_120 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5] 32469155867 9884791175 := by
  exact ⟨48703733801, by decide, ⟨36527800351, by decide, ⟨54791700527, by decide, ⟨82187550791, by decide, ⟨123281326187, by decide, ⟨184921989281, by decide, ⟨138691491961, by decide, ⟨104018618971, by decide, ⟨156027928457, by decide, ⟨117020946343, by decide, ⟨175531419515, by decide, ⟨263297129273, by decide, ⟨197472846955, by decide, ⟨296209270433, by decide, ⟨222156952825, by decide, ⟨166617714619, by decide, ⟨249926571929, by decide, ⟨187444928947, by decide, ⟨281167393421, by decide, ⟨105437772533, by decide, ⟨9884791175, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_120 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5] (32469155867 + q * 2 ^ 36) endpoint ∧ endpoint < 32469155867 + q * 2 ^ 36 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5] frontier_trace_120 (by decide) (by decide) (by decide) q
#print axioms frontier_class_120

theorem frontier_trace_121 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 5] 116221018139 53072853161 := by
  exact ⟨174331527209, by decide, ⟨130748645407, by decide, ⟨196122968111, by decide, ⟨294184452167, by decide, ⟨441276678251, by decide, ⟨661915017377, by decide, ⟨496436263033, by decide, ⟨372327197275, by decide, ⟨558490795913, by decide, ⟨418868096935, by decide, ⟨628302145403, by decide, ⟨942453218105, by decide, ⟨706839913579, by decide, ⟨1060259870369, by decide, ⟨795194902777, by decide, ⟨596396177083, by decide, ⟨894594265625, by decide, ⟨670945699219, by decide, ⟨1006418548829, by decide, ⟨377406955811, by decide, ⟨566110433717, by decide, ⟨53072853161, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_121 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 5] (116221018139 + q * 2 ^ 37) endpoint ∧ endpoint < 116221018139 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 5] frontier_trace_121 (by decide) (by decide) (by decide) q
#print axioms frontier_class_121

theorem frontier_trace_122 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 4] 28174188571 12865870537 := by
  exact ⟨42261282857, by decide, ⟨31695962143, by decide, ⟨47543943215, by decide, ⟨71315914823, by decide, ⟨106973872235, by decide, ⟨160460808353, by decide, ⟨120345606265, by decide, ⟨90259204699, by decide, ⟨135388807049, by decide, ⟨101541605287, by decide, ⟨152312407931, by decide, ⟨228468611897, by decide, ⟨171351458923, by decide, ⟨257027188385, by decide, ⟨192770391289, by decide, ⟨144577793467, by decide, ⟨216866690201, by decide, ⟨162650017651, by decide, ⟨243975026477, by decide, ⟨91490634929, by decide, ⟨68617976197, by decide, ⟨12865870537, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_122 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 4] (28174188571 + q * 2 ^ 37) endpoint ∧ endpoint < 28174188571 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 4] frontier_trace_122 (by decide) (by decide) (by decide) q
#print axioms frontier_class_122

theorem frontier_trace_123 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 3] 126958436379 57976143725 := by
  exact ⟨190437654569, by decide, ⟨142828240927, by decide, ⟨214242361391, by decide, ⟨321363542087, by decide, ⟨482045313131, by decide, ⟨723067969697, by decide, ⟨542300977273, by decide, ⟨406725732955, by decide, ⟨610088599433, by decide, ⟨457566449575, by decide, ⟨686349674363, by decide, ⟨1029524511545, by decide, ⟨772143383659, by decide, ⟨1158215075489, by decide, ⟨868661306617, by decide, ⟨651495979963, by decide, ⟨977243969945, by decide, ⟨732932977459, by decide, ⟨1099399466189, by decide, ⟨412274799821, by decide, ⟨154603049933, by decide, ⟨57976143725, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_123 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 3] (126958436379 + q * 2 ^ 37) endpoint ∧ endpoint < 126958436379 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 3] frontier_trace_123 (by decide) (by decide) (by decide) q
#print axioms frontier_class_123

theorem frontier_trace_124 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 6] 66828894235 10172572189 := by
  exact ⟨100243341353, by decide, ⟨75182506015, by decide, ⟨112773759023, by decide, ⟨169160638535, by decide, ⟨253740957803, by decide, ⟨380611436705, by decide, ⟨285458577529, by decide, ⟨214093933147, by decide, ⟨321140899721, by decide, ⟨240855674791, by decide, ⟨361283512187, by decide, ⟨541925268281, by decide, ⟨406443951211, by decide, ⟨609665926817, by decide, ⟨457249445113, by decide, ⟨342937083835, by decide, ⟨514405625753, by decide, ⟨385804219315, by decide, ⟨578706328973, by decide, ⟨217014873365, by decide, ⟨10172572189, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_124 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 6] (66828894235 + q * 2 ^ 37) endpoint ∧ endpoint < 66828894235 + q * 2 ^ 37 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 6] frontier_trace_124 (by decide) (by decide) (by decide) q
#print axioms frontier_class_124

theorem frontier_trace_125 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5] 34616639515 23711767313 := by
  exact ⟨51924959273, by decide, ⟨38943719455, by decide, ⟨58415579183, by decide, ⟨87623368775, by decide, ⟨131435053163, by decide, ⟨197152579745, by decide, ⟨147864434809, by decide, ⟨110898326107, by decide, ⟨166347489161, by decide, ⟨124760616871, by decide, ⟨187140925307, by decide, ⟨280711387961, by decide, ⟨210533540971, by decide, ⟨315800311457, by decide, ⟨236850233593, by decide, ⟨177637675195, by decide, ⟨266456512793, by decide, ⟨199842384595, by decide, ⟨299763576893, by decide, ⟨112411341335, by decide, ⟨168617012003, by decide, ⟨252925518005, by decide, ⟨23711767313, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_125 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5] (34616639515 + q * 2 ^ 38) endpoint ∧ endpoint < 34616639515 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5] frontier_trace_125 (by decide) (by decide) (by decide) q
#print axioms frontier_class_125

theorem frontier_trace_126 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4] 159170691099 109029023125 := by
  exact ⟨238756036649, by decide, ⟨179067027487, by decide, ⟨268600541231, by decide, ⟨402900811847, by decide, ⟨604351217771, by decide, ⟨906526826657, by decide, ⟨679895119993, by decide, ⟨509921339995, by decide, ⟨764882009993, by decide, ⟨573661507495, by decide, ⟨860492261243, by decide, ⟨1290738391865, by decide, ⟨968053793899, by decide, ⟨1452080690849, by decide, ⟨1089060518137, by decide, ⟨816795388603, by decide, ⟨1225193082905, by decide, ⟨918894812179, by decide, ⟨1378342218269, by decide, ⟨516878331851, by decide, ⟨775317497777, by decide, ⟨581488123333, by decide, ⟨109029023125, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_126 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4] (159170691099 + q * 2 ^ 38) endpoint ∧ endpoint < 159170691099 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4] frontier_trace_126 (by decide) (by decide) (by decide) q
#print axioms frontier_class_126

theorem frontier_trace_127 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 6] 184940494875 42226956385 := by
  exact ⟨277410742313, by decide, ⟨208058056735, by decide, ⟨312087085103, by decide, ⟨468130627655, by decide, ⟨702195941483, by decide, ⟨1053293912225, by decide, ⟨789970434169, by decide, ⟨592477825627, by decide, ⟨888716738441, by decide, ⟨666537553831, by decide, ⟨999806330747, by decide, ⟨1499709496121, by decide, ⟨1124782122091, by decide, ⟨1687173183137, by decide, ⟨1265379887353, by decide, ⟨949034915515, by decide, ⟨1423552373273, by decide, ⟨1067664279955, by decide, ⟨1601496419933, by decide, ⟨600561157475, by decide, ⟨900841736213, by decide, ⟨42226956385, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_127 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 6] (184940494875 + q * 2 ^ 38) endpoint ∧ endpoint < 184940494875 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 6] frontier_trace_127 (by decide) (by decide) (by decide) q
#print axioms frontier_class_127

theorem frontier_trace_128 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3] 133400887323 91377177095 := by
  exact ⟨200101330985, by decide, ⟨150075998239, by decide, ⟨225113997359, by decide, ⟨337670996039, by decide, ⟨506506494059, by decide, ⟨759759741089, by decide, ⟨569819805817, by decide, ⟨427364854363, by decide, ⟨641047281545, by decide, ⟨480785461159, by decide, ⟨721178191739, by decide, ⟨1081767287609, by decide, ⟨811325465707, by decide, ⟨1216988198561, by decide, ⟨912741148921, by decide, ⟨684555861691, by decide, ⟨1026833792537, by decide, ⟨770125344403, by decide, ⟨1155188016605, by decide, ⟨433195506227, by decide, ⟨649793259341, by decide, ⟨243672472253, by decide, ⟨91377177095, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem frontier_class_128 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3] (133400887323 + q * 2 ^ 38) endpoint ∧ endpoint < 133400887323 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3] frontier_trace_128 (by decide) (by decide) (by decide) q
#print axioms frontier_class_128

end CollatzResearch
