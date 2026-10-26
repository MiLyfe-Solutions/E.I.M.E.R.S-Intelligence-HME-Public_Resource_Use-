import BoundedDescent

set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

namespace CollatzResearch

def sibling_q4194354_word : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4]

theorem sibling_q4194354_representative :
    2417880462266991661547547 = 118140960795 + 4194354 * 2^59 := by decide

theorem sibling_q4194354_exact_trace :
    WordTrace sibling_q4194354_word 2417880462266991661547547 2153719637108387804385523 := by
  unfold sibling_q4194354_word
  refine ⟨3626820693400487492321321, by decide, ?_⟩
  refine ⟨2720115520050365619240991, by decide, ?_⟩
  refine ⟨4080173280075548428861487, by decide, ?_⟩
  refine ⟨6120259920113322643292231, by decide, ?_⟩
  refine ⟨9180389880169983964938347, by decide, ?_⟩
  refine ⟨13770584820254975947407521, by decide, ?_⟩
  refine ⟨10327938615191231960555641, by decide, ?_⟩
  refine ⟨7745953961393423970416731, by decide, ?_⟩
  refine ⟨11618930942090135955625097, by decide, ?_⟩
  refine ⟨8714198206567601966718823, by decide, ?_⟩
  refine ⟨13071297309851402950078235, by decide, ?_⟩
  refine ⟨19606945964777104425117353, by decide, ?_⟩
  refine ⟨14705209473582828318838015, by decide, ?_⟩
  refine ⟨22057814210374242478257023, by decide, ?_⟩
  refine ⟨33086721315561363717385535, by decide, ?_⟩
  refine ⟨49630081973342045576078303, by decide, ?_⟩
  refine ⟨74445122960013068364117455, by decide, ?_⟩
  refine ⟨111667684440019602546176183, by decide, ?_⟩
  refine ⟨167501526660029403819264275, by decide, ?_⟩
  refine ⟨251252289990044105728896413, by decide, ?_⟩
  refine ⟨94219608746266539648336155, by decide, ?_⟩
  refine ⟨141329413119399809472504233, by decide, ?_⟩
  refine ⟨105997059839549857104378175, by decide, ?_⟩
  refine ⟨158995589759324785656567263, by decide, ?_⟩
  refine ⟨238493384638987178484850895, by decide, ?_⟩
  refine ⟨357740076958480767727276343, by decide, ?_⟩
  refine ⟨536610115437721151590914515, by decide, ?_⟩
  refine ⟨804915173156581727386371773, by decide, ?_⟩
  refine ⟨301843189933718147769889415, by decide, ?_⟩
  refine ⟨452764784900577221654834123, by decide, ?_⟩
  refine ⟨679147177350865832482251185, by decide, ?_⟩
  refine ⟨509360383013149374361688389, by decide, ?_⟩
  refine ⟨95505071814965507692816573, by decide, ?_⟩
  refine ⟨35814401930612065384806215, by decide, ?_⟩
  refine ⟨53721602895918098077209323, by decide, ?_⟩
  refine ⟨80582404343877147115813985, by decide, ?_⟩
  refine ⟨60436803257907860336860489, by decide, ?_⟩
  refine ⟨45327602443430895252645367, by decide, ?_⟩
  refine ⟨67991403665146342878968051, by decide, ?_⟩
  refine ⟨101987105497719514318452077, by decide, ?_⟩
  refine ⟨38245164561644817869419529, by decide, ?_⟩
  refine ⟨28683873421233613402064647, by decide, ?_⟩
  refine ⟨43025810131850420103096971, by decide, ?_⟩
  refine ⟨64538715197775630154645457, by decide, ?_⟩
  refine ⟨48404036398331722615984093, by decide, ?_⟩
  refine ⟨18151513649374395980994035, by decide, ?_⟩
  refine ⟨27227270474061593971491053, by decide, ?_⟩
  refine ⟨10210226427773097739309145, by decide, ?_⟩
  refine ⟨7657669820829823304481859, by decide, ?_⟩
  refine ⟨11486504731244734956722789, by decide, ?_⟩
  refine ⟨2153719637108387804385523, by decide, ?_⟩
  rfl

theorem sibling_q4194354_arithmetic :
    sibling_q4194354_word.length = 51 ∧ sibling_q4194354_word.sum = 81 ∧ 81 < 82 ∧ 3^51 < 2^81 ∧ 2153719637108387804385523 < 2417880462266991661547547 := by decide

theorem sibling_q4194354_ordinary_descent :
    ∀ u : Nat, ∃ endpoint,
      ordinaryRun 132 (2417880462266991661547547 + u * 2^82) = endpoint ∧
      endpoint < 2417880462266991661547547 + u * 2^82 := by
  intro u
  have hstable : sibling_q4194354_word.sum < 82 := by rw [sibling_q4194354_arithmetic.2.1]; decide
  have hcontract : 3^sibling_q4194354_word.length < 2^sibling_q4194354_word.sum := by rw [sibling_q4194354_arithmetic.1, sibling_q4194354_arithmetic.2.1]; decide
  have hdescent : 2153719637108387804385523 < 2417880462266991661547547 := by decide
  rcases family_descends sibling_q4194354_word sibling_q4194354_exact_trace hstable hcontract hdescent u with ⟨endpoint, htrace, hlt⟩
  refine ⟨endpoint, ?_, hlt⟩
  have hord := wordTrace_ordinary htrace
  simpa only [sibling_q4194354_arithmetic.1, sibling_q4194354_arithmetic.2.1] using hord

#print axioms sibling_q4194354_exact_trace
#print axioms sibling_q4194354_ordinary_descent

end CollatzResearch
