import V185TrunkScan22Chunk387

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3459726 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_3459726 : Nat := 118140960795 + 3459726 * 2 ^ 59
def prefixEnd_3459726 : Nat := 4983230072969 + 3 ^ 40 * 3459726 * 2
def baseEnd_3459726 : Nat := 1184334913904824026542677

theorem tailTrace_3459726 : CollatzResearch.WordTrace tailWord_3459726 prefixEnd_3459726 1184334913904824026542677 := by
  unfold tailWord_3459726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15773321733001381375501879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84124382576007367336010021 15773321733001381375501879)
  ·
    refine ⟨23659982599502072063252819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15773321733001381375501879 23659982599502072063252819)
    ·
      refine ⟨35489973899253108094879229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23659982599502072063252819 35489973899253108094879229)
      ·
        refine ⟨13308740212219915535579711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35489973899253108094879229 13308740212219915535579711)
        ·
          refine ⟨19963110318329873303369567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13308740212219915535579711 19963110318329873303369567)
          ·
            refine ⟨29944665477494809955054351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19963110318329873303369567 29944665477494809955054351)
            ·
              refine ⟨44916998216242214932581527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29944665477494809955054351 44916998216242214932581527)
              ·
                refine ⟨67375497324363322398872291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44916998216242214932581527 67375497324363322398872291)
                ·
                  refine ⟨101063245986544983598308437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67375497324363322398872291 101063245986544983598308437)
                  ·
                    refine ⟨1184334913904824026542677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101063245986544983598308437 1184334913904824026542677)
                    ·
                      rfl

theorem cell22_3459726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_3459726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459726 prefixEnd_3459726 := by exact prefixLift 3459726
  have htrace : WordTrace (prefixWord ++ tailWord_3459726) baseStart_3459726 baseEnd_3459726 := by
    simpa [prefixWord, tailWord_3459726, baseEnd_3459726] using wordTrace_append hprefix tailTrace_3459726
  have hstable : (prefixWord ++ tailWord_3459726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459726).length < 2 ^ (prefixWord ++ tailWord_3459726).sum := by decide
  have hdescent : baseEnd_3459726 < baseStart_3459726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459745 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 3, 3]
def baseStart_3459745 : Nat := 118140960795 + 3459745 * 2 ^ 59
def prefixEnd_3459745 : Nat := 4983230072969 + 3 ^ 40 * 3459745 * 2
def baseEnd_3459745 : Nat := 1184341417993114310317619

theorem tailTrace_3459745 : CollatzResearch.WordTrace tailWord_3459745 prefixEnd_3459745 1184341417993114310317619 := by
  unfold tailWord_3459745
  simp only [CollatzResearch.WordTrace]
  refine ⟨126187266850942217248956689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84124844567294811499304459 126187266850942217248956689)
  ·
    refine ⟨94640450138206662936717517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126187266850942217248956689 94640450138206662936717517)
    ·
      refine ⟨35490168801827498601269069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94640450138206662936717517 35490168801827498601269069)
      ·
        refine ⟨13308813300685311975475901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35490168801827498601269069 13308813300685311975475901)
        ·
          refine ⟨4990804987756991990803463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13308813300685311975475901 4990804987756991990803463)
          ·
            refine ⟨7486207481635487986205195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990804987756991990803463 7486207481635487986205195)
            ·
              refine ⟨11229311222453231979307793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7486207481635487986205195 11229311222453231979307793)
              ·
                refine ⟨8421983416839923984480845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11229311222453231979307793 8421983416839923984480845)
                ·
                  refine ⟨3158243781314971494180317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8421983416839923984480845 3158243781314971494180317)
                  ·
                    refine ⟨1184341417993114310317619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158243781314971494180317 1184341417993114310317619)
                    ·
                      rfl

theorem cell22_3459745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_3459745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459745 prefixEnd_3459745 := by exact prefixLift 3459745
  have htrace : WordTrace (prefixWord ++ tailWord_3459745) baseStart_3459745 baseEnd_3459745 := by
    simpa [prefixWord, tailWord_3459745, baseEnd_3459745] using wordTrace_append hprefix tailTrace_3459745
  have hstable : (prefixWord ++ tailWord_3459745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459745).length < 2 ^ (prefixWord ++ tailWord_3459745).sum := by decide
  have hdescent : baseEnd_3459745 < baseStart_3459745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459848 : List Nat := [2, 1, 3, 2, 2, 3, 2, 7]
def baseStart_3459848 : Nat := 118140960795 + 3459848 * 2 ^ 59
def prefixEnd_3459848 : Nat := 4983230072969 + 3 ^ 40 * 3459848 * 2
def baseEnd_3459848 : Nat := 131597408555339597221367

theorem tailTrace_3459848 : CollatzResearch.WordTrace tailWord_3459848 prefixEnd_3459848 131597408555339597221367 := by
  unfold tailWord_3459848
  simp only [CollatzResearch.WordTrace]
  refine ⟨63095511784784532919978099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84127349046379377226637465 63095511784784532919978099)
  ·
    refine ⟨94643267677176799379967149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63095511784784532919978099 94643267677176799379967149)
    ·
      refine ⟨35491225378941299767487681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94643267677176799379967149 35491225378941299767487681)
      ·
        refine ⟨26618419034205974825615761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35491225378941299767487681 26618419034205974825615761)
        ·
          refine ⟨19963814275654481119211821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26618419034205974825615761 19963814275654481119211821)
          ·
            refine ⟨7486430353370430419704433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19963814275654481119211821 7486430353370430419704433)
            ·
              refine ⟨5614822765027822814778325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7486430353370430419704433 5614822765027822814778325)
              ·
                refine ⟨131597408555339597221367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5614822765027822814778325 131597408555339597221367)
                ·
                  rfl

theorem cell22_3459848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 7].length) (baseStart_3459848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459848 prefixEnd_3459848 := by exact prefixLift 3459848
  have htrace : WordTrace (prefixWord ++ tailWord_3459848) baseStart_3459848 baseEnd_3459848 := by
    simpa [prefixWord, tailWord_3459848, baseEnd_3459848] using wordTrace_append hprefix tailTrace_3459848
  have hstable : (prefixWord ++ tailWord_3459848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459848).length < 2 ^ (prefixWord ++ tailWord_3459848).sum := by decide
  have hdescent : baseEnd_3459848 < baseStart_3459848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459955 : List Nat := [1, 1, 1, 2, 2, 1, 6, 4, 4]
def baseStart_3459955 : Nat := 118140960795 + 3459955 * 2 ^ 59
def prefixEnd_3459955 : Nat := 4983230072969 + 3 ^ 40 * 3459955 * 2
def baseEnd_3459955 : Nat := 394804435094914587522325

theorem tailTrace_3459955 : CollatzResearch.WordTrace tailWord_3459955 prefixEnd_3459955 394804435094914587522325 := by
  unfold tailWord_3459955
  simp only [CollatzResearch.WordTrace]
  refine ⟨126194926180181423114101319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84129950786787615409400879 126194926180181423114101319)
  ·
    refine ⟨189292389270272134671151979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126194926180181423114101319 189292389270272134671151979)
    ·
      refine ⟨283938583905408202006727969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189292389270272134671151979 283938583905408202006727969)
      ·
        refine ⟨212953937929056151505045977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283938583905408202006727969 212953937929056151505045977)
        ·
          refine ⟨159715453446792113628784483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212953937929056151505045977 159715453446792113628784483)
          ·
            refine ⟨239573180170188170443176725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159715453446792113628784483 239573180170188170443176725)
            ·
              refine ⟨11229992820477570489523909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 239573180170188170443176725 11229992820477570489523909)
              ·
                refine ⟨2105623653839544466785733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11229992820477570489523909 2105623653839544466785733)
                ·
                  refine ⟨394804435094914587522325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2105623653839544466785733 394804435094914587522325)
                  ·
                    rfl

theorem cell22_3459955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 4].length) (baseStart_3459955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459955 prefixEnd_3459955 := by exact prefixLift 3459955
  have htrace : WordTrace (prefixWord ++ tailWord_3459955) baseStart_3459955 baseEnd_3459955 := by
    simpa [prefixWord, tailWord_3459955, baseEnd_3459955] using wordTrace_append hprefix tailTrace_3459955
  have hstable : (prefixWord ++ tailWord_3459955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459955).length < 2 ^ (prefixWord ++ tailWord_3459955).sum := by decide
  have hdescent : baseEnd_3459955 < baseStart_3459955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459968 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 6, 4]
def baseStart_3459968 : Nat := 118140960795 + 3459968 * 2 ^ 59
def prefixEnd_3459968 : Nat := 4983230072969 + 3 ^ 40 * 3459968 * 2
def baseEnd_3459968 : Nat := 1184417755450416061991935

theorem tailTrace_3459968 : CollatzResearch.WordTrace tailWord_3459968 prefixEnd_3459968 1184417755450416061991935 := by
  unfold tailWord_3459968
  simp only [CollatzResearch.WordTrace]
  refine ⟨63097700164567163167162279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84130266886089550889549705 63097700164567163167162279)
  ·
    refine ⟨94646550246850744750743419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63097700164567163167162279 94646550246850744750743419)
    ·
      refine ⟨141969825370276117126115129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94646550246850744750743419 141969825370276117126115129)
      ·
        refine ⟨106477369027707087844586347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141969825370276117126115129 106477369027707087844586347)
        ·
          refine ⟨159716053541560631766879521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106477369027707087844586347 159716053541560631766879521)
          ·
            refine ⟨119787040156170473825159641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159716053541560631766879521 119787040156170473825159641)
            ·
              refine ⟨89840280117127855368869731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119787040156170473825159641 89840280117127855368869731)
              ·
                refine ⟨134760420175691783053304597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89840280117127855368869731 134760420175691783053304597)
                ·
                  refine ⟨6316894695735552330623653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134760420175691783053304597 6316894695735552330623653)
                  ·
                    refine ⟨1184417755450416061991935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6316894695735552330623653 1184417755450416061991935)
                    ·
                      rfl

theorem cell22_3459968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_3459968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459968 prefixEnd_3459968 := by exact prefixLift 3459968
  have htrace : WordTrace (prefixWord ++ tailWord_3459968) baseStart_3459968 baseEnd_3459968 := by
    simpa [prefixWord, tailWord_3459968, baseEnd_3459968] using wordTrace_append hprefix tailTrace_3459968
  have hstable : (prefixWord ++ tailWord_3459968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459968).length < 2 ^ (prefixWord ++ tailWord_3459968).sum := by decide
  have hdescent : baseEnd_3459968 < baseStart_3459968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460002 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_3460002 : Nat := 118140960795 + 3460002 * 2 ^ 59
def prefixEnd_3460002 : Nat := 4983230072969 + 3 ^ 40 * 3460002 * 2
def baseEnd_3460002 : Nat := 1184429394345251306641831

theorem tailTrace_3460002 : CollatzResearch.WordTrace tailWord_3460002 prefixEnd_3460002 1184429394345251306641831 := by
  unfold tailWord_3460002
  simp only [CollatzResearch.WordTrace]
  refine ⟨31549160102752787535265565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84131093607340766760708173 31549160102752787535265565)
  ·
    refine ⟨11830935038532295325724587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31549160102752787535265565 11830935038532295325724587)
    ·
      refine ⟨17746402557798442988586881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11830935038532295325724587 17746402557798442988586881)
      ·
        refine ⟨13309801918348832241440161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17746402557798442988586881 13309801918348832241440161)
        ·
          refine ⟨9982351438761624181080121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13309801918348832241440161 9982351438761624181080121)
          ·
            refine ⟨7486763579071218135810091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9982351438761624181080121 7486763579071218135810091)
            ·
              refine ⟨11230145368606827203715137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7486763579071218135810091 11230145368606827203715137)
              ·
                refine ⟨8422609026455120402786353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11230145368606827203715137 8422609026455120402786353)
                ·
                  refine ⟨6316956769841340302089765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8422609026455120402786353 6316956769841340302089765)
                  ·
                    refine ⟨1184429394345251306641831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6316956769841340302089765 1184429394345251306641831)
                    ·
                      rfl

theorem cell22_3460002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_3460002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460002 prefixEnd_3460002 := by exact prefixLift 3460002
  have htrace : WordTrace (prefixWord ++ tailWord_3460002) baseStart_3460002 baseEnd_3460002 := by
    simpa [prefixWord, tailWord_3460002, baseEnd_3460002] using wordTrace_append hprefix tailTrace_3460002
  have hstable : (prefixWord ++ tailWord_3460002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460002).length < 2 ^ (prefixWord ++ tailWord_3460002).sum := by decide
  have hdescent : baseEnd_3460002 < baseStart_3460002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460015 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 3, 3]
def baseStart_3460015 : Nat := 118140960795 + 3460015 * 2 ^ 59
def prefixEnd_3460015 : Nat := 4983230072969 + 3 ^ 40 * 3460015 * 2
def baseEnd_3460015 : Nat := 1184433844510923606066791

theorem tailTrace_3460015 : CollatzResearch.WordTrace tailWord_3460015 prefixEnd_3460015 1184433844510923606066791 := by
  unfold tailWord_3460015
  simp only [CollatzResearch.WordTrace]
  refine ⟨126197114559964053361285499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84131409706642702240856999 126197114559964053361285499)
  ·
    refine ⟨189295671839946080041928249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126197114559964053361285499 189295671839946080041928249)
    ·
      refine ⟨141971753879959560031446187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189295671839946080041928249 141971753879959560031446187)
      ·
        refine ⟨212957630819939340047169281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141971753879959560031446187 212957630819939340047169281)
        ·
          refine ⟨159718223114954505035376961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212957630819939340047169281 159718223114954505035376961)
          ·
            refine ⟨119788667336215878776532721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159718223114954505035376961 119788667336215878776532721)
            ·
              refine ⟨89841500502161909082399541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119788667336215878776532721 89841500502161909082399541)
              ·
                refine ⟨8422640672077678976474957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89841500502161909082399541 8422640672077678976474957)
                ·
                  refine ⟨3158490252029129616178109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8422640672077678976474957 3158490252029129616178109)
                  ·
                    refine ⟨1184433844510923606066791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158490252029129616178109 1184433844510923606066791)
                    ·
                      rfl

theorem cell22_3460015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 3].length) (baseStart_3460015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460015 prefixEnd_3460015 := by exact prefixLift 3460015
  have htrace : WordTrace (prefixWord ++ tailWord_3460015) baseStart_3460015 baseEnd_3460015 := by
    simpa [prefixWord, tailWord_3460015, baseEnd_3460015] using wordTrace_append hprefix tailTrace_3460015
  have hstable : (prefixWord ++ tailWord_3460015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460015).length < 2 ^ (prefixWord ++ tailWord_3460015).sum := by decide
  have hdescent : baseEnd_3460015 < baseStart_3460015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460038 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3460038 : Nat := 118140960795 + 3460038 * 2 ^ 59
def prefixEnd_3460038 : Nat := 4983230072969 + 3 ^ 40 * 3460038 * 2
def baseEnd_3460038 : Nat := 1184441717880959212741721

theorem tailTrace_3460038 : CollatzResearch.WordTrace tailWord_3460038 prefixEnd_3460038 1184441717880959212741721 := by
  unfold tailWord_3460038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3943686044965022759042899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84131968959253818859581845 3943686044965022759042899)
  ·
    refine ⟨5915529067447534138564349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3943686044965022759042899 5915529067447534138564349)
    ·
      refine ⟨2218323400292825301961631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5915529067447534138564349 2218323400292825301961631)
      ·
        refine ⟨3327485100439237952942447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218323400292825301961631 3327485100439237952942447)
        ·
          refine ⟨4991227650658856929413671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327485100439237952942447 4991227650658856929413671)
          ·
            refine ⟨7486841475988285394120507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4991227650658856929413671 7486841475988285394120507)
            ·
              refine ⟨11230262213982428091180761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7486841475988285394120507 11230262213982428091180761)
              ·
                refine ⟨8422696660486821068385571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11230262213982428091180761 8422696660486821068385571)
                ·
                  refine ⟨12634044990730231602578357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8422696660486821068385571 12634044990730231602578357)
                  ·
                    refine ⟨1184441717880959212741721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12634044990730231602578357 1184441717880959212741721)
                    ·
                      rfl

theorem cell22_3460038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3460038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460038 prefixEnd_3460038 := by exact prefixLift 3460038
  have htrace : WordTrace (prefixWord ++ tailWord_3460038) baseStart_3460038 baseEnd_3460038 := by
    simpa [prefixWord, tailWord_3460038, baseEnd_3460038] using wordTrace_append hprefix tailTrace_3460038
  have hstable : (prefixWord ++ tailWord_3460038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460038).length < 2 ^ (prefixWord ++ tailWord_3460038).sum := by decide
  have hdescent : baseEnd_3460038 < baseStart_3460038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460073 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 12]
def baseStart_3460073 : Nat := 118140960795 + 3460073 * 2 ^ 59
def prefixEnd_3460073 : Nat := 4983230072969 + 3 ^ 40 * 3460073 * 2
def baseEnd_3460073 : Nat := 394817899698743596038871

theorem tailTrace_3460073 : CollatzResearch.WordTrace tailWord_3460073 prefixEnd_3460073 394817899698743596038871 := by
  unfold tailWord_3460073
  simp only [CollatzResearch.WordTrace]
  refine ⟨126199229993753929266896873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84132819995835952844597915 126199229993753929266896873)
  ·
    refine ⟨94649422495315446950172655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126199229993753929266896873 94649422495315446950172655)
    ·
      refine ⟨141974133742973170425258983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94649422495315446950172655 141974133742973170425258983)
      ·
        refine ⟨212961200614459755637888475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141974133742973170425258983 212961200614459755637888475)
        ·
          refine ⟨319441800921689633456832713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212961200614459755637888475 319441800921689633456832713)
          ·
            refine ⟨239581350691267225092624535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319441800921689633456832713 239581350691267225092624535)
            ·
              refine ⟨359372026036900837638936803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239581350691267225092624535 359372026036900837638936803)
              ·
                refine ⟨539058039055351256458405205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359372026036900837638936803 539058039055351256458405205)
                ·
                  refine ⟨394817899698743596038871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 539058039055351256458405205 394817899698743596038871)
                  ·
                    rfl

theorem cell22_3460073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_3460073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460073 prefixEnd_3460073 := by exact prefixLift 3460073
  have htrace : WordTrace (prefixWord ++ tailWord_3460073) baseStart_3460073 baseEnd_3460073 := by
    simpa [prefixWord, tailWord_3460073, baseEnd_3460073] using wordTrace_append hprefix tailTrace_3460073
  have hstable : (prefixWord ++ tailWord_3460073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460073).length < 2 ^ (prefixWord ++ tailWord_3460073).sum := by decide
  have hdescent : baseEnd_3460073 < baseStart_3460073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460107 : List Nat := [1, 1, 1, 1, 6, 2, 1, 5, 4]
def baseStart_3460107 : Nat := 118140960795 + 3460107 * 2 ^ 59
def prefixEnd_3460107 : Nat := 4983230072969 + 3 ^ 40 * 3460107 * 2
def baseEnd_3460107 : Nat := 394821779330355344255503

theorem tailTrace_3460107 : CollatzResearch.WordTrace tailWord_3460107 prefixEnd_3460107 394821779330355344255503 := by
  unfold tailWord_3460107
  simp only [CollatzResearch.WordTrace]
  refine ⟨126200470075630753073634575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84133646717087168715756383 126200470075630753073634575)
  ·
    refine ⟨189300705113446129610451863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126200470075630753073634575 189300705113446129610451863)
    ·
      refine ⟨283951057670169194415677795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189300705113446129610451863 283951057670169194415677795)
      ·
        refine ⟨425926586505253791623516693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283951057670169194415677795 425926586505253791623516693)
        ·
          refine ⟨19965308742433771482352345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 425926586505253791623516693 19965308742433771482352345)
          ·
            refine ⟨14973981556825328611764259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19965308742433771482352345 14973981556825328611764259)
            ·
              refine ⟨22460972335237992917646389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14973981556825328611764259 22460972335237992917646389)
              ·
                refine ⟨2105716156428561836029349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22460972335237992917646389 2105716156428561836029349)
                ·
                  refine ⟨394821779330355344255503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2105716156428561836029349 394821779330355344255503)
                  ·
                    rfl

theorem cell22_3460107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 4].length) (baseStart_3460107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460107 prefixEnd_3460107 := by exact prefixLift 3460107
  have htrace : WordTrace (prefixWord ++ tailWord_3460107) baseStart_3460107 baseEnd_3460107 := by
    simpa [prefixWord, tailWord_3460107, baseEnd_3460107] using wordTrace_append hprefix tailTrace_3460107
  have hstable : (prefixWord ++ tailWord_3460107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460107).length < 2 ^ (prefixWord ++ tailWord_3460107).sum := by decide
  have hdescent : baseEnd_3460107 < baseStart_3460107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460122 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 4, 3]
def baseStart_3460122 : Nat := 118140960795 + 3460122 * 2 ^ 59
def prefixEnd_3460122 : Nat := 4983230072969 + 3 ^ 40 * 3460122 * 2
def baseEnd_3460122 : Nat := 1184470472797610993641463

theorem tailTrace_3460122 : CollatzResearch.WordTrace tailWord_3460122 prefixEnd_3460122 1184470472797610993641463 := by
  unfold tailWord_3460122
  simp only [CollatzResearch.WordTrace]
  refine ⟨31550254292644102658857655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84134011447050940423620413 31550254292644102658857655)
  ·
    refine ⟨47325381438966153988286483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31550254292644102658857655 47325381438966153988286483)
    ·
      refine ⟨70988072158449230982429725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47325381438966153988286483 70988072158449230982429725)
      ·
        refine ⟨26620527059418461618411147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70988072158449230982429725 26620527059418461618411147)
        ·
          refine ⟨39930790589127692427616721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26620527059418461618411147 39930790589127692427616721)
          ·
            refine ⟨29948092941845769320712541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39930790589127692427616721 29948092941845769320712541)
            ·
              refine ⟨11230534853192163495267203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29948092941845769320712541 11230534853192163495267203)
              ·
                refine ⟨16845802279788245242900805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11230534853192163495267203 16845802279788245242900805)
                ·
                  refine ⟨3158587927460295983043901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16845802279788245242900805 3158587927460295983043901)
                  ·
                    refine ⟨1184470472797610993641463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158587927460295983043901 1184470472797610993641463)
                    ·
                      rfl

theorem cell22_3460122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_3460122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460122 prefixEnd_3460122 := by exact prefixLift 3460122
  have htrace : WordTrace (prefixWord ++ tailWord_3460122) baseStart_3460122 baseEnd_3460122 := by
    simpa [prefixWord, tailWord_3460122, baseEnd_3460122] using wordTrace_append hprefix tailTrace_3460122
  have hstable : (prefixWord ++ tailWord_3460122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460122).length < 2 ^ (prefixWord ++ tailWord_3460122).sum := by decide
  have hdescent : baseEnd_3460122 < baseStart_3460122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460139 : List Nat := [1, 1, 1, 1, 2, 1, 9, 1, 2, 3]
def baseStart_3460139 : Nat := 118140960795 + 3460139 * 2 ^ 59
def prefixEnd_3460139 : Nat := 4983230072969 + 3 ^ 40 * 3460139 * 2
def baseEnd_3460139 : Nat := 1184476292245028615966411

theorem tailTrace_3460139 : CollatzResearch.WordTrace tailWord_3460139 prefixEnd_3460139 1184476292245028615966411 := by
  unfold tailWord_3460139
  simp only [CollatzResearch.WordTrace]
  refine ⟨126201637211514822538799471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84134424807676548359199647 126201637211514822538799471)
  ·
    refine ⟨189302455817272233808199207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126201637211514822538799471 189302455817272233808199207)
    ·
      refine ⟨283953683725908350712298811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189302455817272233808199207 283953683725908350712298811)
      ·
        refine ⟨425930525588862526068448217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283953683725908350712298811 425930525588862526068448217)
        ·
          refine ⟨319447894191646894551336163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425930525588862526068448217 319447894191646894551336163)
          ·
            refine ⟨479171841287470341827004245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319447894191646894551336163 479171841287470341827004245)
            ·
              refine ⟨2807647507543771534142603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 479171841287470341827004245 2807647507543771534142603)
              ·
                refine ⟨4211471261315657301213905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2807647507543771534142603 4211471261315657301213905)
                ·
                  refine ⟨3158603445986742975910429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4211471261315657301213905 3158603445986742975910429)
                  ·
                    refine ⟨1184476292245028615966411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158603445986742975910429 1184476292245028615966411)
                    ·
                      rfl

theorem cell22_3460139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 2, 3].length) (baseStart_3460139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460139 prefixEnd_3460139 := by exact prefixLift 3460139
  have htrace : WordTrace (prefixWord ++ tailWord_3460139) baseStart_3460139 baseEnd_3460139 := by
    simpa [prefixWord, tailWord_3460139, baseEnd_3460139] using wordTrace_append hprefix tailTrace_3460139
  have hstable : (prefixWord ++ tailWord_3460139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460139).length < 2 ^ (prefixWord ++ tailWord_3460139).sum := by decide
  have hdescent : baseEnd_3460139 < baseStart_3460139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460152 : List Nat := [2, 1, 2, 1, 5, 1, 4, 6]
def baseStart_3460152 : Nat := 118140960795 + 3460152 * 2 ^ 59
def prefixEnd_3460152 : Nat := 4983230072969 + 3 ^ 40 * 3460152 * 2
def baseEnd_3460152 : Nat := 131608971378966768376819

theorem tailTrace_3460152 : CollatzResearch.WordTrace tailWord_3460152 prefixEnd_3460152 131608971378966768376819 := by
  unfold tailWord_3460152
  simp only [CollatzResearch.WordTrace]
  refine ⟨63101055680233862879511355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84134740906978483839348473 63101055680233862879511355)
  ·
    refine ⟨94651583520350794319267033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63101055680233862879511355 94651583520350794319267033)
    ·
      refine ⟨70988687640263095739450275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94651583520350794319267033 70988687640263095739450275)
      ·
        refine ⟨106483031460394643609175413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70988687640263095739450275 106483031460394643609175413)
        ·
          refine ⟨9982784199411997838360195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106483031460394643609175413 9982784199411997838360195)
          ·
            refine ⟨14974176299117996757540293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9982784199411997838360195 14974176299117996757540293)
            ·
              refine ⟨2807658056084624392038805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14974176299117996757540293 2807658056084624392038805)
              ·
                refine ⟨131608971378966768376819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2807658056084624392038805 131608971378966768376819)
                ·
                  rfl

theorem cell22_3460152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 6].length) (baseStart_3460152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460152 prefixEnd_3460152 := by exact prefixLift 3460152
  have htrace : WordTrace (prefixWord ++ tailWord_3460152) baseStart_3460152 baseEnd_3460152 := by
    simpa [prefixWord, tailWord_3460152, baseEnd_3460152] using wordTrace_append hprefix tailTrace_3460152
  have hstable : (prefixWord ++ tailWord_3460152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460152).length < 2 ^ (prefixWord ++ tailWord_3460152).sum := by decide
  have hdescent : baseEnd_3460152 < baseStart_3460152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460190 : List Nat := [4, 4, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3460190 : Nat := 118140960795 + 3460190 * 2 ^ 59
def prefixEnd_3460190 : Nat := 4983230072969 + 3 ^ 40 * 3460190 * 2
def baseEnd_3460190 : Nat := 1184493750587281482941255

theorem tailTrace_3460190 : CollatzResearch.WordTrace tailWord_3460190 prefixEnd_3460190 1184493750587281482941255 := by
  unfold tailWord_3460190
  simp only [CollatzResearch.WordTrace]
  refine ⟨15775437166791257281113253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84135664889553372165937349 15775437166791257281113253)
  ·
    refine ⟨2957894468773360740208735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15775437166791257281113253 2957894468773360740208735)
    ·
      refine ⟨4436841703160041110313103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2957894468773360740208735 4436841703160041110313103)
      ·
        refine ⟨6655262554740061665469655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4436841703160041110313103 6655262554740061665469655)
        ·
          refine ⟨9982893832110092498204483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6655262554740061665469655 9982893832110092498204483)
          ·
            refine ⟨14974340748165138747306725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9982893832110092498204483 14974340748165138747306725)
            ·
              refine ⟨2807688890280963515120011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14974340748165138747306725 2807688890280963515120011)
              ·
                refine ⟨4211533335421445272680017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2807688890280963515120011 4211533335421445272680017)
                ·
                  refine ⟨3158650001566083954510013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4211533335421445272680017 3158650001566083954510013)
                  ·
                    refine ⟨1184493750587281482941255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158650001566083954510013 1184493750587281482941255)
                    ·
                      rfl

theorem cell22_3460190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3460190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460190 prefixEnd_3460190 := by exact prefixLift 3460190
  have htrace : WordTrace (prefixWord ++ tailWord_3460190) baseStart_3460190 baseEnd_3460190 := by
    simpa [prefixWord, tailWord_3460190, baseEnd_3460190] using wordTrace_append hprefix tailTrace_3460190
  have hstable : (prefixWord ++ tailWord_3460190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460190).length < 2 ^ (prefixWord ++ tailWord_3460190).sum := by decide
  have hdescent : baseEnd_3460190 < baseStart_3460190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460195 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 1, 7]
def baseStart_3460195 : Nat := 118140960795 + 3460195 * 2 ^ 59
def prefixEnd_3460195 : Nat := 4983230072969 + 3 ^ 40 * 3460195 * 2
def baseEnd_3460195 : Nat := 1184495462189463136566239

theorem tailTrace_3460195 : CollatzResearch.WordTrace tailWord_3460195 prefixEnd_3460195 1184495462189463136566239 := by
  unfold tailWord_3460195
  simp only [CollatzResearch.WordTrace]
  refine ⟨126203679699311944102838039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84135786466207962735225359 126203679699311944102838039)
  ·
    refine ⟨189305519548967916154257059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126203679699311944102838039 189305519548967916154257059)
    ·
      refine ⟨283958279323451874231385589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189305519548967916154257059 283958279323451874231385589)
      ·
        refine ⟨26621088686573613209192399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283958279323451874231385589 26621088686573613209192399)
        ·
          refine ⟨39931633029860419813788599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26621088686573613209192399 39931633029860419813788599)
          ·
            refine ⟨59897449544790629720682899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39931633029860419813788599 59897449544790629720682899)
            ·
              refine ⟨89846174317185944581024349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59897449544790629720682899 89846174317185944581024349)
              ·
                refine ⟨33692315368944729217884131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89846174317185944581024349 33692315368944729217884131)
                ·
                  refine ⟨50538473053417093826826197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33692315368944729217884131 50538473053417093826826197)
                  ·
                    refine ⟨1184495462189463136566239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50538473053417093826826197 1184495462189463136566239)
                    ·
                      rfl

theorem cell22_3460195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_3460195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460195 prefixEnd_3460195 := by exact prefixLift 3460195
  have htrace : WordTrace (prefixWord ++ tailWord_3460195) baseStart_3460195 baseEnd_3460195 := by
    simpa [prefixWord, tailWord_3460195, baseEnd_3460195] using wordTrace_append hprefix tailTrace_3460195
  have hstable : (prefixWord ++ tailWord_3460195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460195).length < 2 ^ (prefixWord ++ tailWord_3460195).sum := by decide
  have hdescent : baseEnd_3460195 < baseStart_3460195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460197 : List Nat := [1, 3, 1, 3, 2, 1, 3, 3, 5]
def baseStart_3460197 : Nat := 118140960795 + 3460197 * 2 ^ 59
def prefixEnd_3460197 : Nat := 4983230072969 + 3 ^ 40 * 3460197 * 2
def baseEnd_3460197 : Nat := 394832048943445266005411

theorem tailTrace_3460197 : CollatzResearch.WordTrace tailWord_3460197 prefixEnd_3460197 394832048943445266005411 := by
  unfold tailWord_3460197
  simp only [CollatzResearch.WordTrace]
  refine ⟨126203752645304698444410845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84135835096869798962940563 126203752645304698444410845)
  ·
    refine ⟨47326407241989261916654067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126203752645304698444410845 47326407241989261916654067)
    ·
      refine ⟨70989610862983892874981101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47326407241989261916654067 70989610862983892874981101)
      ·
        refine ⟨26621104073618959828117913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70989610862983892874981101 26621104073618959828117913)
        ·
          refine ⟨19965828055214219871088435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26621104073618959828117913 19965828055214219871088435)
          ·
            refine ⟨29948742082821329806632653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19965828055214219871088435 29948742082821329806632653)
            ·
              refine ⟨11230778281057998677487245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29948742082821329806632653 11230778281057998677487245)
              ·
                refine ⟨4211541855396749504057717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11230778281057998677487245 4211541855396749504057717)
                ·
                  refine ⟨394832048943445266005411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4211541855396749504057717 394832048943445266005411)
                  ·
                    rfl

theorem cell22_3460197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_3460197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460197 prefixEnd_3460197 := by exact prefixLift 3460197
  have htrace : WordTrace (prefixWord ++ tailWord_3460197) baseStart_3460197 baseEnd_3460197 := by
    simpa [prefixWord, tailWord_3460197, baseEnd_3460197] using wordTrace_append hprefix tailTrace_3460197
  have hstable : (prefixWord ++ tailWord_3460197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460197).length < 2 ^ (prefixWord ++ tailWord_3460197).sum := by decide
  have hdescent : baseEnd_3460197 < baseStart_3460197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460308 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_3460308 : Nat := 118140960795 + 3460308 * 2 ^ 59
def prefixEnd_3460308 : Nat := 4983230072969 + 3 ^ 40 * 3460308 * 2
def baseEnd_3460308 : Nat := 1184534144398768508490893

theorem tailTrace_3460308 : CollatzResearch.WordTrace tailWord_3460308 prefixEnd_3460308 1184534144398768508490893 := by
  unfold tailWord_3460308
  simp only [CollatzResearch.WordTrace]
  refine ⟨63103900573951282200850789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84138534098601709601134385 63103900573951282200850789)
  ·
    refine ⟨11831981357615865412659523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63103900573951282200850789 11831981357615865412659523)
    ·
      refine ⟨17747972036423798118989285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11831981357615865412659523 17747972036423798118989285)
      ·
        refine ⟨3327744756829462147310491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17747972036423798118989285 3327744756829462147310491)
        ·
          refine ⟨4991617135244193220965737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327744756829462147310491 4991617135244193220965737)
          ·
            refine ⟨3743712851433144915724303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4991617135244193220965737 3743712851433144915724303)
            ·
              refine ⟨5615569277149717373586455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743712851433144915724303 5615569277149717373586455)
              ·
                refine ⟨8423353915724576060379683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5615569277149717373586455 8423353915724576060379683)
                ·
                  refine ⟨12635030873586864090569525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8423353915724576060379683 12635030873586864090569525)
                  ·
                    refine ⟨1184534144398768508490893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12635030873586864090569525 1184534144398768508490893)
                    ·
                      rfl

theorem cell22_3460308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_3460308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460308 prefixEnd_3460308 := by exact prefixLift 3460308
  have htrace : WordTrace (prefixWord ++ tailWord_3460308) baseStart_3460308 baseEnd_3460308 := by
    simpa [prefixWord, tailWord_3460308, baseEnd_3460308] using wordTrace_append hprefix tailTrace_3460308
  have hstable : (prefixWord ++ tailWord_3460308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460308).length < 2 ^ (prefixWord ++ tailWord_3460308).sum := by decide
  have hdescent : baseEnd_3460308 < baseStart_3460308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460319 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 3, 3]
def baseStart_3460319 : Nat := 118140960795 + 3460319 * 2 ^ 59
def prefixEnd_3460319 : Nat := 4983230072969 + 3 ^ 40 * 3460319 * 2
def baseEnd_3460319 : Nat := 1184537909923568146465859

theorem tailTrace_3460319 : CollatzResearch.WordTrace tailWord_3460319 prefixEnd_3460319 1184537909923568146465859 := by
  unfold tailWord_3460319
  simp only [CollatzResearch.WordTrace]
  refine ⟨126208202350862713280352011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84138801567241808853568007 126208202350862713280352011)
  ·
    refine ⟨189312303526294069920528017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126208202350862713280352011 189312303526294069920528017)
    ·
      refine ⟨141984227644720552440396013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189312303526294069920528017 141984227644720552440396013)
      ·
        refine ⟨53244085366770207165148505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141984227644720552440396013 53244085366770207165148505)
        ·
          refine ⟨39933064025077655373861379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53244085366770207165148505 39933064025077655373861379)
          ·
            refine ⟨59899596037616483060792069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39933064025077655373861379 59899596037616483060792069)
            ·
              refine ⟨11231174257053090573898513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59899596037616483060792069 11231174257053090573898513)
              ·
                refine ⟨8423380692789817930423885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11231174257053090573898513 8423380692789817930423885)
                ·
                  refine ⟨3158767759796181723908957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8423380692789817930423885 3158767759796181723908957)
                  ·
                    refine ⟨1184537909923568146465859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158767759796181723908957 1184537909923568146465859)
                    ·
                      rfl

theorem cell22_3460319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 3].length) (baseStart_3460319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460319 prefixEnd_3460319 := by exact prefixLift 3460319
  have htrace : WordTrace (prefixWord ++ tailWord_3460319) baseStart_3460319 baseEnd_3460319 := by
    simpa [prefixWord, tailWord_3460319, baseEnd_3460319] using wordTrace_append hprefix tailTrace_3460319
  have hstable : (prefixWord ++ tailWord_3460319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460319).length < 2 ^ (prefixWord ++ tailWord_3460319).sum := by decide
  have hdescent : baseEnd_3460319 < baseStart_3460319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460332 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 7]
def baseStart_3460332 : Nat := 118140960795 + 3460332 * 2 ^ 59
def prefixEnd_3460332 : Nat := 4983230072969 + 3 ^ 40 * 3460332 * 2
def baseEnd_3460332 : Nat := 394847453363080148630273

theorem tailTrace_3460332 : CollatzResearch.WordTrace tailWord_3460332 prefixEnd_3460332 394847453363080148630273 := by
  unfold tailWord_3460332
  simp only [CollatzResearch.WordTrace]
  refine ⟨63104338249907808250287625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84139117666543744333716833 63104338249907808250287625)
  ·
    refine ⟨47328253687430856187715719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63104338249907808250287625 47328253687430856187715719)
    ·
      refine ⟨70992380531146284281573579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47328253687430856187715719 70992380531146284281573579)
      ·
        refine ⟨106488570796719426422360369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70992380531146284281573579 106488570796719426422360369)
        ·
          refine ⟨79866428097539569816770277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106488570796719426422360369 79866428097539569816770277)
          ·
            refine ⟨14974955268288669340644427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79866428097539569816770277 14974955268288669340644427)
            ·
              refine ⟨22462432902433004010966641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14974955268288669340644427 22462432902433004010966641)
              ·
                refine ⟨16846824676824753008224981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22462432902433004010966641 16846824676824753008224981)
                ·
                  refine ⟨394847453363080148630273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16846824676824753008224981 394847453363080148630273)
                  ·
                    rfl

theorem cell22_3460332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_3460332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460332 prefixEnd_3460332 := by exact prefixLift 3460332
  have htrace : WordTrace (prefixWord ++ tailWord_3460332) baseStart_3460332 baseEnd_3460332 := by
    simpa [prefixWord, tailWord_3460332, baseEnd_3460332] using wordTrace_append hprefix tailTrace_3460332
  have hstable : (prefixWord ++ tailWord_3460332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460332).length < 2 ^ (prefixWord ++ tailWord_3460332).sum := by decide
  have hdescent : baseEnd_3460332 < baseStart_3460332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460340 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_3460340 : Nat := 118140960795 + 3460340 * 2 ^ 59
def prefixEnd_3460340 : Nat := 4983230072969 + 3 ^ 40 * 3460340 * 2
def baseEnd_3460340 : Nat := 1184545098652731091690795

theorem tailTrace_3460340 : CollatzResearch.WordTrace tailWord_3460340 prefixEnd_3460340 1184545098652731091690795 := by
  unfold tailWord_3460340
  simp only [CollatzResearch.WordTrace]
  refine ⟨63104484141893316933433237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84139312189191089244577649 63104484141893316933433237)
  ·
    refine ⟨2958022694151249231254683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63104484141893316933433237 2958022694151249231254683)
    ·
      refine ⟨4437034041226873846882025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2958022694151249231254683 4437034041226873846882025)
      ·
        refine ⟨3327775530920155385161519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4437034041226873846882025 3327775530920155385161519)
        ·
          refine ⟨4991663296380233077742279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327775530920155385161519 4991663296380233077742279)
          ·
            refine ⟨7487494944570349616613419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4991663296380233077742279 7487494944570349616613419)
            ·
              refine ⟨11231242416855524424920129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7487494944570349616613419 11231242416855524424920129)
              ·
                refine ⟨8423431812641643318690097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11231242416855524424920129 8423431812641643318690097)
                ·
                  refine ⟨6317573859481232489017573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8423431812641643318690097 6317573859481232489017573)
                  ·
                    refine ⟨1184545098652731091690795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6317573859481232489017573 1184545098652731091690795)
                    ·
                      rfl

theorem cell22_3460340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_3460340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460340 prefixEnd_3460340 := by exact prefixLift 3460340
  have htrace : WordTrace (prefixWord ++ tailWord_3460340) baseStart_3460340 baseEnd_3460340 := by
    simpa [prefixWord, tailWord_3460340, baseEnd_3460340] using wordTrace_append hprefix tailTrace_3460340
  have hstable : (prefixWord ++ tailWord_3460340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460340).length < 2 ^ (prefixWord ++ tailWord_3460340).sum := by decide
  have hdescent : baseEnd_3460340 < baseStart_3460340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460362 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_3460362 : Nat := 118140960795 + 3460362 * 2 ^ 59
def prefixEnd_3460362 : Nat := 4983230072969 + 3 ^ 40 * 3460362 * 2
def baseEnd_3460362 : Nat := 1184552629702330367640727

theorem tailTrace_3460362 : CollatzResearch.WordTrace tailWord_3460362 prefixEnd_3460362 1184552629702330367640727 := by
  unfold tailWord_3460362
  simp only [CollatzResearch.WordTrace]
  refine ⟨31552442672426732906041835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84139847126471287749444893 31552442672426732906041835)
  ·
    refine ⟨47328664008640099359062753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31552442672426732906041835 47328664008640099359062753)
    ·
      refine ⟨35496498006480074519297065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47328664008640099359062753 35496498006480074519297065)
      ·
        refine ⟨26622373504860055889472799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35496498006480074519297065 26622373504860055889472799)
        ·
          refine ⟨39933560257290083834209199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26622373504860055889472799 39933560257290083834209199)
          ·
            refine ⟨59900340385935125751313799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39933560257290083834209199 59900340385935125751313799)
            ·
              refine ⟨89850510578902688626970699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59900340385935125751313799 89850510578902688626970699)
              ·
                refine ⟨134775765868354032940456049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89850510578902688626970699 134775765868354032940456049)
                ·
                  refine ⟨101081824401265524705342037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134775765868354032940456049 101081824401265524705342037)
                  ·
                    refine ⟨1184552629702330367640727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101081824401265524705342037 1184552629702330367640727)
                    ·
                      rfl

theorem cell22_3460362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_3460362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460362 prefixEnd_3460362 := by exact prefixLift 3460362
  have htrace : WordTrace (prefixWord ++ tailWord_3460362) baseStart_3460362 baseEnd_3460362 := by
    simpa [prefixWord, tailWord_3460362, baseEnd_3460362] using wordTrace_append hprefix tailTrace_3460362
  have hstable : (prefixWord ++ tailWord_3460362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460362).length < 2 ^ (prefixWord ++ tailWord_3460362).sum := by decide
  have hdescent : baseEnd_3460362 < baseStart_3460362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460366 : List Nat := [4, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_3460366 : Nat := 118140960795 + 3460366 * 2 ^ 59
def prefixEnd_3460366 : Nat := 4983230072969 + 3 ^ 40 * 3460366 * 2
def baseEnd_3460366 : Nat := 394851332994691896846905

theorem tailTrace_3460366 : CollatzResearch.WordTrace tailWord_3460366 prefixEnd_3460366 394851332994691896846905 := by
  unfold tailWord_3460366
  simp only [CollatzResearch.WordTrace]
  refine ⟨15776239572711555038414119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84139944387794960204875301 15776239572711555038414119)
  ·
    refine ⟨23664359359067332557621179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15776239572711555038414119 23664359359067332557621179)
    ·
      refine ⟨35496539038600998836431769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23664359359067332557621179 35496539038600998836431769)
      ·
        refine ⟨26622404278950749127323827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35496539038600998836431769 26622404278950749127323827)
        ·
          refine ⟨39933606418426123690985741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26622404278950749127323827 39933606418426123690985741)
          ·
            refine ⟨14975102406909796384119653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39933606418426123690985741 14975102406909796384119653)
            ·
              refine ⟨2807831701295586822022435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14975102406909796384119653 2807831701295586822022435)
              ·
                refine ⟨4211747551943380233033653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2807831701295586822022435 4211747551943380233033653)
                ·
                  refine ⟨394851332994691896846905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4211747551943380233033653 394851332994691896846905)
                  ·
                    rfl

theorem cell22_3460366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_3460366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460366 prefixEnd_3460366 := by exact prefixLift 3460366
  have htrace : WordTrace (prefixWord ++ tailWord_3460366) baseStart_3460366 baseEnd_3460366 := by
    simpa [prefixWord, tailWord_3460366, baseEnd_3460366] using wordTrace_append hprefix tailTrace_3460366
  have hstable : (prefixWord ++ tailWord_3460366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460366).length < 2 ^ (prefixWord ++ tailWord_3460366).sum := by decide
  have hdescent : baseEnd_3460366 < baseStart_3460366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460407 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 5, 6]
def baseStart_3460407 : Nat := 118140960795 + 3460407 * 2 ^ 59
def prefixEnd_3460407 : Nat := 4983230072969 + 3 ^ 40 * 3460407 * 2
def baseEnd_3460407 : Nat := 1184568034121965250265589

theorem tailTrace_3460407 : CollatzResearch.WordTrace tailWord_3460407 prefixEnd_3460407 1184568034121965250265589 := by
  unfold tailWord_3460407
  simp only [CollatzResearch.WordTrace]
  refine ⟨126211411974543904309555475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84140941316362602873036983 126211411974543904309555475)
  ·
    refine ⟨189317117961815856464333213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126211411974543904309555475 189317117961815856464333213)
    ·
      refine ⟨70993919235680946174124955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189317117961815856464333213 70993919235680946174124955)
      ·
        refine ⟨106490878853521419261187433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70993919235680946174124955 106490878853521419261187433)
        ·
          refine ⟨79868159140141064445890575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106490878853521419261187433 79868159140141064445890575)
          ·
            refine ⟨119802238710211596668835863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79868159140141064445890575 119802238710211596668835863)
            ·
              refine ⟨179703358065317395003253795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119802238710211596668835863 179703358065317395003253795)
              ·
                refine ⟨269555037097976092504880693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179703358065317395003253795 269555037097976092504880693)
                ·
                  refine ⟨25270784727935258672332565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269555037097976092504880693 25270784727935258672332565)
                  ·
                    refine ⟨1184568034121965250265589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25270784727935258672332565 1184568034121965250265589)
                    ·
                      rfl

theorem cell22_3460407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_3460407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460407 prefixEnd_3460407 := by exact prefixLift 3460407
  have htrace : WordTrace (prefixWord ++ tailWord_3460407) baseStart_3460407 baseEnd_3460407 := by
    simpa [prefixWord, tailWord_3460407, baseEnd_3460407] using wordTrace_append hprefix tailTrace_3460407
  have hstable : (prefixWord ++ tailWord_3460407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460407).length < 2 ^ (prefixWord ++ tailWord_3460407).sum := by decide
  have hdescent : baseEnd_3460407 < baseStart_3460407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460471 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 3, 3]
def baseStart_3460471 : Nat := 118140960795 + 3460471 * 2 ^ 59
def prefixEnd_3460471 : Nat := 4983230072969 + 3 ^ 40 * 3460471 * 2
def baseEnd_3460471 : Nat := 1184589942629890416665393

theorem tailTrace_3460471 : CollatzResearch.WordTrace tailWord_3460471 prefixEnd_3460471 1184589942629890416665393 := by
  unfold tailWord_3460471
  simp only [CollatzResearch.WordTrace]
  refine ⟨126213746246312043239885267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84142497497541362159923511 126213746246312043239885267)
  ·
    refine ⟨189320619369468064859827901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126213746246312043239885267 189320619369468064859827901)
    ·
      refine ⟨70995232263550524322435463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189320619369468064859827901 70995232263550524322435463)
      ·
        refine ⟨106492848395325786483653195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70995232263550524322435463 106492848395325786483653195)
        ·
          refine ⟨159739272592988679725479793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106492848395325786483653195 159739272592988679725479793)
          ·
            refine ⟨119804454444741509794109845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159739272592988679725479793 119804454444741509794109845)
            ·
              refine ⟨5615833802097258271598899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119804454444741509794109845 5615833802097258271598899)
              ·
                refine ⟨8423750703145887407398349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5615833802097258271598899 8423750703145887407398349)
                ·
                  refine ⟨3158906513679707777774381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8423750703145887407398349 3158906513679707777774381)
                  ·
                    refine ⟨1184589942629890416665393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158906513679707777774381 1184589942629890416665393)
                    ·
                      rfl

theorem cell22_3460471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_3460471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460471 prefixEnd_3460471 := by exact prefixLift 3460471
  have htrace : WordTrace (prefixWord ++ tailWord_3460471) baseStart_3460471 baseEnd_3460471 := by
    simpa [prefixWord, tailWord_3460471, baseEnd_3460471] using wordTrace_append hprefix tailTrace_3460471
  have hstable : (prefixWord ++ tailWord_3460471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460471).length < 2 ^ (prefixWord ++ tailWord_3460471).sum := by decide
  have hdescent : baseEnd_3460471 < baseStart_3460471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460505 : List Nat := [1, 2, 1, 2, 1, 7, 1, 3, 1, 3]
def baseStart_3460505 : Nat := 118140960795 + 3460505 * 2 ^ 59
def prefixEnd_3460505 : Nat := 4983230072969 + 3 ^ 40 * 3460505 * 2
def baseEnd_3460505 : Nat := 1184601581524725661315289

theorem tailTrace_3460505 : CollatzResearch.WordTrace tailWord_3460505 prefixEnd_3460505 1184601581524725661315289 := by
  unfold tailWord_3460505
  simp only [CollatzResearch.WordTrace]
  refine ⟨126214986328188867046622969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84143324218792578031081979 126214986328188867046622969)
  ·
    refine ⟨94661239746141650284967227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126214986328188867046622969 94661239746141650284967227)
    ·
      refine ⟨141991859619212475427450841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94661239746141650284967227 141991859619212475427450841)
      ·
        refine ⟨106493894714409356570588131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141991859619212475427450841 106493894714409356570588131)
        ·
          refine ⟨159740842071614034855882197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106493894714409356570588131 159740842071614034855882197)
          ·
            refine ⟨3743925986053453941934739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 159740842071614034855882197 3743925986053453941934739)
            ·
              refine ⟨5615888979080180912902109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743925986053453941934739 5615888979080180912902109)
              ·
                refine ⟨2105958367155067842338291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5615888979080180912902109 2105958367155067842338291)
                ·
                  refine ⟨3158937550732601763507437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2105958367155067842338291 3158937550732601763507437)
                  ·
                    refine ⟨1184601581524725661315289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158937550732601763507437 1184601581524725661315289)
                    ·
                      rfl

theorem cell22_3460505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 1, 3].length) (baseStart_3460505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460505 prefixEnd_3460505 := by exact prefixLift 3460505
  have htrace : WordTrace (prefixWord ++ tailWord_3460505) baseStart_3460505 baseEnd_3460505 := by
    simpa [prefixWord, tailWord_3460505, baseEnd_3460505] using wordTrace_append hprefix tailTrace_3460505
  have hstable : (prefixWord ++ tailWord_3460505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460505).length < 2 ^ (prefixWord ++ tailWord_3460505).sum := by decide
  have hdescent : baseEnd_3460505 < baseStart_3460505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460548 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3460548 : Nat := 118140960795 + 3460548 * 2 ^ 59
def prefixEnd_3460548 : Nat := 4983230072969 + 3 ^ 40 * 3460548 * 2
def baseEnd_3460548 : Nat := 1184616301303487882490157

theorem tailTrace_3460548 : CollatzResearch.WordTrace tailWord_3460548 prefixEnd_3460548 1184616301303487882490157 := by
  unfold tailWord_3460548
  simp only [CollatzResearch.WordTrace]
  refine ⟨63108277333516542695219149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84144369778022056926958865 63108277333516542695219149)
  ·
    refine ⟨23665604000068703510707181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63108277333516542695219149 23665604000068703510707181)
    ·
      refine ⟨8874601500025763816515193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23665604000068703510707181 8874601500025763816515193)
      ·
        refine ⟨6655951125019322862386395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8874601500025763816515193 6655951125019322862386395)
        ·
          refine ⟨9983926687528984293579593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6655951125019322862386395 9983926687528984293579593)
          ·
            refine ⟨7487945015646738220184695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9983926687528984293579593 7487945015646738220184695)
            ·
              refine ⟨11231917523470107330277043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7487945015646738220184695 11231917523470107330277043)
              ·
                refine ⟨16847876285205160995415565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11231917523470107330277043 16847876285205160995415565)
                ·
                  refine ⟨6317953606951935373280837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16847876285205160995415565 6317953606951935373280837)
                  ·
                    refine ⟨1184616301303487882490157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6317953606951935373280837 1184616301303487882490157)
                    ·
                      rfl

theorem cell22_3460548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3460548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460548 prefixEnd_3460548 := by exact prefixLift 3460548
  have htrace : WordTrace (prefixWord ++ tailWord_3460548) baseStart_3460548 baseEnd_3460548 := by
    simpa [prefixWord, tailWord_3460548, baseEnd_3460548] using wordTrace_append hprefix tailTrace_3460548
  have hstable : (prefixWord ++ tailWord_3460548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460548).length < 2 ^ (prefixWord ++ tailWord_3460548).sum := by decide
  have hdescent : baseEnd_3460548 < baseStart_3460548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460559 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 1, 6]
def baseStart_3460559 : Nat := 118140960795 + 3460559 * 2 ^ 59
def prefixEnd_3460559 : Nat := 4983230072969 + 3 ^ 40 * 3460559 * 2
def baseEnd_3460559 : Nat := 1184620066828287520465123

theorem tailTrace_3460559 : CollatzResearch.WordTrace tailWord_3460559 prefixEnd_3460559 1184620066828287520465123 := by
  unfold tailWord_3460559
  simp only [CollatzResearch.WordTrace]
  refine ⟨126216955869993234269088731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84144637246662156179392487 126216955869993234269088731)
  ·
    refine ⟨189325433804989851403633097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126216955869993234269088731 189325433804989851403633097)
    ·
      refine ⟨141994075353742388552724823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189325433804989851403633097 141994075353742388552724823)
      ·
        refine ⟨212991113030613582829087235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141994075353742388552724823 212991113030613582829087235)
        ·
          refine ⟨319486669545920374243630853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212991113030613582829087235 319486669545920374243630853)
          ·
            refine ⟨59903750539860070170680785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319486669545920374243630853 59903750539860070170680785)
            ·
              refine ⟨44927812904895052628010589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59903750539860070170680785 44927812904895052628010589)
              ·
                refine ⟨16847929839335644735503971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44927812904895052628010589 16847929839335644735503971)
                ·
                  refine ⟨25271894759003467103255957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16847929839335644735503971 25271894759003467103255957)
                  ·
                    refine ⟨1184620066828287520465123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25271894759003467103255957 1184620066828287520465123)
                    ·
                      rfl

theorem cell22_3460559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_3460559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460559 prefixEnd_3460559 := by exact prefixLift 3460559
  have htrace : WordTrace (prefixWord ++ tailWord_3460559) baseStart_3460559 baseEnd_3460559 := by
    simpa [prefixWord, tailWord_3460559, baseEnd_3460559] using wordTrace_append hprefix tailTrace_3460559
  have hstable : (prefixWord ++ tailWord_3460559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460559).length < 2 ^ (prefixWord ++ tailWord_3460559).sum := by decide
  have hdescent : baseEnd_3460559 < baseStart_3460559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460610 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3460610 : Nat := 118140960795 + 3460610 * 2 ^ 59
def prefixEnd_3460610 : Nat := 4983230072969 + 3 ^ 40 * 3460610 * 2
def baseEnd_3460610 : Nat := 1184637525170540387439967

theorem tailTrace_3460610 : CollatzResearch.WordTrace tailWord_3460610 prefixEnd_3460610 1184637525170540387439967 := by
  unfold tailWord_3460610
  simp only [CollatzResearch.WordTrace]
  refine ⟨31554703998202117494798821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84145877328538979986130189 31554703998202117494798821)
  ·
    refine ⟨5916506999662897030274779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31554703998202117494798821 5916506999662897030274779)
    ·
      refine ⟨8874760499494345545412169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5916506999662897030274779 8874760499494345545412169)
      ·
        refine ⟨6656070374620759159059127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8874760499494345545412169 6656070374620759159059127)
        ·
          refine ⟨9984105561931138738588691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6656070374620759159059127 9984105561931138738588691)
          ·
            refine ⟨14976158342896708107883037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9984105561931138738588691 14976158342896708107883037)
            ·
              refine ⟨5616059378586265540456139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14976158342896708107883037 5616059378586265540456139)
              ·
                refine ⟨8424089067879398310684209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5616059378586265540456139 8424089067879398310684209)
                ·
                  refine ⟨6318066800909548733013157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8424089067879398310684209 6318066800909548733013157)
                  ·
                    refine ⟨1184637525170540387439967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6318066800909548733013157 1184637525170540387439967)
                    ·
                      rfl

theorem cell22_3460610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3460610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460610 prefixEnd_3460610 := by exact prefixLift 3460610
  have htrace : WordTrace (prefixWord ++ tailWord_3460610) baseStart_3460610 baseEnd_3460610 := by
    simpa [prefixWord, tailWord_3460610, baseEnd_3460610] using wordTrace_append hprefix tailTrace_3460610
  have hstable : (prefixWord ++ tailWord_3460610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460610).length < 2 ^ (prefixWord ++ tailWord_3460610).sum := by decide
  have hdescent : baseEnd_3460610 < baseStart_3460610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460636 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 7]
def baseStart_3460636 : Nat := 118140960795 + 3460636 * 2 ^ 59
def prefixEnd_3460636 : Nat := 4983230072969 + 3 ^ 40 * 3460636 * 2
def baseEnd_3460636 : Nat := 394882141833961662096629

theorem tailTrace_3460636 : CollatzResearch.WordTrace tailWord_3460636 prefixEnd_3460636 394882141833961662096629 := by
  unfold tailWord_3460636
  simp only [CollatzResearch.WordTrace]
  refine ⟨63109882145357138209820881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84146509527142850946427841 63109882145357138209820881)
  ·
    refine ⟨47332411609017853657365661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63109882145357138209820881 47332411609017853657365661)
    ·
      refine ⟨17749654353381695121512123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47332411609017853657365661 17749654353381695121512123)
      ·
        refine ⟨26624481530072542682268185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17749654353381695121512123 26624481530072542682268185)
        ·
          refine ⟨19968361147554407011701139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26624481530072542682268185 19968361147554407011701139)
          ·
            refine ⟨29952541721331610517551709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19968361147554407011701139 29952541721331610517551709)
            ·
              refine ⟨11232203145499353944081891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29952541721331610517551709 11232203145499353944081891)
              ·
                refine ⟨16848304718249030916122837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11232203145499353944081891 16848304718249030916122837)
                ·
                  refine ⟨394882141833961662096629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16848304718249030916122837 394882141833961662096629)
                  ·
                    rfl

theorem cell22_3460636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_3460636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460636 prefixEnd_3460636 := by exact prefixLift 3460636
  have htrace : WordTrace (prefixWord ++ tailWord_3460636) baseStart_3460636 baseEnd_3460636 := by
    simpa [prefixWord, tailWord_3460636, baseEnd_3460636] using wordTrace_append hprefix tailTrace_3460636
  have hstable : (prefixWord ++ tailWord_3460636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460636).length < 2 ^ (prefixWord ++ tailWord_3460636).sum := by decide
  have hdescent : baseEnd_3460636 < baseStart_3460636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460640 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 3, 3]
def baseStart_3460640 : Nat := 118140960795 + 3460640 * 2 ^ 59
def prefixEnd_3460640 : Nat := 4983230072969 + 3 ^ 40 * 3460640 * 2
def baseEnd_3460640 : Nat := 1184647794783630309189875

theorem tailTrace_3460640 : CollatzResearch.WordTrace tailWord_3460640 prefixEnd_3460640 1184647794783630309189875 := by
  unfold tailWord_3460640
  simp only [CollatzResearch.WordTrace]
  refine ⟨63109955091349892551393687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84146606788466523401858249 63109955091349892551393687)
  ·
    refine ⟨94664932637024838827090531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63109955091349892551393687 94664932637024838827090531)
    ·
      refine ⟨141997398955537258240635797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94664932637024838827090531 141997398955537258240635797)
      ·
        refine ⟨6656128076040808980029803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141997398955537258240635797 6656128076040808980029803)
        ·
          refine ⟨9984192114061213470044705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6656128076040808980029803 9984192114061213470044705)
          ·
            refine ⟨7488144085545910102533529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9984192114061213470044705 7488144085545910102533529)
            ·
              refine ⟨5616108064159432576900147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7488144085545910102533529 5616108064159432576900147)
              ·
                refine ⟨8424162096239148865350221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5616108064159432576900147 8424162096239148865350221)
                ·
                  refine ⟨3159060786089680824506333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8424162096239148865350221 3159060786089680824506333)
                  ·
                    refine ⟨1184647794783630309189875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3159060786089680824506333 1184647794783630309189875)
                    ·
                      rfl

theorem cell22_3460640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 3, 3].length) (baseStart_3460640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460640 prefixEnd_3460640 := by exact prefixLift 3460640
  have htrace : WordTrace (prefixWord ++ tailWord_3460640) baseStart_3460640 baseEnd_3460640 := by
    simpa [prefixWord, tailWord_3460640, baseEnd_3460640] using wordTrace_append hprefix tailTrace_3460640
  have hstable : (prefixWord ++ tailWord_3460640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460640).length < 2 ^ (prefixWord ++ tailWord_3460640).sum := by decide
  have hdescent : baseEnd_3460640 < baseStart_3460640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460698 : List Nat := [3, 1, 1, 2, 1, 1, 1, 8, 4]
def baseStart_3460698 : Nat := 118140960795 + 3460698 * 2 ^ 59
def prefixEnd_3460698 : Nat := 4983230072969 + 3 ^ 40 * 3460698 * 2
def baseEnd_3460698 : Nat := 394889216456312497079899

theorem tailTrace_3460698 : CollatzResearch.WordTrace tailWord_3460698 prefixEnd_3460698 394889216456312497079899 := by
  unfold tailWord_3460698
  simp only [CollatzResearch.WordTrace]
  refine ⟨31555506404122415252099687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84148017077659774005599165 31555506404122415252099687)
  ·
    refine ⟨47333259606183622878149531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31555506404122415252099687 47333259606183622878149531)
    ·
      refine ⟨70999889409275434317224297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47333259606183622878149531 70999889409275434317224297)
      ·
        refine ⟨53249917056956575737918223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70999889409275434317224297 53249917056956575737918223)
        ·
          refine ⟨79874875585434863606877335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53249917056956575737918223 79874875585434863606877335)
          ·
            refine ⟨119812313378152295410316003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79874875585434863606877335 119812313378152295410316003)
            ·
              refine ⟨179718470067228443115474005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119812313378152295410316003 179718470067228443115474005)
              ·
                refine ⟨2106075821100333317759461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 179718470067228443115474005 2106075821100333317759461)
                ·
                  refine ⟨394889216456312497079899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2106075821100333317759461 394889216456312497079899)
                  ·
                    rfl

theorem cell22_3460698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_3460698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460698 prefixEnd_3460698 := by exact prefixLift 3460698
  have htrace : WordTrace (prefixWord ++ tailWord_3460698) baseStart_3460698 baseEnd_3460698 := by
    simpa [prefixWord, tailWord_3460698, baseEnd_3460698] using wordTrace_append hprefix tailTrace_3460698
  have hstable : (prefixWord ++ tailWord_3460698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460698).length < 2 ^ (prefixWord ++ tailWord_3460698).sum := by decide
  have hdescent : baseEnd_3460698 < baseStart_3460698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460711 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3460711 : Nat := 118140960795 + 3460711 * 2 ^ 59
def prefixEnd_3460711 : Nat := 4983230072969 + 3 ^ 40 * 3460711 * 2
def baseEnd_3460711 : Nat := 1184672099534609790664657

theorem tailTrace_3460711 : CollatzResearch.WordTrace tailWord_3460711 prefixEnd_3460711 1184672099534609790664657 := by
  unfold tailWord_3460711
  simp only [CollatzResearch.WordTrace]
  refine ⟨126222499765442564228621987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84148333176961709485747991 126222499765442564228621987)
  ·
    refine ⟨189333749648163846342932981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126222499765442564228621987 189333749648163846342932981)
    ·
      refine ⟨17750039029515360594649967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189333749648163846342932981 17750039029515360594649967)
      ·
        refine ⟨26625058544273040891974951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17750039029515360594649967 26625058544273040891974951)
        ·
          refine ⟨39937587816409561337962427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26625058544273040891974951 39937587816409561337962427)
          ·
            refine ⟨59906381724614342006943641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39937587816409561337962427 59906381724614342006943641)
            ·
              refine ⟨44929786293460756505207731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59906381724614342006943641 44929786293460756505207731)
              ·
                refine ⟨67394679440191134757811597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44929786293460756505207731 67394679440191134757811597)
                ·
                  refine ⟨25273004790071675534179349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67394679440191134757811597 25273004790071675534179349)
                  ·
                    refine ⟨1184672099534609790664657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25273004790071675534179349 1184672099534609790664657)
                    ·
                      rfl

theorem cell22_3460711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3460711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460711 prefixEnd_3460711 := by exact prefixLift 3460711
  have htrace : WordTrace (prefixWord ++ tailWord_3460711) baseStart_3460711 baseEnd_3460711 := by
    simpa [prefixWord, tailWord_3460711, baseEnd_3460711] using wordTrace_append hprefix tailTrace_3460711
  have hstable : (prefixWord ++ tailWord_3460711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460711).length < 2 ^ (prefixWord ++ tailWord_3460711).sum := by decide
  have hdescent : baseEnd_3460711 < baseStart_3460711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460717 : List Nat := [1, 5, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_3460717 : Nat := 118140960795 + 3460717 * 2 ^ 59
def prefixEnd_3460717 : Nat := 4983230072969 + 3 ^ 40 * 3460717 * 2
def baseEnd_3460717 : Nat := 1184674153457227775014639

theorem tailTrace_3460717 : CollatzResearch.WordTrace tailWord_3460717 prefixEnd_3460717 1184674153457227775014639 := by
  unfold tailWord_3460717
  simp only [CollatzResearch.WordTrace]
  refine ⟨126222718603420827253340405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84148479068947218168893603 126222718603420827253340405)
  ·
    refine ⟨11833379869070702555000663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126222718603420827253340405 11833379869070702555000663)
    ·
      refine ⟨17750069803606053832500995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11833379869070702555000663 17750069803606053832500995)
      ·
        refine ⟨26625104705409080748751493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17750069803606053832500995 26625104705409080748751493)
        ·
          refine ⟨4992207132264202640390905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26625104705409080748751493 4992207132264202640390905)
          ·
            refine ⟨3744155349198151980293179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4992207132264202640390905 3744155349198151980293179)
            ·
              refine ⟨5616233023797227970439769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744155349198151980293179 5616233023797227970439769)
              ·
                refine ⟨4212174767847920977829827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616233023797227970439769 4212174767847920977829827)
                ·
                  refine ⟨6318262151771881466744741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212174767847920977829827 6318262151771881466744741)
                  ·
                    refine ⟨1184674153457227775014639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6318262151771881466744741 1184674153457227775014639)
                    ·
                      rfl

theorem cell22_3460717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_3460717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460717 prefixEnd_3460717 := by exact prefixLift 3460717
  have htrace : WordTrace (prefixWord ++ tailWord_3460717) baseStart_3460717 baseEnd_3460717 := by
    simpa [prefixWord, tailWord_3460717, baseEnd_3460717] using wordTrace_append hprefix tailTrace_3460717
  have hstable : (prefixWord ++ tailWord_3460717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460717).length < 2 ^ (prefixWord ++ tailWord_3460717).sum := by decide
  have hdescent : baseEnd_3460717 < baseStart_3460717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460820 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3460820 : Nat := 118140960795 + 3460820 * 2 ^ 59
def prefixEnd_3460820 : Nat := 4983230072969 + 3 ^ 40 * 3460820 * 2
def baseEnd_3460820 : Nat := 1184709412462169839689323

theorem tailTrace_3460820 : CollatzResearch.WordTrace tailWord_3460820 prefixEnd_3460820 1184709412462169839689323 := by
  unfold tailWord_3460820
  simp only [CollatzResearch.WordTrace]
  refine ⟨63113237661023837922169957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84150983548031783896226609 63113237661023837922169957)
  ·
    refine ⟨11833732061441969610406867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63113237661023837922169957 11833732061441969610406867)
    ·
      refine ⟨17750598092162954415610301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11833732061441969610406867 17750598092162954415610301)
      ·
        refine ⟨6656474284561107905853863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17750598092162954415610301 6656474284561107905853863)
        ·
          refine ⟨9984711426841661858780795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6656474284561107905853863 9984711426841661858780795)
          ·
            refine ⟨14977067140262492788171193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9984711426841661858780795 14977067140262492788171193)
            ·
              refine ⟨11232800355196869591128395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14977067140262492788171193 11232800355196869591128395)
              ·
                refine ⟨16849200532795304386692593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11232800355196869591128395 16849200532795304386692593)
                ·
                  refine ⟨12636900399596478290019445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16849200532795304386692593 12636900399596478290019445)
                  ·
                    refine ⟨1184709412462169839689323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12636900399596478290019445 1184709412462169839689323)
                    ·
                      rfl

theorem cell22_3460820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3460820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460820 prefixEnd_3460820 := by exact prefixLift 3460820
  have htrace : WordTrace (prefixWord ++ tailWord_3460820) baseStart_3460820 baseEnd_3460820 := by
    simpa [prefixWord, tailWord_3460820, baseEnd_3460820] using wordTrace_append hprefix tailTrace_3460820
  have hstable : (prefixWord ++ tailWord_3460820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460820).length < 2 ^ (prefixWord ++ tailWord_3460820).sum := by decide
  have hdescent : baseEnd_3460820 < baseStart_3460820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460863 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 4, 4]
def baseStart_3460863 : Nat := 118140960795 + 3460863 * 2 ^ 59
def prefixEnd_3460863 : Nat := 4983230072969 + 3 ^ 40 * 3460863 * 2
def baseEnd_3460863 : Nat := 1184724132240932060864191

theorem tailTrace_3460863 : CollatzResearch.WordTrace tailWord_3460863 prefixEnd_3460863 1184724132240932060864191 := by
  unfold tailWord_3460863
  simp only [CollatzResearch.WordTrace]
  refine ⟨126228043660891894188155243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84152029107261262792103495 126228043660891894188155243)
  ·
    refine ⟨189342065491337841282232865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126228043660891894188155243 189342065491337841282232865)
    ·
      refine ⟨142006549118503380961674649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189342065491337841282232865 142006549118503380961674649)
      ·
        refine ⟨106504911838877535721255987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142006549118503380961674649 106504911838877535721255987)
        ·
          refine ⟨159757367758316303581883981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106504911838877535721255987 159757367758316303581883981)
          ·
            refine ⟨59909012909368613843206493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159757367758316303581883981 59909012909368613843206493)
            ·
              refine ⟨22465879841013230191202435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59909012909368613843206493 22465879841013230191202435)
              ·
                refine ⟨33698819761519845286803653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22465879841013230191202435 33698819761519845286803653)
                ·
                  refine ⟨6318528705284970991275685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33698819761519845286803653 6318528705284970991275685)
                  ·
                    refine ⟨1184724132240932060864191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6318528705284970991275685 1184724132240932060864191)
                    ·
                      rfl

theorem cell22_3460863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_3460863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460863 prefixEnd_3460863 := by exact prefixLift 3460863
  have htrace : WordTrace (prefixWord ++ tailWord_3460863) baseStart_3460863 baseEnd_3460863 := by
    simpa [prefixWord, tailWord_3460863, baseEnd_3460863] using wordTrace_append hprefix tailTrace_3460863
  have hstable : (prefixWord ++ tailWord_3460863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460863).length < 2 ^ (prefixWord ++ tailWord_3460863).sum := by decide
  have hdescent : baseEnd_3460863 < baseStart_3460863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460865 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 4, 3]
def baseStart_3460865 : Nat := 118140960795 + 3460865 * 2 ^ 59
def prefixEnd_3460865 : Nat := 4983230072969 + 3 ^ 40 * 3460865 * 2
def baseEnd_3460865 : Nat := 1184724816881804722314185

theorem tailTrace_3460865 : CollatzResearch.WordTrace tailWord_3460865 prefixEnd_3460865 1184724816881804722314185 := by
  unfold tailWord_3460865
  simp only [CollatzResearch.WordTrace]
  refine ⟨126228116606884648529728049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84152077737923099019818699 126228116606884648529728049)
  ·
    refine ⟨94671087455163486397296037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126228116606884648529728049 94671087455163486397296037)
    ·
      refine ⟨17750828897843153699493007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94671087455163486397296037 17750828897843153699493007)
      ·
        refine ⟨26626243346764730549239511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17750828897843153699493007 26626243346764730549239511)
        ·
          refine ⟨39939365020147095823859267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26626243346764730549239511 39939365020147095823859267)
          ·
            refine ⟨59909047530220643735788901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39939365020147095823859267 59909047530220643735788901)
            ·
              refine ⟨11232946411916370700460419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59909047530220643735788901 11232946411916370700460419)
              ·
                refine ⟨16849419617874556050690629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11232946411916370700460419 16849419617874556050690629)
                ·
                  refine ⟨3159266178351479259504493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16849419617874556050690629 3159266178351479259504493)
                  ·
                    refine ⟨1184724816881804722314185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3159266178351479259504493 1184724816881804722314185)
                    ·
                      rfl

theorem cell22_3460865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_3460865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460865 prefixEnd_3460865 := by exact prefixLift 3460865
  have htrace : WordTrace (prefixWord ++ tailWord_3460865) baseStart_3460865 baseEnd_3460865 := by
    simpa [prefixWord, tailWord_3460865, baseEnd_3460865] using wordTrace_append hprefix tailTrace_3460865
  have hstable : (prefixWord ++ tailWord_3460865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460865).length < 2 ^ (prefixWord ++ tailWord_3460865).sum := by decide
  have hdescent : baseEnd_3460865 < baseStart_3460865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460878 : List Nat := [4, 1, 1, 2, 1, 1, 3, 9]
def baseStart_3460878 : Nat := 118140960795 + 3460878 * 2 ^ 59
def prefixEnd_3460878 : Nat := 4983230072969 + 3 ^ 40 * 3460878 * 2
def baseEnd_3460878 : Nat := 131636585227497446859905

theorem tailTrace_3460878 : CollatzResearch.WordTrace tailWord_3460878 prefixEnd_3460878 131636585227497446859905 := by
  unfold tailWord_3460878
  simp only [CollatzResearch.WordTrace]
  refine ⟨15778573844479693968743911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84152393837225034499967525 15778573844479693968743911)
  ·
    refine ⟨23667860766719540953115867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15778573844479693968743911 23667860766719540953115867)
    ·
      refine ⟨35501791150079311429673801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23667860766719540953115867 35501791150079311429673801)
      ·
        refine ⟨26626343362559483572255351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35501791150079311429673801 26626343362559483572255351)
        ·
          refine ⟨39939515043839225358383027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26626343362559483572255351 39939515043839225358383027)
          ·
            refine ⟨59909272565758838037574541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39939515043839225358383027 59909272565758838037574541)
            ·
              refine ⟨22465977212159564264090453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59909272565758838037574541 22465977212159564264090453)
              ·
                refine ⟨131636585227497446859905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22465977212159564264090453 131636585227497446859905)
                ·
                  rfl

theorem cell22_3460878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_3460878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460878 prefixEnd_3460878 := by exact prefixLift 3460878
  have htrace : WordTrace (prefixWord ++ tailWord_3460878) baseStart_3460878 baseEnd_3460878 := by
    simpa [prefixWord, tailWord_3460878, baseEnd_3460878] using wordTrace_append hprefix tailTrace_3460878
  have hstable : (prefixWord ++ tailWord_3460878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460878).length < 2 ^ (prefixWord ++ tailWord_3460878).sum := by decide
  have hdescent : baseEnd_3460878 < baseStart_3460878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460925 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_3460925 : Nat := 118140960795 + 3460925 * 2 ^ 59
def prefixEnd_3460925 : Nat := 4983230072969 + 3 ^ 40 * 3460925 * 2
def baseEnd_3460925 : Nat := 1184745356107984565814001

theorem tailTrace_3460925 : CollatzResearch.WordTrace tailWord_3460925 prefixEnd_3460925 1184745356107984565814001 := by
  unfold tailWord_3460925
  simp only [CollatzResearch.WordTrace]
  refine ⟨126230304986667278776912229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84153536657778185851274819 126230304986667278776912229)
  ·
    refine ⟨23668182185000114770671043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126230304986667278776912229 23668182185000114770671043)
    ·
      refine ⟨35502273277500172156006565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23668182185000114770671043 35502273277500172156006565)
      ·
        refine ⟨6656676239531282279251231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35502273277500172156006565 6656676239531282279251231)
        ·
          refine ⟨9985014359296923418876847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6656676239531282279251231 9985014359296923418876847)
          ·
            refine ⟨14977521538945385128315271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9985014359296923418876847 14977521538945385128315271)
            ·
              refine ⟨22466282308418077692472907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14977521538945385128315271 22466282308418077692472907)
              ·
                refine ⟨33699423462627116538709361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22466282308418077692472907 33699423462627116538709361)
                ·
                  refine ⟨25274567596970337404032021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33699423462627116538709361 25274567596970337404032021)
                  ·
                    refine ⟨1184745356107984565814001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25274567596970337404032021 1184745356107984565814001)
                    ·
                      rfl

theorem cell22_3460925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_3460925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460925 prefixEnd_3460925 := by exact prefixLift 3460925
  have htrace : WordTrace (prefixWord ++ tailWord_3460925) baseStart_3460925 baseEnd_3460925 := by
    simpa [prefixWord, tailWord_3460925, baseEnd_3460925] using wordTrace_append hprefix tailTrace_3460925
  have hstable : (prefixWord ++ tailWord_3460925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460925).length < 2 ^ (prefixWord ++ tailWord_3460925).sum := by decide
  have hdescent : baseEnd_3460925 < baseStart_3460925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460974 : List Nat := [4, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_3460974 : Nat := 118140960795 + 3460974 * 2 ^ 59
def prefixEnd_3460974 : Nat := 4983230072969 + 3 ^ 40 * 3460974 * 2
def baseEnd_3460974 : Nat := 394920709936454923779617

theorem tailTrace_3460974 : CollatzResearch.WordTrace tailWord_3460974 prefixEnd_3460974 394920709936454923779617 := by
  unfold tailWord_3460974
  simp only [CollatzResearch.WordTrace]
  refine ⟨15779011520436220018180747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84154728108993173430297317 15779011520436220018180747)
  ·
    refine ⟨23668517280654330027271121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15779011520436220018180747 23668517280654330027271121)
    ·
      refine ⟨17751387960490747520453341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23668517280654330027271121 17751387960490747520453341)
      ·
        refine ⟨6656770485184030320170003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17751387960490747520453341 6656770485184030320170003)
        ·
          refine ⟨9985155727776045480255005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6656770485184030320170003 9985155727776045480255005)
          ·
            refine ⟨3744433397916017055095627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9985155727776045480255005 3744433397916017055095627)
            ·
              refine ⟨5616650096874025582643441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744433397916017055095627 5616650096874025582643441)
              ·
                refine ⟨4212487572655519186982581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616650096874025582643441 4212487572655519186982581)
                ·
                  refine ⟨394920709936454923779617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4212487572655519186982581 394920709936454923779617)
                  ·
                    rfl

theorem cell22_3460974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_3460974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460974 prefixEnd_3460974 := by exact prefixLift 3460974
  have htrace : WordTrace (prefixWord ++ tailWord_3460974) baseStart_3460974 baseEnd_3460974 := by
    simpa [prefixWord, tailWord_3460974, baseEnd_3460974] using wordTrace_append hprefix tailTrace_3460974
  have hstable : (prefixWord ++ tailWord_3460974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460974).length < 2 ^ (prefixWord ++ tailWord_3460974).sum := by decide
  have hdescent : baseEnd_3460974 < baseStart_3460974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460983 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 2, 9]
def baseStart_3460983 : Nat := 118140960795 + 3460983 * 2 ^ 59
def prefixEnd_3460983 : Nat := 4983230072969 + 3 ^ 40 * 3460983 * 2
def baseEnd_3460983 : Nat := 1184765210693291747863823

theorem tailTrace_3460983 : CollatzResearch.WordTrace tailWord_3460983 prefixEnd_3460983 1184765210693291747863823 := by
  unfold tailWord_3460983
  simp only [CollatzResearch.WordTrace]
  refine ⟨126232420420457154682523603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84154946946971436455015735 126232420420457154682523603)
  ·
    refine ⟨189348630630685732023785405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126232420420457154682523603 189348630630685732023785405)
    ·
      refine ⟨71005736486507149508919527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189348630630685732023785405 71005736486507149508919527)
      ·
        refine ⟨106508604729760724263379291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71005736486507149508919527 106508604729760724263379291)
        ·
          refine ⟨159762907094641086395068937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106508604729760724263379291 159762907094641086395068937)
          ·
            refine ⟨119822180320980814796301703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159762907094641086395068937 119822180320980814796301703)
            ·
              refine ⟨179733270481471222194452555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119822180320980814796301703 179733270481471222194452555)
              ·
                refine ⟨269599905722206833291678833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179733270481471222194452555 269599905722206833291678833)
                ·
                  refine ⟨202199929291655124968759125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269599905722206833291678833 202199929291655124968759125)
                  ·
                    refine ⟨1184765210693291747863823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 202199929291655124968759125 1184765210693291747863823)
                    ·
                      rfl

theorem cell22_3460983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_3460983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460983 prefixEnd_3460983 := by exact prefixLift 3460983
  have htrace : WordTrace (prefixWord ++ tailWord_3460983) baseStart_3460983 baseEnd_3460983 := by
    simpa [prefixWord, tailWord_3460983, baseEnd_3460983] using wordTrace_append hprefix tailTrace_3460983
  have hstable : (prefixWord ++ tailWord_3460983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460983).length < 2 ^ (prefixWord ++ tailWord_3460983).sum := by decide
  have hdescent : baseEnd_3460983 < baseStart_3460983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460985 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 6]
def baseStart_3460985 : Nat := 118140960795 + 3460985 * 2 ^ 59
def prefixEnd_3460985 : Nat := 4983230072969 + 3 ^ 40 * 3460985 * 2
def baseEnd_3460985 : Nat := 394921965111388136437939

theorem tailTrace_3460985 : CollatzResearch.WordTrace tailWord_3460985 prefixEnd_3460985 394921965111388136437939 := by
  unfold tailWord_3460985
  simp only [CollatzResearch.WordTrace]
  refine ⟨126232493366449909024096409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84154995577633272682730939 126232493366449909024096409)
  ·
    refine ⟨94674370024837431768072307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126232493366449909024096409 94674370024837431768072307)
    ·
      refine ⟨142011555037256147652108461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94674370024837431768072307 142011555037256147652108461)
      ·
        refine ⟨53254333138971055369540673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142011555037256147652108461 53254333138971055369540673)
        ·
          refine ⟨39940749854228291527155505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53254333138971055369540673 39940749854228291527155505)
          ·
            refine ⟨29955562390671218645366629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39940749854228291527155505 29955562390671218645366629)
            ·
              refine ⟨5616667948250853496006243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29955562390671218645366629 5616667948250853496006243)
              ·
                refine ⟨8425001922376280244009365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5616667948250853496006243 8425001922376280244009365)
                ·
                  refine ⟨394921965111388136437939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8425001922376280244009365 394921965111388136437939)
                  ·
                    rfl

theorem cell22_3460985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_3460985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3460985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3460985 prefixEnd_3460985 := by exact prefixLift 3460985
  have htrace : WordTrace (prefixWord ++ tailWord_3460985) baseStart_3460985 baseEnd_3460985 := by
    simpa [prefixWord, tailWord_3460985, baseEnd_3460985] using wordTrace_append hprefix tailTrace_3460985
  have hstable : (prefixWord ++ tailWord_3460985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460985).length < 2 ^ (prefixWord ++ tailWord_3460985).sum := by decide
  have hdescent : baseEnd_3460985 < baseStart_3460985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461015 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 1, 6]
def baseStart_3461015 : Nat := 118140960795 + 3461015 * 2 ^ 59
def prefixEnd_3461015 : Nat := 4983230072969 + 3 ^ 40 * 3461015 * 2
def baseEnd_3461015 : Nat := 1184776164947254331063725

theorem tailTrace_3461015 : CollatzResearch.WordTrace tailWord_3461015 prefixEnd_3461015 1184776164947254331063725 := by
  unfold tailWord_3461015
  simp only [CollatzResearch.WordTrace]
  refine ⟨126233587556341224147688499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84155725037560816098458999 126233587556341224147688499)
  ·
    refine ⟨189350381334511836221532749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126233587556341224147688499 189350381334511836221532749)
    ·
      refine ⟨71006393000441938583074781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189350381334511836221532749 71006393000441938583074781)
      ·
        refine ⟨26627397375165726968653043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71006393000441938583074781 26627397375165726968653043)
        ·
          refine ⟨39941096062748590452979565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26627397375165726968653043 39941096062748590452979565)
          ·
            refine ⟨14977911023530721419867337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39941096062748590452979565 14977911023530721419867337)
            ·
              refine ⟨11233433267648041064900503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14977911023530721419867337 11233433267648041064900503)
              ·
                refine ⟨16850149901472061597350755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11233433267648041064900503 16850149901472061597350755)
                ·
                  refine ⟨25275224852208092396026133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16850149901472061597350755 25275224852208092396026133)
                  ·
                    refine ⟨1184776164947254331063725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25275224852208092396026133 1184776164947254331063725)
                    ·
                      rfl

theorem cell22_3461015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_3461015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461015 prefixEnd_3461015 := by exact prefixLift 3461015
  have htrace : WordTrace (prefixWord ++ tailWord_3461015) baseStart_3461015 baseEnd_3461015 := by
    simpa [prefixWord, tailWord_3461015, baseEnd_3461015] using wordTrace_append hprefix tailTrace_3461015
  have hstable : (prefixWord ++ tailWord_3461015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461015).length < 2 ^ (prefixWord ++ tailWord_3461015).sum := by decide
  have hdescent : baseEnd_3461015 < baseStart_3461015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461079 : List Nat := [1, 1, 3, 2, 1, 1, 4, 5, 1, 3]
def baseStart_3461079 : Nat := 118140960795 + 3461079 * 2 ^ 59
def prefixEnd_3461079 : Nat := 4983230072969 + 3 ^ 40 * 3461079 * 2
def baseEnd_3461079 : Nat := 1184798073455179497463529

theorem tailTrace_3461079 : CollatzResearch.WordTrace tailWord_3461079 prefixEnd_3461079 1184798073455179497463529 := by
  unfold tailWord_3461079
  simp only [CollatzResearch.WordTrace]
  refine ⟨126235921828109363078018291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84157281218739575385345527 126235921828109363078018291)
  ·
    refine ⟨189353882742164044617027437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126235921828109363078018291 189353882742164044617027437)
    ·
      refine ⟨71007706028311516731385289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189353882742164044617027437 71007706028311516731385289)
      ·
        refine ⟨53255779521233637548538967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71007706028311516731385289 53255779521233637548538967)
        ·
          refine ⟨79883669281850456322808451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53255779521233637548538967 79883669281850456322808451)
          ·
            refine ⟨119825503922775684484212677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79883669281850456322808451 119825503922775684484212677)
            ·
              refine ⟨22467281985520440840789877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119825503922775684484212677 22467281985520440840789877)
              ·
                refine ⟨2106307686142541328824051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22467281985520440840789877 2106307686142541328824051)
                ·
                  refine ⟨3159461529213811993236077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106307686142541328824051 3159461529213811993236077)
                  ·
                    refine ⟨1184798073455179497463529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3159461529213811993236077 1184798073455179497463529)
                    ·
                      rfl

theorem cell22_3461079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_3461079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461079 prefixEnd_3461079 := by exact prefixLift 3461079
  have htrace : WordTrace (prefixWord ++ tailWord_3461079) baseStart_3461079 baseEnd_3461079 := by
    simpa [prefixWord, tailWord_3461079, baseEnd_3461079] using wordTrace_append hprefix tailTrace_3461079
  have hstable : (prefixWord ++ tailWord_3461079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461079).length < 2 ^ (prefixWord ++ tailWord_3461079).sum := by decide
  have hdescent : baseEnd_3461079 < baseStart_3461079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461092 : List Nat := [2, 3, 1, 1, 1, 1, 6, 2, 5]
def baseStart_3461092 : Nat := 118140960795 + 3461092 * 2 ^ 59
def prefixEnd_3461092 : Nat := 4983230072969 + 3 ^ 40 * 3461092 * 2
def baseEnd_3461092 : Nat := 394934174540283932296163

theorem tailTrace_3461092 : CollatzResearch.WordTrace tailWord_3461092 prefixEnd_3461092 394934174540283932296163 := by
  unfold tailWord_3461092
  simp only [CollatzResearch.WordTrace]
  refine ⟨63118197988531133149120765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84157597318041510865494353 63118197988531133149120765)
  ·
    refine ⟨23669324245699174930920287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63118197988531133149120765 23669324245699174930920287)
    ·
      refine ⟨35503986368548762396380431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23669324245699174930920287 35503986368548762396380431)
      ·
        refine ⟨53255979552823143594570647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35503986368548762396380431 53255979552823143594570647)
        ·
          refine ⟨79883969329234715391855971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53255979552823143594570647 79883969329234715391855971)
          ·
            refine ⟨119825953993852073087783957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79883969329234715391855971 119825953993852073087783957)
            ·
              refine ⟨5616841593461815925989873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119825953993852073087783957 5616841593461815925989873)
              ·
                refine ⟨4212631195096361944492405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616841593461815925989873 4212631195096361944492405)
                ·
                  refine ⟨394934174540283932296163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4212631195096361944492405 394934174540283932296163)
                  ·
                    rfl

theorem cell22_3461092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_3461092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461092 prefixEnd_3461092 := by exact prefixLift 3461092
  have htrace : WordTrace (prefixWord ++ tailWord_3461092) baseStart_3461092 baseEnd_3461092 := by
    simpa [prefixWord, tailWord_3461092, baseEnd_3461092] using wordTrace_append hprefix tailTrace_3461092
  have hstable : (prefixWord ++ tailWord_3461092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461092).length < 2 ^ (prefixWord ++ tailWord_3461092).sum := by decide
  have hdescent : baseEnd_3461092 < baseStart_3461092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461139 : List Nat := [1, 1, 1, 2, 1, 4, 6, 1, 1, 4]
def baseStart_3461139 : Nat := 118140960795 + 3461139 * 2 ^ 59
def prefixEnd_3461139 : Nat := 4983230072969 + 3 ^ 40 * 3461139 * 2
def baseEnd_3461139 : Nat := 1184818612681359340963345

theorem tailTrace_3461139 : CollatzResearch.WordTrace tailWord_3461139 prefixEnd_3461139 1184818612681359340963345 := by
  unfold tailWord_3461139
  simp only [CollatzResearch.WordTrace]
  refine ⟨126238110207891993325202471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84158740138594662216801647 126238110207891993325202471)
  ·
    refine ⟨189357165311837989987803707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126238110207891993325202471 189357165311837989987803707)
    ·
      refine ⟨284035747967756984981705561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189357165311837989987803707 284035747967756984981705561)
      ·
        refine ⟨213026810975817738736279171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284035747967756984981705561 213026810975817738736279171)
        ·
          refine ⟨319540216463726608104418757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213026810975817738736279171 319540216463726608104418757)
          ·
            refine ⟨59913790586948739019578517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319540216463726608104418757 59913790586948739019578517)
            ·
              refine ⟨2808458933763222141542743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59913790586948739019578517 2808458933763222141542743)
              ·
                refine ⟨4212688400644833212314115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2808458933763222141542743 4212688400644833212314115)
                ·
                  refine ⟨6319032600967249818471173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212688400644833212314115 6319032600967249818471173)
                  ·
                    refine ⟨1184818612681359340963345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6319032600967249818471173 1184818612681359340963345)
                    ·
                      rfl

theorem cell22_3461139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 1, 4].length) (baseStart_3461139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461139 prefixEnd_3461139 := by exact prefixLift 3461139
  have htrace : WordTrace (prefixWord ++ tailWord_3461139) baseStart_3461139 baseEnd_3461139 := by
    simpa [prefixWord, tailWord_3461139, baseEnd_3461139] using wordTrace_append hprefix tailTrace_3461139
  have hstable : (prefixWord ++ tailWord_3461139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461139).length < 2 ^ (prefixWord ++ tailWord_3461139).sum := by decide
  have hdescent : baseEnd_3461139 < baseStart_3461139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461154 : List Nat := [3, 3, 1, 1, 1, 2, 1, 6, 4]
def baseStart_3461154 : Nat := 118140960795 + 3461154 * 2 ^ 59
def prefixEnd_3461154 : Nat := 4983230072969 + 3 ^ 40 * 3461154 * 2
def baseEnd_3461154 : Nat := 394941249162634767279433

theorem tailTrace_3461154 : CollatzResearch.WordTrace tailWord_3461154 prefixEnd_3461154 394941249162634767279433 := by
  unfold tailWord_3461154
  simp only [CollatzResearch.WordTrace]
  refine ⟨31559664325709412721749629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84159104868558433924665677 31559664325709412721749629)
  ·
    refine ⟨11834874122141029770656111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31559664325709412721749629 11834874122141029770656111)
    ·
      refine ⟨17752311183211544655984167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11834874122141029770656111 17752311183211544655984167)
      ·
        refine ⟨26628466774817316983976251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17752311183211544655984167 26628466774817316983976251)
        ·
          refine ⟨39942700162225975475964377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26628466774817316983976251 39942700162225975475964377)
          ·
            refine ⟨29957025121669481606973283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39942700162225975475964377 29957025121669481606973283)
            ·
              refine ⟨44935537682504222410459925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29957025121669481606973283 44935537682504222410459925)
              ·
                refine ⟨2106353328867385425490309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44935537682504222410459925 2106353328867385425490309)
                ·
                  refine ⟨394941249162634767279433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2106353328867385425490309 394941249162634767279433)
                  ·
                    rfl

theorem cell22_3461154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_3461154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461154 prefixEnd_3461154 := by exact prefixLift 3461154
  have htrace : WordTrace (prefixWord ++ tailWord_3461154) baseStart_3461154 baseEnd_3461154 := by
    simpa [prefixWord, tailWord_3461154, baseEnd_3461154] using wordTrace_append hprefix tailTrace_3461154
  have hstable : (prefixWord ++ tailWord_3461154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461154).length < 2 ^ (prefixWord ++ tailWord_3461154).sum := by decide
  have hdescent : baseEnd_3461154 < baseStart_3461154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461169 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 1, 5]
def baseStart_3461169 : Nat := 118140960795 + 3461169 * 2 ^ 59
def prefixEnd_3461169 : Nat := 4983230072969 + 3 ^ 40 * 3461169 * 2
def baseEnd_3461169 : Nat := 1184828882294449262713253

theorem tailTrace_3461169 : CollatzResearch.WordTrace tailWord_3461169 prefixEnd_3461169 1184828882294449262713253 := by
  unfold tailWord_3461169
  simp only [CollatzResearch.WordTrace]
  refine ⟨126239204397783308448794561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84159469598522205632529707 126239204397783308448794561)
  ·
    refine ⟨94679403298337481336595921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126239204397783308448794561 94679403298337481336595921)
    ·
      refine ⟨71009552473753111002446941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94679403298337481336595921 71009552473753111002446941)
      ·
        refine ⟨26628582177657416625917603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71009552473753111002446941 26628582177657416625917603)
        ·
          refine ⟨39942873266486124938876405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26628582177657416625917603 39942873266486124938876405)
          ·
            refine ⟨3744644368733074213019663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39942873266486124938876405 3744644368733074213019663)
            ·
              refine ⟨5616966553099611319529495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744644368733074213019663 5616966553099611319529495)
              ·
                refine ⟨8425449829649416979294243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5616966553099611319529495 8425449829649416979294243)
                ·
                  refine ⟨12638174744474125468941365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8425449829649416979294243 12638174744474125468941365)
                  ·
                    refine ⟨1184828882294449262713253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12638174744474125468941365 1184828882294449262713253)
                    ·
                      rfl

theorem cell22_3461169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_3461169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461169 prefixEnd_3461169 := by exact prefixLift 3461169
  have htrace : WordTrace (prefixWord ++ tailWord_3461169) baseStart_3461169 baseEnd_3461169 := by
    simpa [prefixWord, tailWord_3461169, baseEnd_3461169] using wordTrace_append hprefix tailTrace_3461169
  have hstable : (prefixWord ++ tailWord_3461169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461169).length < 2 ^ (prefixWord ++ tailWord_3461169).sum := by decide
  have hdescent : baseEnd_3461169 < baseStart_3461169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461304 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 4, 3]
def baseStart_3461304 : Nat := 118140960795 + 3461304 * 2 ^ 59
def prefixEnd_3461304 : Nat := 4983230072969 + 3 ^ 40 * 3461304 * 2
def baseEnd_3461304 : Nat := 1184875095553353910587839

theorem tailTrace_3461304 : CollatzResearch.WordTrace tailWord_3461304 prefixEnd_3461304 1184875095553353910587839 := by
  unfold tailWord_3461304
  simp only [CollatzResearch.WordTrace]
  refine ⟨63122064126147113252479483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84162752168196151003305977 63122064126147113252479483)
  ·
    refine ⟨94683096189220669878719225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63122064126147113252479483 94683096189220669878719225)
    ·
      refine ⟨71012322141915502409039419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94683096189220669878719225 71012322141915502409039419)
      ·
        refine ⟨106518483212873253613559129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71012322141915502409039419 106518483212873253613559129)
        ·
          refine ⟨79888862409654940210169347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106518483212873253613559129 79888862409654940210169347)
          ·
            refine ⟨119833293614482410315254021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79888862409654940210169347 119833293614482410315254021)
            ·
              refine ⟨22468742552715451934110129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119833293614482410315254021 22468742552715451934110129)
              ·
                refine ⟨16851556914536588950582597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22468742552715451934110129 16851556914536588950582597)
                ·
                  refine ⟨3159666921475610428234237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16851556914536588950582597 3159666921475610428234237)
                  ·
                    refine ⟨1184875095553353910587839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3159666921475610428234237 1184875095553353910587839)
                    ·
                      rfl

theorem cell22_3461304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_3461304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461304 prefixEnd_3461304 := by exact prefixLift 3461304
  have htrace : WordTrace (prefixWord ++ tailWord_3461304) baseStart_3461304 baseEnd_3461304 := by
    simpa [prefixWord, tailWord_3461304, baseEnd_3461304] using wordTrace_append hprefix tailTrace_3461304
  have hstable : (prefixWord ++ tailWord_3461304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461304).length < 2 ^ (prefixWord ++ tailWord_3461304).sum := by decide
  have hdescent : baseEnd_3461304 < baseStart_3461304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461351 : List Nat := [1, 1, 5, 3, 1, 1, 4, 6]
def baseStart_3461351 : Nat := 118140960795 + 3461351 * 2 ^ 59
def prefixEnd_3461351 : Nat := 4983230072969 + 3 ^ 40 * 3461351 * 2
def baseEnd_3461351 : Nat := 131654576068206828295855

theorem tailTrace_3461351 : CollatzResearch.WordTrace tailWord_3461351 prefixEnd_3461351 131654576068206828295855 := by
  unfold tailWord_3461351
  simp only [CollatzResearch.WordTrace]
  refine ⟨126245842483123953531919907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84163894988749302354613271 126245842483123953531919907)
  ·
    refine ⟨189368763724685930297879861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126245842483123953531919907 189368763724685930297879861)
    ·
      refine ⟨17753321599189305965426237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189368763724685930297879861 17753321599189305965426237)
      ·
        refine ⟨6657495599695989737034839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17753321599189305965426237 6657495599695989737034839)
        ·
          refine ⟨9986243399543984605552259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6657495599695989737034839 9986243399543984605552259)
          ·
            refine ⟨14979365099315976908328389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9986243399543984605552259 14979365099315976908328389)
            ·
              refine ⟨2808630956121745670311573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14979365099315976908328389 2808630956121745670311573)
              ·
                refine ⟨131654576068206828295855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2808630956121745670311573 131654576068206828295855)
                ·
                  rfl

theorem cell22_3461351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 6].length) (baseStart_3461351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461351 prefixEnd_3461351 := by exact prefixLift 3461351
  have htrace : WordTrace (prefixWord ++ tailWord_3461351) baseStart_3461351 baseEnd_3461351 := by
    simpa [prefixWord, tailWord_3461351, baseEnd_3461351] using wordTrace_append hprefix tailTrace_3461351
  have hstable : (prefixWord ++ tailWord_3461351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461351).length < 2 ^ (prefixWord ++ tailWord_3461351).sum := by decide
  have hdescent : baseEnd_3461351 < baseStart_3461351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461366 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_3461366 : Nat := 118140960795 + 3461366 * 2 ^ 59
def prefixEnd_3461366 : Nat := 4983230072969 + 3 ^ 40 * 3461366 * 2
def baseEnd_3461366 : Nat := 1184896319420406415537649

theorem tailTrace_3461366 : CollatzResearch.WordTrace tailWord_3461366 prefixEnd_3461366 1184896319420406415537649 := by
  unfold tailWord_3461366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7890399348629350693357247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84164259718713074062477301 7890399348629350693357247)
  ·
    refine ⟨11835599022944026040035871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7890399348629350693357247 11835599022944026040035871)
    ·
      refine ⟨17753398534416039060053807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11835599022944026040035871 17753398534416039060053807)
      ·
        refine ⟨26630097801624058590080711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17753398534416039060053807 26630097801624058590080711)
        ·
          refine ⟨39945146702436087885121067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26630097801624058590080711 39945146702436087885121067)
          ·
            refine ⟨59917720053654131827681601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39945146702436087885121067 59917720053654131827681601)
            ·
              refine ⟨44938290040240598870761201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59917720053654131827681601 44938290040240598870761201)
              ·
                refine ⟨33703717530180449153070901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44938290040240598870761201 33703717530180449153070901)
                ·
                  refine ⟨3159723518454417108100397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33703717530180449153070901 3159723518454417108100397)
                  ·
                    refine ⟨1184896319420406415537649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3159723518454417108100397 1184896319420406415537649)
                    ·
                      rfl

theorem cell22_3461366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_3461366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461366 prefixEnd_3461366 := by exact prefixLift 3461366
  have htrace : WordTrace (prefixWord ++ tailWord_3461366) baseStart_3461366 baseEnd_3461366 := by
    simpa [prefixWord, tailWord_3461366, baseEnd_3461366] using wordTrace_append hprefix tailTrace_3461366
  have hstable : (prefixWord ++ tailWord_3461366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461366).length < 2 ^ (prefixWord ++ tailWord_3461366).sum := by decide
  have hdescent : baseEnd_3461366 < baseStart_3461366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461379 : List Nat := [1, 1, 1, 3, 2, 3, 2, 4, 5]
def baseStart_3461379 : Nat := 118140960795 + 3461379 * 2 ^ 59
def prefixEnd_3461379 : Nat := 4983230072969 + 3 ^ 40 * 3461379 * 2
def baseEnd_3461379 : Nat := 394966923195359571654203

theorem tailTrace_3461379 : CollatzResearch.WordTrace tailWord_3461379 prefixEnd_3461379 394966923195359571654203 := by
  unfold tailWord_3461379
  simp only [CollatzResearch.WordTrace]
  refine ⟨126246863727022514313939191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84164575818015009542626127 126246863727022514313939191)
  ·
    refine ⟨189370295590533771470908787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126246863727022514313939191 189370295590533771470908787)
    ·
      refine ⟨284055443385800657206363181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189370295590533771470908787 284055443385800657206363181)
      ·
        refine ⟨106520791269675246452386193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284055443385800657206363181 106520791269675246452386193)
        ·
          refine ⟨79890593452256434839289645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106520791269675246452386193 79890593452256434839289645)
          ·
            refine ⟨29958972544596163064733617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79890593452256434839289645 29958972544596163064733617)
            ·
              refine ⟨22469229408447122298550213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29958972544596163064733617 22469229408447122298550213)
              ·
                refine ⟨4212980514083835430978165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22469229408447122298550213 4212980514083835430978165)
                ·
                  refine ⟨394966923195359571654203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4212980514083835430978165 394966923195359571654203)
                  ·
                    rfl

theorem cell22_3461379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 5].length) (baseStart_3461379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461379 prefixEnd_3461379 := by exact prefixLift 3461379
  have htrace : WordTrace (prefixWord ++ tailWord_3461379) baseStart_3461379 baseEnd_3461379 := by
    simpa [prefixWord, tailWord_3461379, baseEnd_3461379] using wordTrace_append hprefix tailTrace_3461379
  have hstable : (prefixWord ++ tailWord_3461379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461379).length < 2 ^ (prefixWord ++ tailWord_3461379).sum := by decide
  have hdescent : baseEnd_3461379 < baseStart_3461379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461439 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 3, 5]
def baseStart_3461439 : Nat := 118140960795 + 3461439 * 2 ^ 59
def prefixEnd_3461439 : Nat := 4983230072969 + 3 ^ 40 * 3461439 * 2
def baseEnd_3461439 : Nat := 1184921308812258558462425

theorem tailTrace_3461439 : CollatzResearch.WordTrace tailWord_3461439 prefixEnd_3461439 1184921308812258558462425 := by
  unfold tailWord_3461439
  simp only [CollatzResearch.WordTrace]
  refine ⟨126249052106805144561123371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84166034737870096374082247 126249052106805144561123371)
  ·
    refine ⟨189373578160207716841685057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126249052106805144561123371 189373578160207716841685057)
    ·
      refine ⟨142030183620155787631263793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189373578160207716841685057 142030183620155787631263793)
      ·
        refine ⟨106522637715116840723447845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142030183620155787631263793 106522637715116840723447845)
        ·
          refine ⟨19972994571584407635646471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106522637715116840723447845 19972994571584407635646471)
          ·
            refine ⟨29959491857376611453469707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19972994571584407635646471 29959491857376611453469707)
            ·
              refine ⟨44939237786064917180204561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29959491857376611453469707 44939237786064917180204561)
              ·
                refine ⟨33704428339548687885153421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44939237786064917180204561 33704428339548687885153421)
                ·
                  refine ⟨12639160627330757956932533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33704428339548687885153421 12639160627330757956932533)
                  ·
                    refine ⟨1184921308812258558462425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12639160627330757956932533 1184921308812258558462425)
                    ·
                      rfl

theorem cell22_3461439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_3461439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461439 prefixEnd_3461439 := by exact prefixLift 3461439
  have htrace : WordTrace (prefixWord ++ tailWord_3461439) baseStart_3461439 baseEnd_3461439 := by
    simpa [prefixWord, tailWord_3461439, baseEnd_3461439] using wordTrace_append hprefix tailTrace_3461439
  have hstable : (prefixWord ++ tailWord_3461439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461439).length < 2 ^ (prefixWord ++ tailWord_3461439).sum := by decide
  have hdescent : baseEnd_3461439 < baseStart_3461439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461456 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 1, 5]
def baseStart_3461456 : Nat := 118140960795 + 3461456 * 2 ^ 59
def prefixEnd_3461456 : Nat := 4983230072969 + 3 ^ 40 * 3461456 * 2
def baseEnd_3461456 : Nat := 1184927128259676180787373

theorem tailTrace_3461456 : CollatzResearch.WordTrace tailWord_3461456 prefixEnd_3461456 1184927128259676180787373 := by
  unfold tailWord_3461456
  simp only [CollatzResearch.WordTrace]
  refine ⟨63124836073871778232246111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84166448098495704309661481 63124836073871778232246111)
  ·
    refine ⟨94687254110807667348369167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63124836073871778232246111 94687254110807667348369167)
    ·
      refine ⟨142030881166211501022553751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94687254110807667348369167 142030881166211501022553751)
      ·
        refine ⟨213046321749317251533830627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142030881166211501022553751 213046321749317251533830627)
        ·
          refine ⟨319569482623975877300745941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213046321749317251533830627 319569482623975877300745941)
          ·
            refine ⟨7489909748999434624236233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 319569482623975877300745941 7489909748999434624236233)
            ·
              refine ⟨5617432311749575968177175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7489909748999434624236233 5617432311749575968177175)
              ·
                refine ⟨8426148467624363952265763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5617432311749575968177175 8426148467624363952265763)
                ·
                  refine ⟨12639222701436545928398645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8426148467624363952265763 12639222701436545928398645)
                  ·
                    refine ⟨1184927128259676180787373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12639222701436545928398645 1184927128259676180787373)
                    ·
                      rfl

theorem cell22_3461456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_3461456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461456 prefixEnd_3461456 := by exact prefixLift 3461456
  have htrace : WordTrace (prefixWord ++ tailWord_3461456) baseStart_3461456 baseEnd_3461456 := by
    simpa [prefixWord, tailWord_3461456, baseEnd_3461456] using wordTrace_append hprefix tailTrace_3461456
  have hstable : (prefixWord ++ tailWord_3461456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461456).length < 2 ^ (prefixWord ++ tailWord_3461456).sum := by decide
  have hdescent : baseEnd_3461456 < baseStart_3461456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461471 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 2, 4]
def baseStart_3461471 : Nat := 118140960795 + 3461471 * 2 ^ 59
def prefixEnd_3461471 : Nat := 4983230072969 + 3 ^ 40 * 3461471 * 2
def baseEnd_3461471 : Nat := 1184932263066221141662327

theorem tailTrace_3461471 : CollatzResearch.WordTrace tailWord_3461471 prefixEnd_3461471 1184932263066221141662327 := by
  unfold tailWord_3461471
  simp only [CollatzResearch.WordTrace]
  refine ⟨126250219242689214026288267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84166812828459476017525511 126250219242689214026288267)
  ·
    refine ⟨189375328864033821039432401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126250219242689214026288267 189375328864033821039432401)
    ·
      refine ⟨142031496648025365779574301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189375328864033821039432401 142031496648025365779574301)
      ·
        refine ⟨53261811243009512167340363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142031496648025365779574301 53261811243009512167340363)
        ·
          refine ⟨79892716864514268251010545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53261811243009512167340363 79892716864514268251010545)
          ·
            refine ⟨59919537648385701188257909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79892716864514268251010545 59919537648385701188257909)
            ·
              refine ⟨5617456654536159486399179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59919537648385701188257909 5617456654536159486399179)
              ·
                refine ⟨8426184981804239229598769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5617456654536159486399179 8426184981804239229598769)
                ·
                  refine ⟨6319638736353179422199077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8426184981804239229598769 6319638736353179422199077)
                  ·
                    refine ⟨1184932263066221141662327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6319638736353179422199077 1184932263066221141662327)
                    ·
                      rfl

theorem cell22_3461471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_3461471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461471 prefixEnd_3461471 := by exact prefixLift 3461471
  have htrace : WordTrace (prefixWord ++ tailWord_3461471) baseStart_3461471 baseEnd_3461471 := by
    simpa [prefixWord, tailWord_3461471, baseEnd_3461471] using wordTrace_append hprefix tailTrace_3461471
  have hstable : (prefixWord ++ tailWord_3461471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461471).length < 2 ^ (prefixWord ++ tailWord_3461471).sum := by decide
  have hdescent : baseEnd_3461471 < baseStart_3461471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461490 : List Nat := [3, 2, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_3461490 : Nat := 118140960795 + 3461490 * 2 ^ 59
def prefixEnd_3461490 : Nat := 4983230072969 + 3 ^ 40 * 3461490 * 2
def baseEnd_3461490 : Nat := 1184938767154511425437269

theorem tailTrace_3461490 : CollatzResearch.WordTrace tailWord_3461490 prefixEnd_3461490 1184938767154511425437269 := by
  unfold tailWord_3461490
  simp only [CollatzResearch.WordTrace]
  refine ⟨31562728057405095067807481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84167274819746920180819949 31562728057405095067807481)
  ·
    refine ⟨23672046043053821300855611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31562728057405095067807481 23672046043053821300855611)
    ·
      refine ⟨35508069064580731951283417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23672046043053821300855611 35508069064580731951283417)
      ·
        refine ⟨26631051798435548963462563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35508069064580731951283417 26631051798435548963462563)
        ·
          refine ⟨39946577697653323445193845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26631051798435548963462563 39946577697653323445193845)
          ·
            refine ⟨3744991659154999072986923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39946577697653323445193845 3744991659154999072986923)
            ·
              refine ⟨5617487488732498609480385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744991659154999072986923 5617487488732498609480385)
              ·
                refine ⟨4213115616549373957110289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5617487488732498609480385 4213115616549373957110289)
                ·
                  refine ⟨3159836712412030467832717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4213115616549373957110289 3159836712412030467832717)
                  ·
                    refine ⟨1184938767154511425437269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3159836712412030467832717 1184938767154511425437269)
                    ·
                      rfl

theorem cell22_3461490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_3461490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461490 prefixEnd_3461490 := by exact prefixLift 3461490
  have htrace : WordTrace (prefixWord ++ tailWord_3461490) baseStart_3461490 baseEnd_3461490 := by
    simpa [prefixWord, tailWord_3461490, baseEnd_3461490] using wordTrace_append hprefix tailTrace_3461490
  have hstable : (prefixWord ++ tailWord_3461490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461490).length < 2 ^ (prefixWord ++ tailWord_3461490).sum := by decide
  have hdescent : baseEnd_3461490 < baseStart_3461490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461526 : List Nat := [5, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3461526 : Nat := 118140960795 + 3461526 * 2 ^ 59
def prefixEnd_3461526 : Nat := 4983230072969 + 3 ^ 40 * 3461526 * 2
def baseEnd_3461526 : Nat := 394983696896739777179053

theorem tailTrace_3461526 : CollatzResearch.WordTrace tailWord_3461526 prefixEnd_3461526 394983696896739777179053 := by
  unfold tailWord_3461526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7890764078593122401221277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84168150171659972279693621 7890764078593122401221277)
  ·
    refine ⟨2959036529472420900457979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7890764078593122401221277 2959036529472420900457979)
    ·
      refine ⟨4438554794208631350686969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959036529472420900457979 4438554794208631350686969)
      ·
        refine ⟨3328916095656473513015227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4438554794208631350686969 3328916095656473513015227)
        ·
          refine ⟨4993374143484710269522841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328916095656473513015227 4993374143484710269522841)
          ·
            refine ⟨3745030607613532702142131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4993374143484710269522841 3745030607613532702142131)
            ·
              refine ⟨5617545911420299053213197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745030607613532702142131 5617545911420299053213197)
              ·
                refine ⟨2106579716782612144954949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5617545911420299053213197 2106579716782612144954949)
                ·
                  refine ⟨394983696896739777179053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2106579716782612144954949 394983696896739777179053)
                  ·
                    rfl

theorem cell22_3461526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3461526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461526 prefixEnd_3461526 := by exact prefixLift 3461526
  have htrace : WordTrace (prefixWord ++ tailWord_3461526) baseStart_3461526 baseEnd_3461526 := by
    simpa [prefixWord, tailWord_3461526, baseEnd_3461526] using wordTrace_append hprefix tailTrace_3461526
  have hstable : (prefixWord ++ tailWord_3461526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461526).length < 2 ^ (prefixWord ++ tailWord_3461526).sum := by decide
  have hdescent : baseEnd_3461526 < baseStart_3461526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461565 : List Nat := [1, 4, 1, 2, 2, 4, 2, 1, 5]
def baseStart_3461565 : Nat := 118140960795 + 3461565 * 2 ^ 59
def prefixEnd_3461565 : Nat := 4983230072969 + 3 ^ 40 * 3461565 * 2
def baseEnd_3461565 : Nat := 394988147062412076604013

theorem tailTrace_3461565 : CollatzResearch.WordTrace tailWord_3461565 prefixEnd_3461565 394988147062412076604013 := by
  unfold tailWord_3461565
  simp only [CollatzResearch.WordTrace]
  refine ⟨126253647704348668080210149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84169098469565778720140099 126253647704348668080210149)
  ·
    refine ⟨23672558944565375265039403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126253647704348668080210149 23672558944565375265039403)
    ·
      refine ⟨35508838416848062897559105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23672558944565375265039403 35508838416848062897559105)
      ·
        refine ⟨26631628812636047173169329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35508838416848062897559105 26631628812636047173169329)
        ·
          refine ⟨19973721609477035379876997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26631628812636047173169329 19973721609477035379876997)
          ·
            refine ⟨3745072801776944133726937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19973721609477035379876997 3745072801776944133726937)
            ·
              refine ⟨2808804601332708100295203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3745072801776944133726937 2808804601332708100295203)
              ·
                refine ⟨4213206901999062150442805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2808804601332708100295203 4213206901999062150442805)
                ·
                  refine ⟨394988147062412076604013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4213206901999062150442805 394988147062412076604013)
                  ·
                    rfl

theorem cell22_3461565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_3461565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461565 prefixEnd_3461565 := by exact prefixLift 3461565
  have htrace : WordTrace (prefixWord ++ tailWord_3461565) baseStart_3461565 baseEnd_3461565 := by
    simpa [prefixWord, tailWord_3461565, baseEnd_3461565] using wordTrace_append hprefix tailTrace_3461565
  have hstable : (prefixWord ++ tailWord_3461565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461565).length < 2 ^ (prefixWord ++ tailWord_3461565).sum := by decide
  have hdescent : baseEnd_3461565 < baseStart_3461565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461593 : List Nat := [1, 2, 1, 2, 4, 1, 2, 5, 4]
def baseStart_3461593 : Nat := 118140960795 + 3461593 * 2 ^ 59
def prefixEnd_3461593 : Nat := 4983230072969 + 3 ^ 40 * 3461593 * 2
def baseEnd_3461593 : Nat := 394991342053151163370651

theorem tailTrace_3461593 : CollatzResearch.WordTrace tailWord_3461593 prefixEnd_3461593 394991342053151163370651 := by
  unfold tailWord_3461593
  simp only [CollatzResearch.WordTrace]
  refine ⟨126254668948247228862229433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84169779298831485908152955 126254668948247228862229433)
  ·
    refine ⟨94691001711185421646672075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126254668948247228862229433 94691001711185421646672075)
    ·
      refine ⟨142036502566778132470008113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94691001711185421646672075 142036502566778132470008113)
      ·
        refine ⟨106527376925083599352506085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142036502566778132470008113 106527376925083599352506085)
        ·
          refine ⟨19973883173453174878594891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106527376925083599352506085 19973883173453174878594891)
          ·
            refine ⟨29960824760179762317892337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19973883173453174878594891 29960824760179762317892337)
            ·
              refine ⟨22470618570134821738419253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29960824760179762317892337 22470618570134821738419253)
              ·
                refine ⟨2106620490950139537976805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22470618570134821738419253 2106620490950139537976805)
                ·
                  refine ⟨394991342053151163370651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2106620490950139537976805 394991342053151163370651)
                  ·
                    rfl

theorem cell22_3461593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 4].length) (baseStart_3461593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461593 prefixEnd_3461593 := by exact prefixLift 3461593
  have htrace : WordTrace (prefixWord ++ tailWord_3461593) baseStart_3461593 baseEnd_3461593 := by
    simpa [prefixWord, tailWord_3461593, baseEnd_3461593] using wordTrace_append hprefix tailTrace_3461593
  have hstable : (prefixWord ++ tailWord_3461593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461593).length < 2 ^ (prefixWord ++ tailWord_3461593).sum := by decide
  have hdescent : baseEnd_3461593 < baseStart_3461593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461610 : List Nat := [3, 1, 3, 1, 3, 2, 1, 4, 4]
def baseStart_3461610 : Nat := 118140960795 + 3461610 * 2 ^ 59
def prefixEnd_3461610 : Nat := 4983230072969 + 3 ^ 40 * 3461610 * 2
def baseEnd_3461610 : Nat := 394993281868957037478967

theorem tailTrace_3461610 : CollatzResearch.WordTrace tailWord_3461610 prefixEnd_3461610 394993281868957037478967 := by
  unfold tailWord_3461610
  simp only [CollatzResearch.WordTrace]
  refine ⟨31563822247296410191399571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84170192659457093843732189 31563822247296410191399571)
  ·
    refine ⟨47345733370944615287099357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31563822247296410191399571 47345733370944615287099357)
    ·
      refine ⟨17754650014104230732662259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47345733370944615287099357 17754650014104230732662259)
      ·
        refine ⟨26631975021156346098993389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17754650014104230732662259 26631975021156346098993389)
        ·
          refine ⟨9986990632933629787122521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26631975021156346098993389 9986990632933629787122521)
          ·
            refine ⟨7490242974700222340341891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9986990632933629787122521 7490242974700222340341891)
            ·
              refine ⟨11235364462050333510512837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7490242974700222340341891 11235364462050333510512837)
              ·
                refine ⟨2106630836634437533221157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11235364462050333510512837 2106630836634437533221157)
                ·
                  refine ⟨394993281868957037478967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2106630836634437533221157 394993281868957037478967)
                  ·
                    rfl

theorem cell22_3461610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_3461610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461610 prefixEnd_3461610 := by exact prefixLift 3461610
  have htrace : WordTrace (prefixWord ++ tailWord_3461610) baseStart_3461610 baseEnd_3461610 := by
    simpa [prefixWord, tailWord_3461610, baseEnd_3461610] using wordTrace_append hprefix tailTrace_3461610
  have hstable : (prefixWord ++ tailWord_3461610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461610).length < 2 ^ (prefixWord ++ tailWord_3461610).sum := by decide
  have hdescent : baseEnd_3461610 < baseStart_3461610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461653 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 5, 3]
def baseStart_3461653 : Nat := 118140960795 + 3461653 * 2 ^ 59
def prefixEnd_3461653 : Nat := 4983230072969 + 3 ^ 40 * 3461653 * 2
def baseEnd_3461653 : Nat := 1184994565385633333611769

theorem tailTrace_3461653 : CollatzResearch.WordTrace tailWord_3461653 prefixEnd_3461653 1184994565385633333611769 := by
  unfold tailWord_3461653
  simp only [CollatzResearch.WordTrace]
  refine ⟨126256857328029859109413613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84171238218686572739609075 126256857328029859109413613)
  ·
    refine ⟨47346321498011197166030105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126256857328029859109413613 47346321498011197166030105)
    ·
      refine ⟨35509741123508397874522579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47346321498011197166030105 35509741123508397874522579)
      ·
        refine ⟨53264611685262596811783869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35509741123508397874522579 53264611685262596811783869)
        ·
          refine ⟨19974229381973473804418951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53264611685262596811783869 19974229381973473804418951)
          ·
            refine ⟨29961344072960210706628427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19974229381973473804418951 29961344072960210706628427)
            ·
              refine ⟨44942016109440316059942641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29961344072960210706628427 44942016109440316059942641)
              ·
                refine ⟨33706512082080237044956981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44942016109440316059942641 33706512082080237044956981)
                ·
                  refine ⟨3159985507695022222964717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33706512082080237044956981 3159985507695022222964717)
                  ·
                    refine ⟨1184994565385633333611769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3159985507695022222964717 1184994565385633333611769)
                    ·
                      rfl

theorem cell22_3461653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_3461653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461653 prefixEnd_3461653 := by exact prefixLift 3461653
  have htrace : WordTrace (prefixWord ++ tailWord_3461653) baseStart_3461653 baseEnd_3461653 := by
    simpa [prefixWord, tailWord_3461653, baseEnd_3461653] using wordTrace_append hprefix tailTrace_3461653
  have hstable : (prefixWord ++ tailWord_3461653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461653).length < 2 ^ (prefixWord ++ tailWord_3461653).sum := by decide
  have hdescent : baseEnd_3461653 < baseStart_3461653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461711 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 8]
def baseStart_3461711 : Nat := 118140960795 + 3461711 * 2 ^ 59
def prefixEnd_3461711 : Nat := 4983230072969 + 3 ^ 40 * 3461711 * 2
def baseEnd_3461711 : Nat := 395004806656980171887197

theorem tailTrace_3461711 : CollatzResearch.WordTrace tailWord_3461711 prefixEnd_3461711 395004806656980171887197 := by
  unfold tailWord_3461711
  simp only [CollatzResearch.WordTrace]
  refine ⟨126258972761819735015024987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84172648507879823343349991 126258972761819735015024987)
  ·
    refine ⟨189388459142729602522537481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126258972761819735015024987 189388459142729602522537481)
    ·
      refine ⟨142041344357047201891903111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189388459142729602522537481 142041344357047201891903111)
      ·
        refine ⟨213062016535570802837854667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142041344357047201891903111 213062016535570802837854667)
        ·
          refine ⟨319593024803356204256782001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213062016535570802837854667 319593024803356204256782001)
          ·
            refine ⟨239694768602517153192586501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319593024803356204256782001 239694768602517153192586501)
            ·
              refine ⟨44942769112971966223609969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239694768602517153192586501 44942769112971966223609969)
              ·
                refine ⟨33707076834728974667707477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44942769112971966223609969 33707076834728974667707477)
                ·
                  refine ⟨395004806656980171887197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33707076834728974667707477 395004806656980171887197)
                  ·
                    rfl

theorem cell22_3461711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 8].length) (baseStart_3461711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461711 prefixEnd_3461711 := by exact prefixLift 3461711
  have htrace : WordTrace (prefixWord ++ tailWord_3461711) baseStart_3461711 baseEnd_3461711 := by
    simpa [prefixWord, tailWord_3461711, baseEnd_3461711] using wordTrace_append hprefix tailTrace_3461711
  have hstable : (prefixWord ++ tailWord_3461711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461711).length < 2 ^ (prefixWord ++ tailWord_3461711).sum := by decide
  have hdescent : baseEnd_3461711 < baseStart_3461711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461728 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 6]
def baseStart_3461728 : Nat := 118140960795 + 3461728 * 2 ^ 59
def prefixEnd_3461728 : Nat := 4983230072969 + 3 ^ 40 * 3461728 * 2
def baseEnd_3461728 : Nat := 395006746472786045995513

theorem tailTrace_3461728 : CollatzResearch.WordTrace tailWord_3461728 prefixEnd_3461728 395006746472786045995513 := by
  unfold tailWord_3461728
  simp only [CollatzResearch.WordTrace]
  refine ⟨63129796401379073459196919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84173061868505431278929225 63129796401379073459196919)
  ·
    refine ⟨94694694602068610188795379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63129796401379073459196919 94694694602068610188795379)
    ·
      refine ⟨142042041903102915283193069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94694694602068610188795379 142042041903102915283193069)
      ·
        refine ⟨53265765713663593231197401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142042041903102915283193069 53265765713663593231197401)
        ·
          refine ⟨39949324285247694923398051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53265765713663593231197401 39949324285247694923398051)
          ·
            refine ⟨59923986427871542385097077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39949324285247694923398051 59923986427871542385097077)
            ·
              refine ⟨5617873727612957098602851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59923986427871542385097077 5617873727612957098602851)
              ·
                refine ⟨8426810591419435647904277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5617873727612957098602851 8426810591419435647904277)
                ·
                  refine ⟨395006746472786045995513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8426810591419435647904277 395006746472786045995513)
                  ·
                    rfl

theorem cell22_3461728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_3461728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461728 prefixEnd_3461728 := by exact prefixLift 3461728
  have htrace : WordTrace (prefixWord ++ tailWord_3461728) baseStart_3461728 baseEnd_3461728 := by
    simpa [prefixWord, tailWord_3461728, baseEnd_3461728] using wordTrace_append hprefix tailTrace_3461728
  have hstable : (prefixWord ++ tailWord_3461728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461728).length < 2 ^ (prefixWord ++ tailWord_3461728).sum := by decide
  have hdescent : baseEnd_3461728 < baseStart_3461728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461809 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 2, 4]
def baseStart_3461809 : Nat := 118140960795 + 3461809 * 2 ^ 59
def prefixEnd_3461809 : Nat := 4983230072969 + 3 ^ 40 * 3461809 * 2
def baseEnd_3461809 : Nat := 1185047967373700926711291

theorem tailTrace_3461809 : CollatzResearch.WordTrace tailWord_3461809 prefixEnd_3461809 1185047967373700926711291 := by
  unfold tailWord_3461809
  simp only [CollatzResearch.WordTrace]
  refine ⟨126262547115464697752092481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84175031410309798501394987 126262547115464697752092481)
  ·
    refine ⟨94696910336598523314069361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126262547115464697752092481 94696910336598523314069361)
    ·
      refine ⟨71022682752448892485552021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94696910336598523314069361 71022682752448892485552021)
      ·
        refine ⟨3329188254021041835260251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71022682752448892485552021 3329188254021041835260251)
        ·
          refine ⟨4993782381031562752890377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3329188254021041835260251 4993782381031562752890377)
          ·
            refine ⟨3745336785773672064667783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4993782381031562752890377 3745336785773672064667783)
            ·
              refine ⟨5618005178660508097001675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745336785773672064667783 5618005178660508097001675)
              ·
                refine ⟨8427007767990762145502513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5618005178660508097001675 8427007767990762145502513)
                ·
                  refine ⟨6320255825993071609126885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8427007767990762145502513 6320255825993071609126885)
                  ·
                    refine ⟨1185047967373700926711291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6320255825993071609126885 1185047967373700926711291)
                    ·
                      rfl

theorem cell22_3461809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_3461809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461809 prefixEnd_3461809 := by exact prefixLift 3461809
  have htrace : WordTrace (prefixWord ++ tailWord_3461809) baseStart_3461809 baseEnd_3461809 := by
    simpa [prefixWord, tailWord_3461809, baseEnd_3461809] using wordTrace_append hprefix tailTrace_3461809
  have hstable : (prefixWord ++ tailWord_3461809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461809).length < 2 ^ (prefixWord ++ tailWord_3461809).sum := by decide
  have hdescent : baseEnd_3461809 < baseStart_3461809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461818 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 7]
def baseStart_3461818 : Nat := 118140960795 + 3461818 * 2 ^ 59
def prefixEnd_3461818 : Nat := 4983230072969 + 3 ^ 40 * 3461818 * 2
def baseEnd_3461818 : Nat := 395017016085875967745421

theorem tailTrace_3461818 : CollatzResearch.WordTrace tailWord_3461818 prefixEnd_3461818 395017016085875967745421 := by
  unfold tailWord_3461818
  simp only [CollatzResearch.WordTrace]
  refine ⟨31565718843108023072292527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84175250248288061526113405 31565718843108023072292527)
  ·
    refine ⟨47348578264662034608438791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31565718843108023072292527 47348578264662034608438791)
    ·
      refine ⟨71022867396993051912658187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47348578264662034608438791 71022867396993051912658187)
      ·
        refine ⟨106534301095489577868987281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71022867396993051912658187 106534301095489577868987281)
        ·
          refine ⟨79900725821617183401740461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106534301095489577868987281 79900725821617183401740461)
          ·
            refine ⟨29962772183106443775652673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79900725821617183401740461 29962772183106443775652673)
            ·
              refine ⟨22472079137329832831739505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29962772183106443775652673 22472079137329832831739505)
              ·
                refine ⟨16854059352997374623804629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22472079137329832831739505 16854059352997374623804629)
                ·
                  refine ⟨395017016085875967745421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16854059352997374623804629 395017016085875967745421)
                  ·
                    rfl

theorem cell22_3461818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_3461818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461818 prefixEnd_3461818 := by exact prefixLift 3461818
  have htrace : WordTrace (prefixWord ++ tailWord_3461818) baseStart_3461818 baseEnd_3461818 := by
    simpa [prefixWord, tailWord_3461818, baseEnd_3461818] using wordTrace_append hprefix tailTrace_3461818
  have hstable : (prefixWord ++ tailWord_3461818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461818).length < 2 ^ (prefixWord ++ tailWord_3461818).sum := by decide
  have hdescent : baseEnd_3461818 < baseStart_3461818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461865 : List Nat := [1, 2, 1, 1, 1, 2, 5, 4, 1, 4]
def baseStart_3461865 : Nat := 118140960795 + 3461865 * 2 ^ 59
def prefixEnd_3461865 : Nat := 4983230072969 + 3 ^ 40 * 3461865 * 2
def baseEnd_3461865 : Nat := 1185067137318135447311119

theorem tailTrace_3461865 : CollatzResearch.WordTrace tailWord_3461865 prefixEnd_3461865 1185067137318135447311119 := by
  unfold tailWord_3461865
  simp only [CollatzResearch.WordTrace]
  refine ⟨126264589603261819316131049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84176393068841212877420699 126264589603261819316131049)
  ·
    refine ⟨94698442202446364487098287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126264589603261819316131049 94698442202446364487098287)
    ·
      refine ⟨142047663303669546730647431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94698442202446364487098287 142047663303669546730647431)
      ·
        refine ⟨213071494955504320095971147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142047663303669546730647431 213071494955504320095971147)
        ·
          refine ⟨319607242433256480143956721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213071494955504320095971147 319607242433256480143956721)
          ·
            refine ⟨239705431824942360107967541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319607242433256480143956721 239705431824942360107967541)
            ·
              refine ⟨22472384233588346260121957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239705431824942360107967541 22472384233588346260121957)
              ·
                refine ⟨4213572043797814923772867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22472384233588346260121957 4213572043797814923772867)
                ·
                  refine ⟨6320358065696722385659301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4213572043797814923772867 6320358065696722385659301)
                  ·
                    refine ⟨1185067137318135447311119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6320358065696722385659301 1185067137318135447311119)
                    ·
                      rfl

theorem cell22_3461865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_3461865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461865 prefixEnd_3461865 := by exact prefixLift 3461865
  have htrace : WordTrace (prefixWord ++ tailWord_3461865) baseStart_3461865 baseEnd_3461865 := by
    simpa [prefixWord, tailWord_3461865, baseEnd_3461865] using wordTrace_append hprefix tailTrace_3461865
  have hstable : (prefixWord ++ tailWord_3461865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461865).length < 2 ^ (prefixWord ++ tailWord_3461865).sum := by decide
  have hdescent : baseEnd_3461865 < baseStart_3461865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461933 : List Nat := [1, 5, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3461933 : Nat := 118140960795 + 3461933 * 2 ^ 59
def prefixEnd_3461933 : Nat := 4983230072969 + 3 ^ 40 * 3461933 * 2
def baseEnd_3461933 : Nat := 1185090415107805936610911

theorem tailTrace_3461933 : CollatzResearch.WordTrace tailWord_3461933 prefixEnd_3461933 1185090415107805936610911 := by
  unfold tailWord_3461933
  simp only [CollatzResearch.WordTrace]
  refine ⟨126267069767015466929606453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84178046511343644619737635 126267069767015466929606453)
  ·
    refine ⟨11837537790657700024650605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126267069767015466929606453 11837537790657700024650605)
    ·
      refine ⟨4439076671496637509243977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11837537790657700024650605 4439076671496637509243977)
      ·
        refine ⟨3329307503622478131932983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4439076671496637509243977 3329307503622478131932983)
        ·
          refine ⟨4993961255433717197899475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3329307503622478131932983 4993961255433717197899475)
          ·
            refine ⟨7490941883150575796849213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993961255433717197899475 7490941883150575796849213)
            ·
              refine ⟨2809103206181465923818455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7490941883150575796849213 2809103206181465923818455)
              ·
                refine ⟨4213654809272198885727683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809103206181465923818455 4213654809272198885727683)
                ·
                  refine ⟨6320482213908298328591525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4213654809272198885727683 6320482213908298328591525)
                  ·
                    refine ⟨1185090415107805936610911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6320482213908298328591525 1185090415107805936610911)
                    ·
                      rfl

theorem cell22_3461933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3461933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461933 prefixEnd_3461933 := by exact prefixLift 3461933
  have htrace : WordTrace (prefixWord ++ tailWord_3461933) baseStart_3461933 baseEnd_3461933 := by
    simpa [prefixWord, tailWord_3461933, baseEnd_3461933] using wordTrace_append hprefix tailTrace_3461933
  have hstable : (prefixWord ++ tailWord_3461933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461933).length < 2 ^ (prefixWord ++ tailWord_3461933).sum := by decide
  have hdescent : baseEnd_3461933 < baseStart_3461933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461942 : List Nat := [5, 1, 2, 2, 2, 10]
def baseStart_3461942 : Nat := 118140960795 + 3461942 * 2 ^ 59
def prefixEnd_3461942 : Nat := 4983230072969 + 3 ^ 40 * 3461942 * 2
def baseEnd_3461942 : Nat := 14630783901132505100443

theorem tailTrace_3461942 : CollatzResearch.WordTrace tailWord_3461942 prefixEnd_3461942 14630783901132505100443 := by
  unfold tailWord_3461942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7891712376498928841667755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84178265349321907644456053 7891712376498928841667755)
  ·
    refine ⟨11837568564748393262501633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7891712376498928841667755 11837568564748393262501633)
    ·
      refine ⟨8878176423561294946876225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11837568564748393262501633 8878176423561294946876225)
      ·
        refine ⟨6658632317670971210157169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8878176423561294946876225 6658632317670971210157169)
        ·
          refine ⟨4993974238253228407617877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6658632317670971210157169 4993974238253228407617877)
          ·
            refine ⟨14630783901132505100443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4993974238253228407617877 14630783901132505100443)
            ·
              rfl

theorem cell22_3461942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 10].length) (baseStart_3461942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461942 prefixEnd_3461942 := by exact prefixLift 3461942
  have htrace : WordTrace (prefixWord ++ tailWord_3461942) baseStart_3461942 baseEnd_3461942 := by
    simpa [prefixWord, tailWord_3461942, baseEnd_3461942] using wordTrace_append hprefix tailTrace_3461942
  have hstable : (prefixWord ++ tailWord_3461942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461942).length < 2 ^ (prefixWord ++ tailWord_3461942).sum := by decide
  have hdescent : baseEnd_3461942 < baseStart_3461942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461991 : List Nat := [1, 1, 5, 1, 2, 3, 2, 3, 1, 3]
def baseStart_3461991 : Nat := 118140960795 + 3461991 * 2 ^ 59
def prefixEnd_3461991 : Nat := 4983230072969 + 3 ^ 40 * 3461991 * 2
def baseEnd_3461991 : Nat := 1185110269693113118660733

theorem tailTrace_3461991 : CollatzResearch.WordTrace tailWord_3461991 prefixEnd_3461991 1185110269693113118660733 := by
  unfold tailWord_3461991
  simp only [CollatzResearch.WordTrace]
  refine ⟨126269185200805342835217827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84179456800536895223478551 126269185200805342835217827)
  ·
    refine ⟨189403777801208014252826741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126269185200805342835217827 189403777801208014252826741)
    ·
      refine ⟨17756604168863251336202507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189403777801208014252826741 17756604168863251336202507)
      ·
        refine ⟨26634906253294877004303761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17756604168863251336202507 26634906253294877004303761)
        ·
          refine ⟨19976179689971157753227821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26634906253294877004303761 19976179689971157753227821)
          ·
            refine ⟨7491067383739184157460433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19976179689971157753227821 7491067383739184157460433)
            ·
              refine ⟨5618300537804388118095325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7491067383739184157460433 5618300537804388118095325)
              ·
                refine ⟨2106862701676645544285747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5618300537804388118095325 2106862701676645544285747)
                ·
                  refine ⟨3160294052514968316428621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106862701676645544285747 3160294052514968316428621)
                  ·
                    refine ⟨1185110269693113118660733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3160294052514968316428621 1185110269693113118660733)
                    ·
                      rfl

theorem cell22_3461991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_3461991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3461991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3461991 prefixEnd_3461991 := by exact prefixLift 3461991
  have htrace : WordTrace (prefixWord ++ tailWord_3461991) baseStart_3461991 baseEnd_3461991 := by
    simpa [prefixWord, tailWord_3461991, baseEnd_3461991] using wordTrace_append hprefix tailTrace_3461991
  have hstable : (prefixWord ++ tailWord_3461991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461991).length < 2 ^ (prefixWord ++ tailWord_3461991).sum := by decide
  have hdescent : baseEnd_3461991 < baseStart_3461991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462015 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 6]
def baseStart_3462015 : Nat := 118140960795 + 3462015 * 2 ^ 59
def prefixEnd_3462015 : Nat := 4983230072969 + 3 ^ 40 * 3462015 * 2
def baseEnd_3462015 : Nat := 395039495127861685353553

theorem tailTrace_3462015 : CollatzResearch.WordTrace tailWord_3462015 prefixEnd_3462015 395039495127861685353553 := by
  unfold tailWord_3462015
  simp only [CollatzResearch.WordTrace]
  refine ⟨126270060552718394934091499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84180040368478929956060999 126270060552718394934091499)
  ·
    refine ⟨189405090829077592401137249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126270060552718394934091499 189405090829077592401137249)
    ·
      refine ⟨142053818121808194300852937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189405090829077592401137249 142053818121808194300852937)
      ·
        refine ⟨106540363591356145725639703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142053818121808194300852937 106540363591356145725639703)
        ·
          refine ⟨159810545387034218588459555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106540363591356145725639703 159810545387034218588459555)
          ·
            refine ⟨239715818080551327882689333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159810545387034218588459555 239715818080551327882689333)
            ·
              refine ⟨22473357945051686989002125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239715818080551327882689333 22473357945051686989002125)
              ·
                refine ⟨8427509229394382620875797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22473357945051686989002125 8427509229394382620875797)
                ·
                  refine ⟨395039495127861685353553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8427509229394382620875797 395039495127861685353553)
                  ·
                    rfl

theorem cell22_3462015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 6].length) (baseStart_3462015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462015 prefixEnd_3462015 := by exact prefixLift 3462015
  have htrace : WordTrace (prefixWord ++ tailWord_3462015) baseStart_3462015 baseEnd_3462015 := by
    simpa [prefixWord, tailWord_3462015, baseEnd_3462015] using wordTrace_append hprefix tailTrace_3462015
  have hstable : (prefixWord ++ tailWord_3462015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462015).length < 2 ^ (prefixWord ++ tailWord_3462015).sum := by decide
  have hdescent : baseEnd_3462015 < baseStart_3462015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462137 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 2, 5]
def baseStart_3462137 : Nat := 118140960795 + 3462137 * 2 ^ 59
def prefixEnd_3462137 : Nat := 4983230072969 + 3 ^ 40 * 3462137 * 2
def baseEnd_3462137 : Nat := 1185160248476817404510285

theorem tailTrace_3462137 : CollatzResearch.WordTrace tailWord_3462137 prefixEnd_3462137 1185160248476817404510285 := by
  unfold tailWord_3462137
  simp only [CollatzResearch.WordTrace]
  refine ⟨126274510258276409770032665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84183006838850939846688443 126274510258276409770032665)
  ·
    refine ⟨94705882693707307327524499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126274510258276409770032665 94705882693707307327524499)
    ·
      refine ⟨142058824040560960991286749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94705882693707307327524499 142058824040560960991286749)
      ·
        refine ⟨53272059015210360371732531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142058824040560960991286749 53272059015210360371732531)
        ·
          refine ⟨79908088522815540557598797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53272059015210360371732531 79908088522815540557598797)
          ·
            refine ⟨29965533196055827709099549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79908088522815540557598797 29965533196055827709099549)
            ·
              refine ⟨11237074948520935390912331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29965533196055827709099549 11237074948520935390912331)
              ·
                refine ⟨16855612422781403086368497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11237074948520935390912331 16855612422781403086368497)
                ·
                  refine ⟨12641709317086052314776373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16855612422781403086368497 12641709317086052314776373)
                  ·
                    refine ⟨1185160248476817404510285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12641709317086052314776373 1185160248476817404510285)
                    ·
                      rfl

theorem cell22_3462137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_3462137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462137 prefixEnd_3462137 := by exact prefixLift 3462137
  have htrace : WordTrace (prefixWord ++ tailWord_3462137) baseStart_3462137 baseEnd_3462137 := by
    simpa [prefixWord, tailWord_3462137, baseEnd_3462137] using wordTrace_append hprefix tailTrace_3462137
  have hstable : (prefixWord ++ tailWord_3462137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462137).length < 2 ^ (prefixWord ++ tailWord_3462137).sum := by decide
  have hdescent : baseEnd_3462137 < baseStart_3462137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462173 : List Nat := [1, 4, 2, 2, 4, 1, 1, 2, 5]
def baseStart_3462173 : Nat := 118140960795 + 3462173 * 2 ^ 59
def prefixEnd_3462173 : Nat := 4983230072969 + 3 ^ 40 * 3462173 * 2
def baseEnd_3462173 : Nat := 395057524004175103536725

theorem tailTrace_3462173 : CollatzResearch.WordTrace tailWord_3462173 prefixEnd_3462173 395057524004175103536725 := by
  unfold tailWord_3462173
  simp only [CollatzResearch.WordTrace]
  refine ⟨126275823286145987918343173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84183882190763991945562115 126275823286145987918343173)
  ·
    refine ⟨23676716866152372734689345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126275823286145987918343173 23676716866152372734689345)
    ·
      refine ⟨17757537649614279551017009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23676716866152372734689345 17757537649614279551017009)
      ·
        refine ⟨13318153237210709663262757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17757537649614279551017009 13318153237210709663262757)
        ·
          refine ⟨2497153731977008061861767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13318153237210709663262757 2497153731977008061861767)
          ·
            refine ⟨3745730597965512092792651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497153731977008061861767 3745730597965512092792651)
            ·
              refine ⟨5618595896948268139188977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745730597965512092792651 5618595896948268139188977)
              ·
                refine ⟨4213946922711201104391733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5618595896948268139188977 4213946922711201104391733)
                ·
                  refine ⟨395057524004175103536725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4213946922711201104391733 395057524004175103536725)
                  ·
                    rfl

theorem cell22_3462173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_3462173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462173 prefixEnd_3462173 := by exact prefixLift 3462173
  have htrace : WordTrace (prefixWord ++ tailWord_3462173) baseStart_3462173 baseEnd_3462173 := by
    simpa [prefixWord, tailWord_3462173, baseEnd_3462173] using wordTrace_append hprefix tailTrace_3462173
  have hstable : (prefixWord ++ tailWord_3462173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462173).length < 2 ^ (prefixWord ++ tailWord_3462173).sum := by decide
  have hdescent : baseEnd_3462173 < baseStart_3462173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462250 : List Nat := [3, 1, 3, 2, 2, 3, 2, 1, 2, 3]
def baseStart_3462250 : Nat := 118140960795 + 3462250 * 2 ^ 59
def prefixEnd_3462250 : Nat := 4983230072969 + 3 ^ 40 * 3462250 * 2
def baseEnd_3462250 : Nat := 1185198930686122776434939

theorem tailTrace_3462250 : CollatzResearch.WordTrace tailWord_3462250 prefixEnd_3462250 1185198930686122776434939 := by
  unfold tailWord_3462250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31569657926716757517224051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84185754471244686712597469 31569657926716757517224051)
  ·
    refine ⟨47354486890075136275836077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31569657926716757517224051 47354486890075136275836077)
    ·
      refine ⟨17757932583778176103438529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47354486890075136275836077 17757932583778176103438529)
      ·
        refine ⟨13318449437833632077578897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17757932583778176103438529 13318449437833632077578897)
        ·
          refine ⟨9988837078375224058184173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13318449437833632077578897 9988837078375224058184173)
          ·
            refine ⟨3745813904390709021819065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9988837078375224058184173 3745813904390709021819065)
            ·
              refine ⟨2809360428293031766364299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3745813904390709021819065 2809360428293031766364299)
              ·
                refine ⟨4214040642439547649546449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809360428293031766364299 4214040642439547649546449)
                ·
                  refine ⟨3160530481829660737159837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4214040642439547649546449 3160530481829660737159837)
                  ·
                    refine ⟨1185198930686122776434939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3160530481829660737159837 1185198930686122776434939)
                    ·
                      rfl

theorem cell22_3462250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_3462250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462250 prefixEnd_3462250 := by exact prefixLift 3462250
  have htrace : WordTrace (prefixWord ++ tailWord_3462250) baseStart_3462250 baseEnd_3462250 := by
    simpa [prefixWord, tailWord_3462250, baseEnd_3462250] using wordTrace_append hprefix tailTrace_3462250
  have hstable : (prefixWord ++ tailWord_3462250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462250).length < 2 ^ (prefixWord ++ tailWord_3462250).sum := by decide
  have hdescent : baseEnd_3462250 < baseStart_3462250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462257 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 9]
def baseStart_3462257 : Nat := 118140960795 + 3462257 * 2 ^ 59
def prefixEnd_3462257 : Nat := 4983230072969 + 3 ^ 40 * 3462257 * 2
def baseEnd_3462257 : Nat := 395067108976392363836639

theorem tailTrace_3462257 : CollatzResearch.WordTrace tailWord_3462257 prefixEnd_3462257 395067108976392363836639 := by
  unfold tailWord_3462257
  simp only [CollatzResearch.WordTrace]
  refine ⟨126278887017841670264401025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84185924678561113509600683 126278887017841670264401025)
  ·
    refine ⟨94709165263381252698300769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126278887017841670264401025 94709165263381252698300769)
    ·
      refine ⟨71031873947535939523725577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94709165263381252698300769 71031873947535939523725577)
      ·
        refine ⟨53273905460651954642794183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71031873947535939523725577 53273905460651954642794183)
        ·
          refine ⟨79910858190977931964191275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53273905460651954642794183 79910858190977931964191275)
          ·
            refine ⟨119866287286466897946286913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79910858190977931964191275 119866287286466897946286913)
            ·
              refine ⟨89899715464850173459715185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119866287286466897946286913 89899715464850173459715185)
              ·
                refine ⟨67424786598637630094786389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89899715464850173459715185 67424786598637630094786389)
                ·
                  refine ⟨395067108976392363836639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67424786598637630094786389 395067108976392363836639)
                  ·
                    rfl

theorem cell22_3462257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_3462257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462257 prefixEnd_3462257 := by exact prefixLift 3462257
  have htrace : WordTrace (prefixWord ++ tailWord_3462257) baseStart_3462257 baseEnd_3462257 := by
    simpa [prefixWord, tailWord_3462257, baseEnd_3462257] using wordTrace_append hprefix tailTrace_3462257
  have hstable : (prefixWord ++ tailWord_3462257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462257).length < 2 ^ (prefixWord ++ tailWord_3462257).sum := by decide
  have hdescent : baseEnd_3462257 < baseStart_3462257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462287 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 4, 8]
def baseStart_3462287 : Nat := 118140960795 + 3462287 * 2 ^ 59
def prefixEnd_3462287 : Nat := 4983230072969 + 3 ^ 40 * 3462287 * 2
def baseEnd_3462287 : Nat := 1185211596542267013259825

theorem tailTrace_3462287 : CollatzResearch.WordTrace tailWord_3462287 prefixEnd_3462287 1185211596542267013259825 := by
  unfold tailWord_3462287
  simp only [CollatzResearch.WordTrace]
  refine ⟨126279981207732985387993115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84186654138488656925328743 126279981207732985387993115)
  ·
    refine ⟨189419971811599478081989673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126279981207732985387993115 189419971811599478081989673)
    ·
      refine ⟨142064978858699608561492255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189419971811599478081989673 142064978858699608561492255)
      ·
        refine ⟨213097468288049412842238383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142064978858699608561492255 213097468288049412842238383)
        ·
          refine ⟨319646202432074119263357575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213097468288049412842238383 319646202432074119263357575)
          ·
            refine ⟨479469303648111178895036363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319646202432074119263357575 479469303648111178895036363)
            ·
              refine ⟨719203955472166768342554545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479469303648111178895036363 719203955472166768342554545)
              ·
                refine ⟨539402966604125076256915909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719203955472166768342554545 539402966604125076256915909)
                ·
                  refine ⟨101138056238273451798171733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 539402966604125076256915909 101138056238273451798171733)
                  ·
                    refine ⟨1185211596542267013259825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101138056238273451798171733 1185211596542267013259825)
                    ·
                      rfl

theorem cell22_3462287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_3462287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462287 prefixEnd_3462287 := by exact prefixLift 3462287
  have htrace : WordTrace (prefixWord ++ tailWord_3462287) baseStart_3462287 baseEnd_3462287 := by
    simpa [prefixWord, tailWord_3462287, baseEnd_3462287] using wordTrace_append hprefix tailTrace_3462287
  have hstable : (prefixWord ++ tailWord_3462287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462287).length < 2 ^ (prefixWord ++ tailWord_3462287).sum := by decide
  have hdescent : baseEnd_3462287 < baseStart_3462287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462295 : List Nat := [1, 1, 3, 3, 3, 1, 4, 2, 1, 3]
def baseStart_3462295 : Nat := 118140960795 + 3462295 * 2 ^ 59
def prefixEnd_3462295 : Nat := 4983230072969 + 3 ^ 40 * 3462295 * 2
def baseEnd_3462295 : Nat := 1185214335105757659059801

theorem tailTrace_3462295 : CollatzResearch.WordTrace tailWord_3462295 prefixEnd_3462295 1185214335105757659059801 := by
  unfold tailWord_3462295
  simp only [CollatzResearch.WordTrace]
  refine ⟨126280272991704002754284339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84186848661136001836189559 126280272991704002754284339)
  ·
    refine ⟨189420409487556004131426509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126280272991704002754284339 189420409487556004131426509)
    ·
      refine ⟨71032653557833501549284941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189420409487556004131426509 71032653557833501549284941)
      ·
        refine ⟨26637245084187563080981853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71032653557833501549284941 26637245084187563080981853)
        ·
          refine ⟨9988966906570336155368195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26637245084187563080981853 9988966906570336155368195)
          ·
            refine ⟨14983450359855504233052293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9988966906570336155368195 14983450359855504233052293)
            ·
              refine ⟨2809396942472907043697305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14983450359855504233052293 2809396942472907043697305)
              ·
                refine ⟨2107047706854680282772979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2809396942472907043697305 2107047706854680282772979)
                ·
                  refine ⟨3160571560282020424159469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107047706854680282772979 3160571560282020424159469)
                  ·
                    refine ⟨1185214335105757659059801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3160571560282020424159469 1185214335105757659059801)
                    ·
                      rfl

theorem cell22_3462295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_3462295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462295 prefixEnd_3462295 := by exact prefixLift 3462295
  have htrace : WordTrace (prefixWord ++ tailWord_3462295) baseStart_3462295 baseEnd_3462295 := by
    simpa [prefixWord, tailWord_3462295, baseEnd_3462295] using wordTrace_append hprefix tailTrace_3462295
  have hstable : (prefixWord ++ tailWord_3462295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462295).length < 2 ^ (prefixWord ++ tailWord_3462295).sum := by decide
  have hdescent : baseEnd_3462295 < baseStart_3462295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462304 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 5, 4]
def baseStart_3462304 : Nat := 118140960795 + 3462304 * 2 ^ 59
def prefixEnd_3462304 : Nat := 4983230072969 + 3 ^ 40 * 3462304 * 2
def baseEnd_3462304 : Nat := 1185217415989684635584773

theorem tailTrace_3462304 : CollatzResearch.WordTrace tailWord_3462304 prefixEnd_3462304 1185217415989684635584773 := by
  unfold tailWord_3462304
  simp only [CollatzResearch.WordTrace]
  refine ⟨63140300624335698645680983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84187067499114264860907977 63140300624335698645680983)
  ·
    refine ⟨94710450936503547968521475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63140300624335698645680983 94710450936503547968521475)
    ·
      refine ⟨142065676404755321952782213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94710450936503547968521475 142065676404755321952782213)
      ·
        refine ⟨26637314325891622866146665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142065676404755321952782213 26637314325891622866146665)
        ·
          refine ⟨19977985744418717149609999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26637314325891622866146665 19977985744418717149609999)
          ·
            refine ⟨29966978616628075724414999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19977985744418717149609999 29966978616628075724414999)
            ·
              refine ⟨44950467924942113586622499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29966978616628075724414999 44950467924942113586622499)
              ·
                refine ⟨67425701887413170379933749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44950467924942113586622499 67425701887413170379933749)
                ·
                  refine ⟨6321159551944984723118789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67425701887413170379933749 6321159551944984723118789)
                  ·
                    refine ⟨1185217415989684635584773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6321159551944984723118789 1185217415989684635584773)
                    ·
                      rfl

theorem cell22_3462304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_3462304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462304 prefixEnd_3462304 := by exact prefixLift 3462304
  have htrace : WordTrace (prefixWord ++ tailWord_3462304) baseStart_3462304 baseEnd_3462304 := by
    simpa [prefixWord, tailWord_3462304, baseEnd_3462304] using wordTrace_append hprefix tailTrace_3462304
  have hstable : (prefixWord ++ tailWord_3462304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462304).length < 2 ^ (prefixWord ++ tailWord_3462304).sum := by decide
  have hdescent : baseEnd_3462304 < baseStart_3462304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462321 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 3, 4]
def baseStart_3462321 : Nat := 118140960795 + 3462321 * 2 ^ 59
def prefixEnd_3462321 : Nat := 4983230072969 + 3 ^ 40 * 3462321 * 2
def baseEnd_3462321 : Nat := 1185223235437102257909721

theorem tailTrace_3462321 : CollatzResearch.WordTrace tailWord_3462321 prefixEnd_3462321 1185223235437102257909721 := by
  unfold tailWord_3462321
  simp only [CollatzResearch.WordTrace]
  refine ⟨126281221289609809194730817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84187480859739872796487211 126281221289609809194730817)
  ·
    refine ⟨94710915967207356896048113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126281221289609809194730817 94710915967207356896048113)
    ·
      refine ⟨71033186975405517672036085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94710915967207356896048113 71033186975405517672036085)
      ·
        refine ⟨6659361278944267281753383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71033186975405517672036085 6659361278944267281753383)
        ·
          refine ⟨9989041918416400922630075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6659361278944267281753383 9989041918416400922630075)
          ·
            refine ⟨14983562877624601383945113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9989041918416400922630075 14983562877624601383945113)
            ·
              refine ⟨11237672158218451037958835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14983562877624601383945113 11237672158218451037958835)
              ·
                refine ⟨16856508237327676556938253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11237672158218451037958835 16856508237327676556938253)
                ·
                  refine ⟨6321190588997878708851845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16856508237327676556938253 6321190588997878708851845)
                  ·
                    refine ⟨1185223235437102257909721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6321190588997878708851845 1185223235437102257909721)
                    ·
                      rfl

theorem cell22_3462321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_3462321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462321 prefixEnd_3462321 := by exact prefixLift 3462321
  have htrace : WordTrace (prefixWord ++ tailWord_3462321) baseStart_3462321 baseEnd_3462321 := by
    simpa [prefixWord, tailWord_3462321, baseEnd_3462321] using wordTrace_append hprefix tailTrace_3462321
  have hstable : (prefixWord ++ tailWord_3462321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462321).length < 2 ^ (prefixWord ++ tailWord_3462321).sum := by decide
  have hdescent : baseEnd_3462321 < baseStart_3462321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462351 : List Nat := [1, 1, 2, 1, 1, 3, 2, 6, 2, 3]
def baseStart_3462351 : Nat := 118140960795 + 3462351 * 2 ^ 59
def prefixEnd_3462351 : Nat := 4983230072969 + 3 ^ 40 * 3462351 * 2
def baseEnd_3462351 : Nat := 1185233505050192179659629

theorem tailTrace_3462351 : CollatzResearch.WordTrace tailWord_3462351 prefixEnd_3462351 1185233505050192179659629 := by
  unfold tailWord_3462351
  simp only [CollatzResearch.WordTrace]
  refine ⟨126282315479501124318322907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84188210319667416212215271 126282315479501124318322907)
  ·
    refine ⟨189423473219251686477484361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126282315479501124318322907 189423473219251686477484361)
    ·
      refine ⟨142067604914438764858113271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189423473219251686477484361 142067604914438764858113271)
      ·
        refine ⟨213101407371658147287169907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142067604914438764858113271 213101407371658147287169907)
        ·
          refine ⟨319652111057487220930754861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213101407371658147287169907 319652111057487220930754861)
          ·
            refine ⟨119869541646557707849033073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319652111057487220930754861 119869541646557707849033073)
            ·
              refine ⟨89902156234918280886774805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119869541646557707849033073 89902156234918280886774805)
              ·
                refine ⟨4214163573511794416567569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89902156234918280886774805 4214163573511794416567569)
                ·
                  refine ⟨3160622680133845812425677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4214163573511794416567569 3160622680133845812425677)
                  ·
                    refine ⟨1185233505050192179659629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3160622680133845812425677 1185233505050192179659629)
                    ·
                      rfl

theorem cell22_3462351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 3].length) (baseStart_3462351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462351 prefixEnd_3462351 := by exact prefixLift 3462351
  have htrace : WordTrace (prefixWord ++ tailWord_3462351) baseStart_3462351 baseEnd_3462351 := by
    simpa [prefixWord, tailWord_3462351, baseEnd_3462351] using wordTrace_append hprefix tailTrace_3462351
  have hstable : (prefixWord ++ tailWord_3462351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462351).length < 2 ^ (prefixWord ++ tailWord_3462351).sum := by decide
  have hdescent : baseEnd_3462351 < baseStart_3462351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462381 : List Nat := [1, 5, 1, 2, 2, 2, 1, 8]
def baseStart_3462381 : Nat := 118140960795 + 3462381 * 2 ^ 59
def prefixEnd_3462381 : Nat := 4983230072969 + 3 ^ 40 * 3462381 * 2
def baseEnd_3462381 : Nat := 131693752740364677934393

theorem tailTrace_3462381 : CollatzResearch.WordTrace tailWord_3462381 prefixEnd_3462381 131693752740364677934393 := by
  unfold tailWord_3462381
  simp only [CollatzResearch.WordTrace]
  refine ⟨126283409669392439441914997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84188939779594959627943331 126283409669392439441914997)
  ·
    refine ⟨11839069656505541197679531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126283409669392439441914997 11839069656505541197679531)
    ·
      refine ⟨17758604484758311796519297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11839069656505541197679531 17758604484758311796519297)
      ·
        refine ⟨13318953363568733847389473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17758604484758311796519297 13318953363568733847389473)
        ·
          refine ⟨9989215022676550385542105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13318953363568733847389473 9989215022676550385542105)
          ·
            refine ⟨7491911267007412789156579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9989215022676550385542105 7491911267007412789156579)
            ·
              refine ⟨11237866900511119183734869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7491911267007412789156579 11237866900511119183734869)
              ·
                refine ⟨131693752740364677934393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11237866900511119183734869 131693752740364677934393)
                ·
                  rfl

theorem cell22_3462381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 8].length) (baseStart_3462381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462381 prefixEnd_3462381 := by exact prefixLift 3462381
  have htrace : WordTrace (prefixWord ++ tailWord_3462381) baseStart_3462381 baseEnd_3462381 := by
    simpa [prefixWord, tailWord_3462381, baseEnd_3462381] using wordTrace_append hprefix tailTrace_3462381
  have hstable : (prefixWord ++ tailWord_3462381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462381).length < 2 ^ (prefixWord ++ tailWord_3462381).sum := by decide
  have hdescent : baseEnd_3462381 < baseStart_3462381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462409 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 7]
def baseStart_3462409 : Nat := 118140960795 + 3462409 * 2 ^ 59
def prefixEnd_3462409 : Nat := 4983230072969 + 3 ^ 40 * 3462409 * 2
def baseEnd_3462409 : Nat := 395084453211833120569817

theorem tailTrace_3462409 : CollatzResearch.WordTrace tailWord_3462409 prefixEnd_3462409 395084453211833120569817 := by
  unfold tailWord_3462409
  simp only [CollatzResearch.WordTrace]
  refine ⟨126284430913291000223934281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84189620608860666815956187 126284430913291000223934281)
  ·
    refine ⟨94713323184968250167950711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126284430913291000223934281 94713323184968250167950711)
    ·
      refine ⟨142069984777452375251926067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94713323184968250167950711 142069984777452375251926067)
      ·
        refine ⟨213104977166178562877889101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142069984777452375251926067 213104977166178562877889101)
        ·
          refine ⟨79914366437316961079208413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213104977166178562877889101 79914366437316961079208413)
          ·
            refine ⟨29967887413993860404703155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79914366437316961079208413 29967887413993860404703155)
            ·
              refine ⟨44951831120990790607054733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29967887413993860404703155 44951831120990790607054733)
              ·
                refine ⟨16856936670371546477645525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44951831120990790607054733 16856936670371546477645525)
                ·
                  refine ⟨395084453211833120569817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16856936670371546477645525 395084453211833120569817)
                  ·
                    rfl

theorem cell22_3462409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_3462409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462409 prefixEnd_3462409 := by exact prefixLift 3462409
  have htrace : WordTrace (prefixWord ++ tailWord_3462409) baseStart_3462409 baseEnd_3462409 := by
    simpa [prefixWord, tailWord_3462409, baseEnd_3462409] using wordTrace_append hprefix tailTrace_3462409
  have hstable : (prefixWord ++ tailWord_3462409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462409).length < 2 ^ (prefixWord ++ tailWord_3462409).sum := by decide
  have hdescent : baseEnd_3462409 < baseStart_3462409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462501 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_3462501 : Nat := 118140960795 + 3462501 * 2 ^ 59
def prefixEnd_3462501 : Nat := 4983230072969 + 3 ^ 40 * 3462501 * 2
def baseEnd_3462501 : Nat := 1185284853115641788409169

theorem tailTrace_3462501 : CollatzResearch.WordTrace tailWord_3462501 prefixEnd_3462501 1185284853115641788409169 := by
  unfold tailWord_3462501
  simp only [CollatzResearch.WordTrace]
  refine ⟨126287786428957699936283357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84191857619305133290855571 126287786428957699936283357)
  ·
    refine ⟨47357919910859137476106259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126287786428957699936283357 47357919910859137476106259)
    ·
      refine ⟨71036879866288706214159389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47357919910859137476106259 71036879866288706214159389)
      ·
        refine ⟨26638829949858264830309771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71036879866288706214159389 26638829949858264830309771)
        ·
          refine ⟨39958244924787397245464657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26638829949858264830309771 39958244924787397245464657)
          ·
            refine ⟨29968683693590547934098493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39958244924787397245464657 29968683693590547934098493)
            ·
              refine ⟨11238256385096455475286935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29968683693590547934098493 11238256385096455475286935)
              ·
                refine ⟨16857384577644683212930403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11238256385096455475286935 16857384577644683212930403)
                ·
                  refine ⟨25286076866467024819395605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16857384577644683212930403 25286076866467024819395605)
                  ·
                    refine ⟨1185284853115641788409169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25286076866467024819395605 1185284853115641788409169)
                    ·
                      rfl

theorem cell22_3462501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_3462501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462501 prefixEnd_3462501 := by exact prefixLift 3462501
  have htrace : WordTrace (prefixWord ++ tailWord_3462501) baseStart_3462501 baseEnd_3462501 := by
    simpa [prefixWord, tailWord_3462501, baseEnd_3462501] using wordTrace_append hprefix tailTrace_3462501
  have hstable : (prefixWord ++ tailWord_3462501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462501).length < 2 ^ (prefixWord ++ tailWord_3462501).sum := by decide
  have hdescent : baseEnd_3462501 < baseStart_3462501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462537 : List Nat := [1, 2, 1, 1, 7, 1, 3, 1, 2, 3]
def baseStart_3462537 : Nat := 118140960795 + 3462537 * 2 ^ 59
def prefixEnd_3462537 : Nat := 4983230072969 + 3 ^ 40 * 3462537 * 2
def baseEnd_3462537 : Nat := 1185297176651349694509059

theorem tailTrace_3462537 : CollatzResearch.WordTrace tailWord_3462537 prefixEnd_3462537 1185297176651349694509059 := by
  unfold tailWord_3462537
  simp only [CollatzResearch.WordTrace]
  refine ⟨126289099456827278084593865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84192732971218185389729243 126289099456827278084593865)
  ·
    refine ⟨94716824592620458563445399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126289099456827278084593865 94716824592620458563445399)
    ·
      refine ⟨142075236888930687845168099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94716824592620458563445399 142075236888930687845168099)
      ·
        refine ⟨213112855333396031767752149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142075236888930687845168099 213112855333396031767752149)
        ·
          refine ⟨4994832546876469494556691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 213112855333396031767752149 4994832546876469494556691)
          ·
            refine ⟨7492248820314704241835037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4994832546876469494556691 7492248820314704241835037)
            ·
              refine ⟨2809593307618014090688139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7492248820314704241835037 2809593307618014090688139)
              ·
                refine ⟨4214389961427021136032209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809593307618014090688139 4214389961427021136032209)
                ·
                  refine ⟨3160792471070265852024157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4214389961427021136032209 3160792471070265852024157)
                  ·
                    refine ⟨1185297176651349694509059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3160792471070265852024157 1185297176651349694509059)
                    ·
                      rfl

theorem cell22_3462537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 2, 3].length) (baseStart_3462537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462537 prefixEnd_3462537 := by exact prefixLift 3462537
  have htrace : WordTrace (prefixWord ++ tailWord_3462537) baseStart_3462537 baseEnd_3462537 := by
    simpa [prefixWord, tailWord_3462537, baseEnd_3462537] using wordTrace_append hprefix tailTrace_3462537
  have hstable : (prefixWord ++ tailWord_3462537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462537).length < 2 ^ (prefixWord ++ tailWord_3462537).sum := by decide
  have hdescent : baseEnd_3462537 < baseStart_3462537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462565 : List Nat := [1, 3, 1, 2, 1, 1, 2, 7, 1, 3]
def baseStart_3462565 : Nat := 118140960795 + 3462565 * 2 ^ 59
def prefixEnd_3462565 : Nat := 4983230072969 + 3 ^ 40 * 3462565 * 2
def baseEnd_3462565 : Nat := 1185306761623566954808973

theorem tailTrace_3462565 : CollatzResearch.WordTrace tailWord_3462565 prefixEnd_3462565 1185306761623566954808973 := by
  unfold tailWord_3462565
  simp only [CollatzResearch.WordTrace]
  refine ⟨126290120700725838866613149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84193413800483892577742099 126290120700725838866613149)
  ·
    refine ⟨47358795262772189574979931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126290120700725838866613149 47358795262772189574979931)
    ·
      refine ⟨71038192894158284362469897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47358795262772189574979931 71038192894158284362469897)
      ·
        refine ⟨53278644670618713271852423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71038192894158284362469897 53278644670618713271852423)
        ·
          refine ⟨79917967005928069907778635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53278644670618713271852423 79917967005928069907778635)
          ·
            refine ⟨119876950508892104861667953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79917967005928069907778635 119876950508892104861667953)
            ·
              refine ⟨89907712881669078646250965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119876950508892104861667953 89907712881669078646250965)
              ·
                refine ⟨2107212020664119030771507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89907712881669078646250965 2107212020664119030771507)
                ·
                  refine ⟨3160818030996178546157261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107212020664119030771507 3160818030996178546157261)
                  ·
                    refine ⟨1185306761623566954808973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3160818030996178546157261 1185306761623566954808973)
                    ·
                      rfl

theorem cell22_3462565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_3462565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462565 prefixEnd_3462565 := by exact prefixLift 3462565
  have htrace : WordTrace (prefixWord ++ tailWord_3462565) baseStart_3462565 baseEnd_3462565 := by
    simpa [prefixWord, tailWord_3462565, baseEnd_3462565] using wordTrace_append hprefix tailTrace_3462565
  have hstable : (prefixWord ++ tailWord_3462565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462565).length < 2 ^ (prefixWord ++ tailWord_3462565).sum := by decide
  have hdescent : baseEnd_3462565 < baseStart_3462565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462576 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 2, 5]
def baseStart_3462576 : Nat := 118140960795 + 3462576 * 2 ^ 59
def prefixEnd_3462576 : Nat := 4983230072969 + 3 ^ 40 * 3462576 * 2
def baseEnd_3462576 : Nat := 1185310527148366592783939

theorem tailTrace_3462576 : CollatzResearch.WordTrace tailWord_3462576 prefixEnd_3462576 1185310527148366592783939 := by
  unfold tailWord_3462576
  simp only [CollatzResearch.WordTrace]
  refine ⟨63145260951842993872631791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84193681269123991830175721 63145260951842993872631791)
  ·
    refine ⟨94717891427764490808947687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63145260951842993872631791 94717891427764490808947687)
    ·
      refine ⟨142076837141646736213421531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94717891427764490808947687 142076837141646736213421531)
      ·
        refine ⟨213115255712470104320132297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142076837141646736213421531 213115255712470104320132297)
        ·
          refine ⟨159836441784352578240099223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213115255712470104320132297 159836441784352578240099223)
          ·
            refine ⟨239754662676528867360148835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159836441784352578240099223 239754662676528867360148835)
            ·
              refine ⟨359631994014793301040223253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239754662676528867360148835 359631994014793301040223253)
              ·
                refine ⟨16857749719443435986260465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 359631994014793301040223253 16857749719443435986260465)
                ·
                  refine ⟨12643312289582576989695349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16857749719443435986260465 12643312289582576989695349)
                  ·
                    refine ⟨1185310527148366592783939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12643312289582576989695349 1185310527148366592783939)
                    ·
                      rfl

theorem cell22_3462576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_3462576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462576 prefixEnd_3462576 := by exact prefixLift 3462576
  have htrace : WordTrace (prefixWord ++ tailWord_3462576) baseStart_3462576 baseEnd_3462576 := by
    simpa [prefixWord, tailWord_3462576, baseEnd_3462576] using wordTrace_append hprefix tailTrace_3462576
  have hstable : (prefixWord ++ tailWord_3462576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462576).length < 2 ^ (prefixWord ++ tailWord_3462576).sum := by decide
  have hdescent : baseEnd_3462576 < baseStart_3462576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462638 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3462638 : Nat := 118140960795 + 3462638 * 2 ^ 59
def prefixEnd_3462638 : Nat := 4983230072969 + 3 ^ 40 * 3462638 * 2
def baseEnd_3462638 : Nat := 1185331751015419097733749

theorem tailTrace_3462638 : CollatzResearch.WordTrace tailWord_3462638 prefixEnd_3462638 1185331751015419097733749 := by
  unfold tailWord_3462638
  simp only [CollatzResearch.WordTrace]
  refine ⟨15786597903682671541752571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84195188819640914889347045 15786597903682671541752571)
  ·
    refine ⟨23679896855524007312628857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15786597903682671541752571 23679896855524007312628857)
    ·
      refine ⟨17759922641643005484471643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23679896855524007312628857 17759922641643005484471643)
      ·
        refine ⟨26639883962464508226707465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17759922641643005484471643 26639883962464508226707465)
        ·
          refine ⟨19979912971848381170030599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26639883962464508226707465 19979912971848381170030599)
          ·
            refine ⟨29969869457772571755045899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19979912971848381170030599 29969869457772571755045899)
            ·
              refine ⟨44954804186658857632568849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29969869457772571755045899 44954804186658857632568849)
              ·
                refine ⟨33716103139994143224426637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44954804186658857632568849 33716103139994143224426637)
                ·
                  refine ⟨12643538677497803709159989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33716103139994143224426637 12643538677497803709159989)
                  ·
                    refine ⟨1185331751015419097733749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12643538677497803709159989 1185331751015419097733749)
                    ·
                      rfl

theorem cell22_3462638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3462638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462638 prefixEnd_3462638 := by exact prefixLift 3462638
  have htrace : WordTrace (prefixWord ++ tailWord_3462638) baseStart_3462638 baseEnd_3462638 := by
    simpa [prefixWord, tailWord_3462638, baseEnd_3462638] using wordTrace_append hprefix tailTrace_3462638
  have hstable : (prefixWord ++ tailWord_3462638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462638).length < 2 ^ (prefixWord ++ tailWord_3462638).sum := by decide
  have hdescent : baseEnd_3462638 < baseStart_3462638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462640 : List Nat := [2, 1, 1, 1, 3, 5, 1, 4, 4]
def baseStart_3462640 : Nat := 118140960795 + 3462640 * 2 ^ 59
def prefixEnd_3462640 : Nat := 4983230072969 + 3 ^ 40 * 3462640 * 2
def baseEnd_3462640 : Nat := 395110811885430586394581

theorem tailTrace_3462640 : CollatzResearch.WordTrace tailWord_3462640 prefixEnd_3462640 395110811885430586394581 := by
  unfold tailWord_3462640
  simp only [CollatzResearch.WordTrace]
  refine ⟨63146428087727063337796687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84195237450302751117062249 63146428087727063337796687)
  ·
    refine ⟨94719642131590595006695031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63146428087727063337796687 94719642131590595006695031)
    ·
      refine ⟨142079463197385892510042547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94719642131590595006695031 142079463197385892510042547)
      ·
        refine ⟨213119194796078838765063821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142079463197385892510042547 213119194796078838765063821)
        ·
          refine ⟨79919698048529564536898933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213119194796078838765063821 79919698048529564536898933)
          ·
            refine ⟨7492471692049646675334275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79919698048529564536898933 7492471692049646675334275)
            ·
              refine ⟨11238707538074470013001413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7492471692049646675334275 11238707538074470013001413)
              ·
                refine ⟨2107257663388963127437765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11238707538074470013001413 2107257663388963127437765)
                ·
                  refine ⟨395110811885430586394581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2107257663388963127437765 395110811885430586394581)
                  ·
                    rfl

theorem cell22_3462640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 4].length) (baseStart_3462640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462640 prefixEnd_3462640 := by exact prefixLift 3462640
  have htrace : WordTrace (prefixWord ++ tailWord_3462640) baseStart_3462640 baseEnd_3462640 := by
    simpa [prefixWord, tailWord_3462640, baseEnd_3462640] using wordTrace_append hprefix tailTrace_3462640
  have hstable : (prefixWord ++ tailWord_3462640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462640).length < 2 ^ (prefixWord ++ tailWord_3462640).sum := by decide
  have hdescent : baseEnd_3462640 < baseStart_3462640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462670 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_3462670 : Nat := 118140960795 + 3462670 * 2 ^ 59
def prefixEnd_3462670 : Nat := 4983230072969 + 3 ^ 40 * 3462670 * 2
def baseEnd_3462670 : Nat := 1185342705269381680933651

theorem tailTrace_3462670 : CollatzResearch.WordTrace tailWord_3462670 prefixEnd_3462670 1185342705269381680933651 := by
  unfold tailWord_3462670
  simp only [CollatzResearch.WordTrace]
  refine ⟨15786743795668180224898183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84195966910230294532790309 15786743795668180224898183)
  ·
    refine ⟨23680115693502270337347275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15786743795668180224898183 23680115693502270337347275)
    ·
      refine ⟨35520173540253405506020913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23680115693502270337347275 35520173540253405506020913)
      ·
        refine ⟨26640130155190054129515685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35520173540253405506020913 26640130155190054129515685)
        ·
          refine ⟨4995024404098135149284191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26640130155190054129515685 4995024404098135149284191)
          ·
            refine ⟨7492536606147202723926287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4995024404098135149284191 7492536606147202723926287)
            ·
              refine ⟨11238804909220804085889431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7492536606147202723926287 11238804909220804085889431)
              ·
                refine ⟨16858207363831206128834147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11238804909220804085889431 16858207363831206128834147)
                ·
                  refine ⟨25287311045746809193251221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16858207363831206128834147 25287311045746809193251221)
                  ·
                    refine ⟨1185342705269381680933651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25287311045746809193251221 1185342705269381680933651)
                    ·
                      rfl

theorem cell22_3462670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_3462670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462670 prefixEnd_3462670 := by exact prefixLift 3462670
  have htrace : WordTrace (prefixWord ++ tailWord_3462670) baseStart_3462670 baseEnd_3462670 := by
    simpa [prefixWord, tailWord_3462670, baseEnd_3462670] using wordTrace_append hprefix tailTrace_3462670
  have hstable : (prefixWord ++ tailWord_3462670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462670).length < 2 ^ (prefixWord ++ tailWord_3462670).sum := by decide
  have hdescent : baseEnd_3462670 < baseStart_3462670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462676 : List Nat := [2, 4, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3462676 : Nat := 118140960795 + 3462676 * 2 ^ 59
def prefixEnd_3462676 : Nat := 4983230072969 + 3 ^ 40 * 3462676 * 2
def baseEnd_3462676 : Nat := 1185344759191999665283633

theorem tailTrace_3462676 : CollatzResearch.WordTrace tailWord_3462676 prefixEnd_3462676 1185344759191999665283633 := by
  unfold tailWord_3462676
  simp only [CollatzResearch.WordTrace]
  refine ⟨63147084601661852411951941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84196112802215803215935921 63147084601661852411951941)
  ·
    refine ⟨11840078362811597327240989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63147084601661852411951941 11840078362811597327240989)
    ·
      refine ⟨4440029386054348997715371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11840078362811597327240989 4440029386054348997715371)
      ·
        refine ⟨6660044079081523496573057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440029386054348997715371 6660044079081523496573057)
        ·
          refine ⟨4995033059311142622429793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6660044079081523496573057 4995033059311142622429793)
          ·
            refine ⟨3746274794483356966822345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4995033059311142622429793 3746274794483356966822345)
            ·
              refine ⟨2809706095862517725116759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3746274794483356966822345 2809706095862517725116759)
              ·
                refine ⟨4214559143793776587675139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809706095862517725116759 4214559143793776587675139)
                ·
                  refine ⟨6321838715690664881512709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4214559143793776587675139 6321838715690664881512709)
                  ·
                    refine ⟨1185344759191999665283633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6321838715690664881512709 1185344759191999665283633)
                    ·
                      rfl

theorem cell22_3462676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3462676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462676 prefixEnd_3462676 := by exact prefixLift 3462676
  have htrace : WordTrace (prefixWord ++ tailWord_3462676) baseStart_3462676 baseEnd_3462676 := by
    simpa [prefixWord, tailWord_3462676, baseEnd_3462676] using wordTrace_append hprefix tailTrace_3462676
  have hstable : (prefixWord ++ tailWord_3462676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462676).length < 2 ^ (prefixWord ++ tailWord_3462676).sum := by decide
  have hdescent : baseEnd_3462676 < baseStart_3462676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462794 : List Nat := [3, 1, 2, 3, 2, 2, 3, 1, 1, 4]
def baseStart_3462794 : Nat := 118140960795 + 3462794 * 2 ^ 59
def prefixEnd_3462794 : Nat := 4983230072969 + 3 ^ 40 * 3462794 * 2
def baseEnd_3462794 : Nat := 1185385153003486690833271

theorem tailTrace_3462794 : CollatzResearch.WordTrace tailWord_3462794 prefixEnd_3462794 1185385153003486690833271 := by
  unfold tailWord_3462794
  simp only [CollatzResearch.WordTrace]
  refine ⟨31574618254224052744174859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84198982011264140651132957 31574618254224052744174859)
  ·
    refine ⟨47361927381336079116262289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31574618254224052744174859 47361927381336079116262289)
    ·
      refine ⟨35521445536002059337196717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47361927381336079116262289 35521445536002059337196717)
      ·
        refine ⟨13320542076000772251448769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35521445536002059337196717 13320542076000772251448769)
        ·
          refine ⟨9990406557000579188586577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13320542076000772251448769 9990406557000579188586577)
          ·
            refine ⟨7492804917750434391439933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9990406557000579188586577 7492804917750434391439933)
            ·
              refine ⟨2809801844156412896789975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7492804917750434391439933 2809801844156412896789975)
              ·
                refine ⟨4214702766234619345184963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809801844156412896789975 4214702766234619345184963)
                ·
                  refine ⟨6322054149351929017777445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4214702766234619345184963 6322054149351929017777445)
                  ·
                    refine ⟨1185385153003486690833271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6322054149351929017777445 1185385153003486690833271)
                    ·
                      rfl

theorem cell22_3462794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_3462794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462794 prefixEnd_3462794 := by exact prefixLift 3462794
  have htrace : WordTrace (prefixWord ++ tailWord_3462794) baseStart_3462794 baseEnd_3462794 := by
    simpa [prefixWord, tailWord_3462794, baseEnd_3462794] using wordTrace_append hprefix tailTrace_3462794
  have hstable : (prefixWord ++ tailWord_3462794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462794).length < 2 ^ (prefixWord ++ tailWord_3462794).sum := by decide
  have hdescent : baseEnd_3462794 < baseStart_3462794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462807 : List Nat := [1, 1, 3, 3, 2, 2, 1, 4, 2, 3]
def baseStart_3462807 : Nat := 118140960795 + 3462807 * 2 ^ 59
def prefixEnd_3462807 : Nat := 4983230072969 + 3 ^ 40 * 3462807 * 2
def baseEnd_3462807 : Nat := 1185389603169158990258231

theorem tailTrace_3462807 : CollatzResearch.WordTrace tailWord_3462807 prefixEnd_3462807 1185389603169158990258231 := by
  unfold tailWord_3462807
  simp only [CollatzResearch.WordTrace]
  refine ⟨126298947165849114196922675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84199298110566076131281783 126298947165849114196922675)
  ·
    refine ⟨189448420748773671295384013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126298947165849114196922675 189448420748773671295384013)
    ·
      refine ⟨71043157780790126735769005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189448420748773671295384013 71043157780790126735769005)
      ·
        refine ⟨26641184167796297525913377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71043157780790126735769005 26641184167796297525913377)
        ·
          refine ⟨19980888125847223144435033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26641184167796297525913377 19980888125847223144435033)
          ·
            refine ⟨14985666094385417358326275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19980888125847223144435033 14985666094385417358326275)
            ·
              refine ⟨22478499141578126037489413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14985666094385417358326275 22478499141578126037489413)
              ·
                refine ⟨4214718589045898632029265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22478499141578126037489413 4214718589045898632029265)
                ·
                  refine ⟨3161038941784423974021949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4214718589045898632029265 3161038941784423974021949)
                  ·
                    refine ⟨1185389603169158990258231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161038941784423974021949 1185389603169158990258231)
                    ·
                      rfl

theorem cell22_3462807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_3462807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462807 prefixEnd_3462807 := by exact prefixLift 3462807
  have htrace : WordTrace (prefixWord ++ tailWord_3462807) baseStart_3462807 baseEnd_3462807 := by
    simpa [prefixWord, tailWord_3462807, baseEnd_3462807] using wordTrace_append hprefix tailTrace_3462807
  have hstable : (prefixWord ++ tailWord_3462807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462807).length < 2 ^ (prefixWord ++ tailWord_3462807).sum := by decide
  have hdescent : baseEnd_3462807 < baseStart_3462807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462820 : List Nat := [2, 3, 1, 2, 2, 2, 3, 7]
def baseStart_3462820 : Nat := 118140960795 + 3462820 * 2 ^ 59
def prefixEnd_3462820 : Nat := 4983230072969 + 3 ^ 40 * 3462820 * 2
def baseEnd_3462820 : Nat := 131710450370536809964799

theorem tailTrace_3462820 : CollatzResearch.WordTrace tailWord_3462820 prefixEnd_3462820 131710450370536809964799 := by
  unfold tailWord_3462820
  simp only [CollatzResearch.WordTrace]
  refine ⟨63149710657401008708572957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84199614209868011611430609 63149710657401008708572957)
  ·
    refine ⟨23681141496525378265714859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63149710657401008708572957 23681141496525378265714859)
    ·
      refine ⟨35521712244788067398572289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23681141496525378265714859 35521712244788067398572289)
      ·
        refine ⟨26641284183591050548929217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35521712244788067398572289 26641284183591050548929217)
        ·
          refine ⟨19980963137693287911696913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26641284183591050548929217 19980963137693287911696913)
          ·
            refine ⟨14985722353269965933772685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19980963137693287911696913 14985722353269965933772685)
            ·
              refine ⟨5619645882476237225164757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14985722353269965933772685 5619645882476237225164757)
              ·
                refine ⟨131710450370536809964799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5619645882476237225164757 131710450370536809964799)
                ·
                  rfl

theorem cell22_3462820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 7].length) (baseStart_3462820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462820 prefixEnd_3462820 := by exact prefixLift 3462820
  have htrace : WordTrace (prefixWord ++ tailWord_3462820) baseStart_3462820 baseEnd_3462820 := by
    simpa [prefixWord, tailWord_3462820, baseEnd_3462820] using wordTrace_append hprefix tailTrace_3462820
  have hstable : (prefixWord ++ tailWord_3462820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462820).length < 2 ^ (prefixWord ++ tailWord_3462820).sum := by decide
  have hdescent : baseEnd_3462820 < baseStart_3462820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462852 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_3462852 : Nat := 118140960795 + 3462852 * 2 ^ 59
def prefixEnd_3462852 : Nat := 4983230072969 + 3 ^ 40 * 3462852 * 2
def baseEnd_3462852 : Nat := 1185405007588793872883093

theorem tailTrace_3462852 : CollatzResearch.WordTrace tailWord_3462852 prefixEnd_3462852 1185405007588793872883093 := by
  unfold tailWord_3462852
  simp only [CollatzResearch.WordTrace]
  refine ⟨63150294225343043441155405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84200392300457391254873873 63150294225343043441155405)
  ·
    refine ⟨23681360334503641290433277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63150294225343043441155405 23681360334503641290433277)
    ·
      refine ⟨8880510125438865483912479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23681360334503641290433277 8880510125438865483912479)
      ·
        refine ⟨13320765188158298225868719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8880510125438865483912479 13320765188158298225868719)
        ·
          refine ⟨19981147782237447338803079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13320765188158298225868719 19981147782237447338803079)
          ·
            refine ⟨29971721673356171008204619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19981147782237447338803079 29971721673356171008204619)
            ·
              refine ⟨44957582510034256512306929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29971721673356171008204619 44957582510034256512306929)
              ·
                refine ⟨33718186882525692384230197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44957582510034256512306929 33718186882525692384230197)
                ·
                  refine ⟨3161080020236783661021581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33718186882525692384230197 3161080020236783661021581)
                  ·
                    refine ⟨1185405007588793872883093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161080020236783661021581 1185405007588793872883093)
                    ·
                      rfl

theorem cell22_3462852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_3462852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462852 prefixEnd_3462852 := by exact prefixLift 3462852
  have htrace : WordTrace (prefixWord ++ tailWord_3462852) baseStart_3462852 baseEnd_3462852 := by
    simpa [prefixWord, tailWord_3462852, baseEnd_3462852] using wordTrace_append hprefix tailTrace_3462852
  have hstable : (prefixWord ++ tailWord_3462852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462852).length < 2 ^ (prefixWord ++ tailWord_3462852).sum := by decide
  have hdescent : baseEnd_3462852 < baseStart_3462852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462854 : List Nat := [6, 1, 2, 1, 1, 2, 9]
def baseStart_3462854 : Nat := 118140960795 + 3462854 * 2 ^ 59
def prefixEnd_3462854 : Nat := 4983230072969 + 3 ^ 40 * 3462854 * 2
def baseEnd_3462854 : Nat := 43903914527024686456781

theorem tailTrace_3462854 : CollatzResearch.WordTrace tailWord_3462854 prefixEnd_3462854 43903914527024686456781 := by
  unfold tailWord_3462854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3946895668646213788246363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84200440931119227482589077 3946895668646213788246363)
  ·
    refine ⟨5920343502969320682369545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3946895668646213788246363 5920343502969320682369545)
    ·
      refine ⟨4440257627226990511777159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5920343502969320682369545 4440257627226990511777159)
      ·
        refine ⟨6660386440840485767665739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440257627226990511777159 6660386440840485767665739)
        ·
          refine ⟨9990579661260728651498609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6660386440840485767665739 9990579661260728651498609)
          ·
            refine ⟨7492934745945546488623957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9990579661260728651498609 7492934745945546488623957)
            ·
              refine ⟨43903914527024686456781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7492934745945546488623957 43903914527024686456781)
              ·
                rfl

theorem cell22_3462854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 9].length) (baseStart_3462854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462854 prefixEnd_3462854 := by exact prefixLift 3462854
  have htrace : WordTrace (prefixWord ++ tailWord_3462854) baseStart_3462854 baseEnd_3462854 := by
    simpa [prefixWord, tailWord_3462854, baseEnd_3462854] using wordTrace_append hprefix tailTrace_3462854
  have hstable : (prefixWord ++ tailWord_3462854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462854).length < 2 ^ (prefixWord ++ tailWord_3462854).sum := by decide
  have hdescent : baseEnd_3462854 < baseStart_3462854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462865 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 7]
def baseStart_3462865 : Nat := 118140960795 + 3462865 * 2 ^ 59
def prefixEnd_3462865 : Nat := 4983230072969 + 3 ^ 40 * 3462865 * 2
def baseEnd_3462865 : Nat := 395136485918155390769351

theorem tailTrace_3462865 : CollatzResearch.WordTrace tailWord_3462865 prefixEnd_3462865 395136485918155390769351 := by
  unfold tailWord_3462865
  simp only [CollatzResearch.WordTrace]
  refine ⟨126301062599638990102534049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84200708399759326735022699 126301062599638990102534049)
  ·
    refine ⟨94725796949729242576900537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126301062599638990102534049 94725796949729242576900537)
    ·
      refine ⟨71044347712296931932675403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94725796949729242576900537 71044347712296931932675403)
      ·
        refine ⟨106566521568445397899013105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71044347712296931932675403 106566521568445397899013105)
        ·
          refine ⟨79924891176334048424259829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106566521568445397899013105 79924891176334048424259829)
          ·
            refine ⟨7492958547781317039774359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79924891176334048424259829 7492958547781317039774359)
            ·
              refine ⟨11239437821671975559661539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7492958547781317039774359 11239437821671975559661539)
              ·
                refine ⟨16859156732507963339492309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11239437821671975559661539 16859156732507963339492309)
                ·
                  refine ⟨395136485918155390769351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16859156732507963339492309 395136485918155390769351)
                  ·
                    rfl

theorem cell22_3462865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_3462865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462865 prefixEnd_3462865 := by exact prefixLift 3462865
  have htrace : WordTrace (prefixWord ++ tailWord_3462865) baseStart_3462865 baseEnd_3462865 := by
    simpa [prefixWord, tailWord_3462865, baseEnd_3462865] using wordTrace_append hprefix tailTrace_3462865
  have hstable : (prefixWord ++ tailWord_3462865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462865).length < 2 ^ (prefixWord ++ tailWord_3462865).sum := by decide
  have hdescent : baseEnd_3462865 < baseStart_3462865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462880 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 2, 5]
def baseStart_3462880 : Nat := 118140960795 + 3462880 * 2 ^ 59
def prefixEnd_3462880 : Nat := 4983230072969 + 3 ^ 40 * 3462880 * 2
def baseEnd_3462880 : Nat := 1185414592561011133183007

theorem tailTrace_3462880 : CollatzResearch.WordTrace tailWord_3462880 prefixEnd_3462880 1185414592561011133183007 := by
  unfold tailWord_3462880
  simp only [CollatzResearch.WordTrace]
  refine ⟨63150804847292323832165047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84201073129723098442886729 63150804847292323832165047)
  ·
    refine ⟨94726207270938485748247571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63150804847292323832165047 94726207270938485748247571)
    ·
      refine ⟨142089310906407728622371357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94726207270938485748247571 142089310906407728622371357)
      ·
        refine ⟨53283491589902898233389259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142089310906407728622371357 53283491589902898233389259)
        ·
          refine ⟨79925237384854347350083889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53283491589902898233389259 79925237384854347350083889)
          ·
            refine ⟨59943928038640760512562917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79925237384854347350083889 59943928038640760512562917)
            ·
              refine ⟨11239486507245142596105547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59943928038640760512562917 11239486507245142596105547)
              ·
                refine ⟨16859229760867713894158321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11239486507245142596105547 16859229760867713894158321)
                ·
                  refine ⟨12644422320650785420618741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16859229760867713894158321 12644422320650785420618741)
                  ·
                    refine ⟨1185414592561011133183007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12644422320650785420618741 1185414592561011133183007)
                    ·
                      rfl

theorem cell22_3462880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_3462880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462880 prefixEnd_3462880 := by exact prefixLift 3462880
  have htrace : WordTrace (prefixWord ++ tailWord_3462880) baseStart_3462880 baseEnd_3462880 := by
    simpa [prefixWord, tailWord_3462880, baseEnd_3462880] using wordTrace_append hprefix tailTrace_3462880
  have hstable : (prefixWord ++ tailWord_3462880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462880).length < 2 ^ (prefixWord ++ tailWord_3462880).sum := by decide
  have hdescent : baseEnd_3462880 < baseStart_3462880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462974 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3462974 : Nat := 118140960795 + 3462974 * 2 ^ 59
def prefixEnd_3462974 : Nat := 4983230072969 + 3 ^ 40 * 3462974 * 2
def baseEnd_3462974 : Nat := 1185446770682026221332719

theorem tailTrace_3462974 : CollatzResearch.WordTrace tailWord_3462974 prefixEnd_3462974 1185446770682026221332719 := by
  unfold tailWord_3462974
  simp only [CollatzResearch.WordTrace]
  refine ⟨15788129769530512714781497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84203358770829401145501317 15788129769530512714781497)
  ·
    refine ⟨11841097327147884536086123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15788129769530512714781497 11841097327147884536086123)
    ·
      refine ⟨17761645990721826804129185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11841097327147884536086123 17761645990721826804129185)
      ·
        refine ⟨13321234493041370103096889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17761645990721826804129185 13321234493041370103096889)
        ·
          refine ⟨9990925869781027577322667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13321234493041370103096889 9990925869781027577322667)
          ·
            refine ⟨14986388804671541365984001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9990925869781027577322667 14986388804671541365984001)
            ·
              refine ⟨11239791603503656024488001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14986388804671541365984001 11239791603503656024488001)
              ·
                refine ⟨8429843702627742018366001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11239791603503656024488001 8429843702627742018366001)
                ·
                  refine ⟨6322382776970806513774501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8429843702627742018366001 6322382776970806513774501)
                  ·
                    refine ⟨1185446770682026221332719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6322382776970806513774501 1185446770682026221332719)
                    ·
                      rfl

theorem cell22_3462974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3462974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462974 prefixEnd_3462974 := by exact prefixLift 3462974
  have htrace : WordTrace (prefixWord ++ tailWord_3462974) baseStart_3462974 baseEnd_3462974 := by
    simpa [prefixWord, tailWord_3462974, baseEnd_3462974] using wordTrace_append hprefix tailTrace_3462974
  have hstable : (prefixWord ++ tailWord_3462974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462974).length < 2 ^ (prefixWord ++ tailWord_3462974).sum := by decide
  have hdescent : baseEnd_3462974 < baseStart_3462974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462985 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 1, 8]
def baseStart_3462985 : Nat := 118140960795 + 3462985 * 2 ^ 59
def prefixEnd_3462985 : Nat := 4983230072969 + 3 ^ 40 * 3462985 * 2
def baseEnd_3462985 : Nat := 1185450536206825859307685

theorem tailTrace_3462985 : CollatzResearch.WordTrace tailWord_3462985 prefixEnd_3462985 1185450536206825859307685 := by
  unfold tailWord_3462985
  simp only [CollatzResearch.WordTrace]
  refine ⟨126305439359204250596902409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84203626239469500397934939 126305439359204250596902409)
  ·
    refine ⟨94729079519403187947676807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126305439359204250596902409 94729079519403187947676807)
    ·
      refine ⟨142093619279104781921515211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94729079519403187947676807 142093619279104781921515211)
      ·
        refine ⟨213140428918657172882272817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142093619279104781921515211 213140428918657172882272817)
        ·
          refine ⟨159855321688992879661704613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213140428918657172882272817 159855321688992879661704613)
          ·
            refine ⟨29972872816686164936569615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159855321688992879661704613 29972872816686164936569615)
            ·
              refine ⟨44959309225029247404854423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29972872816686164936569615 44959309225029247404854423)
              ·
                refine ⟨67438963837543871107281635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44959309225029247404854423 67438963837543871107281635)
                ·
                  refine ⟨101158445756315806660922453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67438963837543871107281635 101158445756315806660922453)
                  ·
                    refine ⟨1185450536206825859307685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101158445756315806660922453 1185450536206825859307685)
                    ·
                      rfl

theorem cell22_3462985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_3462985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462985 prefixEnd_3462985 := by exact prefixLift 3462985
  have htrace : WordTrace (prefixWord ++ tailWord_3462985) baseStart_3462985 baseEnd_3462985 := by
    simpa [prefixWord, tailWord_3462985, baseEnd_3462985] using wordTrace_append hprefix tailTrace_3462985
  have hstable : (prefixWord ++ tailWord_3462985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462985).length < 2 ^ (prefixWord ++ tailWord_3462985).sum := by decide
  have hdescent : baseEnd_3462985 < baseStart_3462985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462989 : List Nat := [1, 6, 1, 2, 1, 1, 3, 7]
def baseStart_3462989 : Nat := 118140960795 + 3462989 * 2 ^ 59
def prefixEnd_3462989 : Nat := 4983230072969 + 3 ^ 40 * 3462989 * 2
def baseEnd_3462989 : Nat := 131716878387619020245297

theorem tailTrace_3462989 : CollatzResearch.WordTrace tailWord_3462989 prefixEnd_3462989 131716878387619020245297 := by
  unfold tailWord_3462989
  simp only [CollatzResearch.WordTrace]
  refine ⟨126305585251189759280048021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84203723500793172853365347 126305585251189759280048021)
  ·
    refine ⟨5920574308649519966252251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126305585251189759280048021 5920574308649519966252251)
    ·
      refine ⟨8880861462974279949378377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5920574308649519966252251 8880861462974279949378377)
      ·
        refine ⟨6660646097230709962033783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8880861462974279949378377 6660646097230709962033783)
        ·
          refine ⟨9990969145846064943050675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6660646097230709962033783 9990969145846064943050675)
          ·
            refine ⟨14986453718769097414576013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9990969145846064943050675 14986453718769097414576013)
            ·
              refine ⟨5619920144538411530466005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14986453718769097414576013 5619920144538411530466005)
              ·
                refine ⟨131716878387619020245297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5619920144538411530466005 131716878387619020245297)
                ·
                  rfl

theorem cell22_3462989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 7].length) (baseStart_3462989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3462989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3462989 prefixEnd_3462989 := by exact prefixLift 3462989
  have htrace : WordTrace (prefixWord ++ tailWord_3462989) baseStart_3462989 baseEnd_3462989 := by
    simpa [prefixWord, tailWord_3462989, baseEnd_3462989] using wordTrace_append hprefix tailTrace_3462989
  have hstable : (prefixWord ++ tailWord_3462989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462989).length < 2 ^ (prefixWord ++ tailWord_3462989).sum := by decide
  have hdescent : baseEnd_3462989 < baseStart_3462989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463000 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 11]
def baseStart_3463000 : Nat := 118140960795 + 3463000 * 2 ^ 59
def prefixEnd_3463000 : Nat := 4983230072969 + 3 ^ 40 * 3463000 * 2
def baseEnd_3463000 : Nat := 395151890337790273394213

theorem tailTrace_3463000 : CollatzResearch.WordTrace tailWord_3463000 prefixEnd_3463000 395151890337790273394213 := by
  unfold tailWord_3463000
  simp only [CollatzResearch.WordTrace]
  refine ⟨63152993227074954079349227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84203990969433272105798969 63152993227074954079349227)
  ·
    refine ⟨94729489840612431119023841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63152993227074954079349227 94729489840612431119023841)
    ·
      refine ⟨71047117380459323339267881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94729489840612431119023841 71047117380459323339267881)
      ·
        refine ⟨53285338035344492504450911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71047117380459323339267881 53285338035344492504450911)
        ·
          refine ⟨79928007053016738756676367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53285338035344492504450911 79928007053016738756676367)
          ·
            refine ⟨119892010579525108135014551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79928007053016738756676367 119892010579525108135014551)
            ·
              refine ⟨179838015869287662202521827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119892010579525108135014551 179838015869287662202521827)
              ·
                refine ⟨269757023803931493303782741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179838015869287662202521827 269757023803931493303782741)
                ·
                  refine ⟨395151890337790273394213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 269757023803931493303782741 395151890337790273394213)
                  ·
                    rfl

theorem cell22_3463000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_3463000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463000 prefixEnd_3463000 := by exact prefixLift 3463000
  have htrace : WordTrace (prefixWord ++ tailWord_3463000) baseStart_3463000 baseEnd_3463000 := by
    simpa [prefixWord, tailWord_3463000, baseEnd_3463000] using wordTrace_append hprefix tailTrace_3463000
  have hstable : (prefixWord ++ tailWord_3463000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463000).length < 2 ^ (prefixWord ++ tailWord_3463000).sum := by decide
  have hdescent : baseEnd_3463000 < baseStart_3463000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463021 : List Nat := [1, 5, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_3463021 : Nat := 118140960795 + 3463021 * 2 ^ 59
def prefixEnd_3463021 : Nat := 4983230072969 + 3 ^ 40 * 3463021 * 2
def baseEnd_3463021 : Nat := 1185462859742533765407575

theorem tailTrace_3463021 : CollatzResearch.WordTrace tailWord_3463021 prefixEnd_3463021 1185462859742533765407575 := by
  unfold tailWord_3463021
  simp only [CollatzResearch.WordTrace]
  refine ⟨126306752387073828745212917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84204501591382552496808611 126306752387073828745212917)
  ·
    refine ⟨11841258036288171444863711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126306752387073828745212917 11841258036288171444863711)
    ·
      refine ⟨17761887054432257167295567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11841258036288171444863711 17761887054432257167295567)
      ·
        refine ⟨26642830581648385750943351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17761887054432257167295567 26642830581648385750943351)
        ·
          refine ⟨39964245872472578626415027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26642830581648385750943351 39964245872472578626415027)
          ·
            refine ⟨59946368808708867939622541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39964245872472578626415027 59946368808708867939622541)
            ·
              refine ⟨22479888303265825477358453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59946368808708867939622541 22479888303265825477358453)
              ·
                refine ⟨2107489528431171138502355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22479888303265825477358453 2107489528431171138502355)
                ·
                  refine ⟨3161234292646756707753533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107489528431171138502355 3161234292646756707753533)
                  ·
                    refine ⟨1185462859742533765407575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161234292646756707753533 1185462859742533765407575)
                    ·
                      rfl

theorem cell22_3463021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_3463021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463021 prefixEnd_3463021 := by exact prefixLift 3463021
  have htrace : WordTrace (prefixWord ++ tailWord_3463021) baseStart_3463021 baseEnd_3463021 := by
    simpa [prefixWord, tailWord_3463021, baseEnd_3463021] using wordTrace_append hprefix tailTrace_3463021
  have hstable : (prefixWord ++ tailWord_3463021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463021).length < 2 ^ (prefixWord ++ tailWord_3463021).sum := by decide
  have hdescent : baseEnd_3463021 < baseStart_3463021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463038 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_3463038 : Nat := 118140960795 + 3463038 * 2 ^ 59
def prefixEnd_3463038 : Nat := 4983230072969 + 3 ^ 40 * 3463038 * 2
def baseEnd_3463038 : Nat := 1185468679189951387732523

theorem tailTrace_3463038 : CollatzResearch.WordTrace tailWord_3463038 prefixEnd_3463038 1185468679189951387732523 := by
  unfold tailWord_3463038
  simp only [CollatzResearch.WordTrace]
  refine ⟨15788421553501530081072721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84204914952008160432387845 15788421553501530081072721)
  ·
    refine ⟨11841316165126147560804541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15788421553501530081072721 11841316165126147560804541)
    ·
      refine ⟨4440493561922305335301703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11841316165126147560804541 4440493561922305335301703)
      ·
        refine ⟨6660740342883458002952555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440493561922305335301703 6660740342883458002952555)
        ·
          refine ⟨9991110514325187004428833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6660740342883458002952555 9991110514325187004428833)
          ·
            refine ⟨7493332885743890253321625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9991110514325187004428833 7493332885743890253321625)
            ·
              refine ⟨5619999664307917689991219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7493332885743890253321625 5619999664307917689991219)
              ·
                refine ⟨8429999496461876534986829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5619999664307917689991219 8429999496461876534986829)
                ·
                  refine ⟨3161249811173203700620061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8429999496461876534986829 3161249811173203700620061)
                  ·
                    refine ⟨1185468679189951387732523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161249811173203700620061 1185468679189951387732523)
                    ·
                      rfl

theorem cell22_3463038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_3463038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463038 prefixEnd_3463038 := by exact prefixLift 3463038
  have htrace : WordTrace (prefixWord ++ tailWord_3463038) baseStart_3463038 baseEnd_3463038 := by
    simpa [prefixWord, tailWord_3463038, baseEnd_3463038] using wordTrace_append hprefix tailTrace_3463038
  have hstable : (prefixWord ++ tailWord_3463038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463038).length < 2 ^ (prefixWord ++ tailWord_3463038).sum := by decide
  have hdescent : baseEnd_3463038 < baseStart_3463038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463077 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_3463077 : Nat := 118140960795 + 3463077 * 2 ^ 59
def prefixEnd_3463077 : Nat := 4983230072969 + 3 ^ 40 * 3463077 * 2
def baseEnd_3463077 : Nat := 1185482029686968286007403

theorem tailTrace_3463077 : CollatzResearch.WordTrace tailWord_3463077 prefixEnd_3463077 1185482029686968286007403 := by
  unfold tailWord_3463077
  simp only [CollatzResearch.WordTrace]
  refine ⟨126308794874870950309251485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84205863249913966872834323 126308794874870950309251485)
  ·
    refine ⟨47365798078076606365969307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126308794874870950309251485 47365798078076606365969307)
    ·
      refine ⟨71048697117114909548953961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47365798078076606365969307 71048697117114909548953961)
      ·
        refine ⟨53286522837836182161715471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71048697117114909548953961 53286522837836182161715471)
        ·
          refine ⟨79929784256754273242573207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53286522837836182161715471 79929784256754273242573207)
          ·
            refine ⟨119894676385131409863859811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79929784256754273242573207 119894676385131409863859811)
            ·
              refine ⟨179842014577697114795789717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119894676385131409863859811 179842014577697114795789717)
              ·
                refine ⟨8430094433329552256052643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179842014577697114795789717 8430094433329552256052643)
                ·
                  refine ⟨12645141649994328384078965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8430094433329552256052643 12645141649994328384078965)
                  ·
                    refine ⟨1185482029686968286007403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12645141649994328384078965 1185482029686968286007403)
                    ·
                      rfl

theorem cell22_3463077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_3463077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463077 prefixEnd_3463077 := by exact prefixLift 3463077
  have htrace : WordTrace (prefixWord ++ tailWord_3463077) baseStart_3463077 baseEnd_3463077 := by
    simpa [prefixWord, tailWord_3463077, baseEnd_3463077] using wordTrace_append hprefix tailTrace_3463077
  have hstable : (prefixWord ++ tailWord_3463077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463077).length < 2 ^ (prefixWord ++ tailWord_3463077).sum := by decide
  have hdescent : baseEnd_3463077 < baseStart_3463077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463096 : List Nat := [2, 1, 2, 1, 2, 3, 5, 2, 4]
def baseStart_3463096 : Nat := 118140960795 + 3463096 * 2 ^ 59
def prefixEnd_3463096 : Nat := 4983230072969 + 3 ^ 40 * 3463096 * 2
def baseEnd_3463096 : Nat := 395162844591752856594115

theorem tailTrace_3463096 : CollatzResearch.WordTrace tailWord_3463096 prefixEnd_3463096 395162844591752856594115 := by
  unfold tailWord_3463096
  simp only [CollatzResearch.WordTrace]
  refine ⟨63154743930901058277096571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84206325241201411036128761 63154743930901058277096571)
  ·
    refine ⟨94732115896351587415644857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63154743930901058277096571 94732115896351587415644857)
    ·
      refine ⟨71049086922263690561733643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94732115896351587415644857 71049086922263690561733643)
      ·
        refine ⟨106573630383395535842600465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71049086922263690561733643 106573630383395535842600465)
        ·
          refine ⟨79930222787546651881950349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106573630383395535842600465 79930222787546651881950349)
          ·
            refine ⟨29973833545329994455731381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79930222787546651881950349 29973833545329994455731381)
            ·
              refine ⟨2810046894874686980224817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29973833545329994455731381 2810046894874686980224817)
              ·
                refine ⟨2107535171156015235168613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2810046894874686980224817 2107535171156015235168613)
                ·
                  refine ⟨395162844591752856594115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2107535171156015235168613 395162844591752856594115)
                  ·
                    rfl

theorem cell22_3463096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 4].length) (baseStart_3463096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463096 prefixEnd_3463096 := by exact prefixLift 3463096
  have htrace : WordTrace (prefixWord ++ tailWord_3463096) baseStart_3463096 baseEnd_3463096 := by
    simpa [prefixWord, tailWord_3463096, baseEnd_3463096] using wordTrace_append hprefix tailTrace_3463096
  have hstable : (prefixWord ++ tailWord_3463096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463096).length < 2 ^ (prefixWord ++ tailWord_3463096).sum := by decide
  have hdescent : baseEnd_3463096 < baseStart_3463096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463132 : List Nat := [2, 2, 6, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3463132 : Nat := 118140960795 + 3463132 * 2 ^ 59
def prefixEnd_3463132 : Nat := 4983230072969 + 3 ^ 40 * 3463132 * 2
def baseEnd_3463132 : Nat := 1185500857310966475882235

theorem tailTrace_3463132 : CollatzResearch.WordTrace tailWord_3463132 prefixEnd_3463132 1185500857310966475882235 := by
  unfold tailWord_3463132
  simp only [CollatzResearch.WordTrace]
  refine ⟨63155400444835847351251825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84207200593114463135002433 63155400444835847351251825)
  ·
    refine ⟨47366550333626885513438869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63155400444835847351251825 47366550333626885513438869)
    ·
      refine ⟨2220307046888760258442447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47366550333626885513438869 2220307046888760258442447)
      ·
        refine ⟨3330460570333140387663671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2220307046888760258442447 3330460570333140387663671)
        ·
          refine ⟨4995690855499710581495507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3330460570333140387663671 4995690855499710581495507)
          ·
            refine ⟨7493536283249565872243261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4995690855499710581495507 7493536283249565872243261)
            ·
              refine ⟨2810076106218587202091223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7493536283249565872243261 2810076106218587202091223)
              ·
                refine ⟨4215114159327880803136835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810076106218587202091223 4215114159327880803136835)
                ·
                  refine ⟨6322671238991821204705253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215114159327880803136835 6322671238991821204705253)
                  ·
                    refine ⟨1185500857310966475882235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6322671238991821204705253 1185500857310966475882235)
                    ·
                      rfl

theorem cell22_3463132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3463132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463132 prefixEnd_3463132 := by exact prefixLift 3463132
  have htrace : WordTrace (prefixWord ++ tailWord_3463132) baseStart_3463132 baseEnd_3463132 := by
    simpa [prefixWord, tailWord_3463132, baseEnd_3463132] using wordTrace_append hprefix tailTrace_3463132
  have hstable : (prefixWord ++ tailWord_3463132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463132).length < 2 ^ (prefixWord ++ tailWord_3463132).sum := by decide
  have hdescent : baseEnd_3463132 < baseStart_3463132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463152 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 7]
def baseStart_3463152 : Nat := 118140960795 + 3463152 * 2 ^ 59
def prefixEnd_3463152 : Nat := 4983230072969 + 3 ^ 40 * 3463152 * 2
def baseEnd_3463152 : Nat := 395169234573231030127391

theorem tailTrace_3463152 : CollatzResearch.WordTrace tailWord_3463152 prefixEnd_3463152 395169234573231030127391 := by
  unfold tailWord_3463152
  simp only [CollatzResearch.WordTrace]
  refine ⟨63155765174799619059115855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84207686899732825412154473 63155765174799619059115855)
  ·
    refine ⟨94733647762199428588673783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63155765174799619059115855 94733647762199428588673783)
    ·
      refine ⟨142100471643299142883010675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94733647762199428588673783 142100471643299142883010675)
      ·
        refine ⟨213150707464948714324516013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142100471643299142883010675 213150707464948714324516013)
        ·
          refine ⟨79931515299355767871693505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213150707464948714324516013 79931515299355767871693505)
          ·
            refine ⟨59948636474516825903770129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79931515299355767871693505 59948636474516825903770129)
            ·
              refine ⟨44961477355887619427827597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59948636474516825903770129 44961477355887619427827597)
              ·
                refine ⟨16860554008457857285435349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44961477355887619427827597 16860554008457857285435349)
                ·
                  refine ⟨395169234573231030127391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16860554008457857285435349 395169234573231030127391)
                  ·
                    rfl

theorem cell22_3463152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_3463152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463152 prefixEnd_3463152 := by exact prefixLift 3463152
  have htrace : WordTrace (prefixWord ++ tailWord_3463152) baseStart_3463152 baseEnd_3463152 := by
    simpa [prefixWord, tailWord_3463152, baseEnd_3463152] using wordTrace_append hprefix tailTrace_3463152
  have hstable : (prefixWord ++ tailWord_3463152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463152).length < 2 ^ (prefixWord ++ tailWord_3463152).sum := by decide
  have hdescent : baseEnd_3463152 < baseStart_3463152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463158 : List Nat := [5, 1, 1, 1, 5, 1, 1, 7]
def baseStart_3463158 : Nat := 118140960795 + 3463158 * 2 ^ 59
def prefixEnd_3463158 : Nat := 4983230072969 + 3 ^ 40 * 3463158 * 2
def baseEnd_3463158 : Nat := 131723306404701230525795

theorem tailTrace_3463158 : CollatzResearch.WordTrace tailWord_3463158 prefixEnd_3463158 131723306404701230525795 := by
  unfold tailWord_3463158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7894484324223593821434383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84207832791718334095300085 7894484324223593821434383)
  ·
    refine ⟨11841726486335390732151575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7894484324223593821434383 11841726486335390732151575)
    ·
      refine ⟨17762589729503086098227363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11841726486335390732151575 17762589729503086098227363)
      ·
        refine ⟨26643884594254629147341045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17762589729503086098227363 26643884594254629147341045)
        ·
          refine ⟨2497864180711371482563223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26643884594254629147341045 2497864180711371482563223)
          ·
            refine ⟨3746796271067057223844835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497864180711371482563223 3746796271067057223844835)
            ·
              refine ⟨5620194406600585835767253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3746796271067057223844835 5620194406600585835767253)
              ·
                refine ⟨131723306404701230525795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5620194406600585835767253 131723306404701230525795)
                ·
                  rfl

theorem cell22_3463158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_3463158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463158 prefixEnd_3463158 := by exact prefixLift 3463158
  have htrace : WordTrace (prefixWord ++ tailWord_3463158) baseStart_3463158 baseEnd_3463158 := by
    simpa [prefixWord, tailWord_3463158, baseEnd_3463158] using wordTrace_append hprefix tailTrace_3463158
  have hstable : (prefixWord ++ tailWord_3463158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463158).length < 2 ^ (prefixWord ++ tailWord_3463158).sum := by decide
  have hdescent : baseEnd_3463158 < baseStart_3463158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463169 : List Nat := [1, 2, 4, 1, 2, 1, 1, 5, 5]
def baseStart_3463169 : Nat := 118140960795 + 3463169 * 2 ^ 59
def prefixEnd_3463169 : Nat := 4983230072969 + 3 ^ 40 * 3463169 * 2
def baseEnd_3463169 : Nat := 395171174389036904235707

theorem tailTrace_3463169 : CollatzResearch.WordTrace tailWord_3463169 prefixEnd_3463169 395171174389036904235707 := by
  unfold tailWord_3463169
  simp only [CollatzResearch.WordTrace]
  refine ⟨126312150390537650021600561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84208100260358433347733707 126312150390537650021600561)
  ·
    refine ⟨94734112792903237516200421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126312150390537650021600561 94734112792903237516200421)
    ·
      refine ⟨17762646148669357034287579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94734112792903237516200421 17762646148669357034287579)
      ·
        refine ⟨26643969223004035551431369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17762646148669357034287579 26643969223004035551431369)
        ·
          refine ⟨19982976917253026663573527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26643969223004035551431369 19982976917253026663573527)
          ·
            refine ⟨29974465375879539995360291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19982976917253026663573527 29974465375879539995360291)
            ·
              refine ⟨44961698063819309993040437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29974465375879539995360291 44961698063819309993040437)
              ·
                refine ⟨4215159193483060311847541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44961698063819309993040437 4215159193483060311847541)
                ·
                  refine ⟨395171174389036904235707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4215159193483060311847541 395171174389036904235707)
                  ·
                    rfl

theorem cell22_3463169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_3463169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463169 prefixEnd_3463169 := by exact prefixLift 3463169
  have htrace : WordTrace (prefixWord ++ tailWord_3463169) baseStart_3463169 baseEnd_3463169 := by
    simpa [prefixWord, tailWord_3463169, baseEnd_3463169] using wordTrace_append hprefix tailTrace_3463169
  have hstable : (prefixWord ++ tailWord_3463169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463169).length < 2 ^ (prefixWord ++ tailWord_3463169).sum := by decide
  have hdescent : baseEnd_3463169 < baseStart_3463169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463220 : List Nat := [2, 5, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3463220 : Nat := 118140960795 + 3463220 * 2 ^ 59
def prefixEnd_3463220 : Nat := 4983230072969 + 3 ^ 40 * 3463220 * 2
def baseEnd_3463220 : Nat := 395176993836454526560655

theorem tailTrace_3463220 : CollatzResearch.WordTrace tailWord_3463220 prefixEnd_3463220 395176993836454526560655 := by
  unfold tailWord_3463220
  simp only [CollatzResearch.WordTrace]
  refine ⟨63157005256676442865853557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84209340342235257154471409 63157005256676442865853557)
  ·
    refine ⟨5920969242813416518673771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63157005256676442865853557 5920969242813416518673771)
    ·
      refine ⟨8881453864220124778010657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5920969242813416518673771 8881453864220124778010657)
      ·
        refine ⟨6661090398165093583507993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8881453864220124778010657 6661090398165093583507993)
        ·
          refine ⟨4995817798623820187630995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6661090398165093583507993 4995817798623820187630995)
          ·
            refine ⟨7493726697935730281446493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4995817798623820187630995 7493726697935730281446493)
            ·
              refine ⟨2810147511725898855542435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7493726697935730281446493 2810147511725898855542435)
              ·
                refine ⟨4215221267588848283313653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810147511725898855542435 4215221267588848283313653)
                ·
                  refine ⟨395176993836454526560655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4215221267588848283313653 395176993836454526560655)
                  ·
                    rfl

theorem cell22_3463220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3463220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463220 prefixEnd_3463220 := by exact prefixLift 3463220
  have htrace : WordTrace (prefixWord ++ tailWord_3463220) baseStart_3463220 baseEnd_3463220 := by
    simpa [prefixWord, tailWord_3463220, baseEnd_3463220] using wordTrace_append hprefix tailTrace_3463220
  have hstable : (prefixWord ++ tailWord_3463220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463220).length < 2 ^ (prefixWord ++ tailWord_3463220).sum := by decide
  have hdescent : baseEnd_3463220 < baseStart_3463220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463233 : List Nat := [1, 2, 5, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3463233 : Nat := 118140960795 + 3463233 * 2 ^ 59
def prefixEnd_3463233 : Nat := 4983230072969 + 3 ^ 40 * 3463233 * 2
def baseEnd_3463233 : Nat := 1185535431675035879106925

theorem tailTrace_3463233 : CollatzResearch.WordTrace tailWord_3463233 prefixEnd_3463233 1185535431675035879106925 := by
  unfold tailWord_3463233
  simp only [CollatzResearch.WordTrace]
  refine ⟨126314484662305788951930353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84209656441537192634620235 126314484662305788951930353)
  ·
    refine ⟨94735863496729341713947765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126314484662305788951930353 94735863496729341713947765)
    ·
      refine ⟨8881487202818375785682603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94735863496729341713947765 8881487202818375785682603)
      ·
        refine ⟨13322230804227563678523905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8881487202818375785682603 13322230804227563678523905)
        ·
          refine ⟨9991673103170672758892929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13322230804227563678523905 9991673103170672758892929)
          ·
            refine ⟨7493754827378004569169697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9991673103170672758892929 7493754827378004569169697)
            ·
              refine ⟨5620316120533503426877273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7493754827378004569169697 5620316120533503426877273)
              ·
                refine ⟨4215237090400127570157955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5620316120533503426877273 4215237090400127570157955)
                ·
                  refine ⟨6322855635600191355236933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215237090400127570157955 6322855635600191355236933)
                  ·
                    refine ⟨1185535431675035879106925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6322855635600191355236933 1185535431675035879106925)
                    ·
                      rfl

theorem cell22_3463233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3463233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463233 prefixEnd_3463233 := by exact prefixLift 3463233
  have htrace : WordTrace (prefixWord ++ tailWord_3463233) baseStart_3463233 baseEnd_3463233 := by
    simpa [prefixWord, tailWord_3463233, baseEnd_3463233] using wordTrace_append hprefix tailTrace_3463233
  have hstable : (prefixWord ++ tailWord_3463233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463233).length < 2 ^ (prefixWord ++ tailWord_3463233).sum := by decide
  have hdescent : baseEnd_3463233 < baseStart_3463233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463244 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_3463244 : Nat := 118140960795 + 3463244 * 2 ^ 59
def prefixEnd_3463244 : Nat := 4983230072969 + 3 ^ 40 * 3463244 * 2
def baseEnd_3463244 : Nat := 1185539197199835517081891

theorem tailTrace_3463244 : CollatzResearch.WordTrace tailWord_3463244 prefixEnd_3463244 1185539197199835517081891 := by
  unfold tailWord_3463244
  simp only [CollatzResearch.WordTrace]
  refine ⟨63157442932632968915290393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84209923910177291887053857 63157442932632968915290393)
  ·
    refine ⟨47368082199474726686467795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63157442932632968915290393 47368082199474726686467795)
    ·
      refine ⟨71052123299212090029701693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47368082199474726686467795 71052123299212090029701693)
      ·
        refine ⟨26644546237204533761138135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71052123299212090029701693 26644546237204533761138135)
        ·
          refine ⟨39966819355806800641707203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26644546237204533761138135 39966819355806800641707203)
          ·
            refine ⟨59950229033710200962560805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39966819355806800641707203 59950229033710200962560805)
            ·
              refine ⟨11240667943820662680480151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59950229033710200962560805 11240667943820662680480151)
              ·
                refine ⟨16861001915730994020720227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11240667943820662680480151 16861001915730994020720227)
                ·
                  refine ⟨25291502873596491031080341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16861001915730994020720227 25291502873596491031080341)
                  ·
                    refine ⟨1185539197199835517081891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25291502873596491031080341 1185539197199835517081891)
                    ·
                      rfl

theorem cell22_3463244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_3463244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463244 prefixEnd_3463244 := by exact prefixLift 3463244
  have htrace : WordTrace (prefixWord ++ tailWord_3463244) baseStart_3463244 baseEnd_3463244 := by
    simpa [prefixWord, tailWord_3463244, baseEnd_3463244] using wordTrace_append hprefix tailTrace_3463244
  have hstable : (prefixWord ++ tailWord_3463244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463244).length < 2 ^ (prefixWord ++ tailWord_3463244).sum := by decide
  have hdescent : baseEnd_3463244 < baseStart_3463244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463246 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_3463246 : Nat := 118140960795 + 3463246 * 2 ^ 59
def prefixEnd_3463246 : Nat := 4983230072969 + 3 ^ 40 * 3463246 * 2
def baseEnd_3463246 : Nat := 1185539881840708178531885

theorem tailTrace_3463246 : CollatzResearch.WordTrace tailWord_3463246 prefixEnd_3463246 1185539881840708178531885 := by
  unfold tailWord_3463246
  simp only [CollatzResearch.WordTrace]
  refine ⟨15789369851407336521519199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84209972540839128114769061 15789369851407336521519199)
  ·
    refine ⟨23684054777111004782278799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15789369851407336521519199 23684054777111004782278799)
    ·
      refine ⟨35526082165666507173418199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23684054777111004782278799 35526082165666507173418199)
      ·
        refine ⟨53289123248499760760127299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35526082165666507173418199 53289123248499760760127299)
        ·
          refine ⟨79933684872749641140190949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53289123248499760760127299 79933684872749641140190949)
          ·
            refine ⟨14987565913640557713785803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79933684872749641140190949 14987565913640557713785803)
            ·
              refine ⟨22481348870460836570678705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14987565913640557713785803 22481348870460836570678705)
              ·
                refine ⟨16861011652845627428009029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22481348870460836570678705 16861011652845627428009029)
                ·
                  refine ⟨3161439684908555142751693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16861011652845627428009029 3161439684908555142751693)
                  ·
                    refine ⟨1185539881840708178531885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161439684908555142751693 1185539881840708178531885)
                    ·
                      rfl

theorem cell22_3463246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_3463246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463246 prefixEnd_3463246 := by exact prefixLift 3463246
  have htrace : WordTrace (prefixWord ++ tailWord_3463246) baseStart_3463246 baseEnd_3463246 := by
    simpa [prefixWord, tailWord_3463246, baseEnd_3463246] using wordTrace_append hprefix tailTrace_3463246
  have hstable : (prefixWord ++ tailWord_3463246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463246).length < 2 ^ (prefixWord ++ tailWord_3463246).sum := by decide
  have hdescent : baseEnd_3463246 < baseStart_3463246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463280 : List Nat := [2, 1, 1, 1, 5, 4, 2, 1, 2, 3]
def baseStart_3463280 : Nat := 118140960795 + 3463280 * 2 ^ 59
def prefixEnd_3463280 : Nat := 4983230072969 + 3 ^ 40 * 3463280 * 2
def baseEnd_3463280 : Nat := 1185551520735543423181781

theorem tailTrace_3463280 : CollatzResearch.WordTrace tailWord_3463280 prefixEnd_3463280 1185551520735543423181781 := by
  unfold tailWord_3463280
  simp only [CollatzResearch.WordTrace]
  refine ⟨63158099446567757989445647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84210799262090343985927529 63158099446567757989445647)
  ·
    refine ⟨94737149169851636984168471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63158099446567757989445647 94737149169851636984168471)
    ·
      refine ⟨142105723754777455476252707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94737149169851636984168471 142105723754777455476252707)
      ·
        refine ⟨213158585632166183214379061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142105723754777455476252707 213158585632166183214379061)
        ·
          refine ⟨19983617403015579676348037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213158585632166183214379061 19983617403015579676348037)
          ·
            refine ⟨3746928263065421189315257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19983617403015579676348037 3746928263065421189315257)
            ·
              refine ⟨2810196197299065891986443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3746928263065421189315257 2810196197299065891986443)
              ·
                refine ⟨4215294295948598837979665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810196197299065891986443 4215294295948598837979665)
                ·
                  refine ⟨3161470721961449128484749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4215294295948598837979665 3161470721961449128484749)
                  ·
                    refine ⟨1185551520735543423181781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161470721961449128484749 1185551520735543423181781)
                    ·
                      rfl

theorem cell22_3463280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 2, 3].length) (baseStart_3463280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463280 prefixEnd_3463280 := by exact prefixLift 3463280
  have htrace : WordTrace (prefixWord ++ tailWord_3463280) baseStart_3463280 baseEnd_3463280 := by
    simpa [prefixWord, tailWord_3463280, baseEnd_3463280] using wordTrace_append hprefix tailTrace_3463280
  have hstable : (prefixWord ++ tailWord_3463280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463280).length < 2 ^ (prefixWord ++ tailWord_3463280).sum := by decide
  have hdescent : baseEnd_3463280 < baseStart_3463280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463325 : List Nat := [1, 4, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_3463325 : Nat := 118140960795 + 3463325 * 2 ^ 59
def prefixEnd_3463325 : Nat := 4983230072969 + 3 ^ 40 * 3463325 * 2
def baseEnd_3463325 : Nat := 1185566925155178305806643

theorem tailTrace_3463325 : CollatzResearch.WordTrace tailWord_3463325 prefixEnd_3463325 1185566925155178305806643 := by
  unfold tailWord_3463325
  simp only [CollatzResearch.WordTrace]
  refine ⟨126317840177972488664279429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84211893451981659109519619 126317840177972488664279429)
  ·
    refine ⟨23684595033369841624552393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126317840177972488664279429 23684595033369841624552393)
    ·
      refine ⟨17763446275027381218414295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23684595033369841624552393 17763446275027381218414295)
      ·
        refine ⟨26645169412541071827621443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17763446275027381218414295 26645169412541071827621443)
        ·
          refine ⟨39967754118811607741432165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26645169412541071827621443 39967754118811607741432165)
          ·
            refine ⟨7493953897277176451518531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39967754118811607741432165 7493953897277176451518531)
            ·
              refine ⟨11240930845915764677277797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7493953897277176451518531 11240930845915764677277797)
              ·
                refine ⟨2107674533609205876989587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11240930845915764677277797 2107674533609205876989587)
                ·
                  refine ⟨3161511800413808815484381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107674533609205876989587 3161511800413808815484381)
                  ·
                    refine ⟨1185566925155178305806643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161511800413808815484381 1185566925155178305806643)
                    ·
                      rfl

theorem cell22_3463325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_3463325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463325 prefixEnd_3463325 := by exact prefixLift 3463325
  have htrace : WordTrace (prefixWord ++ tailWord_3463325) baseStart_3463325 baseEnd_3463325 := by
    simpa [prefixWord, tailWord_3463325, baseEnd_3463325] using wordTrace_append hprefix tailTrace_3463325
  have hstable : (prefixWord ++ tailWord_3463325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463325).length < 2 ^ (prefixWord ++ tailWord_3463325).sum := by decide
  have hdescent : baseEnd_3463325 < baseStart_3463325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463342 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3463342 : Nat := 118140960795 + 3463342 * 2 ^ 59
def prefixEnd_3463342 : Nat := 4983230072969 + 3 ^ 40 * 3463342 * 2
def baseEnd_3463342 : Nat := 1185572744602595928131591

theorem tailTrace_3463342 : CollatzResearch.WordTrace tailWord_3463342 prefixEnd_3463342 1185572744602595928131591 := by
  unfold tailWord_3463342
  simp only [CollatzResearch.WordTrace]
  refine ⟨15789807527363862570956035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84212306812607267045098853 15789807527363862570956035)
  ·
    refine ⟨23684711291045793856434053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15789807527363862570956035 23684711291045793856434053)
    ·
      refine ⟨4440883367071086348081385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23684711291045793856434053 4440883367071086348081385)
      ·
        refine ⟨3330662525303314761061039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4440883367071086348081385 3330662525303314761061039)
        ·
          refine ⟨4995993787954972141591559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3330662525303314761061039 4995993787954972141591559)
          ·
            refine ⟨7493990681932458212387339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4995993787954972141591559 7493990681932458212387339)
            ·
              refine ⟨11240986022898687318581009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7493990681932458212387339 11240986022898687318581009)
              ·
                refine ⟨8430739517174015488935757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11240986022898687318581009 8430739517174015488935757)
                ·
                  refine ⟨3161527318940255808350909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8430739517174015488935757 3161527318940255808350909)
                  ·
                    refine ⟨1185572744602595928131591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161527318940255808350909 1185572744602595928131591)
                    ·
                      rfl

theorem cell22_3463342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3463342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463342 prefixEnd_3463342 := by exact prefixLift 3463342
  have htrace : WordTrace (prefixWord ++ tailWord_3463342) baseStart_3463342 baseEnd_3463342 := by
    simpa [prefixWord, tailWord_3463342, baseEnd_3463342] using wordTrace_append hprefix tailTrace_3463342
  have hstable : (prefixWord ++ tailWord_3463342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463342).length < 2 ^ (prefixWord ++ tailWord_3463342).sum := by decide
  have hdescent : baseEnd_3463342 < baseStart_3463342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463351 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 3, 4]
def baseStart_3463351 : Nat := 118140960795 + 3463351 * 2 ^ 59
def prefixEnd_3463351 : Nat := 4983230072969 + 3 ^ 40 * 3463351 * 2
def baseEnd_3463351 : Nat := 1185575825486522904656563

theorem tailTrace_3463351 : CollatzResearch.WordTrace tailWord_3463351 prefixEnd_3463351 1185575825486522904656563 := by
  unfold tailWord_3463351
  simp only [CollatzResearch.WordTrace]
  refine ⟨126318788475878295104725907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84212525650585530069817271 126318788475878295104725907)
  ·
    refine ⟨189478182713817442657088861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126318788475878295104725907 189478182713817442657088861)
    ·
      refine ⟨71054318517681540996408323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189478182713817442657088861 71054318517681540996408323)
      ·
        refine ⟨106581477776522311494612485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71054318517681540996408323 106581477776522311494612485)
        ·
          refine ⟨19984027083097933405239841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106581477776522311494612485 19984027083097933405239841)
          ·
            refine ⟨14988020312323450053929881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19984027083097933405239841 14988020312323450053929881)
            ·
              refine ⟨11241015234242587540447411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14988020312323450053929881 11241015234242587540447411)
              ·
                refine ⟨16861522851363881310671117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11241015234242587540447411 16861522851363881310671117)
                ·
                  refine ⟨6323071069261455491501669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16861522851363881310671117 6323071069261455491501669)
                  ·
                    refine ⟨1185575825486522904656563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6323071069261455491501669 1185575825486522904656563)
                    ·
                      rfl

theorem cell22_3463351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_3463351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463351 prefixEnd_3463351 := by exact prefixLift 3463351
  have htrace : WordTrace (prefixWord ++ tailWord_3463351) baseStart_3463351 baseEnd_3463351 := by
    simpa [prefixWord, tailWord_3463351, baseEnd_3463351] using wordTrace_append hprefix tailTrace_3463351
  have hstable : (prefixWord ++ tailWord_3463351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463351).length < 2 ^ (prefixWord ++ tailWord_3463351).sum := by decide
  have hdescent : baseEnd_3463351 < baseStart_3463351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463372 : List Nat := [2, 2, 1, 6, 2, 1, 1, 2, 5]
def baseStart_3463372 : Nat := 118140960795 + 3463372 * 2 ^ 59
def prefixEnd_3463372 : Nat := 4983230072969 + 3 ^ 40 * 3463372 * 2
def baseEnd_3463372 : Nat := 395194338071895283293833

theorem tailTrace_3463372 : CollatzResearch.WordTrace tailWord_3463372 prefixEnd_3463372 395194338071895283293833 := by
  unfold tailWord_3463372
  simp only [CollatzResearch.WordTrace]
  refine ⟨63159777204401107845620185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84213036272534810460826913 63159777204401107845620185)
  ·
    refine ⟨47369832903300830884215139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63159777204401107845620185 47369832903300830884215139)
    ·
      refine ⟨71054749354951246326322709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47369832903300830884215139 71054749354951246326322709)
      ·
        refine ⟨3330691376013339671546377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71054749354951246326322709 3330691376013339671546377)
        ·
          refine ⟨2498018532010004753659783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3330691376013339671546377 2498018532010004753659783)
          ·
            refine ⟨3747027798015007130489675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498018532010004753659783 3747027798015007130489675)
            ·
              refine ⟨5620541697022510695734513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3747027798015007130489675 5620541697022510695734513)
              ·
                refine ⟨4215406272766883021800885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5620541697022510695734513 4215406272766883021800885)
                ·
                  refine ⟨395194338071895283293833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4215406272766883021800885 395194338071895283293833)
                  ·
                    rfl

theorem cell22_3463372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_3463372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463372 prefixEnd_3463372 := by exact prefixLift 3463372
  have htrace : WordTrace (prefixWord ++ tailWord_3463372) baseStart_3463372 baseEnd_3463372 := by
    simpa [prefixWord, tailWord_3463372, baseEnd_3463372] using wordTrace_append hprefix tailTrace_3463372
  have hstable : (prefixWord ++ tailWord_3463372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463372).length < 2 ^ (prefixWord ++ tailWord_3463372).sum := by decide
  have hdescent : baseEnd_3463372 < baseStart_3463372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463379 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 5, 6]
def baseStart_3463379 : Nat := 118140960795 + 3463379 * 2 ^ 59
def prefixEnd_3463379 : Nat := 4983230072969 + 3 ^ 40 * 3463379 * 2
def baseEnd_3463379 : Nat := 1185585410458740164956477

theorem tailTrace_3463379 : CollatzResearch.WordTrace tailWord_3463379 prefixEnd_3463379 1185585410458740164956477 := by
  unfold tailWord_3463379
  simp only [CollatzResearch.WordTrace]
  refine ⟨126319809719776855886745191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84213206479851237257830127 126319809719776855886745191)
  ·
    refine ⟨189479714579665283830117787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126319809719776855886745191 189479714579665283830117787)
    ·
      refine ⟨284219571869497925745176681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189479714579665283830117787 284219571869497925745176681)
      ·
        refine ⟨213164678902123444308882511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284219571869497925745176681 213164678902123444308882511)
        ·
          refine ⟨319747018353185166463323767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213164678902123444308882511 319747018353185166463323767)
          ·
            refine ⟨479620527529777749694985651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319747018353185166463323767 479620527529777749694985651)
            ·
              refine ⟨719430791294666624542478477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479620527529777749694985651 719430791294666624542478477)
              ·
                refine ⟨269786546735499984203429429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 719430791294666624542478477 269786546735499984203429429)
                ·
                  refine ⟨25292488756453123519071509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269786546735499984203429429 25292488756453123519071509)
                  ·
                    refine ⟨1185585410458740164956477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25292488756453123519071509 1185585410458740164956477)
                    ·
                      rfl

theorem cell22_3463379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_3463379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463379 prefixEnd_3463379 := by exact prefixLift 3463379
  have htrace : WordTrace (prefixWord ++ tailWord_3463379) baseStart_3463379 baseEnd_3463379 := by
    simpa [prefixWord, tailWord_3463379, baseEnd_3463379] using wordTrace_append hprefix tailTrace_3463379
  have hstable : (prefixWord ++ tailWord_3463379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463379).length < 2 ^ (prefixWord ++ tailWord_3463379).sum := by decide
  have hdescent : baseEnd_3463379 < baseStart_3463379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463428 : List Nat := [2, 3, 2, 2, 3, 2, 8]
def baseStart_3463428 : Nat := 118140960795 + 3463428 * 2 ^ 59
def prefixEnd_3463428 : Nat := 4983230072969 + 3 ^ 40 * 3463428 * 2
def baseEnd_3463428 : Nat := 43911192005930384091901

theorem tailTrace_3463428 : CollatzResearch.WordTrace tailWord_3463428 prefixEnd_3463428 43911192005930384091901 := by
  unfold tailWord_3463428
  simp only [CollatzResearch.WordTrace]
  refine ⟨63160798448299668627639469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84214397931066224836852625 63160798448299668627639469)
  ·
    refine ⟨23685299418112375735364801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63160798448299668627639469 23685299418112375735364801)
    ·
      refine ⟨17763974563584281801523601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23685299418112375735364801 17763974563584281801523601)
      ·
        refine ⟨13322980922688211351142701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17763974563584281801523601 13322980922688211351142701)
        ·
          refine ⟨4996117846008079256678513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13322980922688211351142701 4996117846008079256678513)
          ·
            refine ⟨3747088384506059442508885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4996117846008079256678513 3747088384506059442508885)
            ·
              refine ⟨43911192005930384091901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3747088384506059442508885 43911192005930384091901)
              ·
                rfl

theorem cell22_3463428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 8].length) (baseStart_3463428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463428 prefixEnd_3463428 := by exact prefixLift 3463428
  have htrace : WordTrace (prefixWord ++ tailWord_3463428) baseStart_3463428 baseEnd_3463428 := by
    simpa [prefixWord, tailWord_3463428, baseEnd_3463428] using wordTrace_append hprefix tailTrace_3463428
  have hstable : (prefixWord ++ tailWord_3463428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463428).length < 2 ^ (prefixWord ++ tailWord_3463428).sum := by decide
  have hdescent : baseEnd_3463428 < baseStart_3463428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463531 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 1, 6]
def baseStart_3463531 : Nat := 118140960795 + 3463531 * 2 ^ 59
def prefixEnd_3463531 : Nat := 4983230072969 + 3 ^ 40 * 3463531 * 2
def baseEnd_3463531 : Nat := 1185637443165062435156011

theorem tailTrace_3463531 : CollatzResearch.WordTrace tailWord_3463531 prefixEnd_3463531 1185637443165062435156011 := by
  unfold tailWord_3463531
  simp only [CollatzResearch.WordTrace]
  refine ⟨126325353615226185846278447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84216902410150790564185631 126325353615226185846278447)
  ·
    refine ⟨189488030422839278769417671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126325353615226185846278447 189488030422839278769417671)
    ·
      refine ⟨284232045634258918154126507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189488030422839278769417671 284232045634258918154126507)
      ·
        refine ⟨426348068451388377231189761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284232045634258918154126507 426348068451388377231189761)
        ·
          refine ⟨319761051338541282923392321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426348068451388377231189761 319761051338541282923392321)
          ·
            refine ⟨239820788503905962192544241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319761051338541282923392321 239820788503905962192544241)
            ·
              refine ⟨179865591377929471644408181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239820788503905962192544241 179865591377929471644408181)
              ·
                refine ⟨16862399191680887966663267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179865591377929471644408181 16862399191680887966663267)
                ·
                  refine ⟨25293598787521331949994901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16862399191680887966663267 25293598787521331949994901)
                  ·
                    refine ⟨1185637443165062435156011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25293598787521331949994901 1185637443165062435156011)
                    ·
                      rfl

theorem cell22_3463531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_3463531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463531 prefixEnd_3463531 := by exact prefixLift 3463531
  have htrace : WordTrace (prefixWord ++ tailWord_3463531) baseStart_3463531 baseEnd_3463531 := by
    simpa [prefixWord, tailWord_3463531, baseEnd_3463531] using wordTrace_append hprefix tailTrace_3463531
  have hstable : (prefixWord ++ tailWord_3463531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463531).length < 2 ^ (prefixWord ++ tailWord_3463531).sum := by decide
  have hdescent : baseEnd_3463531 < baseStart_3463531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463533 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_3463533 : Nat := 118140960795 + 3463533 * 2 ^ 59
def prefixEnd_3463533 : Nat := 4983230072969 + 3 ^ 40 * 3463533 * 2
def baseEnd_3463533 : Nat := 1185638127805935096606005

theorem tailTrace_3463533 : CollatzResearch.WordTrace tailWord_3463533 prefixEnd_3463533 1185638127805935096606005 := by
  unfold tailWord_3463533
  simp only [CollatzResearch.WordTrace]
  refine ⟨126325426561218940187851253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84216951040812626791900835 126325426561218940187851253)
  ·
    refine ⟨11843008740114275642611055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126325426561218940187851253 11843008740114275642611055)
    ·
      refine ⟨17764513110171413463916583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11843008740114275642611055 17764513110171413463916583)
      ·
        refine ⟨26646769665257120195874875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17764513110171413463916583 26646769665257120195874875)
        ·
          refine ⟨39970154497885680293812313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26646769665257120195874875 39970154497885680293812313)
          ·
            refine ⟨29977615873414260220359235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39970154497885680293812313 29977615873414260220359235)
            ·
              refine ⟨44966423810121390330538853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29977615873414260220359235 44966423810121390330538853)
              ·
                refine ⟨8431204464397760686976035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44966423810121390330538853 8431204464397760686976035)
                ·
                  refine ⟨12646806696596641030464053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8431204464397760686976035 12646806696596641030464053)
                  ·
                    refine ⟨1185638127805935096606005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12646806696596641030464053 1185638127805935096606005)
                    ·
                      rfl

theorem cell22_3463533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_3463533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463533 prefixEnd_3463533 := by exact prefixLift 3463533
  have htrace : WordTrace (prefixWord ++ tailWord_3463533) baseStart_3463533 baseEnd_3463533 := by
    simpa [prefixWord, tailWord_3463533, baseEnd_3463533] using wordTrace_append hprefix tailTrace_3463533
  have hstable : (prefixWord ++ tailWord_3463533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463533).length < 2 ^ (prefixWord ++ tailWord_3463533).sum := by decide
  have hdescent : baseEnd_3463533 < baseStart_3463533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463597 : List Nat := [1, 5, 2, 2, 3, 1, 8]
def baseStart_3463597 : Nat := 118140960795 + 3463597 * 2 ^ 59
def prefixEnd_3463597 : Nat := 4983230072969 + 3 ^ 40 * 3463597 * 2
def baseEnd_3463597 : Nat := 43913334678291120852067

theorem tailTrace_3463597 : CollatzResearch.WordTrace tailWord_3463597 prefixEnd_3463597 43913334678291120852067 := by
  unfold tailWord_3463597
  simp only [CollatzResearch.WordTrace]
  refine ⟨126327760832987079118181045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84218507221991386078787363 126327760832987079118181045)
  ·
    refine ⟨11843227578092538667329473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126327760832987079118181045 11843227578092538667329473)
    ·
      refine ⟨8882420683569404000497105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11843227578092538667329473 8882420683569404000497105)
      ·
        refine ⟨6661815512677053000372829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8882420683569404000497105 6661815512677053000372829)
        ·
          refine ⟨2498180817253894875139811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6661815512677053000372829 2498180817253894875139811)
          ·
            refine ⟨3747271225880842312709717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498180817253894875139811 3747271225880842312709717)
            ·
              refine ⟨43913334678291120852067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3747271225880842312709717 43913334678291120852067)
              ·
                rfl

theorem cell22_3463597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 8].length) (baseStart_3463597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463597 prefixEnd_3463597 := by exact prefixLift 3463597
  have htrace : WordTrace (prefixWord ++ tailWord_3463597) baseStart_3463597 baseEnd_3463597 := by
    simpa [prefixWord, tailWord_3463597, baseEnd_3463597] using wordTrace_append hprefix tailTrace_3463597
  have hstable : (prefixWord ++ tailWord_3463597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463597).length < 2 ^ (prefixWord ++ tailWord_3463597).sum := by decide
  have hdescent : baseEnd_3463597 < baseStart_3463597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463608 : List Nat := [2, 1, 2, 1, 2, 2, 1, 6, 5]
def baseStart_3463608 : Nat := 118140960795 + 3463608 * 2 ^ 59
def prefixEnd_3463608 : Nat := 4983230072969 + 3 ^ 40 * 3463608 * 2
def baseEnd_3463608 : Nat := 395221267279553300326925

theorem tailTrace_3463608 : CollatzResearch.WordTrace tailWord_3463608 prefixEnd_3463608 395221267279553300326925 := by
  unfold tailWord_3463608
  simp only [CollatzResearch.WordTrace]
  refine ⟨63164081017973613998415739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84218774690631485331220985 63164081017973613998415739)
  ·
    refine ⟨94746121526960420997623609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63164081017973613998415739 94746121526960420997623609)
    ·
      refine ⟨71059591145220315748217707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94746121526960420997623609 71059591145220315748217707)
      ·
        refine ⟨106589386717830473622326561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71059591145220315748217707 106589386717830473622326561)
        ·
          refine ⟨79942040038372855216744921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106589386717830473622326561 79942040038372855216744921)
          ·
            refine ⟨59956530028779641412558691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79942040038372855216744921 59956530028779641412558691)
            ·
              refine ⟨89934795043169462118838037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59956530028779641412558691 89934795043169462118838037)
              ·
                refine ⟨4215693517648568536820533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89934795043169462118838037 4215693517648568536820533)
                ·
                  refine ⟨395221267279553300326925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4215693517648568536820533 395221267279553300326925)
                  ·
                    rfl

theorem cell22_3463608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_3463608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463608 prefixEnd_3463608 := by exact prefixLift 3463608
  have htrace : WordTrace (prefixWord ++ tailWord_3463608) baseStart_3463608 baseEnd_3463608 := by
    simpa [prefixWord, tailWord_3463608, baseEnd_3463608] using wordTrace_append hprefix tailTrace_3463608
  have hstable : (prefixWord ++ tailWord_3463608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463608).length < 2 ^ (prefixWord ++ tailWord_3463608).sum := by decide
  have hdescent : baseEnd_3463608 < baseStart_3463608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463612 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 3, 3]
def baseStart_3463612 : Nat := 118140960795 + 3463612 * 2 ^ 59
def prefixEnd_3463612 : Nat := 4983230072969 + 3 ^ 40 * 3463612 * 2
def baseEnd_3463612 : Nat := 1185665171120405223880763

theorem tailTrace_3463612 : CollatzResearch.WordTrace tailWord_3463612 prefixEnd_3463612 1185665171120405223880763 := by
  unfold tailWord_3463612
  simp only [CollatzResearch.WordTrace]
  refine ⟨63164153963966368339988545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84218871951955157786651393 63164153963966368339988545)
  ·
    refine ⟨47373115472974776254991409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63164153963966368339988545 47373115472974776254991409)
    ·
      refine ⟨35529836604731082191243557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47373115472974776254991409 35529836604731082191243557)
      ·
        refine ⟨6661844363387077910858167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35529836604731082191243557 6661844363387077910858167)
        ·
          refine ⟨9992766545080616866287251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6661844363387077910858167 9992766545080616866287251)
          ·
            refine ⟨14989149817620925299430877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9992766545080616866287251 14989149817620925299430877)
            ·
              refine ⟨5620931181607846987286579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14989149817620925299430877 5620931181607846987286579)
              ·
                refine ⟨8431396772411770480929869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620931181607846987286579 8431396772411770480929869)
                ·
                  refine ⟨3161773789654413930348701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8431396772411770480929869 3161773789654413930348701)
                  ·
                    refine ⟨1185665171120405223880763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161773789654413930348701 1185665171120405223880763)
                    ·
                      rfl

theorem cell22_3463612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_3463612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463612 prefixEnd_3463612 := by exact prefixLift 3463612
  have htrace : WordTrace (prefixWord ++ tailWord_3463612) baseStart_3463612 baseEnd_3463612 := by
    simpa [prefixWord, tailWord_3463612, baseEnd_3463612] using wordTrace_append hprefix tailTrace_3463612
  have hstable : (prefixWord ++ tailWord_3463612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463612).length < 2 ^ (prefixWord ++ tailWord_3463612).sum := by decide
  have hdescent : baseEnd_3463612 < baseStart_3463612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463625 : List Nat := [1, 2, 1, 1, 2, 1, 8, 1, 5]
def baseStart_3463625 : Nat := 118140960795 + 3463625 * 2 ^ 59
def prefixEnd_3463625 : Nat := 4983230072969 + 3 ^ 40 * 3463625 * 2
def baseEnd_3463625 : Nat := 395223207095359174435241

theorem tailTrace_3463625 : CollatzResearch.WordTrace tailWord_3463625 prefixEnd_3463625 395223207095359174435241 := by
  unfold tailWord_3463625
  simp only [CollatzResearch.WordTrace]
  refine ⟨126328782076885639900200329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84219188051257093266800219 126328782076885639900200329)
  ·
    refine ⟨94746586557664229925150247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126328782076885639900200329 94746586557664229925150247)
    ·
      refine ⟨142119879836496344887725371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94746586557664229925150247 142119879836496344887725371)
      ·
        refine ⟨213179819754744517331588057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142119879836496344887725371 213179819754744517331588057)
        ·
          refine ⟨159884864816058387998691043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213179819754744517331588057 159884864816058387998691043)
          ·
            refine ⟨239827297224087581998036565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159884864816058387998691043 239827297224087581998036565)
            ·
              refine ⟨2810476139344776351539491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 239827297224087581998036565 2810476139344776351539491)
              ·
                refine ⟨4215714209017164527309237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810476139344776351539491 4215714209017164527309237)
                ·
                  refine ⟨395223207095359174435241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4215714209017164527309237 395223207095359174435241)
                  ·
                    rfl

theorem cell22_3463625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 5].length) (baseStart_3463625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463625 prefixEnd_3463625 := by exact prefixLift 3463625
  have htrace : WordTrace (prefixWord ++ tailWord_3463625) baseStart_3463625 baseEnd_3463625 := by
    simpa [prefixWord, tailWord_3463625, baseEnd_3463625] using wordTrace_append hprefix tailTrace_3463625
  have hstable : (prefixWord ++ tailWord_3463625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463625).length < 2 ^ (prefixWord ++ tailWord_3463625).sum := by decide
  have hdescent : baseEnd_3463625 < baseStart_3463625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463670 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_3463670 : Nat := 118140960795 + 3463670 * 2 ^ 59
def prefixEnd_3463670 : Nat := 4983230072969 + 3 ^ 40 * 3463670 * 2
def baseEnd_3463670 : Nat := 395228341901904135310195

theorem tailTrace_3463670 : CollatzResearch.WordTrace tailWord_3463670 prefixEnd_3463670 395228341901904135310195 := by
  unfold tailWord_3463670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7895651460107663286599279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84220282241148408390392309 7895651460107663286599279)
  ·
    refine ⟨11843477190161494929898919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7895651460107663286599279 11843477190161494929898919)
    ·
      refine ⟨17765215785242242394848379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11843477190161494929898919 17765215785242242394848379)
      ·
        refine ⟨26647823677863363592272569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17765215785242242394848379 26647823677863363592272569)
        ·
          refine ⟨19985867758397522694204427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26647823677863363592272569 19985867758397522694204427)
          ·
            refine ⟨29978801637596284041306641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19985867758397522694204427 29978801637596284041306641)
            ·
              refine ⟨22484101228197213030979981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29978801637596284041306641 22484101228197213030979981)
              ·
                refine ⟨8431537960573954886617493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22484101228197213030979981 8431537960573954886617493)
                ·
                  refine ⟨395228341901904135310195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8431537960573954886617493 395228341901904135310195)
                  ·
                    rfl

theorem cell22_3463670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_3463670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463670 prefixEnd_3463670 := by exact prefixLift 3463670
  have htrace : WordTrace (prefixWord ++ tailWord_3463670) baseStart_3463670 baseEnd_3463670 := by
    simpa [prefixWord, tailWord_3463670, baseEnd_3463670] using wordTrace_append hprefix tailTrace_3463670
  have hstable : (prefixWord ++ tailWord_3463670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463670).length < 2 ^ (prefixWord ++ tailWord_3463670).sum := by decide
  have hdescent : baseEnd_3463670 < baseStart_3463670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463683 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 1, 6]
def baseStart_3463683 : Nat := 118140960795 + 3463683 * 2 ^ 59
def prefixEnd_3463683 : Nat := 4983230072969 + 3 ^ 40 * 3463683 * 2
def baseEnd_3463683 : Nat := 1185689475871384705355545

theorem tailTrace_3463683 : CollatzResearch.WordTrace tailWord_3463683 prefixEnd_3463683 1185689475871384705355545 := by
  unfold tailWord_3463683
  simp only [CollatzResearch.WordTrace]
  refine ⟨126330897510675515805811703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84220598340450343870541135 126330897510675515805811703)
  ·
    refine ⟨189496346266013273708717555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126330897510675515805811703 189496346266013273708717555)
    ·
      refine ⟨284244519399019910563076333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189496346266013273708717555 284244519399019910563076333)
      ·
        refine ⟨106591694774632466461153625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284244519399019910563076333 106591694774632466461153625)
        ·
          refine ⟨79943771080974349845865219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106591694774632466461153625 79943771080974349845865219)
          ·
            refine ⟨119915656621461524768797829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79943771080974349845865219 119915656621461524768797829)
            ·
              refine ⟨22484185616524035894149593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119915656621461524768797829 22484185616524035894149593)
              ·
                refine ⟨16863139212393026920612195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22484185616524035894149593 16863139212393026920612195)
                ·
                  refine ⟨25294708818589540380918293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16863139212393026920612195 25294708818589540380918293)
                  ·
                    refine ⟨1185689475871384705355545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25294708818589540380918293 1185689475871384705355545)
                    ·
                      rfl

theorem cell22_3463683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_3463683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463683 prefixEnd_3463683 := by exact prefixLift 3463683
  have htrace : WordTrace (prefixWord ++ tailWord_3463683) baseStart_3463683 baseEnd_3463683 := by
    simpa [prefixWord, tailWord_3463683, baseEnd_3463683] using wordTrace_append hprefix tailTrace_3463683
  have hstable : (prefixWord ++ tailWord_3463683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463683).length < 2 ^ (prefixWord ++ tailWord_3463683).sum := by decide
  have hdescent : baseEnd_3463683 < baseStart_3463683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463728 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 1, 8]
def baseStart_3463728 : Nat := 118140960795 + 3463728 * 2 ^ 59
def prefixEnd_3463728 : Nat := 4983230072969 + 3 ^ 40 * 3463728 * 2
def baseEnd_3463728 : Nat := 1185704880291019587980407

theorem tailTrace_3463728 : CollatzResearch.WordTrace tailWord_3463728 prefixEnd_3463728 1185704880291019587980407 := by
  unfold tailWord_3463728
  simp only [CollatzResearch.WordTrace]
  refine ⟨63166269397756244245599919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84221692530341658994133225 63166269397756244245599919)
  ·
    refine ⟨94749404096634366368399879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63166269397756244245599919 94749404096634366368399879)
    ·
      refine ⟨142124106144951549552599819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94749404096634366368399879 142124106144951549552599819)
      ·
        refine ⟨213186159217427324328899729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142124106144951549552599819 213186159217427324328899729)
        ·
          refine ⟨159889619413070493246674797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213186159217427324328899729 159889619413070493246674797)
          ·
            refine ⟨59958607279901434967503049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159889619413070493246674797 59958607279901434967503049)
            ·
              refine ⟨44968955459926076225627287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59958607279901434967503049 44968955459926076225627287)
              ·
                refine ⟨67453433189889114338440931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44968955459926076225627287 67453433189889114338440931)
                ·
                  refine ⟨101180149784833671507661397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67453433189889114338440931 101180149784833671507661397)
                  ·
                    refine ⟨1185704880291019587980407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101180149784833671507661397 1185704880291019587980407)
                    ·
                      rfl

theorem cell22_3463728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_3463728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463728 prefixEnd_3463728 := by exact prefixLift 3463728
  have htrace : WordTrace (prefixWord ++ tailWord_3463728) baseStart_3463728 baseEnd_3463728 := by
    simpa [prefixWord, tailWord_3463728, baseEnd_3463728] using wordTrace_append hprefix tailTrace_3463728
  have hstable : (prefixWord ++ tailWord_3463728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463728).length < 2 ^ (prefixWord ++ tailWord_3463728).sum := by decide
  have hdescent : baseEnd_3463728 < baseStart_3463728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463781 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 3, 3]
def baseStart_3463781 : Nat := 118140960795 + 3463781 * 2 ^ 59
def prefixEnd_3463781 : Nat := 4983230072969 + 3 ^ 40 * 3463781 * 2
def baseEnd_3463781 : Nat := 1185723023274145116405245

theorem tailTrace_3463781 : CollatzResearch.WordTrace tailWord_3463781 prefixEnd_3463781 1185723023274145116405245 := by
  unfold tailWord_3463781
  simp only [CollatzResearch.WordTrace]
  refine ⟨126334471864320478542879197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84222981242880319028586131 126334471864320478542879197)
  ·
    refine ⟨47375426949120179453579699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126334471864320478542879197 47375426949120179453579699)
    ·
      refine ⟨71063140423680269180369549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47375426949120179453579699 71063140423680269180369549)
      ·
        refine ⟨26648677658880100942638581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71063140423680269180369549 26648677658880100942638581)
        ·
          refine ⟨2498313530520009463372367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26648677658880100942638581 2498313530520009463372367)
          ·
            refine ⟨3747470295780014195058551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498313530520009463372367 3747470295780014195058551)
            ·
              refine ⟨5621205443670021292587827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3747470295780014195058551 5621205443670021292587827)
              ·
                refine ⟨8431808165505031938881741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5621205443670021292587827 8431808165505031938881741)
                ·
                  refine ⟨3161928062064386977080653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8431808165505031938881741 3161928062064386977080653)
                  ·
                    refine ⟨1185723023274145116405245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161928062064386977080653 1185723023274145116405245)
                    ·
                      rfl

theorem cell22_3463781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_3463781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463781 prefixEnd_3463781 := by exact prefixLift 3463781
  have htrace : WordTrace (prefixWord ++ tailWord_3463781) baseStart_3463781 baseEnd_3463781 := by
    simpa [prefixWord, tailWord_3463781, baseEnd_3463781] using wordTrace_append hprefix tailTrace_3463781
  have hstable : (prefixWord ++ tailWord_3463781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463781).length < 2 ^ (prefixWord ++ tailWord_3463781).sum := by decide
  have hdescent : baseEnd_3463781 < baseStart_3463781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463837 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_3463837 : Nat := 118140960795 + 3463837 * 2 ^ 59
def prefixEnd_3463837 : Nat := 4983230072969 + 3 ^ 40 * 3463837 * 2
def baseEnd_3463837 : Nat := 1185742193218579637005073

theorem tailTrace_3463837 : CollatzResearch.WordTrace tailWord_3463837 prefixEnd_3463837 1185742193218579637005073 := by
  unfold tailWord_3463837
  simp only [CollatzResearch.WordTrace]
  refine ⟨126336514352117600106917765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84224342901411733404611843 126336514352117600106917765)
  ·
    refine ⟨23688096441022050020047081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126336514352117600106917765 23688096441022050020047081)
    ·
      refine ⟨17766072330766537515035311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23688096441022050020047081 17766072330766537515035311)
      ·
        refine ⟨26649108496149806272552967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17766072330766537515035311 26649108496149806272552967)
        ·
          refine ⟨39973662744224709408829451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26649108496149806272552967 39973662744224709408829451)
          ·
            refine ⟨59960494116337064113244177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39973662744224709408829451 59960494116337064113244177)
            ·
              refine ⟨44970370587252798084933133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59960494116337064113244177 44970370587252798084933133)
              ·
                refine ⟨16863888970219799281849925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44970370587252798084933133 16863888970219799281849925)
                ·
                  refine ⟨3161979181916212365346861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16863888970219799281849925 3161979181916212365346861)
                  ·
                    refine ⟨1185742193218579637005073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161979181916212365346861 1185742193218579637005073)
                    ·
                      rfl

theorem cell22_3463837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_3463837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463837 prefixEnd_3463837 := by exact prefixLift 3463837
  have htrace : WordTrace (prefixWord ++ tailWord_3463837) baseStart_3463837 baseEnd_3463837 := by
    simpa [prefixWord, tailWord_3463837, baseEnd_3463837] using wordTrace_append hprefix tailTrace_3463837
  have hstable : (prefixWord ++ tailWord_3463837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463837).length < 2 ^ (prefixWord ++ tailWord_3463837).sum := by decide
  have hdescent : baseEnd_3463837 < baseStart_3463837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463854 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3463854 : Nat := 118140960795 + 3463854 * 2 ^ 59
def prefixEnd_3463854 : Nat := 4983230072969 + 3 ^ 40 * 3463854 * 2
def baseEnd_3463854 : Nat := 1185748012665997259330021

theorem tailTrace_3463854 : CollatzResearch.WordTrace tailWord_3463854 prefixEnd_3463854 1185748012665997259330021 := by
  unfold tailWord_3463854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15792141799132001501285827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84224756262037341340191077 15792141799132001501285827)
  ·
    refine ⟨23688212698698002251928741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15792141799132001501285827 23688212698698002251928741)
    ·
      refine ⟨4441539881005875422236639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23688212698698002251928741 4441539881005875422236639)
      ·
        refine ⟨6662309821508813133354959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4441539881005875422236639 6662309821508813133354959)
        ·
          refine ⟨9993464732263219700032439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6662309821508813133354959 9993464732263219700032439)
          ·
            refine ⟨14990197098394829550048659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9993464732263219700032439 14990197098394829550048659)
            ·
              refine ⟨22485295647592244325072989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14990197098394829550048659 22485295647592244325072989)
              ·
                refine ⟨8431985867847091621902371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22485295647592244325072989 8431985867847091621902371)
                ·
                  refine ⟨12647978801770637432853557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8431985867847091621902371 12647978801770637432853557)
                  ·
                    refine ⟨1185748012665997259330021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12647978801770637432853557 1185748012665997259330021)
                    ·
                      rfl

theorem cell22_3463854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3463854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463854 prefixEnd_3463854 := by exact prefixLift 3463854
  have htrace : WordTrace (prefixWord ++ tailWord_3463854) baseStart_3463854 baseEnd_3463854 := by
    simpa [prefixWord, tailWord_3463854, baseEnd_3463854] using wordTrace_append hprefix tailTrace_3463854
  have hstable : (prefixWord ++ tailWord_3463854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463854).length < 2 ^ (prefixWord ++ tailWord_3463854).sum := by decide
  have hdescent : baseEnd_3463854 < baseStart_3463854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463869 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_3463869 : Nat := 118140960795 + 3463869 * 2 ^ 59
def prefixEnd_3463869 : Nat := 4983230072969 + 3 ^ 40 * 3463869 * 2
def baseEnd_3463869 : Nat := 1185753147472542220204975

theorem tailTrace_3463869 : CollatzResearch.WordTrace tailWord_3463869 prefixEnd_3463869 1185753147472542220204975 := by
  unfold tailWord_3463869
  simp only [CollatzResearch.WordTrace]
  refine ⟨126337681488001669572082661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84225120992001113048055107 126337681488001669572082661)
  ·
    refine ⟨23688315279000313044765499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126337681488001669572082661 23688315279000313044765499)
    ·
      refine ⟨35532472918500469567148249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23688315279000313044765499 35532472918500469567148249)
      ·
        refine ⟨26649354688875352175361187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35532472918500469567148249 26649354688875352175361187)
        ·
          refine ⟨39974032033313028263041781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26649354688875352175361187 39974032033313028263041781)
          ·
            refine ⟨3747565503123096399660167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39974032033313028263041781 3747565503123096399660167)
            ·
              refine ⟨5621348254684644599490251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3747565503123096399660167 5621348254684644599490251)
              ·
                refine ⟨8432022382026966899235377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5621348254684644599490251 8432022382026966899235377)
                ·
                  refine ⟨6324016786520225174426533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8432022382026966899235377 6324016786520225174426533)
                  ·
                    refine ⟨1185753147472542220204975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6324016786520225174426533 1185753147472542220204975)
                    ·
                      rfl

theorem cell22_3463869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_3463869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463869 prefixEnd_3463869 := by exact prefixLift 3463869
  have htrace : WordTrace (prefixWord ++ tailWord_3463869) baseStart_3463869 baseEnd_3463869 := by
    simpa [prefixWord, tailWord_3463869, baseEnd_3463869] using wordTrace_append hprefix tailTrace_3463869
  have hstable : (prefixWord ++ tailWord_3463869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463869).length < 2 ^ (prefixWord ++ tailWord_3463869).sum := by decide
  have hdescent : baseEnd_3463869 < baseStart_3463869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463873 : List Nat := [1, 2, 6, 2, 1, 1, 2, 3, 4]
def baseStart_3463873 : Nat := 118140960795 + 3463873 * 2 ^ 59
def prefixEnd_3463873 : Nat := 4983230072969 + 3 ^ 40 * 3463873 * 2
def baseEnd_3463873 : Nat := 395251505584762514368321

theorem tailTrace_3463873 : CollatzResearch.WordTrace tailWord_3463873 prefixEnd_3463873 395251505584762514368321 := by
  unfold tailWord_3463873
  simp only [CollatzResearch.WordTrace]
  refine ⟨126337827379987178255228273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84225218253324785503485515 126337827379987178255228273)
  ·
    refine ⟨94753370534990383691421205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126337827379987178255228273 94753370534990383691421205)
    ·
      refine ⟨4441564243827674235535369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94753370534990383691421205 4441564243827674235535369)
      ·
        refine ⟨3331173182870755676651527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4441564243827674235535369 3331173182870755676651527)
        ·
          refine ⟨4996759774306133514977291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331173182870755676651527 4996759774306133514977291)
          ·
            refine ⟨7495139661459200272465937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4996759774306133514977291 7495139661459200272465937)
            ·
              refine ⟨5621354746094400204349453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7495139661459200272465937 5621354746094400204349453)
              ·
                refine ⟨2108008029785400076631045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5621354746094400204349453 2108008029785400076631045)
                ·
                  refine ⟨395251505584762514368321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2108008029785400076631045 395251505584762514368321)
                  ·
                    rfl

theorem cell22_3463873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 4].length) (baseStart_3463873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463873 prefixEnd_3463873 := by exact prefixLift 3463873
  have htrace : WordTrace (prefixWord ++ tailWord_3463873) baseStart_3463873 baseEnd_3463873 := by
    simpa [prefixWord, tailWord_3463873, baseEnd_3463873] using wordTrace_append hprefix tailTrace_3463873
  have hstable : (prefixWord ++ tailWord_3463873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463873).length < 2 ^ (prefixWord ++ tailWord_3463873).sum := by decide
  have hdescent : baseEnd_3463873 < baseStart_3463873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463989 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3463989 : Nat := 118140960795 + 3463989 * 2 ^ 59
def prefixEnd_3463989 : Nat := 4983230072969 + 3 ^ 40 * 3463989 * 2
def baseEnd_3463989 : Nat := 1185794225924901907204607

theorem tailTrace_3463989 : CollatzResearch.WordTrace tailWord_3463989 prefixEnd_3463989 1185794225924901907204607 := by
  unfold tailWord_3463989
  simp only [CollatzResearch.WordTrace]
  refine ⟨126342058247566930066451021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84228038831711286710967347 126342058247566930066451021)
  ·
    refine ⟨47378271842837598774919133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126342058247566930066451021 47378271842837598774919133)
    ·
      refine ⟨17766851941064099540594675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47378271842837598774919133 17766851941064099540594675)
      ·
        refine ⟨26650277911596149310892013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17766851941064099540594675 26650277911596149310892013)
        ·
          refine ⟨9993854216848555991584505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26650277911596149310892013 9993854216848555991584505)
          ·
            refine ⟨7495390662636416993688379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9993854216848555991584505 7495390662636416993688379)
            ·
              refine ⟨11243085993954625490532569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7495390662636416993688379 11243085993954625490532569)
              ·
                refine ⟨8432314495465969117899427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11243085993954625490532569 8432314495465969117899427)
                ·
                  refine ⟨12648471743198953676849141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8432314495465969117899427 12648471743198953676849141)
                  ·
                    refine ⟨1185794225924901907204607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12648471743198953676849141 1185794225924901907204607)
                    ·
                      rfl

theorem cell22_3463989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3463989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3463989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3463989 prefixEnd_3463989 := by exact prefixLift 3463989
  have htrace : WordTrace (prefixWord ++ tailWord_3463989) baseStart_3463989 baseEnd_3463989 := by
    simpa [prefixWord, tailWord_3463989, baseEnd_3463989] using wordTrace_append hprefix tailTrace_3463989
  have hstable : (prefixWord ++ tailWord_3463989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463989).length < 2 ^ (prefixWord ++ tailWord_3463989).sum := by decide
  have hdescent : baseEnd_3463989 < baseStart_3463989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464032 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 2, 6]
def baseStart_3464032 : Nat := 118140960795 + 3464032 * 2 ^ 59
def prefixEnd_3464032 : Nat := 4983230072969 + 3 ^ 40 * 3464032 * 2
def baseEnd_3464032 : Nat := 1185808945703664128379475

theorem tailTrace_3464032 : CollatzResearch.WordTrace tailWord_3464032 prefixEnd_3464032 1185808945703664128379475 := by
  unfold tailWord_3464032
  simp only [CollatzResearch.WordTrace]
  refine ⟨63171813293205574205133175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84229084390940765606844233 63171813293205574205133175)
  ·
    refine ⟨94757719939808361307699763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63171813293205574205133175 94757719939808361307699763)
    ·
      refine ⟨142136579909712541961549645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94757719939808361307699763 142136579909712541961549645)
      ·
        refine ⟨53301217466142203235581117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142136579909712541961549645 53301217466142203235581117)
        ·
          refine ⟨19987956549803326213342919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53301217466142203235581117 19987956549803326213342919)
          ·
            refine ⟨29981934824704989320014379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19987956549803326213342919 29981934824704989320014379)
            ·
              refine ⟨44972902237057483980021569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29981934824704989320014379 44972902237057483980021569)
              ·
                refine ⟨33729676677793112985016177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44972902237057483980021569 33729676677793112985016177)
                ·
                  refine ⟨25297257508344834738762133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33729676677793112985016177 25297257508344834738762133)
                  ·
                    refine ⟨1185808945703664128379475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25297257508344834738762133 1185808945703664128379475)
                    ·
                      rfl

theorem cell22_3464032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_3464032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464032 prefixEnd_3464032 := by exact prefixLift 3464032
  have htrace : WordTrace (prefixWord ++ tailWord_3464032) baseStart_3464032 baseEnd_3464032 := by
    simpa [prefixWord, tailWord_3464032, baseEnd_3464032] using wordTrace_append hprefix tailTrace_3464032
  have hstable : (prefixWord ++ tailWord_3464032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464032).length < 2 ^ (prefixWord ++ tailWord_3464032).sum := by decide
  have hdescent : baseEnd_3464032 < baseStart_3464032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464051 : List Nat := [1, 1, 1, 2, 2, 1, 5, 5, 1, 3]
def baseStart_3464051 : Nat := 118140960795 + 3464051 * 2 ^ 59
def prefixEnd_3464051 : Nat := 4983230072969 + 3 ^ 40 * 3464051 * 2
def baseEnd_3464051 : Nat := 1185815449791954412154417

theorem tailTrace_3464051 : CollatzResearch.WordTrace tailWord_3464051 prefixEnd_3464051 1185815449791954412154417 := by
  unfold tailWord_3464051
  simp only [CollatzResearch.WordTrace]
  refine ⟨126344319573342314655208007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84229546382228209770138671 126344319573342314655208007)
  ·
    refine ⟨189516479360013471982812011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126344319573342314655208007 189516479360013471982812011)
    ·
      refine ⟨284274719040020207974218017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189516479360013471982812011 284274719040020207974218017)
      ·
        refine ⟨213206039280015155980663513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284274719040020207974218017 213206039280015155980663513)
        ·
          refine ⟨159904529460011366985497635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213206039280015155980663513 159904529460011366985497635)
          ·
            refine ⟨239856794190017050478246453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159904529460011366985497635 239856794190017050478246453)
            ·
              refine ⟨22486574455314098482335605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239856794190017050478246453 22486574455314098482335605)
              ·
                refine ⟨2108116355185696732718963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22486574455314098482335605 2108116355185696732718963)
                ·
                  refine ⟨3162174532778545099078445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108116355185696732718963 3162174532778545099078445)
                  ·
                    refine ⟨1185815449791954412154417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162174532778545099078445 1185815449791954412154417)
                    ·
                      rfl

theorem cell22_3464051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 1, 3].length) (baseStart_3464051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464051 prefixEnd_3464051 := by exact prefixLift 3464051
  have htrace : WordTrace (prefixWord ++ tailWord_3464051) baseStart_3464051 baseEnd_3464051 := by
    simpa [prefixWord, tailWord_3464051, baseEnd_3464051] using wordTrace_append hprefix tailTrace_3464051
  have hstable : (prefixWord ++ tailWord_3464051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464051).length < 2 ^ (prefixWord ++ tailWord_3464051).sum := by decide
  have hdescent : baseEnd_3464051 < baseStart_3464051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464132 : List Nat := [2, 3, 3, 3, 2, 1, 2, 1, 5]
def baseStart_3464132 : Nat := 118140960795 + 3464132 * 2 ^ 59
def prefixEnd_3464132 : Nat := 4983230072969 + 3 ^ 40 * 3464132 * 2
def baseEnd_3464132 : Nat := 395281059249099066959723

theorem tailTrace_3464132 : CollatzResearch.WordTrace tailWord_3464132 prefixEnd_3464132 395281059249099066959723 := by
  unfold tailWord_3464132
  simp only [CollatzResearch.WordTrace]
  refine ⟨63173636943024432744453325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84231515924032576992604433 63173636943024432744453325)
  ·
    refine ⟨23690113853634162279169997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63173636943024432744453325 23690113853634162279169997)
    ·
      refine ⟨8883792695112810854688749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23690113853634162279169997 8883792695112810854688749)
      ·
        refine ⟨3331422260667304070508281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8883792695112810854688749 3331422260667304070508281)
        ·
          refine ⟨2498566695500478052881211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3331422260667304070508281 2498566695500478052881211)
          ·
            refine ⟨3747850043250717079321817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498566695500478052881211 3747850043250717079321817)
            ·
              refine ⟨2810887532438037809491363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3747850043250717079321817 2810887532438037809491363)
              ·
                refine ⟨4216331298657056714237045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810887532438037809491363 4216331298657056714237045)
                ·
                  refine ⟨395281059249099066959723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4216331298657056714237045 395281059249099066959723)
                  ·
                    rfl

theorem cell22_3464132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_3464132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464132 prefixEnd_3464132 := by exact prefixLift 3464132
  have htrace : WordTrace (prefixWord ++ tailWord_3464132) baseStart_3464132 baseEnd_3464132 := by
    simpa [prefixWord, tailWord_3464132, baseEnd_3464132] using wordTrace_append hprefix tailTrace_3464132
  have hstable : (prefixWord ++ tailWord_3464132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464132).length < 2 ^ (prefixWord ++ tailWord_3464132).sum := by decide
  have hdescent : baseEnd_3464132 < baseStart_3464132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464154 : List Nat := [3, 1, 1, 2, 4, 1, 2, 8]
def baseStart_3464154 : Nat := 118140960795 + 3464154 * 2 ^ 59
def prefixEnd_3464154 : Nat := 4983230072969 + 3 ^ 40 * 3464154 * 2
def baseEnd_3464154 : Nat := 131761189866321830758789

theorem tailTrace_3464154 : CollatzResearch.WordTrace tailWord_3464154 prefixEnd_3464154 131761189866321830758789 := by
  unfold tailWord_3464154
  simp only [CollatzResearch.WordTrace]
  refine ⟨31587019072992290811551879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84232050861312775497471677 31587019072992290811551879)
  ·
    refine ⟨47380528609488436217327819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31587019072992290811551879 47380528609488436217327819)
    ·
      refine ⟨71070792914232654325991729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47380528609488436217327819 71070792914232654325991729)
      ·
        refine ⟨53303094685674490744493797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71070792914232654325991729 53303094685674490744493797)
        ·
          refine ⟨9994330253563967014592587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53303094685674490744493797 9994330253563967014592587)
          ·
            refine ⟨14991495380345950521888881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9994330253563967014592587 14991495380345950521888881)
            ·
              refine ⟨11243621535259462891416661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14991495380345950521888881 11243621535259462891416661)
              ·
                refine ⟨131761189866321830758789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11243621535259462891416661 131761189866321830758789)
                ·
                  rfl

theorem cell22_3464154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_3464154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464154 prefixEnd_3464154 := by exact prefixLift 3464154
  have htrace : WordTrace (prefixWord ++ tailWord_3464154) baseStart_3464154 baseEnd_3464154 := by
    simpa [prefixWord, tailWord_3464154, baseEnd_3464154] using wordTrace_append hprefix tailTrace_3464154
  have hstable : (prefixWord ++ tailWord_3464154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464154).length < 2 ^ (prefixWord ++ tailWord_3464154).sum := by decide
  have hdescent : baseEnd_3464154 < baseStart_3464154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464263 : List Nat := [1, 1, 4, 1, 3, 3, 2, 2, 1, 4]
def baseStart_3464263 : Nat := 118140960795 + 3464263 * 2 ^ 59
def prefixEnd_3464263 : Nat := 4983230072969 + 3 ^ 40 * 3464263 * 2
def baseEnd_3464263 : Nat := 1185888021724456525853767

theorem tailTrace_3464263 : CollatzResearch.WordTrace tailWord_3464263 prefixEnd_3464263 1185888021724456525853767 := by
  unfold tailWord_3464263
  simp only [CollatzResearch.WordTrace]
  refine ⟨126352051848574274861925443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84234701232382849907950295 126352051848574274861925443)
  ·
    refine ⟨189528077772861412292888165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126352051848574274861925443 189528077772861412292888165)
    ·
      refine ⟨35536514582411514804916531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189528077772861412292888165 35536514582411514804916531)
      ·
        refine ⟨53304771873617272207374797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35536514582411514804916531 53304771873617272207374797)
        ·
          refine ⟨19989289452606477077765549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53304771873617272207374797 19989289452606477077765549)
          ·
            refine ⟨7495983544727428904162081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19989289452606477077765549 7495983544727428904162081)
            ·
              refine ⟨5621987658545571678121561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7495983544727428904162081 5621987658545571678121561)
              ·
                refine ⟨4216490743909178758591171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5621987658545571678121561 4216490743909178758591171)
                ·
                  refine ⟨6324736115863768137886757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216490743909178758591171 6324736115863768137886757)
                  ·
                    refine ⟨1185888021724456525853767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6324736115863768137886757 1185888021724456525853767)
                    ·
                      rfl

theorem cell22_3464263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_3464263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464263 prefixEnd_3464263 := by exact prefixLift 3464263
  have htrace : WordTrace (prefixWord ++ tailWord_3464263) baseStart_3464263 baseEnd_3464263 := by
    simpa [prefixWord, tailWord_3464263, baseEnd_3464263] using wordTrace_append hprefix tailTrace_3464263
  have hstable : (prefixWord ++ tailWord_3464263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464263).length < 2 ^ (prefixWord ++ tailWord_3464263).sum := by decide
  have hdescent : baseEnd_3464263 < baseStart_3464263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464276 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3464276 : Nat := 118140960795 + 3464276 * 2 ^ 59
def prefixEnd_3464276 : Nat := 4983230072969 + 3 ^ 40 * 3464276 * 2
def baseEnd_3464276 : Nat := 1185892471890128825278727

theorem tailTrace_3464276 : CollatzResearch.WordTrace tailWord_3464276 prefixEnd_3464276 1185892471890128825278727 := by
  unfold tailWord_3464276
  simp only [CollatzResearch.WordTrace]
  refine ⟨63176262998763589041074341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84235017331684785388099121 63176262998763589041074341)
  ·
    refine ⟨11845549312268172945201439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63176262998763589041074341 11845549312268172945201439)
    ·
      refine ⟨17768323968402259417802159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11845549312268172945201439 17768323968402259417802159)
      ·
        refine ⟨26652485952603389126703239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17768323968402259417802159 26652485952603389126703239)
        ·
          refine ⟨39978728928905083690054859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26652485952603389126703239 39978728928905083690054859)
          ·
            refine ⟨59968093393357625535082289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39978728928905083690054859 59968093393357625535082289)
            ·
              refine ⟨44976070045018219151311717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59968093393357625535082289 44976070045018219151311717)
              ·
                refine ⟨8433013133440916090870947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44976070045018219151311717 8433013133440916090870947)
                ·
                  refine ⟨12649519700161374136306421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8433013133440916090870947 12649519700161374136306421)
                  ·
                    refine ⟨1185892471890128825278727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12649519700161374136306421 1185892471890128825278727)
                    ·
                      rfl

theorem cell22_3464276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3464276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464276 prefixEnd_3464276 := by exact prefixLift 3464276
  have htrace : WordTrace (prefixWord ++ tailWord_3464276) baseStart_3464276 baseEnd_3464276 := by
    simpa [prefixWord, tailWord_3464276, baseEnd_3464276] using wordTrace_append hprefix tailTrace_3464276
  have hstable : (prefixWord ++ tailWord_3464276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464276).length < 2 ^ (prefixWord ++ tailWord_3464276).sum := by decide
  have hdescent : baseEnd_3464276 < baseStart_3464276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464289 : List Nat := [1, 2, 3, 1, 1, 2, 12]
def baseStart_3464289 : Nat := 118140960795 + 3464289 * 2 ^ 59
def prefixEnd_3464289 : Nat := 4983230072969 + 3 ^ 40 * 3464289 * 2
def baseEnd_3464289 : Nat := 43922108224288930544581

theorem tailTrace_3464289 : CollatzResearch.WordTrace tailWord_3464289 prefixEnd_3464289 43922108224288930544581 := by
  unfold tailWord_3464289
  simp only [CollatzResearch.WordTrace]
  refine ⟨126353000146480081302371921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84235333430986720868247947 126353000146480081302371921)
  ·
    refine ⟨94764750109860060976778941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126353000146480081302371921 94764750109860060976778941)
    ·
      refine ⟨35536781291197522866292103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94764750109860060976778941 35536781291197522866292103)
      ·
        refine ⟨53305171936796284299438155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35536781291197522866292103 53305171936796284299438155)
        ·
          refine ⟨79957757905194426449157233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53305171936796284299438155 79957757905194426449157233)
          ·
            refine ⟨59968318428895819836867925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79957757905194426449157233 59968318428895819836867925)
            ·
              refine ⟨43922108224288930544581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 59968318428895819836867925 43922108224288930544581)
              ·
                rfl

theorem cell22_3464289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 12].length) (baseStart_3464289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464289 prefixEnd_3464289 := by exact prefixLift 3464289
  have htrace : WordTrace (prefixWord ++ tailWord_3464289) baseStart_3464289 baseEnd_3464289 := by
    simpa [prefixWord, tailWord_3464289, baseEnd_3464289] using wordTrace_append hprefix tailTrace_3464289
  have hstable : (prefixWord ++ tailWord_3464289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464289).length < 2 ^ (prefixWord ++ tailWord_3464289).sum := by decide
  have hdescent : baseEnd_3464289 < baseStart_3464289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464293 : List Nat := [1, 3, 1, 3, 2, 1, 2, 4, 2, 3]
def baseStart_3464293 : Nat := 118140960795 + 3464293 * 2 ^ 59
def prefixEnd_3464293 : Nat := 4983230072969 + 3 ^ 40 * 3464293 * 2
def baseEnd_3464293 : Nat := 1185898291337546447603675

theorem tailTrace_3464293 : CollatzResearch.WordTrace tailWord_3464293 prefixEnd_3464293 1185898291337546447603675 := by
  unfold tailWord_3464293
  simp only [CollatzResearch.WordTrace]
  refine ⟨126353146038465589985517533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84235430692310393323678355 126353146038465589985517533)
  ·
    refine ⟨47382429764424596244569075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126353146038465589985517533 47382429764424596244569075)
    ·
      refine ⟨71073644646636894366853613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47382429764424596244569075 71073644646636894366853613)
      ·
        refine ⟨26652616742488835387570105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71073644646636894366853613 26652616742488835387570105)
        ·
          refine ⟨19989462556866626540677579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26652616742488835387570105 19989462556866626540677579)
          ·
            refine ⟨29984193835299939811016369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19989462556866626540677579 29984193835299939811016369)
            ·
              refine ⟨22488145376474954858262277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29984193835299939811016369 22488145376474954858262277)
              ·
                refine ⟨4216527258089054035924177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22488145376474954858262277 4216527258089054035924177)
                ·
                  refine ⟨3162395443566790526943133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4216527258089054035924177 3162395443566790526943133)
                  ·
                    refine ⟨1185898291337546447603675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162395443566790526943133 1185898291337546447603675)
                    ·
                      rfl

theorem cell22_3464293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_3464293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464293 prefixEnd_3464293 := by exact prefixLift 3464293
  have htrace : WordTrace (prefixWord ++ tailWord_3464293) baseStart_3464293 baseEnd_3464293 := by
    simpa [prefixWord, tailWord_3464293, baseEnd_3464293] using wordTrace_append hprefix tailTrace_3464293
  have hstable : (prefixWord ++ tailWord_3464293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464293).length < 2 ^ (prefixWord ++ tailWord_3464293).sum := by decide
  have hdescent : baseEnd_3464293 < baseStart_3464293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464295 : List Nat := [1, 1, 5, 1, 1, 4, 3, 2, 4]
def baseStart_3464295 : Nat := 118140960795 + 3464295 * 2 ^ 59
def prefixEnd_3464295 : Nat := 4983230072969 + 3 ^ 40 * 3464295 * 2
def baseEnd_3464295 : Nat := 395299658659473036351223

theorem tailTrace_3464295 : CollatzResearch.WordTrace tailWord_3464295 prefixEnd_3464295 395299658659473036351223 := by
  unfold tailWord_3464295
  simp only [CollatzResearch.WordTrace]
  refine ⟨126353218984458344327090339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84235479322972229551393559 126353218984458344327090339)
  ·
    refine ⟨189529828476687516490635509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126353218984458344327090339 189529828476687516490635509)
    ·
      refine ⟨17768421419689454670997079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189529828476687516490635509 17768421419689454670997079)
      ·
        refine ⟨26652632129534182006495619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17768421419689454670997079 26652632129534182006495619)
        ·
          refine ⟨39978948194301273009743429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26652632129534182006495619 39978948194301273009743429)
          ·
            refine ⟨7496052786431488689326893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39978948194301273009743429 7496052786431488689326893)
            ·
              refine ⟨2811019794911808258497585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7496052786431488689326893 2811019794911808258497585)
              ·
                refine ⟨2108264846183856193873189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2811019794911808258497585 2108264846183856193873189)
                ·
                  refine ⟨395299658659473036351223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2108264846183856193873189 395299658659473036351223)
                  ·
                    rfl

theorem cell22_3464295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 4].length) (baseStart_3464295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464295 prefixEnd_3464295 := by exact prefixLift 3464295
  have htrace : WordTrace (prefixWord ++ tailWord_3464295) baseStart_3464295 baseEnd_3464295 := by
    simpa [prefixWord, tailWord_3464295, baseEnd_3464295] using wordTrace_append hprefix tailTrace_3464295
  have hstable : (prefixWord ++ tailWord_3464295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464295).length < 2 ^ (prefixWord ++ tailWord_3464295).sum := by decide
  have hdescent : baseEnd_3464295 < baseStart_3464295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464306 : List Nat := [3, 2, 1, 2, 2, 1, 4, 7]
def baseStart_3464306 : Nat := 118140960795 + 3464306 * 2 ^ 59
def prefixEnd_3464306 : Nat := 4983230072969 + 3 ^ 40 * 3464306 * 2
def baseEnd_3464306 : Nat := 131766971278135416336515

theorem tailTrace_3464306 : CollatzResearch.WordTrace tailWord_3464306 prefixEnd_3464306 131766971278135416336515 := by
  unfold tailWord_3464306
  simp only [CollatzResearch.WordTrace]
  refine ⟨31588405046854623301435193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84235746791612328803827181 31588405046854623301435193)
  ·
    refine ⟨23691303785140967476076395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31588405046854623301435193 23691303785140967476076395)
    ·
      refine ⟨35536955677711451214114593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23691303785140967476076395 35536955677711451214114593)
      ·
        refine ⟨26652716758283588410585945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35536955677711451214114593 26652716758283588410585945)
        ·
          refine ⟨19989537568712691307939459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26652716758283588410585945 19989537568712691307939459)
          ·
            refine ⟨29984306353069036961909189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19989537568712691307939459 29984306353069036961909189)
            ·
              refine ⟨5622057441200444430357973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29984306353069036961909189 5622057441200444430357973)
              ·
                refine ⟨131766971278135416336515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5622057441200444430357973 131766971278135416336515)
                ·
                  rfl

theorem cell22_3464306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_3464306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464306 prefixEnd_3464306 := by exact prefixLift 3464306
  have htrace : WordTrace (prefixWord ++ tailWord_3464306) baseStart_3464306 baseEnd_3464306 := by
    simpa [prefixWord, tailWord_3464306, baseEnd_3464306] using wordTrace_append hprefix tailTrace_3464306
  have hstable : (prefixWord ++ tailWord_3464306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464306).length < 2 ^ (prefixWord ++ tailWord_3464306).sum := by decide
  have hdescent : baseEnd_3464306 < baseStart_3464306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464310 : List Nat := [5, 1, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_3464310 : Nat := 118140960795 + 3464310 * 2 ^ 59
def prefixEnd_3464310 : Nat := 4983230072969 + 3 ^ 40 * 3464310 * 2
def baseEnd_3464310 : Nat := 1185904110784964069928623

theorem tailTrace_3464310 : CollatzResearch.WordTrace tailWord_3464310 prefixEnd_3464310 1185904110784964069928623 := by
  unfold tailWord_3464310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7897110379962750118055399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84235844052936001259257589 7897110379962750118055399)
  ·
    refine ⟨11845665569944125177083099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7897110379962750118055399 11845665569944125177083099)
    ·
      refine ⟨17768498354916187765624649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11845665569944125177083099 17768498354916187765624649)
      ·
        refine ⟨13326373766187140824218487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17768498354916187765624649 13326373766187140824218487)
        ·
          refine ⟨19989560649280711236327731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13326373766187140824218487 19989560649280711236327731)
          ·
            refine ⟨29984340973921066854491597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19989560649280711236327731 29984340973921066854491597)
            ·
              refine ⟨11244127865220400070434349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29984340973921066854491597 11244127865220400070434349)
              ·
                refine ⟨4216547949457650026412881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11244127865220400070434349 4216547949457650026412881)
                ·
                  refine ⟨3162410962093237519809661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4216547949457650026412881 3162410962093237519809661)
                  ·
                    refine ⟨1185904110784964069928623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162410962093237519809661 1185904110784964069928623)
                    ·
                      rfl

theorem cell22_3464310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_3464310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464310 prefixEnd_3464310 := by exact prefixLift 3464310
  have htrace : WordTrace (prefixWord ++ tailWord_3464310) baseStart_3464310 baseEnd_3464310 := by
    simpa [prefixWord, tailWord_3464310, baseEnd_3464310] using wordTrace_append hprefix tailTrace_3464310
  have hstable : (prefixWord ++ tailWord_3464310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464310).length < 2 ^ (prefixWord ++ tailWord_3464310).sum := by decide
  have hdescent : baseEnd_3464310 < baseStart_3464310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464428 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_3464428 : Nat := 118140960795 + 3464428 * 2 ^ 59
def prefixEnd_3464428 : Nat := 4983230072969 + 3 ^ 40 * 3464428 * 2
def baseEnd_3464428 : Nat := 1185944504596451095478261

theorem tailTrace_3464428 : CollatzResearch.WordTrace tailWord_3464428 prefixEnd_3464428 1185944504596451095478261 := by
  unfold tailWord_3464428
  simp only [CollatzResearch.WordTrace]
  refine ⟨63179034946488254020840969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84238713261984338694454625 63179034946488254020840969)
  ·
    refine ⟨47384276209866190515630727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63179034946488254020840969 47384276209866190515630727)
    ·
      refine ⟨71076414314799285773446091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47384276209866190515630727 71076414314799285773446091)
      ·
        refine ⟨106614621472198928660169137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71076414314799285773446091 106614621472198928660169137)
        ·
          refine ⟨79960966104149196495126853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106614621472198928660169137 79960966104149196495126853)
          ·
            refine ⟨14992681144527974342836285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79960966104149196495126853 14992681144527974342836285)
            ·
              refine ⟨5622255429197990378563607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14992681144527974342836285 5622255429197990378563607)
              ·
                refine ⟨8433383143796985567845411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622255429197990378563607 8433383143796985567845411)
                ·
                  refine ⟨12650074715695478351768117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8433383143796985567845411 12650074715695478351768117)
                  ·
                    refine ⟨1185944504596451095478261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12650074715695478351768117 1185944504596451095478261)
                    ·
                      rfl

theorem cell22_3464428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_3464428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464428 prefixEnd_3464428 := by exact prefixLift 3464428
  have htrace : WordTrace (prefixWord ++ tailWord_3464428) baseStart_3464428 baseEnd_3464428 := by
    simpa [prefixWord, tailWord_3464428, baseEnd_3464428] using wordTrace_append hprefix tailTrace_3464428
  have hstable : (prefixWord ++ tailWord_3464428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464428).length < 2 ^ (prefixWord ++ tailWord_3464428).sum := by decide
  have hdescent : baseEnd_3464428 < baseStart_3464428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464441 : List Nat := [1, 2, 1, 3, 1, 1, 5, 8]
def baseStart_3464441 : Nat := 118140960795 + 3464441 * 2 ^ 59
def prefixEnd_3464441 : Nat := 4983230072969 + 3 ^ 40 * 3464441 * 2
def baseEnd_3464441 : Nat := 131772106084680377211469

theorem tailTrace_3464441 : CollatzResearch.WordTrace tailWord_3464441 prefixEnd_3464441 131772106084680377211469 := by
  unfold tailWord_3464441
  simp only [CollatzResearch.WordTrace]
  refine ⟨126358544041929411261905177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84239029361286274174603451 126358544041929411261905177)
  ·
    refine ⟨94768908031447058446428883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126358544041929411261905177 94768908031447058446428883)
    ·
      refine ⟨142153362047170587669643325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94768908031447058446428883 142153362047170587669643325)
      ·
        refine ⟨53307510767688970376116247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142153362047170587669643325 53307510767688970376116247)
        ·
          refine ⟨79961266151533455564174371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53307510767688970376116247 79961266151533455564174371)
          ·
            refine ⟨119941899227300183346261557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79961266151533455564174371 119941899227300183346261557)
            ·
              refine ⟨11244553052559392188712021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119941899227300183346261557 11244553052559392188712021)
              ·
                refine ⟨131772106084680377211469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11244553052559392188712021 131772106084680377211469)
                ·
                  rfl

theorem cell22_3464441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 8].length) (baseStart_3464441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464441 prefixEnd_3464441 := by exact prefixLift 3464441
  have htrace : WordTrace (prefixWord ++ tailWord_3464441) baseStart_3464441 baseEnd_3464441 := by
    simpa [prefixWord, tailWord_3464441, baseEnd_3464441] using wordTrace_append hprefix tailTrace_3464441
  have hstable : (prefixWord ++ tailWord_3464441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464441).length < 2 ^ (prefixWord ++ tailWord_3464441).sum := by decide
  have hdescent : baseEnd_3464441 < baseStart_3464441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464479 : List Nat := [1, 1, 2, 4, 4, 2, 2, 1, 2, 3]
def baseStart_3464479 : Nat := 118140960795 + 3464479 * 2 ^ 59
def prefixEnd_3464479 : Nat := 4983230072969 + 3 ^ 40 * 3464479 * 2
def baseEnd_3464479 : Nat := 1185961962938703962453105

theorem tailTrace_3464479 : CollatzResearch.WordTrace tailWord_3464479 prefixEnd_3464479 1185961962938703962453105 := by
  unfold tailWord_3464479
  simp only [CollatzResearch.WordTrace]
  refine ⟨126359930015791743751788491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84239953343861162501192327 126359930015791743751788491)
  ·
    refine ⟨189539895023687615627682737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126359930015791743751788491 189539895023687615627682737)
    ·
      refine ⟨142154921267765711720762053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189539895023687615627682737 142154921267765711720762053)
      ·
        refine ⟨26654047737706070947642885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142154921267765711720762053 26654047737706070947642885)
        ·
          refine ⟨4997633950819888302683041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26654047737706070947642885 4997633950819888302683041)
          ·
            refine ⟨3748225463114916227012281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4997633950819888302683041 3748225463114916227012281)
            ·
              refine ⟨2811169097336187170259211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3748225463114916227012281 2811169097336187170259211)
              ·
                refine ⟨4216753646004280755388817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2811169097336187170259211 4216753646004280755388817)
                ·
                  refine ⟨3162565234503210566541613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4216753646004280755388817 3162565234503210566541613)
                  ·
                    refine ⟨1185961962938703962453105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162565234503210566541613 1185961962938703962453105)
                    ·
                      rfl

theorem cell22_3464479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 2, 3].length) (baseStart_3464479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464479 prefixEnd_3464479 := by exact prefixLift 3464479
  have htrace : WordTrace (prefixWord ++ tailWord_3464479) baseStart_3464479 baseEnd_3464479 := by
    simpa [prefixWord, tailWord_3464479, baseEnd_3464479] using wordTrace_append hprefix tailTrace_3464479
  have hstable : (prefixWord ++ tailWord_3464479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464479).length < 2 ^ (prefixWord ++ tailWord_3464479).sum := by decide
  have hdescent : baseEnd_3464479 < baseStart_3464479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464524 : List Nat := [2, 2, 1, 3, 2, 2, 4, 2, 1, 3]
def baseStart_3464524 : Nat := 118140960795 + 3464524 * 2 ^ 59
def prefixEnd_3464524 : Nat := 4983230072969 + 3 ^ 40 * 3464524 * 2
def baseEnd_3464524 : Nat := 1185977367358338845077967

theorem tailTrace_3464524 : CollatzResearch.WordTrace tailWord_3464524 prefixEnd_3464524 1185977367358338845077967 := by
  unfold tailWord_3464524
  simp only [CollatzResearch.WordTrace]
  refine ⟨63180785650314358218588313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84241047533752477624784417 63180785650314358218588313)
  ·
    refine ⟨47385589237735768663941235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63180785650314358218588313 47385589237735768663941235)
    ·
      refine ⟨71078383856603652995911853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47385589237735768663941235 71078383856603652995911853)
      ·
        refine ⟨26654393946226369873466945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71078383856603652995911853 26654393946226369873466945)
        ·
          refine ⟨19990795459669777405100209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26654393946226369873466945 19990795459669777405100209)
          ·
            refine ⟨14993096594752333053825157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19990795459669777405100209 14993096594752333053825157)
            ·
              refine ⟨2811205611516062447592217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14993096594752333053825157 2811205611516062447592217)
              ·
                refine ⟨2108404208637046835694163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2811205611516062447592217 2108404208637046835694163)
                ·
                  refine ⟨3162606312955570253541245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108404208637046835694163 3162606312955570253541245)
                  ·
                    refine ⟨1185977367358338845077967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162606312955570253541245 1185977367358338845077967)
                    ·
                      rfl

theorem cell22_3464524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_3464524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464524 prefixEnd_3464524 := by exact prefixLift 3464524
  have htrace : WordTrace (prefixWord ++ tailWord_3464524) baseStart_3464524 baseEnd_3464524 := by
    simpa [prefixWord, tailWord_3464524, baseEnd_3464524] using wordTrace_append hprefix tailTrace_3464524
  have hstable : (prefixWord ++ tailWord_3464524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464524).length < 2 ^ (prefixWord ++ tailWord_3464524).sum := by decide
  have hdescent : baseEnd_3464524 < baseStart_3464524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464541 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3464541 : Nat := 118140960795 + 3464541 * 2 ^ 59
def prefixEnd_3464541 : Nat := 4983230072969 + 3 ^ 40 * 3464541 * 2
def baseEnd_3464541 : Nat := 1185983186805756467402915

theorem tailTrace_3464541 : CollatzResearch.WordTrace tailWord_3464541 prefixEnd_3464541 1185983186805756467402915 := by
  unfold tailWord_3464541
  simp only [CollatzResearch.WordTrace]
  refine ⟨126362191341567128340545477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84241460894378085560363651 126362191341567128340545477)
  ·
    refine ⟨23692910876543836563852277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126362191341567128340545477 23692910876543836563852277)
    ·
      refine ⟨2221210394675984677861151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23692910876543836563852277 2221210394675984677861151)
      ·
        refine ⟨3331815592013977016791727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2221210394675984677861151 3331815592013977016791727)
        ·
          refine ⟨4997723388020965525187591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331815592013977016791727 4997723388020965525187591)
          ·
            refine ⟨7496585082031448287781387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997723388020965525187591 7496585082031448287781387)
            ·
              refine ⟨11244877623047172431672081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7496585082031448287781387 11244877623047172431672081)
              ·
                refine ⟨8433658217285379323754061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11244877623047172431672081 8433658217285379323754061)
                ·
                  refine ⟨3162621831482017246407773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8433658217285379323754061 3162621831482017246407773)
                  ·
                    refine ⟨1185983186805756467402915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162621831482017246407773 1185983186805756467402915)
                    ·
                      rfl

theorem cell22_3464541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3464541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464541 prefixEnd_3464541 := by exact prefixLift 3464541
  have htrace : WordTrace (prefixWord ++ tailWord_3464541) baseStart_3464541 baseEnd_3464541 := by
    simpa [prefixWord, tailWord_3464541, baseEnd_3464541] using wordTrace_append hprefix tailTrace_3464541
  have hstable : (prefixWord ++ tailWord_3464541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464541).length < 2 ^ (prefixWord ++ tailWord_3464541).sum := by decide
  have hdescent : baseEnd_3464541 < baseStart_3464541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464548 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 8]
def baseStart_3464548 : Nat := 118140960795 + 3464548 * 2 ^ 59
def prefixEnd_3464548 : Nat := 4983230072969 + 3 ^ 40 * 3464548 * 2
def baseEnd_3464548 : Nat := 395328527682936927492631

theorem tailTrace_3464548 : CollatzResearch.WordTrace tailWord_3464548 prefixEnd_3464548 395328527682936927492631 := by
  unfold tailWord_3464548
  simp only [CollatzResearch.WordTrace]
  refine ⟨63181223326270884268025149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84241631101694512357366865 63181223326270884268025149)
  ·
    refine ⟨23692958747351581600509431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63181223326270884268025149 23692958747351581600509431)
    ·
      refine ⟨35539438121027372400764147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23692958747351581600509431 35539438121027372400764147)
      ·
        refine ⟨53309157181541058601146221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35539438121027372400764147 53309157181541058601146221)
        ·
          refine ⟨19990933943077896975429833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53309157181541058601146221 19990933943077896975429833)
          ·
            refine ⟨14993200457308422731572375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19990933943077896975429833 14993200457308422731572375)
            ·
              refine ⟨22489800685962634097358563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14993200457308422731572375 22489800685962634097358563)
              ·
                refine ⟨33734701028943951146037845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22489800685962634097358563 33734701028943951146037845)
                ·
                  refine ⟨395328527682936927492631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33734701028943951146037845 395328527682936927492631)
                  ·
                    rfl

theorem cell22_3464548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_3464548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464548 prefixEnd_3464548 := by exact prefixLift 3464548
  have htrace : WordTrace (prefixWord ++ tailWord_3464548) baseStart_3464548 baseEnd_3464548 := by
    simpa [prefixWord, tailWord_3464548, baseEnd_3464548] using wordTrace_append hprefix tailTrace_3464548
  have hstable : (prefixWord ++ tailWord_3464548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464548).length < 2 ^ (prefixWord ++ tailWord_3464548).sum := by decide
  have hdescent : baseEnd_3464548 < baseStart_3464548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464608 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 2, 7]
def baseStart_3464608 : Nat := 118140960795 + 3464608 * 2 ^ 59
def prefixEnd_3464608 : Nat := 4983230072969 + 3 ^ 40 * 3464608 * 2
def baseEnd_3464608 : Nat := 1186006122274990625977709

theorem tailTrace_3464608 : CollatzResearch.WordTrace tailWord_3464608 prefixEnd_3464608 1186006122274990625977709 := by
  unfold tailWord_3464608
  simp only [CollatzResearch.WordTrace]
  refine ⟨63182317516162199391617239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84243090021549599188822985 63182317516162199391617239)
  ·
    refine ⟨94773476274243299087425859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63182317516162199391617239 94773476274243299087425859)
    ·
      refine ⟨142160214411364948631138789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94773476274243299087425859 142160214411364948631138789)
      ·
        refine ⟨26655040202130927868338523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142160214411364948631138789 26655040202130927868338523)
        ·
          refine ⟨39982560303196391802507785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26655040202130927868338523 39982560303196391802507785)
          ·
            refine ⟨29986920227397293851880839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39982560303196391802507785 29986920227397293851880839)
            ·
              refine ⟨44980380341095940777821259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29986920227397293851880839 44980380341095940777821259)
              ·
                refine ⟨67470570511643911166731889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44980380341095940777821259 67470570511643911166731889)
                ·
                  refine ⟨50602927883732933375048917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67470570511643911166731889 50602927883732933375048917)
                  ·
                    refine ⟨1186006122274990625977709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50602927883732933375048917 1186006122274990625977709)
                    ·
                      rfl

theorem cell22_3464608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_3464608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464608 prefixEnd_3464608 := by exact prefixLift 3464608
  have htrace : WordTrace (prefixWord ++ tailWord_3464608) baseStart_3464608 baseEnd_3464608 := by
    simpa [prefixWord, tailWord_3464608, baseEnd_3464608] using wordTrace_append hprefix tailTrace_3464608
  have hstable : (prefixWord ++ tailWord_3464608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464608).length < 2 ^ (prefixWord ++ tailWord_3464608).sum := by decide
  have hdescent : baseEnd_3464608 < baseStart_3464608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464610 : List Nat := [3, 3, 1, 2, 1, 3, 1, 8]
def baseStart_3464610 : Nat := 118140960795 + 3464610 * 2 ^ 59
def prefixEnd_3464610 : Nat := 4983230072969 + 3 ^ 40 * 3464610 * 2
def baseEnd_3464610 : Nat := 131778534101762587491967

theorem tailTrace_3464610 : CollatzResearch.WordTrace tailWord_3464610 prefixEnd_3464610 131778534101762587491967 := by
  unfold tailWord_3464610
  simp only [CollatzResearch.WordTrace]
  refine ⟨31591176994579288281201821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84243138652211435416538189 31591176994579288281201821)
  ·
    refine ⟨11846691372967233105450683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31591176994579288281201821 11846691372967233105450683)
    ·
      refine ⟨17770037059450849658176025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11846691372967233105450683 17770037059450849658176025)
      ·
        refine ⟨13327527794588137243632019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17770037059450849658176025 13327527794588137243632019)
        ·
          refine ⟨19991291691882205865448029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13327527794588137243632019 19991291691882205865448029)
          ·
            refine ⟨7496734384455827199543011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19991291691882205865448029 7496734384455827199543011)
            ·
              refine ⟨11245101576683740799314517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7496734384455827199543011 11245101576683740799314517)
              ·
                refine ⟨131778534101762587491967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11245101576683740799314517 131778534101762587491967)
                ·
                  rfl

theorem cell22_3464610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_3464610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464610 prefixEnd_3464610 := by exact prefixLift 3464610
  have htrace : WordTrace (prefixWord ++ tailWord_3464610) baseStart_3464610 baseEnd_3464610 := by
    simpa [prefixWord, tailWord_3464610, baseEnd_3464610] using wordTrace_append hprefix tailTrace_3464610
  have hstable : (prefixWord ++ tailWord_3464610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464610).length < 2 ^ (prefixWord ++ tailWord_3464610).sum := by decide
  have hdescent : baseEnd_3464610 < baseStart_3464610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464616 : List Nat := [2, 1, 6, 1, 2, 2, 1, 3, 4]
def baseStart_3464616 : Nat := 118140960795 + 3464616 * 2 ^ 59
def prefixEnd_3464616 : Nat := 4983230072969 + 3 ^ 40 * 3464616 * 2
def baseEnd_3464616 : Nat := 395336286946160423925895

theorem tailTrace_3464616 : CollatzResearch.WordTrace tailWord_3464616 prefixEnd_3464616 395336286946160423925895 := by
  unfold tailWord_3464616
  simp only [CollatzResearch.WordTrace]
  refine ⟨63182463408147708074762851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84243284544196944099683801 63182463408147708074762851)
  ·
    refine ⟨94773695112221562112144277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63182463408147708074762851 94773695112221562112144277)
    ·
      refine ⟨4442516958385385724006763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94773695112221562112144277 4442516958385385724006763)
      ·
        refine ⟨6663775437578078586010145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4442516958385385724006763 6663775437578078586010145)
        ·
          refine ⟨4997831578183558939507609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6663775437578078586010145 4997831578183558939507609)
          ·
            refine ⟨3748373683637669204630707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4997831578183558939507609 3748373683637669204630707)
            ·
              refine ⟨5622560525456503806946061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3748373683637669204630707 5622560525456503806946061)
              ·
                refine ⟨2108460197046188927604773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5622560525456503806946061 2108460197046188927604773)
                ·
                  refine ⟨395336286946160423925895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2108460197046188927604773 395336286946160423925895)
                  ·
                    rfl

theorem cell22_3464616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 4].length) (baseStart_3464616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464616 prefixEnd_3464616 := by exact prefixLift 3464616
  have htrace : WordTrace (prefixWord ++ tailWord_3464616) baseStart_3464616 baseEnd_3464616 := by
    simpa [prefixWord, tailWord_3464616, baseEnd_3464616] using wordTrace_append hprefix tailTrace_3464616
  have hstable : (prefixWord ++ tailWord_3464616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464616).length < 2 ^ (prefixWord ++ tailWord_3464616).sum := by decide
  have hdescent : baseEnd_3464616 < baseStart_3464616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464683 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 10]
def baseStart_3464683 : Nat := 118140960795 + 3464683 * 2 ^ 59
def prefixEnd_3464683 : Nat := 4983230072969 + 3 ^ 40 * 3464683 * 2
def baseEnd_3464683 : Nat := 395343932102571810117493

theorem tailTrace_3464683 : CollatzResearch.WordTrace tailWord_3464683 prefixEnd_3464683 395343932102571810117493 := by
  unfold tailWord_3464683
  simp only [CollatzResearch.WordTrace]
  refine ⟨126367370507052686592214703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84244913671368457728143135 126367370507052686592214703)
  ·
    refine ⟨189551055760579029888322055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126367370507052686592214703 189551055760579029888322055)
    ·
      refine ⟨284326583640868544832483083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189551055760579029888322055 284326583640868544832483083)
      ·
        refine ⟨426489875461302817248724625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284326583640868544832483083 426489875461302817248724625)
        ·
          refine ⟨319867406595977112936543469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426489875461302817248724625 319867406595977112936543469)
          ·
            refine ⟨119950277473491417351203801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319867406595977112936543469 119950277473491417351203801)
            ·
              refine ⟨89962708105118563013402851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119950277473491417351203801 89962708105118563013402851)
              ·
                refine ⟨134944062157677844520104277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89962708105118563013402851 134944062157677844520104277)
                ·
                  refine ⟨395343932102571810117493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 134944062157677844520104277 395343932102571810117493)
                  ·
                    rfl

theorem cell22_3464683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 10].length) (baseStart_3464683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464683 prefixEnd_3464683 := by exact prefixLift 3464683
  have htrace : WordTrace (prefixWord ++ tailWord_3464683) baseStart_3464683 baseEnd_3464683 := by
    simpa [prefixWord, tailWord_3464683, baseEnd_3464683] using wordTrace_append hprefix tailTrace_3464683
  have hstable : (prefixWord ++ tailWord_3464683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464683).length < 2 ^ (prefixWord ++ tailWord_3464683).sum := by decide
  have hdescent : baseEnd_3464683 < baseStart_3464683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464693 : List Nat := [1, 3, 5, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3464693 : Nat := 118140960795 + 3464693 * 2 ^ 59
def prefixEnd_3464693 : Nat := 4983230072969 + 3 ^ 40 * 3464693 * 2
def baseEnd_3464693 : Nat := 1186035219512078737602449

theorem tailTrace_3464693 : CollatzResearch.WordTrace tailWord_3464693 prefixEnd_3464693 1186035219512078737602449 := by
  unfold tailWord_3464693
  simp only [CollatzResearch.WordTrace]
  refine ⟨126367735237016458300078733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84245156824677638866719155 126367735237016458300078733)
  ·
    refine ⟨47387900713881171862529525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126367735237016458300078733 47387900713881171862529525)
    ·
      refine ⟨4442615691926359862112143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47387900713881171862529525 4442615691926359862112143)
      ·
        refine ⟨6663923537889539793168215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4442615691926359862112143 6663923537889539793168215)
        ·
          refine ⟨9995885306834309689752323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6663923537889539793168215 9995885306834309689752323)
          ·
            refine ⟨14993827960251464534628485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9995885306834309689752323 14993827960251464534628485)
            ·
              refine ⟨2811342742547149600242841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14993827960251464534628485 2811342742547149600242841)
              ·
                refine ⟨2108507056910362200182131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2811342742547149600242841 2108507056910362200182131)
                ·
                  refine ⟨3162760585365543300273197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108507056910362200182131 3162760585365543300273197)
                  ·
                    refine ⟨1186035219512078737602449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162760585365543300273197 1186035219512078737602449)
                    ·
                      rfl

theorem cell22_3464693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3464693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464693 prefixEnd_3464693 := by exact prefixLift 3464693
  have htrace : WordTrace (prefixWord ++ tailWord_3464693) baseStart_3464693 baseEnd_3464693 := by
    simpa [prefixWord, tailWord_3464693, baseEnd_3464693] using wordTrace_append hprefix tailTrace_3464693
  have hstable : (prefixWord ++ tailWord_3464693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464693).length < 2 ^ (prefixWord ++ tailWord_3464693).sum := by decide
  have hdescent : baseEnd_3464693 < baseStart_3464693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464732 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 4, 3]
def baseStart_3464732 : Nat := 118140960795 + 3464732 * 2 ^ 59
def prefixEnd_3464732 : Nat := 4983230072969 + 3 ^ 40 * 3464732 * 2
def baseEnd_3464732 : Nat := 1186048570009095635877329

theorem tailTrace_3464732 : CollatzResearch.WordTrace tailWord_3464732 prefixEnd_3464732 1186048570009095635877329 := by
  unfold tailWord_3464732
  simp only [CollatzResearch.WordTrace]
  refine ⟨63184578841937583980374225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84246105122583445307165633 63184578841937583980374225)
  ·
    refine ⟨47388434131453187985280669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63184578841937583980374225 47388434131453187985280669)
    ·
      refine ⟨17770662799294945494480251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47388434131453187985280669 17770662799294945494480251)
      ·
        refine ⟨26655994198942418241720377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17770662799294945494480251 26655994198942418241720377)
        ·
          refine ⟨19991995649206813681290283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26655994198942418241720377 19991995649206813681290283)
          ·
            refine ⟨29987993473810220521935425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19991995649206813681290283 29987993473810220521935425)
            ·
              refine ⟨22490995105357665391451569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29987993473810220521935425 22490995105357665391451569)
              ·
                refine ⟨16868246329018249043588677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22490995105357665391451569 16868246329018249043588677)
                ·
                  refine ⟨3162796186690921695672877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16868246329018249043588677 3162796186690921695672877)
                  ·
                    refine ⟨1186048570009095635877329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162796186690921695672877 1186048570009095635877329)
                    ·
                      rfl

theorem cell22_3464732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_3464732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464732 prefixEnd_3464732 := by exact prefixLift 3464732
  have htrace : WordTrace (prefixWord ++ tailWord_3464732) baseStart_3464732 baseEnd_3464732 := by
    simpa [prefixWord, tailWord_3464732, baseEnd_3464732] using wordTrace_append hprefix tailTrace_3464732
  have hstable : (prefixWord ++ tailWord_3464732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464732).length < 2 ^ (prefixWord ++ tailWord_3464732).sum := by decide
  have hdescent : baseEnd_3464732 < baseStart_3464732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464736 : List Nat := [2, 1, 1, 6, 1, 3, 2, 1, 1, 4]
def baseStart_3464736 : Nat := 118140960795 + 3464736 * 2 ^ 59
def prefixEnd_3464736 : Nat := 4983230072969 + 3 ^ 40 * 3464736 * 2
def baseEnd_3464736 : Nat := 1186049939290840958777317

theorem tailTrace_3464736 : CollatzResearch.WordTrace tailWord_3464736 prefixEnd_3464736 1186049939290840958777317 := by
  unfold tailWord_3464736
  simp only [CollatzResearch.WordTrace]
  refine ⟨63184651787930338321947031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84246202383907117762596041 63184651787930338321947031)
  ·
    refine ⟨94776977681895507482920547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63184651787930338321947031 94776977681895507482920547)
    ·
      refine ⟨142165466522843261224380821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94776977681895507482920547 142165466522843261224380821)
      ·
        refine ⟨6664006243258277869892851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142165466522843261224380821 6664006243258277869892851)
        ·
          refine ⟨9996009364887416804839277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6664006243258277869892851 9996009364887416804839277)
          ·
            refine ⟨3748503511832781301814729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9996009364887416804839277 3748503511832781301814729)
            ·
              refine ⟨2811377633874585976361047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3748503511832781301814729 2811377633874585976361047)
              ·
                refine ⟨4217066450811878964541571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2811377633874585976361047 4217066450811878964541571)
                ·
                  refine ⟨6325599676217818446812357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4217066450811878964541571 6325599676217818446812357)
                  ·
                    refine ⟨1186049939290840958777317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6325599676217818446812357 1186049939290840958777317)
                    ·
                      rfl

theorem cell22_3464736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 1, 4].length) (baseStart_3464736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464736 prefixEnd_3464736 := by exact prefixLift 3464736
  have htrace : WordTrace (prefixWord ++ tailWord_3464736) baseStart_3464736 baseEnd_3464736 := by
    simpa [prefixWord, tailWord_3464736, baseEnd_3464736] using wordTrace_append hprefix tailTrace_3464736
  have hstable : (prefixWord ++ tailWord_3464736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464736).length < 2 ^ (prefixWord ++ tailWord_3464736).sum := by decide
  have hdescent : baseEnd_3464736 < baseStart_3464736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464835 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 8]
def baseStart_3464835 : Nat := 118140960795 + 3464835 * 2 ^ 59
def prefixEnd_3464835 : Nat := 4983230072969 + 3 ^ 40 * 3464835 * 2
def baseEnd_3464835 : Nat := 395361276338012566850671

theorem tailTrace_3464835 : CollatzResearch.WordTrace tailWord_3464835 prefixEnd_3464835 395361276338012566850671 := by
  unfold tailWord_3464835
  simp only [CollatzResearch.WordTrace]
  refine ⟨126372914402502016551747959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84248609601668011034498639 126372914402502016551747959)
  ·
    refine ⟨189559371603753024827621939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126372914402502016551747959 189559371603753024827621939)
    ·
      refine ⟨284339057405629537241432909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189559371603753024827621939 284339057405629537241432909)
      ·
        refine ⟨106627146527111076465537341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284339057405629537241432909 106627146527111076465537341)
        ·
          refine ⟨39985179947666653674576503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106627146527111076465537341 39985179947666653674576503)
          ·
            refine ⟨59977769921499980511864755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39985179947666653674576503 59977769921499980511864755)
            ·
              refine ⟨89966654882249970767797133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59977769921499980511864755 89966654882249970767797133)
              ·
                refine ⟨33737495580843739037923925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89966654882249970767797133 33737495580843739037923925)
                ·
                  refine ⟨395361276338012566850671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33737495580843739037923925 395361276338012566850671)
                  ·
                    rfl

theorem cell22_3464835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 8].length) (baseStart_3464835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464835 prefixEnd_3464835 := by exact prefixLift 3464835
  have htrace : WordTrace (prefixWord ++ tailWord_3464835) baseStart_3464835 baseEnd_3464835 := by
    simpa [prefixWord, tailWord_3464835, baseEnd_3464835] using wordTrace_append hprefix tailTrace_3464835
  have hstable : (prefixWord ++ tailWord_3464835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464835).length < 2 ^ (prefixWord ++ tailWord_3464835).sum := by decide
  have hdescent : baseEnd_3464835 < baseStart_3464835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464837 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_3464837 : Nat := 118140960795 + 3464837 * 2 ^ 59
def prefixEnd_3464837 : Nat := 4983230072969 + 3 ^ 40 * 3464837 * 2
def baseEnd_3464837 : Nat := 1186084513654910362002007

theorem tailTrace_3464837 : CollatzResearch.WordTrace tailWord_3464837 prefixEnd_3464837 1186084513654910362002007 := by
  unfold tailWord_3464837
  simp only [CollatzResearch.WordTrace]
  refine ⟨126372987348494770893320765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84248658232329847262213843 126372987348494770893320765)
  ·
    refine ⟨47389870255685539084995287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126372987348494770893320765 47389870255685539084995287)
    ·
      refine ⟨71084805383528308627492931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47389870255685539084995287 71084805383528308627492931)
      ·
        refine ⟨106627208075292462941239397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71084805383528308627492931 106627208075292462941239397)
        ·
          refine ⟨19992601514117336801482387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106627208075292462941239397 19992601514117336801482387)
          ·
            refine ⟨29988902271176005202223581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19992601514117336801482387 29988902271176005202223581)
            ·
              refine ⟨11245838351691001950833843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29988902271176005202223581 11245838351691001950833843)
              ·
                refine ⟨16868757527536502926250765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11245838351691001950833843 16868757527536502926250765)
                ·
                  refine ⟨6325784072826188597344037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16868757527536502926250765 6325784072826188597344037)
                  ·
                    refine ⟨1186084513654910362002007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6325784072826188597344037 1186084513654910362002007)
                    ·
                      rfl

theorem cell22_3464837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_3464837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464837 prefixEnd_3464837 := by exact prefixLift 3464837
  have htrace : WordTrace (prefixWord ++ tailWord_3464837) baseStart_3464837 baseEnd_3464837 := by
    simpa [prefixWord, tailWord_3464837, baseEnd_3464837] using wordTrace_append hprefix tailTrace_3464837
  have hstable : (prefixWord ++ tailWord_3464837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464837).length < 2 ^ (prefixWord ++ tailWord_3464837).sum := by decide
  have hdescent : baseEnd_3464837 < baseStart_3464837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464882 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_3464882 : Nat := 118140960795 + 3464882 * 2 ^ 59
def prefixEnd_3464882 : Nat := 4983230072969 + 3 ^ 40 * 3464882 * 2
def baseEnd_3464882 : Nat := 1186099918074545244626869

theorem tailTrace_3464882 : CollatzResearch.WordTrace tailWord_3464882 prefixEnd_3464882 1186099918074545244626869 := by
  unfold tailWord_3464882
  simp only [CollatzResearch.WordTrace]
  refine ⟨31593657158332935894677225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84249752422221162385805933 31593657158332935894677225)
  ·
    refine ⟨23695242868749701921007919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31593657158332935894677225 23695242868749701921007919)
    ·
      refine ⟨35542864303124552881511879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23695242868749701921007919 35542864303124552881511879)
      ·
        refine ⟨53314296454686829322267819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35542864303124552881511879 53314296454686829322267819)
        ·
          refine ⟨79971444682030243983401729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53314296454686829322267819 79971444682030243983401729)
          ·
            refine ⟨59978583511522682987551297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79971444682030243983401729 59978583511522682987551297)
            ·
              refine ⟨44983937633642012240663473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59978583511522682987551297 44983937633642012240663473)
              ·
                refine ⟨33737953225231509180497605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44983937633642012240663473 33737953225231509180497605)
                ·
                  refine ⟨6325866229730907971343301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33737953225231509180497605 6325866229730907971343301)
                  ·
                    refine ⟨1186099918074545244626869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6325866229730907971343301 1186099918074545244626869)
                    ·
                      rfl

theorem cell22_3464882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_3464882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464882 prefixEnd_3464882 := by exact prefixLift 3464882
  have htrace : WordTrace (prefixWord ++ tailWord_3464882) baseStart_3464882 baseEnd_3464882 := by
    simpa [prefixWord, tailWord_3464882, baseEnd_3464882] using wordTrace_append hprefix tailTrace_3464882
  have hstable : (prefixWord ++ tailWord_3464882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464882).length < 2 ^ (prefixWord ++ tailWord_3464882).sum := by decide
  have hdescent : baseEnd_3464882 < baseStart_3464882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464886 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_3464886 : Nat := 118140960795 + 3464886 * 2 ^ 59
def prefixEnd_3464886 : Nat := 4983230072969 + 3 ^ 40 * 3464886 * 2
def baseEnd_3464886 : Nat := 395367095785430189175619

theorem tailTrace_3464886 : CollatzResearch.WordTrace tailWord_3464886 prefixEnd_3464886 395367095785430189175619 := by
  unfold tailWord_3464886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7898423407832328266365907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84249849683544834841236341 7898423407832328266365907)
  ·
    refine ⟨11847635111748492399548861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7898423407832328266365907 11847635111748492399548861)
    ·
      refine ⟨4442863166905684649830823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11847635111748492399548861 4442863166905684649830823)
      ·
        refine ⟨6664294750358526974746235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4442863166905684649830823 6664294750358526974746235)
        ·
          refine ⟨9996442125537790462119353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6664294750358526974746235 9996442125537790462119353)
          ·
            refine ⟨7497331594153342846589515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9996442125537790462119353 7497331594153342846589515)
            ·
              refine ⟨11245997391230014269884273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7497331594153342846589515 11245997391230014269884273)
              ·
                refine ⟨8434498043422510702413205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11245997391230014269884273 8434498043422510702413205)
                ·
                  refine ⟨395367095785430189175619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8434498043422510702413205 395367095785430189175619)
                  ·
                    rfl

theorem cell22_3464886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_3464886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464886 prefixEnd_3464886 := by exact prefixLift 3464886
  have htrace : WordTrace (prefixWord ++ tailWord_3464886) baseStart_3464886 baseEnd_3464886 := by
    simpa [prefixWord, tailWord_3464886, baseEnd_3464886] using wordTrace_append hprefix tailTrace_3464886
  have hstable : (prefixWord ++ tailWord_3464886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464886).length < 2 ^ (prefixWord ++ tailWord_3464886).sum := by decide
  have hdescent : baseEnd_3464886 < baseStart_3464886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464935 : List Nat := [1, 1, 5, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3464935 : Nat := 118140960795 + 3464935 * 2 ^ 59
def prefixEnd_3464935 : Nat := 4983230072969 + 3 ^ 40 * 3464935 * 2
def baseEnd_3464935 : Nat := 1186118061057670773051707

theorem tailTrace_3464935 : CollatzResearch.WordTrace tailWord_3464935 prefixEnd_3464935 1186118061057670773051707 := by
  unfold tailWord_3464935
  simp only [CollatzResearch.WordTrace]
  refine ⟨126376561702139733630388259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84251041134759822420258839 126376561702139733630388259)
  ·
    refine ⟨189564842553209600445582389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126376561702139733630388259 189564842553209600445582389)
    ·
      refine ⟨17771703989363400041773349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189564842553209600445582389 17771703989363400041773349)
      ·
        refine ⟨3332194498005637507832503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17771703989363400041773349 3332194498005637507832503)
        ·
          refine ⟨4998291747008456261748755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3332194498005637507832503 4998291747008456261748755)
          ·
            refine ⟨7497437620512684392623133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4998291747008456261748755 7497437620512684392623133)
            ·
              refine ⟨2811539107692256647233675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7497437620512684392623133 2811539107692256647233675)
              ·
                refine ⟨4217308661538384970850513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2811539107692256647233675 4217308661538384970850513)
                ·
                  refine ⟨3162981496153788728137885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4217308661538384970850513 3162981496153788728137885)
                  ·
                    refine ⟨1186118061057670773051707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162981496153788728137885 1186118061057670773051707)
                    ·
                      rfl

theorem cell22_3464935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3464935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464935 prefixEnd_3464935 := by exact prefixLift 3464935
  have htrace : WordTrace (prefixWord ++ tailWord_3464935) baseStart_3464935 baseEnd_3464935 := by
    simpa [prefixWord, tailWord_3464935, baseEnd_3464935] using wordTrace_append hprefix tailTrace_3464935
  have hstable : (prefixWord ++ tailWord_3464935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464935).length < 2 ^ (prefixWord ++ tailWord_3464935).sum := by decide
  have hdescent : baseEnd_3464935 < baseStart_3464935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464948 : List Nat := [2, 6, 1, 1, 1, 1, 4, 6]
def baseStart_3464948 : Nat := 118140960795 + 3464948 * 2 ^ 59
def prefixEnd_3464948 : Nat := 4983230072969 + 3 ^ 40 * 3464948 * 2
def baseEnd_3464948 : Nat := 131791390135927008052963

theorem tailTrace_3464948 : CollatzResearch.WordTrace tailWord_3464948 prefixEnd_3464948 131791390135927008052963 := by
  unfold tailWord_3464948
  simp only [CollatzResearch.WordTrace]
  refine ⟨63188517925546318425305749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84251357234061757900407665 63188517925546318425305749)
  ·
    refine ⟨2961961777759983676186207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63188517925546318425305749 2961961777759983676186207)
    ·
      refine ⟨4442942666639975514279311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2961961777759983676186207 4442942666639975514279311)
      ·
        refine ⟨6664413999959963271418967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4442942666639975514279311 6664413999959963271418967)
        ·
          refine ⟨9996620999939944907128451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6664413999959963271418967 9996620999939944907128451)
          ·
            refine ⟨14994931499909917360692677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9996620999939944907128451 14994931499909917360692677)
            ·
              refine ⟨2811549656233109505129877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14994931499909917360692677 2811549656233109505129877)
              ·
                refine ⟨131791390135927008052963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2811549656233109505129877 131791390135927008052963)
                ·
                  rfl

theorem cell22_3464948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 6].length) (baseStart_3464948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464948 prefixEnd_3464948 := by exact prefixLift 3464948
  have htrace : WordTrace (prefixWord ++ tailWord_3464948) baseStart_3464948 baseEnd_3464948 := by
    simpa [prefixWord, tailWord_3464948, baseEnd_3464948] using wordTrace_append hprefix tailTrace_3464948
  have hstable : (prefixWord ++ tailWord_3464948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464948).length < 2 ^ (prefixWord ++ tailWord_3464948).sum := by decide
  have hdescent : baseEnd_3464948 < baseStart_3464948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464957 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_3464957 : Nat := 118140960795 + 3464957 * 2 ^ 59
def prefixEnd_3464957 : Nat := 4983230072969 + 3 ^ 40 * 3464957 * 2
def baseEnd_3464957 : Nat := 1186125592107270049001639

theorem tailTrace_3464957 : CollatzResearch.WordTrace tailWord_3464957 prefixEnd_3464957 1186125592107270049001639 := by
  unfold tailWord_3464957
  simp only [CollatzResearch.WordTrace]
  refine ⟨126377364108060031387689125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84251576072040020925126083 126377364108060031387689125)
  ·
    refine ⟨23695755770261255885191711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126377364108060031387689125 23695755770261255885191711)
    ·
      refine ⟨35543633655391883827787567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23695755770261255885191711 35543633655391883827787567)
      ·
        refine ⟨53315450483087825741681351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35543633655391883827787567 53315450483087825741681351)
        ·
          refine ⟨79973175724631738612522027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53315450483087825741681351 79973175724631738612522027)
          ·
            refine ⟨119959763586947607918783041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79973175724631738612522027 119959763586947607918783041)
            ·
              refine ⟨89969822690210705939087281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119959763586947607918783041 89969822690210705939087281)
              ·
                refine ⟨67477367017658029454315461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89969822690210705939087281 67477367017658029454315461)
                ·
                  refine ⟨12652006315810880522684149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67477367017658029454315461 12652006315810880522684149)
                  ·
                    refine ⟨1186125592107270049001639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12652006315810880522684149 1186125592107270049001639)
                    ·
                      rfl

theorem cell22_3464957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_3464957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3464957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3464957 prefixEnd_3464957 := by exact prefixLift 3464957
  have htrace : WordTrace (prefixWord ++ tailWord_3464957) baseStart_3464957 baseEnd_3464957 := by
    simpa [prefixWord, tailWord_3464957, baseEnd_3464957] using wordTrace_append hprefix tailTrace_3464957
  have hstable : (prefixWord ++ tailWord_3464957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464957).length < 2 ^ (prefixWord ++ tailWord_3464957).sum := by decide
  have hdescent : baseEnd_3464957 < baseStart_3464957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465023 : List Nat := [1, 1, 2, 2, 6, 1, 3, 1, 1, 4]
def baseStart_3465023 : Nat := 118140960795 + 3465023 * 2 ^ 59
def prefixEnd_3465023 : Nat := 4983230072969 + 3 ^ 40 * 3465023 * 2
def baseEnd_3465023 : Nat := 1186148185256067876851437

theorem tailTrace_3465023 : CollatzResearch.WordTrace tailWord_3465023 prefixEnd_3465023 1186148185256067876851437 := by
  unfold tailWord_3465023
  simp only [CollatzResearch.WordTrace]
  refine ⟨126379771325820924659591723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84253180883880616439727815 126379771325820924659591723)
  ·
    refine ⟨189569656988731386989387585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126379771325820924659591723 189569656988731386989387585)
    ·
      refine ⟨142177242741548540242040689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189569656988731386989387585 142177242741548540242040689)
      ·
        refine ⟨106632932056161405181530517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142177242741548540242040689 106632932056161405181530517)
        ·
          refine ⟨4998418690132565867884243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106632932056161405181530517 4998418690132565867884243)
          ·
            refine ⟨7497628035198848801826365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4998418690132565867884243 7497628035198848801826365)
            ·
              refine ⟨2811610513199568300684887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7497628035198848801826365 2811610513199568300684887)
              ·
                refine ⟨4217415769799352451027331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2811610513199568300684887 4217415769799352451027331)
                ·
                  refine ⟨6326123654699028676540997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4217415769799352451027331 6326123654699028676540997)
                  ·
                    refine ⟨1186148185256067876851437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6326123654699028676540997 1186148185256067876851437)
                    ·
                      rfl

theorem cell22_3465023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 1, 4].length) (baseStart_3465023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465023 prefixEnd_3465023 := by exact prefixLift 3465023
  have htrace : WordTrace (prefixWord ++ tailWord_3465023) baseStart_3465023 baseEnd_3465023 := by
    simpa [prefixWord, tailWord_3465023, baseEnd_3465023] using wordTrace_append hprefix tailTrace_3465023
  have hstable : (prefixWord ++ tailWord_3465023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465023).length < 2 ^ (prefixWord ++ tailWord_3465023).sum := by decide
  have hdescent : baseEnd_3465023 < baseStart_3465023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465032 : List Nat := [2, 1, 3, 1, 1, 14]
def baseStart_3465032 : Nat := 118140960795 + 3465032 * 2 ^ 59
def prefixEnd_3465032 : Nat := 4983230072969 + 3 ^ 40 * 3465032 * 2
def baseEnd_3465032 : Nat := 14643842791851788313289

theorem tailTrace_3465032 : CollatzResearch.WordTrace tailWord_3465032 prefixEnd_3465032 14643842791851788313289 := by
  unfold tailWord_3465032
  simp only [CollatzResearch.WordTrace]
  refine ⟨63190049791394159598334675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84253399721858879464446233 63190049791394159598334675)
  ·
    refine ⟨94785074687091239397502013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63190049791394159598334675 94785074687091239397502013)
    ·
      refine ⟨35544403007659214774063255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94785074687091239397502013 35544403007659214774063255)
      ·
        refine ⟨53316604511488822161094883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35544403007659214774063255 53316604511488822161094883)
        ·
          refine ⟨79974906767233233241642325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53316604511488822161094883 79974906767233233241642325)
          ·
            refine ⟨14643842791851788313289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 79974906767233233241642325 14643842791851788313289)
            ·
              rfl

theorem cell22_3465032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 14].length) (baseStart_3465032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465032 prefixEnd_3465032 := by exact prefixLift 3465032
  have htrace : WordTrace (prefixWord ++ tailWord_3465032) baseStart_3465032 baseEnd_3465032 := by
    simpa [prefixWord, tailWord_3465032, baseEnd_3465032] using wordTrace_append hprefix tailTrace_3465032
  have hstable : (prefixWord ++ tailWord_3465032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465032).length < 2 ^ (prefixWord ++ tailWord_3465032).sum := by decide
  have hdescent : baseEnd_3465032 < baseStart_3465032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465034 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_3465034 : Nat := 118140960795 + 3465034 * 2 ^ 59
def prefixEnd_3465034 : Nat := 4983230072969 + 3 ^ 40 * 3465034 * 2
def baseEnd_3465034 : Nat := 1186151950780867514826403

theorem tailTrace_3465034 : CollatzResearch.WordTrace tailWord_3465034 prefixEnd_3465034 1186151950780867514826403 := by
  unfold tailWord_3465034
  simp only [CollatzResearch.WordTrace]
  refine ⟨31595043132195268384560539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84253448352520715692161437 31595043132195268384560539)
  ·
    refine ⟨47392564698292902576840809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31595043132195268384560539 47392564698292902576840809)
    ·
      refine ⟨35544423523719676932630607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47392564698292902576840809 35544423523719676932630607)
      ·
        refine ⟨53316635285579515398945911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35544423523719676932630607 53316635285579515398945911)
        ·
          refine ⟨79974952928369273098418867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53316635285579515398945911 79974952928369273098418867)
          ·
            refine ⟨119962429392553909647628301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79974952928369273098418867 119962429392553909647628301)
            ·
              refine ⟨44985911022207716117860613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119962429392553909647628301 44985911022207716117860613)
              ·
                refine ⟨8434858316663946772098865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44985911022207716117860613 8434858316663946772098865)
                ·
                  refine ⟨6326143737497960079074149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8434858316663946772098865 6326143737497960079074149)
                  ·
                    refine ⟨1186151950780867514826403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6326143737497960079074149 1186151950780867514826403)
                    ·
                      rfl

theorem cell22_3465034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_3465034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465034 prefixEnd_3465034 := by exact prefixLift 3465034
  have htrace : WordTrace (prefixWord ++ tailWord_3465034) baseStart_3465034 baseEnd_3465034 := by
    simpa [prefixWord, tailWord_3465034, baseEnd_3465034] using wordTrace_append hprefix tailTrace_3465034
  have hstable : (prefixWord ++ tailWord_3465034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465034).length < 2 ^ (prefixWord ++ tailWord_3465034).sum := by decide
  have hdescent : baseEnd_3465034 < baseStart_3465034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465109 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3465109 : Nat := 118140960795 + 3465109 * 2 ^ 59
def prefixEnd_3465109 : Nat := 4983230072969 + 3 ^ 40 * 3465109 * 2
def baseEnd_3465109 : Nat := 1186177624813592319201173

theorem tailTrace_3465109 : CollatzResearch.WordTrace tailWord_3465109 prefixEnd_3465109 1186177624813592319201173 := by
  unfold tailWord_3465109
  simp only [CollatzResearch.WordTrace]
  refine ⟨126382908003509361347222381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84255272002339574231481587 126382908003509361347222381)
  ·
    refine ⟨47393590501316010505208393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126382908003509361347222381 47393590501316010505208393)
    ·
      refine ⟨35545192875987007878906295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47393590501316010505208393 35545192875987007878906295)
      ·
        refine ⟨53317789313980511818359443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35545192875987007878906295 53317789313980511818359443)
        ·
          refine ⟨79976683970970767727539165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53317789313980511818359443 79976683970970767727539165)
          ·
            refine ⟨29991256489114037897827187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79976683970970767727539165 29991256489114037897827187)
            ·
              refine ⟨44986884733671056846740781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29991256489114037897827187 44986884733671056846740781)
              ·
                refine ⟨16870081775126646317527793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44986884733671056846740781 16870081775126646317527793)
                ·
                  refine ⟨12652561331344984738145845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16870081775126646317527793 12652561331344984738145845)
                  ·
                    refine ⟨1186177624813592319201173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12652561331344984738145845 1186177624813592319201173)
                    ·
                      rfl

theorem cell22_3465109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3465109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465109 prefixEnd_3465109 := by exact prefixLift 3465109
  have htrace : WordTrace (prefixWord ++ tailWord_3465109) baseStart_3465109 baseEnd_3465109 := by
    simpa [prefixWord, tailWord_3465109, baseEnd_3465109] using wordTrace_append hprefix tailTrace_3465109
  have hstable : (prefixWord ++ tailWord_3465109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465109).length < 2 ^ (prefixWord ++ tailWord_3465109).sum := by decide
  have hdescent : baseEnd_3465109 < baseStart_3465109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465169 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 1, 6]
def baseStart_3465169 : Nat := 118140960795 + 3465169 * 2 ^ 59
def prefixEnd_3465169 : Nat := 4983230072969 + 3 ^ 40 * 3465169 * 2
def baseEnd_3465169 : Nat := 1186198164039772162700989

theorem tailTrace_3465169 : CollatzResearch.WordTrace tailWord_3465169 prefixEnd_3465169 1186198164039772162700989 := by
  unfold tailWord_3465169
  simp only [CollatzResearch.WordTrace]
  refine ⟨126385096383291991594406561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84256730922194661062937707 126385096383291991594406561)
  ·
    refine ⟨94788822287468993695804921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126385096383291991594406561 94788822287468993695804921)
    ·
      refine ⟨71091616715601745271853691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94788822287468993695804921 71091616715601745271853691)
      ·
        refine ⟨106637425073402617907780537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71091616715601745271853691 106637425073402617907780537)
        ·
          refine ⟨79978068805051963430835403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106637425073402617907780537 79978068805051963430835403)
          ·
            refine ⟨119967103207577945146253105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79978068805051963430835403 119967103207577945146253105)
            ·
              refine ⟨89975327405683458859689829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119967103207577945146253105 89975327405683458859689829)
              ·
                refine ⟨16870373888565648536191843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89975327405683458859689829 16870373888565648536191843)
                ·
                  refine ⟨25305560832848472804287765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16870373888565648536191843 25305560832848472804287765)
                  ·
                    refine ⟨1186198164039772162700989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25305560832848472804287765 1186198164039772162700989)
                    ·
                      rfl

theorem cell22_3465169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_3465169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465169 prefixEnd_3465169 := by exact prefixLift 3465169
  have htrace : WordTrace (prefixWord ++ tailWord_3465169) baseStart_3465169 baseEnd_3465169 := by
    simpa [prefixWord, tailWord_3465169, baseEnd_3465169] using wordTrace_append hprefix tailTrace_3465169
  have hstable : (prefixWord ++ tailWord_3465169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465169).length < 2 ^ (prefixWord ++ tailWord_3465169).sum := by decide
  have hdescent : baseEnd_3465169 < baseStart_3465169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465201 : List Nat := [1, 2, 2, 2, 6, 9]
def baseStart_3465201 : Nat := 118140960795 + 3465201 * 2 ^ 59
def prefixEnd_3465201 : Nat := 4983230072969 + 3 ^ 40 * 3465201 * 2
def baseEnd_3465201 : Nat := 14644557015972033900011

theorem tailTrace_3465201 : CollatzResearch.WordTrace tailWord_3465201 prefixEnd_3465201 14644557015972033900011 := by
  unfold tailWord_3465201
  simp only [CollatzResearch.WordTrace]
  refine ⟨126386263519176061059571457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84257509012784040706380971 126386263519176061059571457)
  ·
    refine ⟨94789697639382045794678593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126386263519176061059571457 94789697639382045794678593)
    ·
      refine ⟨71092273229536534346008945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94789697639382045794678593 71092273229536534346008945)
      ·
        refine ⟨53319204922152400759506709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71092273229536534346008945 53319204922152400759506709)
        ·
          refine ⟨2499337730725893785601877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53319204922152400759506709 2499337730725893785601877)
          ·
            refine ⟨14644557015972033900011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2499337730725893785601877 14644557015972033900011)
            ·
              rfl

theorem cell22_3465201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 9].length) (baseStart_3465201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465201 prefixEnd_3465201 := by exact prefixLift 3465201
  have htrace : WordTrace (prefixWord ++ tailWord_3465201) baseStart_3465201 baseEnd_3465201 := by
    simpa [prefixWord, tailWord_3465201, baseEnd_3465201] using wordTrace_append hprefix tailTrace_3465201
  have hstable : (prefixWord ++ tailWord_3465201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465201).length < 2 ^ (prefixWord ++ tailWord_3465201).sum := by decide
  have hdescent : baseEnd_3465201 < baseStart_3465201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465306 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_3465306 : Nat := 118140960795 + 3465306 * 2 ^ 59
def prefixEnd_3465306 : Nat := 4983230072969 + 3 ^ 40 * 3465306 * 2
def baseEnd_3465306 : Nat := 1186245061939549472025569

theorem tailTrace_3465306 : CollatzResearch.WordTrace tailWord_3465306 prefixEnd_3465306 1186245061939549472025569 := by
  unfold tailWord_3465306
  simp only [CollatzResearch.WordTrace]
  refine ⟨31597523295948915998035943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84260062122530442661429181 31597523295948915998035943)
  ·
    refine ⟨47396284943923373997053915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31597523295948915998035943 47396284943923373997053915)
    ·
      refine ⟨71094427415885060995580873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47396284943923373997053915 71094427415885060995580873)
      ·
        refine ⟨53320820561913795746685655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71094427415885060995580873 53320820561913795746685655)
        ·
          refine ⟨79981230842870693620028483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53320820561913795746685655 79981230842870693620028483)
          ·
            refine ⟨119971846264306040430042725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79981230842870693620028483 119971846264306040430042725)
            ·
              refine ⟨22494721174557382580633011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119971846264306040430042725 22494721174557382580633011)
              ·
                refine ⟨33742081761836073870949517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22494721174557382580633011 33742081761836073870949517)
                ·
                  refine ⟨12653280660688527701606069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33742081761836073870949517 12653280660688527701606069)
                  ·
                    refine ⟨1186245061939549472025569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12653280660688527701606069 1186245061939549472025569)
                    ·
                      rfl

theorem cell22_3465306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_3465306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465306 prefixEnd_3465306 := by exact prefixLift 3465306
  have htrace : WordTrace (prefixWord ++ tailWord_3465306) baseStart_3465306 baseEnd_3465306 := by
    simpa [prefixWord, tailWord_3465306, baseEnd_3465306] using wordTrace_append hprefix tailTrace_3465306
  have hstable : (prefixWord ++ tailWord_3465306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465306).length < 2 ^ (prefixWord ++ tailWord_3465306).sum := by decide
  have hdescent : baseEnd_3465306 < baseStart_3465306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465340 : List Nat := [2, 2, 2, 1, 1, 5, 1, 3, 2, 3]
def baseStart_3465340 : Nat := 118140960795 + 3465340 * 2 ^ 59
def prefixEnd_3465340 : Nat := 4983230072969 + 3 ^ 40 * 3465340 * 2
def baseEnd_3465340 : Nat := 1186256700834384716675465

theorem tailTrace_3465340 : CollatzResearch.WordTrace tailWord_3465340 prefixEnd_3465340 1186256700834384716675465 := by
  unfold tailWord_3465340
  simp only [CollatzResearch.WordTrace]
  refine ⟨63195666632836243899440737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84260888843781658532587649 63195666632836243899440737)
  ·
    refine ⟨47396749974627182924580553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63195666632836243899440737 47396749974627182924580553)
    ·
      refine ⟨35547562480970387193435415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47396749974627182924580553 35547562480970387193435415)
      ·
        refine ⟨53321343721455580790153123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35547562480970387193435415 53321343721455580790153123)
        ·
          refine ⟨79982015582183371185229685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53321343721455580790153123 79982015582183371185229685)
          ·
            refine ⟨7498313960829691048615283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79982015582183371185229685 7498313960829691048615283)
            ·
              refine ⟨11247470941244536572922925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7498313960829691048615283 11247470941244536572922925)
              ·
                refine ⟨4217801602966701214846097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11247470941244536572922925 4217801602966701214846097)
                ·
                  refine ⟨3163351202225025911134573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4217801602966701214846097 3163351202225025911134573)
                  ·
                    refine ⟨1186256700834384716675465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3163351202225025911134573 1186256700834384716675465)
                    ·
                      rfl

theorem cell22_3465340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_3465340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465340 prefixEnd_3465340 := by exact prefixLift 3465340
  have htrace : WordTrace (prefixWord ++ tailWord_3465340) baseStart_3465340 baseEnd_3465340 := by
    simpa [prefixWord, tailWord_3465340, baseEnd_3465340] using wordTrace_append hprefix tailTrace_3465340
  have hstable : (prefixWord ++ tailWord_3465340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465340).length < 2 ^ (prefixWord ++ tailWord_3465340).sum := by decide
  have hdescent : baseEnd_3465340 < baseStart_3465340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465351 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 2, 7]
def baseStart_3465351 : Nat := 118140960795 + 3465351 * 2 ^ 59
def prefixEnd_3465351 : Nat := 4983230072969 + 3 ^ 40 * 3465351 * 2
def baseEnd_3465351 : Nat := 1186260466359184354650431

theorem tailTrace_3465351 : CollatzResearch.WordTrace tailWord_3465351 prefixEnd_3465351 1186260466359184354650431 := by
  unfold tailWord_3465351
  simp only [CollatzResearch.WordTrace]
  refine ⟨126391734468632636677531907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84261156312421757785021271 126391734468632636677531907)
  ·
    refine ⟨189587601702948955016297861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126391734468632636677531907 189587601702948955016297861)
    ·
      refine ⟨35547675319302929065555849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189587601702948955016297861 35547675319302929065555849)
      ·
        refine ⟨26660756489477196799166887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35547675319302929065555849 26660756489477196799166887)
        ·
          refine ⟨39991134734215795198750331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26660756489477196799166887 39991134734215795198750331)
          ·
            refine ⟨59986702101323692798125497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39991134734215795198750331 59986702101323692798125497)
            ·
              refine ⟨44990026575992769598594123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59986702101323692798125497 44990026575992769598594123)
              ·
                refine ⟨67485039863989154397891185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44990026575992769598594123 67485039863989154397891185)
                ·
                  refine ⟨50613779897991865798418389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67485039863989154397891185 50613779897991865798418389)
                  ·
                    refine ⟨1186260466359184354650431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50613779897991865798418389 1186260466359184354650431)
                    ·
                      rfl

theorem cell22_3465351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_3465351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465351 prefixEnd_3465351 := by exact prefixLift 3465351
  have htrace : WordTrace (prefixWord ++ tailWord_3465351) baseStart_3465351 baseEnd_3465351 := by
    simpa [prefixWord, tailWord_3465351, baseEnd_3465351] using wordTrace_append hprefix tailTrace_3465351
  have hstable : (prefixWord ++ tailWord_3465351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465351).length < 2 ^ (prefixWord ++ tailWord_3465351).sum := by decide
  have hdescent : baseEnd_3465351 < baseStart_3465351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465374 : List Nat := [4, 3, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_3465374 : Nat := 118140960795 + 3465374 * 2 ^ 59
def prefixEnd_3465374 : Nat := 4983230072969 + 3 ^ 40 * 3465374 * 2
def baseEnd_3465374 : Nat := 1186268339729219961325361

theorem tailTrace_3465374 : CollatzResearch.WordTrace tailWord_3465374 prefixEnd_3465374 1186268339729219961325361 := by
  unfold tailWord_3465374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15799071668443663950702397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84261715565032874403746117 15799071668443663950702397)
  ·
    refine ⟨5924651875666373981513399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15799071668443663950702397 5924651875666373981513399)
    ·
      refine ⟨8886977813499560972270099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5924651875666373981513399 8886977813499560972270099)
      ·
        refine ⟨13330466720249341458405149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8886977813499560972270099 13330466720249341458405149)
        ·
          refine ⟨4998925020093503046901931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13330466720249341458405149 4998925020093503046901931)
          ·
            refine ⟨7498387530140254570352897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4998925020093503046901931 7498387530140254570352897)
            ·
              refine ⟨5623790647605190927764673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7498387530140254570352897 5623790647605190927764673)
              ·
                refine ⟨4217842985703893195823505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5623790647605190927764673 4217842985703893195823505)
                ·
                  refine ⟨3163382239277919896867629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4217842985703893195823505 3163382239277919896867629)
                  ·
                    refine ⟨1186268339729219961325361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3163382239277919896867629 1186268339729219961325361)
                    ·
                      rfl

theorem cell22_3465374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_3465374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465374 prefixEnd_3465374 := by exact prefixLift 3465374
  have htrace : WordTrace (prefixWord ++ tailWord_3465374) baseStart_3465374 baseEnd_3465374 := by
    simpa [prefixWord, tailWord_3465374, baseEnd_3465374] using wordTrace_append hprefix tailTrace_3465374
  have hstable : (prefixWord ++ tailWord_3465374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465374).length < 2 ^ (prefixWord ++ tailWord_3465374).sum := by decide
  have hdescent : baseEnd_3465374 < baseStart_3465374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465473 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3465473 : Nat := 118140960795 + 3465473 * 2 ^ 59
def prefixEnd_3465473 : Nat := 4983230072969 + 3 ^ 40 * 3465473 * 2
def baseEnd_3465473 : Nat := 1186302229452416703100057

theorem tailTrace_3465473 : CollatzResearch.WordTrace tailWord_3465473 prefixEnd_3465473 1186302229452416703100057 := by
  unfold tailWord_3465473
  simp only [CollatzResearch.WordTrace]
  refine ⟨126396184174190651513473073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84264122782793767675648715 126396184174190651513473073)
  ·
    refine ⟨94797138130642988635104805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126396184174190651513473073 94797138130642988635104805)
    ·
      refine ⟨17774463399495560369082151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94797138130642988635104805 17774463399495560369082151)
      ·
        refine ⟨26661695099243340553623227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17774463399495560369082151 26661695099243340553623227)
        ·
          refine ⟨39992542648865010830434841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26661695099243340553623227 39992542648865010830434841)
          ·
            refine ⟨29994406986648758122826131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39992542648865010830434841 29994406986648758122826131)
            ·
              refine ⟨44991610479973137184239197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29994406986648758122826131 44991610479973137184239197)
              ·
                refine ⟨16871853929989926444089699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44991610479973137184239197 16871853929989926444089699)
                ·
                  refine ⟨25307780894984889666134549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16871853929989926444089699 25307780894984889666134549)
                  ·
                    refine ⟨1186302229452416703100057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25307780894984889666134549 1186302229452416703100057)
                    ·
                      rfl

theorem cell22_3465473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3465473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465473 prefixEnd_3465473 := by exact prefixLift 3465473
  have htrace : WordTrace (prefixWord ++ tailWord_3465473) baseStart_3465473 baseEnd_3465473 := by
    simpa [prefixWord, tailWord_3465473, baseEnd_3465473] using wordTrace_append hprefix tailTrace_3465473
  have hstable : (prefixWord ++ tailWord_3465473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465473).length < 2 ^ (prefixWord ++ tailWord_3465473).sum := by decide
  have hdescent : baseEnd_3465473 < baseStart_3465473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465597 : List Nat := [1, 4, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_3465597 : Nat := 118140960795 + 3465597 * 2 ^ 59
def prefixEnd_3465597 : Nat := 4983230072969 + 3 ^ 40 * 3465597 * 2
def baseEnd_3465597 : Nat := 1186344677186521712999677

theorem tailTrace_3465597 : CollatzResearch.WordTrace tailWord_3465597 prefixEnd_3465597 1186344677186521712999677 := by
  unfold tailWord_3465597
  simp only [CollatzResearch.WordTrace]
  refine ⟨126400706825741420690987045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84267137883827613793991363 126400706825741420690987045)
  ·
    refine ⟨23700132529826516379560071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126400706825741420690987045 23700132529826516379560071)
    ·
      refine ⟨35550198794739774569340107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23700132529826516379560071 35550198794739774569340107)
      ·
        refine ⟨53325298192109661854010161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35550198794739774569340107 53325298192109661854010161)
        ·
          refine ⟨39993973644082246390507621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53325298192109661854010161 39993973644082246390507621)
          ·
            refine ⟨7498870058265421198220179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39993973644082246390507621 7498870058265421198220179)
            ·
              refine ⟨11248305087398131797330269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7498870058265421198220179 11248305087398131797330269)
              ·
                refine ⟨4218114407774299423998851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11248305087398131797330269 4218114407774299423998851)
                ·
                  refine ⟨6327171611661449135998277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4218114407774299423998851 6327171611661449135998277)
                  ·
                    refine ⟨1186344677186521712999677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6327171611661449135998277 1186344677186521712999677)
                    ·
                      rfl

theorem cell22_3465597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_3465597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465597 prefixEnd_3465597 := by exact prefixLift 3465597
  have htrace : WordTrace (prefixWord ++ tailWord_3465597) baseStart_3465597 baseEnd_3465597 := by
    simpa [prefixWord, tailWord_3465597, baseEnd_3465597] using wordTrace_append hprefix tailTrace_3465597
  have hstable : (prefixWord ++ tailWord_3465597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465597).length < 2 ^ (prefixWord ++ tailWord_3465597).sum := by decide
  have hdescent : baseEnd_3465597 < baseStart_3465597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465612 : List Nat := [2, 2, 1, 2, 1, 4, 2, 4, 4]
def baseStart_3465612 : Nat := 118140960795 + 3465612 * 2 ^ 59
def prefixEnd_3465612 : Nat := 4983230072969 + 3 ^ 40 * 3465612 * 2
def baseEnd_3465612 : Nat := 395449937331022224624877

theorem tailTrace_3465612 : CollatzResearch.WordTrace tailWord_3465612 prefixEnd_3465612 395449937331022224624877 := by
  unfold tailWord_3465612
  simp only [CollatzResearch.WordTrace]
  refine ⟨63200626960343539126391545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84267502613791385501855393 63200626960343539126391545)
  ·
    refine ⟨47400470220257654344793659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63200626960343539126391545 47400470220257654344793659)
    ·
      refine ⟨71100705330386481517190489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47400470220257654344793659 71100705330386481517190489)
      ·
        refine ⟨53325528997789861137892867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71100705330386481517190489 53325528997789861137892867)
        ·
          refine ⟨79988293496684791706839301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53325528997789861137892867 79988293496684791706839301)
          ·
            refine ⟨14997805030628398445032369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79988293496684791706839301 14997805030628398445032369)
            ·
              refine ⟨11248353772971298833774277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14997805030628398445032369 11248353772971298833774277)
              ·
                refine ⟨2109066332432118531332677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11248353772971298833774277 2109066332432118531332677)
                ·
                  refine ⟨395449937331022224624877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2109066332432118531332677 395449937331022224624877)
                  ·
                    rfl

theorem cell22_3465612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_3465612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465612 prefixEnd_3465612 := by exact prefixLift 3465612
  have htrace : WordTrace (prefixWord ++ tailWord_3465612) baseStart_3465612 baseEnd_3465612 := by
    simpa [prefixWord, tailWord_3465612, baseEnd_3465612] using wordTrace_append hprefix tailTrace_3465612
  have hstable : (prefixWord ++ tailWord_3465612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465612).length < 2 ^ (prefixWord ++ tailWord_3465612).sum := by decide
  have hdescent : baseEnd_3465612 < baseStart_3465612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465700 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_3465700 : Nat := 118140960795 + 3465700 * 2 ^ 59
def prefixEnd_3465700 : Nat := 4983230072969 + 3 ^ 40 * 3465700 * 2
def baseEnd_3465700 : Nat := 1186379936191463777674361

theorem tailTrace_3465700 : CollatzResearch.WordTrace tailWord_3465700 prefixEnd_3465700 1186379936191463777674361 := by
  unfold tailWord_3465700
  simp only [CollatzResearch.WordTrace]
  refine ⟨63202231772184134640993277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84269642362912179521324369 63202231772184134640993277)
  ·
    refine ⟨23700836914569050490372479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63202231772184134640993277 23700836914569050490372479)
    ·
      refine ⟨35551255371853575735558719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23700836914569050490372479 35551255371853575735558719)
      ·
        refine ⟨53326883057780363603338079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35551255371853575735558719 53326883057780363603338079)
        ·
          refine ⟨79990324586670545405007119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53326883057780363603338079 79990324586670545405007119)
          ·
            refine ⟨119985486880005818107510679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79990324586670545405007119 119985486880005818107510679)
            ·
              refine ⟨179978230320008727161266019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119985486880005818107510679 179978230320008727161266019)
              ·
                refine ⟨269967345480013090741899029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179978230320008727161266019 269967345480013090741899029)
                ·
                  refine ⟨12654719319375613628526517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 269967345480013090741899029 12654719319375613628526517)
                  ·
                    refine ⟨1186379936191463777674361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12654719319375613628526517 1186379936191463777674361)
                    ·
                      rfl

theorem cell22_3465700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_3465700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465700 prefixEnd_3465700 := by exact prefixLift 3465700
  have htrace : WordTrace (prefixWord ++ tailWord_3465700) baseStart_3465700 baseEnd_3465700 := by
    simpa [prefixWord, tailWord_3465700, baseEnd_3465700] using wordTrace_append hprefix tailTrace_3465700
  have hstable : (prefixWord ++ tailWord_3465700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465700).length < 2 ^ (prefixWord ++ tailWord_3465700).sum := by decide
  have hdescent : baseEnd_3465700 < baseStart_3465700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465777 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 2, 4]
def baseStart_3465777 : Nat := 118140960795 + 3465777 * 2 ^ 59
def prefixEnd_3465777 : Nat := 4983230072969 + 3 ^ 40 * 3465777 * 2
def baseEnd_3465777 : Nat := 1186406294865061243499125

theorem tailTrace_3465777 : CollatzResearch.WordTrace tailWord_3465777 prefixEnd_3465777 1186406294865061243499125 := by
  unfold tailWord_3465777
  simp only [CollatzResearch.WordTrace]
  refine ⟨126407271965089311432539585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84271514643392874288359723 126407271965089311432539585)
  ·
    refine ⟨94805453973816983574404689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126407271965089311432539585 94805453973816983574404689)
    ·
      refine ⟨71104090480362737680803517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94805453973816983574404689 71104090480362737680803517)
      ·
        refine ⟨26664033930136026630301319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71104090480362737680803517 26664033930136026630301319)
        ·
          refine ⟨39996050895204039945451979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26664033930136026630301319 39996050895204039945451979)
          ·
            refine ⟨59994076342806059918177969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39996050895204039945451979 59994076342806059918177969)
            ·
              refine ⟨44995557257104544938633477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59994076342806059918177969 44995557257104544938633477)
              ·
                refine ⟨8436666985707102175993777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44995557257104544938633477 8436666985707102175993777)
                ·
                  refine ⟨6327500239280326631995333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8436666985707102175993777 6327500239280326631995333)
                  ·
                    refine ⟨1186406294865061243499125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6327500239280326631995333 1186406294865061243499125)
                    ·
                      rfl

theorem cell22_3465777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_3465777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465777 prefixEnd_3465777 := by exact prefixLift 3465777
  have htrace : WordTrace (prefixWord ++ tailWord_3465777) baseStart_3465777 baseEnd_3465777 := by
    simpa [prefixWord, tailWord_3465777, baseEnd_3465777] using wordTrace_append hprefix tailTrace_3465777
  have hstable : (prefixWord ++ tailWord_3465777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465777).length < 2 ^ (prefixWord ++ tailWord_3465777).sum := by decide
  have hdescent : baseEnd_3465777 < baseStart_3465777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465809 : List Nat := [1, 2, 2, 1, 3, 5, 2, 6]
def baseStart_3465809 : Nat := 118140960795 + 3465809 * 2 ^ 59
def prefixEnd_3465809 : Nat := 4983230072969 + 3 ^ 40 * 3465809 * 2
def baseEnd_3465809 : Nat := 131824138791002647411003

theorem tailTrace_3465809 : CollatzResearch.WordTrace tailWord_3465809 prefixEnd_3465809 131824138791002647411003 := by
  unfold tailWord_3465809
  simp only [CollatzResearch.WordTrace]
  refine ⟨126408439100973380897704481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84272292733982253931802987 126408439100973380897704481)
  ·
    refine ⟨94806329325730035673278361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126408439100973380897704481 94806329325730035673278361)
    ·
      refine ⟨71104746994297526754958771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94806329325730035673278361 71104746994297526754958771)
      ·
        refine ⟨106657120491446290132438157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71104746994297526754958771 106657120491446290132438157)
        ·
          refine ⟨39996420184292358799664309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106657120491446290132438157 39996420184292358799664309)
          ·
            refine ⟨3749664392277408637468529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39996420184292358799664309 3749664392277408637468529)
            ·
              refine ⟨2812248294208056478101397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3749664392277408637468529 2812248294208056478101397)
              ·
                refine ⟨131824138791002647411003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2812248294208056478101397 131824138791002647411003)
                ·
                  rfl

theorem cell22_3465809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 6].length) (baseStart_3465809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465809 prefixEnd_3465809 := by exact prefixLift 3465809
  have htrace : WordTrace (prefixWord ++ tailWord_3465809) baseStart_3465809 baseEnd_3465809 := by
    simpa [prefixWord, tailWord_3465809, baseEnd_3465809] using wordTrace_append hprefix tailTrace_3465809
  have hstable : (prefixWord ++ tailWord_3465809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465809).length < 2 ^ (prefixWord ++ tailWord_3465809).sum := by decide
  have hdescent : baseEnd_3465809 < baseStart_3465809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465826 : List Nat := [3, 3, 2, 3, 1, 2, 8]
def baseStart_3465826 : Nat := 118140960795 + 3465826 * 2 ^ 59
def prefixEnd_3465826 : Nat := 4983230072969 + 3 ^ 40 * 3465826 * 2
def baseEnd_3465826 : Nat := 43941595132090424037925

theorem tailTrace_3465826 : CollatzResearch.WordTrace tailWord_3465826 prefixEnd_3465826 43941595132090424037925 := by
  unfold tailWord_3465826
  simp only [CollatzResearch.WordTrace]
  refine ⟨31602264785477948200268333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84272706094607861867382221 31602264785477948200268333)
  ·
    refine ⟨11850849294554230575100625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31602264785477948200268333 11850849294554230575100625)
    ·
      refine ⟨8888136970915672931325469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11850849294554230575100625 8888136970915672931325469)
      ·
        refine ⟨3333051364093377349247051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8888136970915672931325469 3333051364093377349247051)
        ·
          refine ⟨4999577046140066023870577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3333051364093377349247051 4999577046140066023870577)
          ·
            refine ⟨3749682784605049517902933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4999577046140066023870577 3749682784605049517902933)
            ·
              refine ⟨43941595132090424037925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3749682784605049517902933 43941595132090424037925)
              ·
                rfl

theorem cell22_3465826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 8].length) (baseStart_3465826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465826 prefixEnd_3465826 := by exact prefixLift 3465826
  have htrace : WordTrace (prefixWord ++ tailWord_3465826) baseStart_3465826 baseEnd_3465826 := by
    simpa [prefixWord, tailWord_3465826, baseEnd_3465826] using wordTrace_append hprefix tailTrace_3465826
  have hstable : (prefixWord ++ tailWord_3465826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465826).length < 2 ^ (prefixWord ++ tailWord_3465826).sum := by decide
  have hdescent : baseEnd_3465826 < baseStart_3465826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465852 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_3465852 : Nat := 118140960795 + 3465852 * 2 ^ 59
def prefixEnd_3465852 : Nat := 4983230072969 + 3 ^ 40 * 3465852 * 2
def baseEnd_3465852 : Nat := 1186431968897786047873895

theorem tailTrace_3465852 : CollatzResearch.WordTrace tailWord_3465852 prefixEnd_3465852 1186431968897786047873895 := by
  unfold tailWord_3465852
  simp only [CollatzResearch.WordTrace]
  refine ⟨63205003719908799620759905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84273338293211732827679873 63205003719908799620759905)
  ·
    refine ⟨47403752789931599715569929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63205003719908799620759905 47403752789931599715569929)
    ·
      refine ⟨35552814592448699786677447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47403752789931599715569929 35552814592448699786677447)
      ·
        refine ⟨53329221888673049680016171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35552814592448699786677447 53329221888673049680016171)
        ·
          refine ⟨79993832833009574520024257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53329221888673049680016171 79993832833009574520024257)
          ·
            refine ⟨59995374624757180890018193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79993832833009574520024257 59995374624757180890018193)
            ·
              refine ⟨44996530968567885667513645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59995374624757180890018193 44996530968567885667513645)
              ·
                refine ⟨16873699113212957125317617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44996530968567885667513645 16873699113212957125317617)
                ·
                  refine ⟨12655274334909717843988213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16873699113212957125317617 12655274334909717843988213)
                  ·
                    refine ⟨1186431968897786047873895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12655274334909717843988213 1186431968897786047873895)
                    ·
                      rfl

theorem cell22_3465852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_3465852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465852 prefixEnd_3465852 := by exact prefixLift 3465852
  have htrace : WordTrace (prefixWord ++ tailWord_3465852) baseStart_3465852 baseEnd_3465852 := by
    simpa [prefixWord, tailWord_3465852, baseEnd_3465852] using wordTrace_append hprefix tailTrace_3465852
  have hstable : (prefixWord ++ tailWord_3465852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465852).length < 2 ^ (prefixWord ++ tailWord_3465852).sum := by decide
  have hdescent : baseEnd_3465852 < baseStart_3465852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465914 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_3465914 : Nat := 118140960795 + 3465914 * 2 ^ 59
def prefixEnd_3465914 : Nat := 4983230072969 + 3 ^ 40 * 3465914 * 2
def baseEnd_3465914 : Nat := 1186453192764838552823705

theorem tailTrace_3465914 : CollatzResearch.WordTrace tailWord_3465914 prefixEnd_3465914 1186453192764838552823705 := by
  unfold tailWord_3465914
  simp only [CollatzResearch.WordTrace]
  refine ⟨31603067191398245957569199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84274845843728655886851197 31603067191398245957569199)
  ·
    refine ⟨47404600787097368936353799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31603067191398245957569199 47404600787097368936353799)
    ·
      refine ⟨71106901180646053404530699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47404600787097368936353799 71106901180646053404530699)
      ·
        refine ⟨106660351770969080106796049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71106901180646053404530699 106660351770969080106796049)
        ·
          refine ⟨79995263828226810080097037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106660351770969080106796049 79995263828226810080097037)
          ·
            refine ⟨29998223935585053780036389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79995263828226810080097037 29998223935585053780036389)
            ·
              refine ⟨5624666987922197583756823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29998223935585053780036389 5624666987922197583756823)
              ·
                refine ⟨8437000481883296375635235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5624666987922197583756823 8437000481883296375635235)
                ·
                  refine ⟨12655500722824944563452853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8437000481883296375635235 12655500722824944563452853)
                  ·
                    refine ⟨1186453192764838552823705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12655500722824944563452853 1186453192764838552823705)
                    ·
                      rfl

theorem cell22_3465914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_3465914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465914 prefixEnd_3465914 := by exact prefixLift 3465914
  have htrace : WordTrace (prefixWord ++ tailWord_3465914) baseStart_3465914 baseEnd_3465914 := by
    simpa [prefixWord, tailWord_3465914, baseEnd_3465914] using wordTrace_append hprefix tailTrace_3465914
  have hstable : (prefixWord ++ tailWord_3465914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465914).length < 2 ^ (prefixWord ++ tailWord_3465914).sum := by decide
  have hdescent : baseEnd_3465914 < baseStart_3465914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465948 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3465948 : Nat := 118140960795 + 3465948 * 2 ^ 59
def prefixEnd_3465948 : Nat := 4983230072969 + 3 ^ 40 * 3465948 * 2
def baseEnd_3465948 : Nat := 1186464831659673797473601

theorem tailTrace_3465948 : CollatzResearch.WordTrace tailWord_3465948 prefixEnd_3465948 1186464831659673797473601 := by
  unfold tailWord_3465948
  simp only [CollatzResearch.WordTrace]
  refine ⟨63206754423734903818507249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84275672564979871758009665 63206754423734903818507249)
  ·
    refine ⟨47405065817801177863880437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63206754423734903818507249 47405065817801177863880437)
    ·
      refine ⟨4444224920418860424738791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47405065817801177863880437 4444224920418860424738791)
      ·
        refine ⟨6666337380628290637108187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444224920418860424738791 6666337380628290637108187)
        ·
          refine ⟨9999506070942435955662281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6666337380628290637108187 9999506070942435955662281)
          ·
            refine ⟨7499629553206826966746711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9999506070942435955662281 7499629553206826966746711)
            ·
              refine ⟨11249444329810240450120067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7499629553206826966746711 11249444329810240450120067)
              ·
                refine ⟨16874166494715360675180101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11249444329810240450120067 16874166494715360675180101)
                ·
                  refine ⟨3163906217759130126596269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16874166494715360675180101 3163906217759130126596269)
                  ·
                    refine ⟨1186464831659673797473601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3163906217759130126596269 1186464831659673797473601)
                    ·
                      rfl

theorem cell22_3465948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3465948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465948 prefixEnd_3465948 := by exact prefixLift 3465948
  have htrace : WordTrace (prefixWord ++ tailWord_3465948) baseStart_3465948 baseEnd_3465948 := by
    simpa [prefixWord, tailWord_3465948, baseEnd_3465948] using wordTrace_append hprefix tailTrace_3465948
  have hstable : (prefixWord ++ tailWord_3465948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465948).length < 2 ^ (prefixWord ++ tailWord_3465948).sum := by decide
  have hdescent : baseEnd_3465948 < baseStart_3465948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465993 : List Nat := [1, 2, 1, 1, 3, 2, 5, 3, 1, 3]
def baseStart_3465993 : Nat := 118140960795 + 3465993 * 2 ^ 59
def prefixEnd_3465993 : Nat := 4983230072969 + 3 ^ 40 * 3465993 * 2
def baseEnd_3465993 : Nat := 1186480236079308680098463

theorem tailTrace_3465993 : CollatzResearch.WordTrace tailWord_3465993 prefixEnd_3465993 1186480236079308680098463 := by
  unfold tailWord_3465993
  simp only [CollatzResearch.WordTrace]
  refine ⟨126415150132306780322402633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84276766754871186881601755 126415150132306780322402633)
  ·
    refine ⟨94811362599230085241801975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126415150132306780322402633 94811362599230085241801975)
    ·
      refine ⟨142217043898845127862702963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94811362599230085241801975 142217043898845127862702963)
      ·
        refine ⟨213325565848267691794054445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142217043898845127862702963 213325565848267691794054445)
        ·
          refine ⟨79997087193100384422770417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213325565848267691794054445 79997087193100384422770417)
          ·
            refine ⟨59997815394825288317077813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79997087193100384422770417 59997815394825288317077813)
            ·
              refine ⟨5624795193264870779726045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59997815394825288317077813 5624795193264870779726045)
              ·
                refine ⟨2109298197474326542397267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5624795193264870779726045 2109298197474326542397267)
                ·
                  refine ⟨3163947296211489813595901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109298197474326542397267 3163947296211489813595901)
                  ·
                    refine ⟨1186480236079308680098463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3163947296211489813595901 1186480236079308680098463)
                    ·
                      rfl

theorem cell22_3465993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 1, 3].length) (baseStart_3465993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3465993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3465993 prefixEnd_3465993 := by exact prefixLift 3465993
  have htrace : WordTrace (prefixWord ++ tailWord_3465993) baseStart_3465993 baseEnd_3465993 := by
    simpa [prefixWord, tailWord_3465993, baseEnd_3465993] using wordTrace_append hprefix tailTrace_3465993
  have hstable : (prefixWord ++ tailWord_3465993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465993).length < 2 ^ (prefixWord ++ tailWord_3465993).sum := by decide
  have hdescent : baseEnd_3465993 < baseStart_3465993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466010 : List Nat := [3, 1, 1, 3, 2, 1, 5, 2, 1, 3]
def baseStart_3466010 : Nat := 118140960795 + 3466010 * 2 ^ 59
def prefixEnd_3466010 : Nat := 4983230072969 + 3 ^ 40 * 3466010 * 2
def baseEnd_3466010 : Nat := 1186486055526726302423411

theorem tailTrace_3466010 : CollatzResearch.WordTrace tailWord_3466010 prefixEnd_3466010 1186486055526726302423411 := by
  unfold tailWord_3466010
  simp only [CollatzResearch.WordTrace]
  refine ⟨31603942543311298056442871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84277180115496794817180989 31603942543311298056442871)
  ·
    refine ⟨47405913814966947084664307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31603942543311298056442871 47405913814966947084664307)
    ·
      refine ⟨71108870722450420626996461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47405913814966947084664307 71108870722450420626996461)
      ·
        refine ⟨26665826520918907735123673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71108870722450420626996461 26665826520918907735123673)
        ·
          refine ⟨19999369890689180801342755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26665826520918907735123673 19999369890689180801342755)
          ·
            refine ⟨29999054836033771202014133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19999369890689180801342755 29999054836033771202014133)
            ·
              refine ⟨2812411390878166050188825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29999054836033771202014133 2812411390878166050188825)
              ·
                refine ⟨2109308543158624537641619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2812411390878166050188825 2109308543158624537641619)
                ·
                  refine ⟨3163962814737936806462429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109308543158624537641619 3163962814737936806462429)
                  ·
                    refine ⟨1186486055526726302423411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3163962814737936806462429 1186486055526726302423411)
                    ·
                      rfl

theorem cell22_3466010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_3466010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466010 prefixEnd_3466010 := by exact prefixLift 3466010
  have htrace : WordTrace (prefixWord ++ tailWord_3466010) baseStart_3466010 baseEnd_3466010 := by
    simpa [prefixWord, tailWord_3466010, baseEnd_3466010] using wordTrace_append hprefix tailTrace_3466010
  have hstable : (prefixWord ++ tailWord_3466010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466010).length < 2 ^ (prefixWord ++ tailWord_3466010).sum := by decide
  have hdescent : baseEnd_3466010 < baseStart_3466010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466019 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 3, 4]
def baseStart_3466019 : Nat := 118140960795 + 3466019 * 2 ^ 59
def prefixEnd_3466019 : Nat := 4983230072969 + 3 ^ 40 * 3466019 * 2
def baseEnd_3466019 : Nat := 1186489136410653278948383

theorem tailTrace_3466019 : CollatzResearch.WordTrace tailWord_3466019 prefixEnd_3466019 1186489136410653278948383 := by
  unfold tailWord_3466019
  simp only [CollatzResearch.WordTrace]
  refine ⟨126416098430212586762849111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84277398953475057841899407 126416098430212586762849111)
  ·
    refine ⟨189624147645318880144273667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126416098430212586762849111 189624147645318880144273667)
    ·
      refine ⟨284436221467978320216410501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189624147645318880144273667 284436221467978320216410501)
      ·
        refine ⟨53331791525245935040576969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284436221467978320216410501 53331791525245935040576969)
        ·
          refine ⟨39998843643934451280432727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53331791525245935040576969 39998843643934451280432727)
          ·
            refine ⟨59998265465901676920649091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39998843643934451280432727 59998265465901676920649091)
            ·
              refine ⟨89997398198852515380973637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59998265465901676920649091 89997398198852515380973637)
              ·
                refine ⟨16874512162284846633932557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89997398198852515380973637 16874512162284846633932557)
                ·
                  refine ⟨6327942060856817487724709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16874512162284846633932557 6327942060856817487724709)
                  ·
                    refine ⟨1186489136410653278948383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6327942060856817487724709 1186489136410653278948383)
                    ·
                      rfl

theorem cell22_3466019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 4].length) (baseStart_3466019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466019 prefixEnd_3466019 := by exact prefixLift 3466019
  have htrace : WordTrace (prefixWord ++ tailWord_3466019) baseStart_3466019 baseEnd_3466019 := by
    simpa [prefixWord, tailWord_3466019, baseEnd_3466019] using wordTrace_append hprefix tailTrace_3466019
  have hstable : (prefixWord ++ tailWord_3466019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466019).length < 2 ^ (prefixWord ++ tailWord_3466019).sum := by decide
  have hdescent : baseEnd_3466019 < baseStart_3466019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466034 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 8]
def baseStart_3466034 : Nat := 118140960795 + 3466034 * 2 ^ 59
def prefixEnd_3466034 : Nat := 4983230072969 + 3 ^ 40 * 3466034 * 2
def baseEnd_3466034 : Nat := 395498090405732746607779

theorem tailTrace_3466034 : CollatzResearch.WordTrace tailWord_3466034 prefixEnd_3466034 395498090405732746607779 := by
  unfold tailWord_3466034
  simp only [CollatzResearch.WordTrace]
  refine ⟨31604161381289561081161289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84277763683438829549763437 31604161381289561081161289)
  ·
    refine ⟨23703121035967170810870967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31604161381289561081161289 23703121035967170810870967)
    ·
      refine ⟨35554681553950756216306451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23703121035967170810870967 35554681553950756216306451)
      ·
        refine ⟨53332022330926134324459677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35554681553950756216306451 53332022330926134324459677)
        ·
          refine ⟨19999508374097300371672379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53332022330926134324459677 19999508374097300371672379)
          ·
            refine ⟨29999262561145950557508569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19999508374097300371672379 29999262561145950557508569)
            ·
              refine ⟨22499446920859462918131427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29999262561145950557508569 22499446920859462918131427)
              ·
                refine ⟨33749170381289194377197141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22499446920859462918131427 33749170381289194377197141)
                ·
                  refine ⟨395498090405732746607779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33749170381289194377197141 395498090405732746607779)
                  ·
                    rfl

theorem cell22_3466034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_3466034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466034 prefixEnd_3466034 := by exact prefixLift 3466034
  have htrace : WordTrace (prefixWord ++ tailWord_3466034) baseStart_3466034 baseEnd_3466034 := by
    simpa [prefixWord, tailWord_3466034, baseEnd_3466034] using wordTrace_append hprefix tailTrace_3466034
  have hstable : (prefixWord ++ tailWord_3466034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466034).length < 2 ^ (prefixWord ++ tailWord_3466034).sum := by decide
  have hdescent : baseEnd_3466034 < baseStart_3466034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466051 : List Nat := [1, 1, 1, 3, 1, 4, 2, 5, 4]
def baseStart_3466051 : Nat := 118140960795 + 3466051 * 2 ^ 59
def prefixEnd_3466051 : Nat := 4983230072969 + 3 ^ 40 * 3466051 * 2
def baseEnd_3466051 : Nat := 395500030221538620716095

theorem tailTrace_3466051 : CollatzResearch.WordTrace tailWord_3466051 prefixEnd_3466051 395500030221538620716095 := by
  unfold tailWord_3466051
  simp only [CollatzResearch.WordTrace]
  refine ⟨126417265566096656228014007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84278177044064437485342671 126417265566096656228014007)
  ·
    refine ⟨189625898349144984342021011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126417265566096656228014007 189625898349144984342021011)
    ·
      refine ⟨284438847523717476513031517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189625898349144984342021011 284438847523717476513031517)
      ·
        refine ⟨106664567821394053692386819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284438847523717476513031517 106664567821394053692386819)
        ·
          refine ⟨159996851732091080538580229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106664567821394053692386819 159996851732091080538580229)
          ·
            refine ⟨29999409699767077600983793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159996851732091080538580229 29999409699767077600983793)
            ·
              refine ⟨22499557274825308200737845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29999409699767077600983793 22499557274825308200737845)
              ·
                refine ⟨2109333494514872643819173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22499557274825308200737845 2109333494514872643819173)
                ·
                  refine ⟨395500030221538620716095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2109333494514872643819173 395500030221538620716095)
                  ·
                    rfl

theorem cell22_3466051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 4].length) (baseStart_3466051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466051 prefixEnd_3466051 := by exact prefixLift 3466051
  have htrace : WordTrace (prefixWord ++ tailWord_3466051) baseStart_3466051 baseEnd_3466051 := by
    simpa [prefixWord, tailWord_3466051, baseEnd_3466051] using wordTrace_append hprefix tailTrace_3466051
  have hstable : (prefixWord ++ tailWord_3466051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466051).length < 2 ^ (prefixWord ++ tailWord_3466051).sum := by decide
  have hdescent : baseEnd_3466051 < baseStart_3466051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466061 : List Nat := [1, 6, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_3466061 : Nat := 118140960795 + 3466061 * 2 ^ 59
def prefixEnd_3466061 : Nat := 4983230072969 + 3 ^ 40 * 3466061 * 2
def baseEnd_3466061 : Nat := 1186503513868979169398255

theorem tailTrace_3466061 : CollatzResearch.WordTrace tailWord_3466061 prefixEnd_3466061 1186503513868979169398255 := by
  unfold tailWord_3466061
  simp only [CollatzResearch.WordTrace]
  refine ⟨126417630296060427935878037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84278420197373618623918691 126417630296060427935878037)
  ·
    refine ⟨5925826420127832559494283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126417630296060427935878037 5925826420127832559494283)
    ·
      refine ⟨8888739630191748839241425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5925826420127832559494283 8888739630191748839241425)
      ·
        refine ⟨6666554722643811629431069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8888739630191748839241425 6666554722643811629431069)
        ·
          refine ⟨2499958020991429361036651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6666554722643811629431069 2499958020991429361036651)
          ·
            refine ⟨3749937031487144041554977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2499958020991429361036651 3749937031487144041554977)
            ·
              refine ⟨2812452773615358031166233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3749937031487144041554977 2812452773615358031166233)
              ·
                refine ⟨2109339580211518523374675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2812452773615358031166233 2109339580211518523374675)
                ·
                  refine ⟨3164009370317277785062013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109339580211518523374675 3164009370317277785062013)
                  ·
                    refine ⟨1186503513868979169398255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3164009370317277785062013 1186503513868979169398255)
                    ·
                      rfl

theorem cell22_3466061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_3466061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466061 prefixEnd_3466061 := by exact prefixLift 3466061
  have htrace : WordTrace (prefixWord ++ tailWord_3466061) baseStart_3466061 baseEnd_3466061 := by
    simpa [prefixWord, tailWord_3466061, baseEnd_3466061] using wordTrace_append hprefix tailTrace_3466061
  have hstable : (prefixWord ++ tailWord_3466061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466061).length < 2 ^ (prefixWord ++ tailWord_3466061).sum := by decide
  have hdescent : baseEnd_3466061 < baseStart_3466061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466083 : List Nat := [1, 1, 1, 5, 3, 1, 2, 3, 2, 3]
def baseStart_3466083 : Nat := 118140960795 + 3466083 * 2 ^ 59
def prefixEnd_3466083 : Nat := 4983230072969 + 3 ^ 40 * 3466083 * 2
def baseEnd_3466083 : Nat := 1186511044918578445348187

theorem tailTrace_3466083 : CollatzResearch.WordTrace tailWord_3466083 prefixEnd_3466083 1186511044918578445348187 := by
  unfold tailWord_3466083
  simp only [CollatzResearch.WordTrace]
  refine ⟨126418432701980725693178903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84278955134653817128785935 126418432701980725693178903)
  ·
    refine ⟨189627649052971088539768355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126418432701980725693178903 189627649052971088539768355)
    ·
      refine ⟨284441473579456632809652533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189627649052971088539768355 284441473579456632809652533)
      ·
        refine ⟨26666388148074059325904925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 284441473579456632809652533 26666388148074059325904925)
        ·
          refine ⟨9999895555527772247214347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26666388148074059325904925 9999895555527772247214347)
          ·
            refine ⟨14999843333291658370821521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9999895555527772247214347 14999843333291658370821521)
            ·
              refine ⟨11249882499968743778116141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14999843333291658370821521 11249882499968743778116141)
              ·
                refine ⟨4218705937488278916793553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11249882499968743778116141 4218705937488278916793553)
                ·
                  refine ⟨3164029453116209187595165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4218705937488278916793553 3164029453116209187595165)
                  ·
                    refine ⟨1186511044918578445348187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3164029453116209187595165 1186511044918578445348187)
                    ·
                      rfl

theorem cell22_3466083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 3].length) (baseStart_3466083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466083 prefixEnd_3466083 := by exact prefixLift 3466083
  have htrace : WordTrace (prefixWord ++ tailWord_3466083) baseStart_3466083 baseEnd_3466083 := by
    simpa [prefixWord, tailWord_3466083, baseEnd_3466083] using wordTrace_append hprefix tailTrace_3466083
  have hstable : (prefixWord ++ tailWord_3466083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466083).length < 2 ^ (prefixWord ++ tailWord_3466083).sum := by decide
  have hdescent : baseEnd_3466083 < baseStart_3466083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466205 : List Nat := [1, 4, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3466205 : Nat := 118140960795 + 3466205 * 2 ^ 59
def prefixEnd_3466205 : Nat := 4983230072969 + 3 ^ 40 * 3466205 * 2
def baseEnd_3466205 : Nat := 1186552808011810793797813

theorem tailTrace_3466205 : CollatzResearch.WordTrace tailWord_3466205 prefixEnd_3466205 1186552808011810793797813 := by
  unfold tailWord_3466205
  simp only [CollatzResearch.WordTrace]
  refine ⟨126422882407538740529120069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84281921605025827019413379 126422882407538740529120069)
  ·
    refine ⟨23704290451413513849210013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126422882407538740529120069 23704290451413513849210013)
    ·
      refine ⟨8889108919280067693453755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23704290451413513849210013 8889108919280067693453755)
      ·
        refine ⟨13333663378920101540180633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8889108919280067693453755 13333663378920101540180633)
        ·
          refine ⟨10000247534190076155135475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13333663378920101540180633 10000247534190076155135475)
          ·
            refine ⟨15000371301285114232703213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10000247534190076155135475 15000371301285114232703213)
            ·
              refine ⟨5625139237981917837263705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15000371301285114232703213 5625139237981917837263705)
              ·
                refine ⟨4218854428486438377947779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5625139237981917837263705 4218854428486438377947779)
                ·
                  refine ⟨6328281642729657566921669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4218854428486438377947779 6328281642729657566921669)
                  ·
                    refine ⟨1186552808011810793797813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6328281642729657566921669 1186552808011810793797813)
                    ·
                      rfl

theorem cell22_3466205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3466205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466205 prefixEnd_3466205 := by exact prefixLift 3466205
  have htrace : WordTrace (prefixWord ++ tailWord_3466205) baseStart_3466205 baseEnd_3466205 := by
    simpa [prefixWord, tailWord_3466205, baseEnd_3466205] using wordTrace_append hprefix tailTrace_3466205
  have hstable : (prefixWord ++ tailWord_3466205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466205).length < 2 ^ (prefixWord ++ tailWord_3466205).sum := by decide
  have hdescent : baseEnd_3466205 < baseStart_3466205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466216 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 1, 6]
def baseStart_3466216 : Nat := 118140960795 + 3466216 * 2 ^ 59
def prefixEnd_3466216 : Nat := 4983230072969 + 3 ^ 40 * 3466216 * 2
def baseEnd_3466216 : Nat := 1186556573536610431772779

theorem tailTrace_3466216 : CollatzResearch.WordTrace tailWord_3466216 prefixEnd_3466216 1186556573536610431772779 := by
  unfold tailWord_3466216
  simp only [CollatzResearch.WordTrace]
  refine ⟨63211641805249444703885251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84282189073665926271847001 63211641805249444703885251)
  ·
    refine ⟨94817462707874167055827877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63211641805249444703885251 94817462707874167055827877)
    ·
      refine ⟨17778274257726406322967727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94817462707874167055827877 17778274257726406322967727)
      ·
        refine ⟨26667411386589609484451591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17778274257726406322967727 26667411386589609484451591)
        ·
          refine ⟨40001117079884414226677387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26667411386589609484451591 40001117079884414226677387)
          ·
            refine ⟨60001675619826621340016081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40001117079884414226677387 60001675619826621340016081)
            ·
              refine ⟨45001256714869966005012061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60001675619826621340016081 45001256714869966005012061)
              ·
                refine ⟨16875471268076237251879523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45001256714869966005012061 16875471268076237251879523)
                ·
                  refine ⟨25313206902114355877819285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16875471268076237251879523 25313206902114355877819285)
                  ·
                    refine ⟨1186556573536610431772779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25313206902114355877819285 1186556573536610431772779)
                    ·
                      rfl

theorem cell22_3466216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_3466216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466216 prefixEnd_3466216 := by exact prefixLift 3466216
  have htrace : WordTrace (prefixWord ++ tailWord_3466216) baseStart_3466216 baseEnd_3466216 := by
    simpa [prefixWord, tailWord_3466216, baseEnd_3466216] using wordTrace_append hprefix tailTrace_3466216
  have hstable : (prefixWord ++ tailWord_3466216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466216).length < 2 ^ (prefixWord ++ tailWord_3466216).sum := by decide
  have hdescent : baseEnd_3466216 < baseStart_3466216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466218 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_3466218 : Nat := 118140960795 + 3466218 * 2 ^ 59
def prefixEnd_3466218 : Nat := 4983230072969 + 3 ^ 40 * 3466218 * 2
def baseEnd_3466218 : Nat := 1186557258177483093222773

theorem tailTrace_3466218 : CollatzResearch.WordTrace tailWord_3466218 prefixEnd_3466218 1186557258177483093222773 := by
  unfold tailWord_3466218
  simp only [CollatzResearch.WordTrace]
  refine ⟨31605839139122910937335827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84282237704327762499562205 31605839139122910937335827)
  ·
    refine ⟨47408758708684366406003741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31605839139122910937335827 47408758708684366406003741)
    ·
      refine ⟨17778284515756637402251403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47408758708684366406003741 17778284515756637402251403)
      ·
        refine ⟨26667426773634956103377105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17778284515756637402251403 26667426773634956103377105)
        ·
          refine ⟨20000570080226217077532829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26667426773634956103377105 20000570080226217077532829)
          ·
            refine ⟨7500213780084831404074811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20000570080226217077532829 7500213780084831404074811)
            ·
              refine ⟨11250320670127247106112217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7500213780084831404074811 11250320670127247106112217)
              ·
                refine ⟨8437740502595435329584163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11250320670127247106112217 8437740502595435329584163)
                ·
                  refine ⟨12656610753893152994376245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8437740502595435329584163 12656610753893152994376245)
                  ·
                    refine ⟨1186557258177483093222773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12656610753893152994376245 1186557258177483093222773)
                    ·
                      rfl

theorem cell22_3466218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_3466218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466218 prefixEnd_3466218 := by exact prefixLift 3466218
  have htrace : WordTrace (prefixWord ++ tailWord_3466218) baseStart_3466218 baseEnd_3466218 := by
    simpa [prefixWord, tailWord_3466218, baseEnd_3466218] using wordTrace_append hprefix tailTrace_3466218
  have hstable : (prefixWord ++ tailWord_3466218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466218).length < 2 ^ (prefixWord ++ tailWord_3466218).sum := by decide
  have hdescent : baseEnd_3466218 < baseStart_3466218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466222 : List Nat := [4, 1, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_3466222 : Nat := 118140960795 + 3466222 * 2 ^ 59
def prefixEnd_3466222 : Nat := 4983230072969 + 3 ^ 40 * 3466222 * 2
def baseEnd_3466222 : Nat := 1186558627459228416122761

theorem tailTrace_3466222 : CollatzResearch.WordTrace tailWord_3466222 prefixEnd_3466222 1186558627459228416122761 := by
  unfold tailWord_3466222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15802937806059644054061115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84282334965651434954992613 15802937806059644054061115)
  ·
    refine ⟨23704406709089466081091673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15802937806059644054061115 23704406709089466081091673)
    ·
      refine ⟨17778305031817099560818755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23704406709089466081091673 17778305031817099560818755)
      ·
        refine ⟨26667457547725649341228133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17778305031817099560818755 26667457547725649341228133)
        ·
          refine ⟨5000148290198559251480275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26667457547725649341228133 5000148290198559251480275)
          ·
            refine ⟨7500222435297838877220413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5000148290198559251480275 7500222435297838877220413)
            ·
              refine ⟨2812583413236689578957655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7500222435297838877220413 2812583413236689578957655)
              ·
                refine ⟨4218875119855034368436483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812583413236689578957655 4218875119855034368436483)
                ·
                  refine ⟨6328312679782551552654725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4218875119855034368436483 6328312679782551552654725)
                  ·
                    refine ⟨1186558627459228416122761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6328312679782551552654725 1186558627459228416122761)
                    ·
                      rfl

theorem cell22_3466222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_3466222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466222 prefixEnd_3466222 := by exact prefixLift 3466222
  have htrace : WordTrace (prefixWord ++ tailWord_3466222) baseStart_3466222 baseEnd_3466222 := by
    simpa [prefixWord, tailWord_3466222, baseEnd_3466222] using wordTrace_append hprefix tailTrace_3466222
  have hstable : (prefixWord ++ tailWord_3466222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466222).length < 2 ^ (prefixWord ++ tailWord_3466222).sum := by decide
  have hdescent : baseEnd_3466222 < baseStart_3466222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466248 : List Nat := [2, 1, 3, 2, 1, 5, 1, 7]
def baseStart_3466248 : Nat := 118140960795 + 3466248 * 2 ^ 59
def prefixEnd_3466248 : Nat := 4983230072969 + 3 ^ 40 * 3466248 * 2
def baseEnd_3466248 : Nat := 131840836421174779441409

theorem tailTrace_3466248 : CollatzResearch.WordTrace tailWord_3466248 prefixEnd_3466248 131840836421174779441409 := by
  unfold tailWord_3466248
  simp only [CollatzResearch.WordTrace]
  refine ⟨63212225373191479436467699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84282967164255305915290265 63212225373191479436467699)
  ·
    refine ⟨94818338059787219154701549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63212225373191479436467699 94818338059787219154701549)
    ·
      refine ⟨35556876772420207183013081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94818338059787219154701549 35556876772420207183013081)
      ·
        refine ⟨26667657579315155387259811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35556876772420207183013081 26667657579315155387259811)
        ·
          refine ⟨40001486368972733080889717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26667657579315155387259811 40001486368972733080889717)
          ·
            refine ⟨3750139347091193726333411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40001486368972733080889717 3750139347091193726333411)
            ·
              refine ⟨5625209020636790589500117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3750139347091193726333411 5625209020636790589500117)
              ·
                refine ⟨131840836421174779441409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5625209020636790589500117 131840836421174779441409)
                ·
                  rfl

theorem cell22_3466248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 7].length) (baseStart_3466248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466248 prefixEnd_3466248 := by exact prefixLift 3466248
  have htrace : WordTrace (prefixWord ++ tailWord_3466248) baseStart_3466248 baseEnd_3466248 := by
    simpa [prefixWord, tailWord_3466248, baseEnd_3466248] using wordTrace_append hprefix tailTrace_3466248
  have hstable : (prefixWord ++ tailWord_3466248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466248).length < 2 ^ (prefixWord ++ tailWord_3466248).sum := by decide
  have hdescent : baseEnd_3466248 < baseStart_3466248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466297 : List Nat := [1, 2, 1, 5, 2, 1, 2, 4, 1, 3]
def baseStart_3466297 : Nat := 118140960795 + 3466297 * 2 ^ 59
def prefixEnd_3466297 : Nat := 4983230072969 + 3 ^ 40 * 3466297 * 2
def baseEnd_3466297 : Nat := 1186584301491953220497531

theorem tailTrace_3466297 : CollatzResearch.WordTrace tailWord_3466297 prefixEnd_3466297 1186584301491953220497531 := by
  unfold tailWord_3466297
  simp only [CollatzResearch.WordTrace]
  refine ⟨126426237923205440241469145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84284158615470293494312763 126426237923205440241469145)
  ·
    refine ⟨94819678442404080181101859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126426237923205440241469145 94819678442404080181101859)
    ·
      refine ⟨142229517663606120271652789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94819678442404080181101859 142229517663606120271652789)
      ·
        refine ⟨13334017280963073775467449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142229517663606120271652789 13334017280963073775467449)
        ·
          refine ⟨10000512960722305331600587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13334017280963073775467449 10000512960722305331600587)
          ·
            refine ⟨15000769441083457997400881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10000512960722305331600587 15000769441083457997400881)
            ·
              refine ⟨11250577080812593498050661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15000769441083457997400881 11250577080812593498050661)
              ·
                refine ⟨2109483202652361280884499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11250577080812593498050661 2109483202652361280884499)
                ·
                  refine ⟨3164224803978541921326749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109483202652361280884499 3164224803978541921326749)
                  ·
                    refine ⟨1186584301491953220497531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3164224803978541921326749 1186584301491953220497531)
                    ·
                      rfl

theorem cell22_3466297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 1, 3].length) (baseStart_3466297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466297 prefixEnd_3466297 := by exact prefixLift 3466297
  have htrace : WordTrace (prefixWord ++ tailWord_3466297) baseStart_3466297 baseEnd_3466297 := by
    simpa [prefixWord, tailWord_3466297, baseEnd_3466297] using wordTrace_append hprefix tailTrace_3466297
  have hstable : (prefixWord ++ tailWord_3466297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466297).length < 2 ^ (prefixWord ++ tailWord_3466297).sum := by decide
  have hdescent : baseEnd_3466297 < baseStart_3466297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466323 : List Nat := [1, 1, 1, 2, 1, 1, 2, 8, 1, 4]
def baseStart_3466323 : Nat := 118140960795 + 3466323 * 2 ^ 59
def prefixEnd_3466323 : Nat := 4983230072969 + 3 ^ 40 * 3466323 * 2
def baseEnd_3466323 : Nat := 1186593201823297819347451

theorem tailTrace_3466323 : CollatzResearch.WordTrace tailWord_3466323 prefixEnd_3466323 1186593201823297819347451 := by
  unfold tailWord_3466323
  simp only [CollatzResearch.WordTrace]
  refine ⟨126427186221111246681915623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84284790814074164454610415 126427186221111246681915623)
  ·
    refine ⟨189640779331666870022873435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126427186221111246681915623 189640779331666870022873435)
    ·
      refine ⟨284461168997500305034310153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189640779331666870022873435 284461168997500305034310153)
      ·
        refine ⟨213345876748125228775732615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284461168997500305034310153 213345876748125228775732615)
        ·
          refine ⟨320018815122187843163598923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213345876748125228775732615 320018815122187843163598923)
          ·
            refine ⟨480028222683281764745398385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320018815122187843163598923 480028222683281764745398385)
            ·
              refine ⟨360021167012461323559048789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480028222683281764745398385 360021167012461323559048789)
              ·
                refine ⟨4218998050927281135457603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 360021167012461323559048789 4218998050927281135457603)
                ·
                  refine ⟨6328497076390921703186405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4218998050927281135457603 6328497076390921703186405)
                  ·
                    refine ⟨1186593201823297819347451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6328497076390921703186405 1186593201823297819347451)
                    ·
                      rfl

theorem cell22_3466323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 4].length) (baseStart_3466323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466323 prefixEnd_3466323 := by exact prefixLift 3466323
  have htrace : WordTrace (prefixWord ++ tailWord_3466323) baseStart_3466323 baseEnd_3466323 := by
    simpa [prefixWord, tailWord_3466323, baseEnd_3466323] using wordTrace_append hprefix tailTrace_3466323
  have hstable : (prefixWord ++ tailWord_3466323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466323).length < 2 ^ (prefixWord ++ tailWord_3466323).sum := by decide
  have hdescent : baseEnd_3466323 < baseStart_3466323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466432 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 3, 3]
def baseStart_3466432 : Nat := 118140960795 + 3466432 * 2 ^ 59
def prefixEnd_3466432 : Nat := 4983230072969 + 3 ^ 40 * 3466432 * 2
def baseEnd_3466432 : Nat := 1186630514750857868372117

theorem tailTrace_3466432 : CollatzResearch.WordTrace tailWord_3466432 prefixEnd_3466432 1186630514750857868372117 := by
  unfold tailWord_3466432
  simp only [CollatzResearch.WordTrace]
  refine ⟨63215580888858179148816775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84287441185144238865089033 63215580888858179148816775)
  ·
    refine ⟨94823371333287268723225163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63215580888858179148816775 94823371333287268723225163)
    ·
      refine ⟨142235056999930903084837745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94823371333287268723225163 142235056999930903084837745)
      ·
        refine ⟨106676292749948177313628309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142235056999930903084837745 106676292749948177313628309)
        ·
          refine ⟨5000451222653820811576327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106676292749948177313628309 5000451222653820811576327)
          ·
            refine ⟨7500676833980731217364491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5000451222653820811576327 7500676833980731217364491)
            ·
              refine ⟨11251015250971096826046737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7500676833980731217364491 11251015250971096826046737)
              ·
                refine ⟨8438261438228322619535053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11251015250971096826046737 8438261438228322619535053)
                ·
                  refine ⟨3164348039335620982325645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8438261438228322619535053 3164348039335620982325645)
                  ·
                    refine ⟨1186630514750857868372117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3164348039335620982325645 1186630514750857868372117)
                    ·
                      rfl

theorem cell22_3466432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 3, 3].length) (baseStart_3466432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466432 prefixEnd_3466432 := by exact prefixLift 3466432
  have htrace : WordTrace (prefixWord ++ tailWord_3466432) baseStart_3466432 baseEnd_3466432 := by
    simpa [prefixWord, tailWord_3466432, baseEnd_3466432] using wordTrace_append hprefix tailTrace_3466432
  have hstable : (prefixWord ++ tailWord_3466432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466432).length < 2 ^ (prefixWord ++ tailWord_3466432).sum := by decide
  have hdescent : baseEnd_3466432 < baseStart_3466432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466505 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 6, 3]
def baseStart_3466505 : Nat := 118140960795 + 3466505 * 2 ^ 59
def prefixEnd_3466505 : Nat := 4983230072969 + 3 ^ 40 * 3466505 * 2
def baseEnd_3466505 : Nat := 1186655504142710011296893

theorem tailTrace_3466505 : CollatzResearch.WordTrace tailWord_3466505 prefixEnd_3466505 1186655504142710011296893 := by
  unfold tailWord_3466505
  simp only [CollatzResearch.WordTrace]
  refine ⟨126433824306451891765040969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84289216204301261176693979 126433824306451891765040969)
  ·
    refine ⟨94825368229838918823780727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126433824306451891765040969 94825368229838918823780727)
    ·
      refine ⟨142238052344758378235671091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94825368229838918823780727 142238052344758378235671091)
      ·
        refine ⟨213357078517137567353506637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142238052344758378235671091 213357078517137567353506637)
        ·
          refine ⟨80008904443926587757564989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213357078517137567353506637 80008904443926587757564989)
          ·
            refine ⟨30003339166472470409086871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80008904443926587757564989 30003339166472470409086871)
            ·
              refine ⟨45005008749708705613630307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30003339166472470409086871 45005008749708705613630307)
              ·
                refine ⟨67507513124563058420445461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45005008749708705613630307 67507513124563058420445461)
                ·
                  refine ⟨3164414677713893363458381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67507513124563058420445461 3164414677713893363458381)
                  ·
                    refine ⟨1186655504142710011296893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3164414677713893363458381 1186655504142710011296893)
                    ·
                      rfl

theorem cell22_3466505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 3].length) (baseStart_3466505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466505 prefixEnd_3466505 := by exact prefixLift 3466505
  have htrace : WordTrace (prefixWord ++ tailWord_3466505) baseStart_3466505 baseEnd_3466505 := by
    simpa [prefixWord, tailWord_3466505, baseEnd_3466505] using wordTrace_append hprefix tailTrace_3466505
  have hstable : (prefixWord ++ tailWord_3466505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466505).length < 2 ^ (prefixWord ++ tailWord_3466505).sum := by decide
  have hdescent : baseEnd_3466505 < baseStart_3466505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466507 : List Nat := [1, 1, 1, 1, 5, 3, 3, 3, 4]
def baseStart_3466507 : Nat := 118140960795 + 3466507 * 2 ^ 59
def prefixEnd_3466507 : Nat := 4983230072969 + 3 ^ 40 * 3466507 * 2
def baseEnd_3466507 : Nat := 395552062927860890915629

theorem tailTrace_3466507 : CollatzResearch.WordTrace tailWord_3466507 prefixEnd_3466507 395552062927860890915629 := by
  unfold tailWord_3466507
  simp only [CollatzResearch.WordTrace]
  refine ⟨126433897252444646106613775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84289264834963097404409183 126433897252444646106613775)
  ·
    refine ⟨189650845878666969159920663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126433897252444646106613775 189650845878666969159920663)
    ·
      refine ⟨284476268818000453739880995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189650845878666969159920663 284476268818000453739880995)
      ·
        refine ⟨426714403227000680609821493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284476268818000453739880995 426714403227000680609821493)
        ·
          refine ⟨40004475302531313807170765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 426714403227000680609821493 40004475302531313807170765)
          ·
            refine ⟨15001678238449242677689037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40004475302531313807170765 15001678238449242677689037)
            ·
              refine ⟨5625629339418466004133389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15001678238449242677689037 5625629339418466004133389)
              ·
                refine ⟨2109611002281924751550021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5625629339418466004133389 2109611002281924751550021)
                ·
                  refine ⟨395552062927860890915629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2109611002281924751550021 395552062927860890915629)
                  ·
                    rfl

theorem cell22_3466507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 4].length) (baseStart_3466507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466507 prefixEnd_3466507 := by exact prefixLift 3466507
  have htrace : WordTrace (prefixWord ++ tailWord_3466507) baseStart_3466507 baseEnd_3466507 := by
    simpa [prefixWord, tailWord_3466507, baseEnd_3466507] using wordTrace_append hprefix tailTrace_3466507
  have hstable : (prefixWord ++ tailWord_3466507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466507).length < 2 ^ (prefixWord ++ tailWord_3466507).sum := by decide
  have hdescent : baseEnd_3466507 < baseStart_3466507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466520 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 4, 4]
def baseStart_3466520 : Nat := 118140960795 + 3466520 * 2 ^ 59
def prefixEnd_3466520 : Nat := 4983230072969 + 3 ^ 40 * 3466520 * 2
def baseEnd_3466520 : Nat := 1186660638949254972171847

theorem tailTrace_3466520 : CollatzResearch.WordTrace tailWord_3466520 prefixEnd_3466520 1186660638949254972171847 := by
  unfold tailWord_3466520
  simp only [CollatzResearch.WordTrace]
  refine ⟨63217185700698774663418507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84289580934265032884558009 63217185700698774663418507)
  ·
    refine ⟨94825778551048161995127761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63217185700698774663418507 94825778551048161995127761)
    ·
      refine ⟨71119333913286121496345821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94825778551048161995127761 71119333913286121496345821)
      ·
        refine ⟨26669750217482295561129683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71119333913286121496345821 26669750217482295561129683)
        ·
          refine ⟨40004625326223443341694525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26669750217482295561129683 40004625326223443341694525)
          ·
            refine ⟨15001734497333791253135447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40004625326223443341694525 15001734497333791253135447)
            ·
              refine ⟨22502601746000686879703171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15001734497333791253135447 22502601746000686879703171)
              ·
                refine ⟨33753902619001030319554757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22502601746000686879703171 33753902619001030319554757)
                ·
                  refine ⟨6328856741062693184916517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33753902619001030319554757 6328856741062693184916517)
                  ·
                    refine ⟨1186660638949254972171847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6328856741062693184916517 1186660638949254972171847)
                    ·
                      rfl

theorem cell22_3466520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_3466520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466520 prefixEnd_3466520 := by exact prefixLift 3466520
  have htrace : WordTrace (prefixWord ++ tailWord_3466520) baseStart_3466520 baseEnd_3466520 := by
    simpa [prefixWord, tailWord_3466520, baseEnd_3466520] using wordTrace_append hprefix tailTrace_3466520
  have hstable : (prefixWord ++ tailWord_3466520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466520).length < 2 ^ (prefixWord ++ tailWord_3466520).sum := by decide
  have hdescent : baseEnd_3466520 < baseStart_3466520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466522 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 4, 3]
def baseStart_3466522 : Nat := 118140960795 + 3466522 * 2 ^ 59
def prefixEnd_3466522 : Nat := 4983230072969 + 3 ^ 40 * 3466522 * 2
def baseEnd_3466522 : Nat := 1186661323590127633621841

theorem tailTrace_3466522 : CollatzResearch.WordTrace tailWord_3466522 prefixEnd_3466522 1186661323590127633621841 := by
  unfold tailWord_3466522
  simp only [CollatzResearch.WordTrace]
  refine ⟨31608611086847575917102455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84289629564926869112273213 31608611086847575917102455)
  ·
    refine ⟨47412916630271363875653683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31608611086847575917102455 47412916630271363875653683)
    ·
      refine ⟨71119374945407045813480525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47412916630271363875653683 71119374945407045813480525)
      ·
        refine ⟨26669765604527642180055197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71119374945407045813480525 26669765604527642180055197)
        ·
          refine ⟨10001162101697865817520699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26669765604527642180055197 10001162101697865817520699)
          ·
            refine ⟨15001743152546798726281049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10001162101697865817520699 15001743152546798726281049)
            ·
              refine ⟨11251307364410099044710787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15001743152546798726281049 11251307364410099044710787)
              ·
                refine ⟨16876961046615148567066181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11251307364410099044710787 16876961046615148567066181)
                ·
                  refine ⟨3164430196240340356324909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16876961046615148567066181 3164430196240340356324909)
                  ·
                    refine ⟨1186661323590127633621841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3164430196240340356324909 1186661323590127633621841)
                    ·
                      rfl

theorem cell22_3466522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_3466522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466522 prefixEnd_3466522 := by exact prefixLift 3466522
  have htrace : WordTrace (prefixWord ++ tailWord_3466522) baseStart_3466522 baseEnd_3466522 := by
    simpa [prefixWord, tailWord_3466522, baseEnd_3466522] using wordTrace_append hprefix tailTrace_3466522
  have hstable : (prefixWord ++ tailWord_3466522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466522).length < 2 ^ (prefixWord ++ tailWord_3466522).sum := by decide
  have hdescent : baseEnd_3466522 < baseStart_3466522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466573 : List Nat := [1, 6, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_3466573 : Nat := 118140960795 + 3466573 * 2 ^ 59
def prefixEnd_3466573 : Nat := 4983230072969 + 3 ^ 40 * 3466573 * 2
def baseEnd_3466573 : Nat := 1186678781932380500596685

theorem tailTrace_3466573 : CollatzResearch.WordTrace tailWord_3466573 prefixEnd_3466573 1186678781932380500596685 := by
  unfold tailWord_3466573
  simp only [CollatzResearch.WordTrace]
  refine ⟨126436304470205539378516373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84290869646803692919010915 126436304470205539378516373)
  ·
    refine ⟨5926701772040884658367955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126436304470205539378516373 5926701772040884658367955)
    ·
      refine ⟨8890052658061326987551933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5926701772040884658367955 8890052658061326987551933)
      ·
        refine ⟨3333769746772997620331975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8890052658061326987551933 3333769746772997620331975)
        ·
          refine ⟨5000654620159496430497963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3333769746772997620331975 5000654620159496430497963)
          ·
            refine ⟨7500981930239244645746945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5000654620159496430497963 7500981930239244645746945)
            ·
              refine ⟨5625736447679433484310209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7500981930239244645746945 5625736447679433484310209)
              ·
                refine ⟨4219302335759575113232657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5625736447679433484310209 4219302335759575113232657)
                ·
                  refine ⟨3164476751819681334924493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4219302335759575113232657 3164476751819681334924493)
                  ·
                    refine ⟨1186678781932380500596685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3164476751819681334924493 1186678781932380500596685)
                    ·
                      rfl

theorem cell22_3466573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_3466573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466573 prefixEnd_3466573 := by exact prefixLift 3466573
  have htrace : WordTrace (prefixWord ++ tailWord_3466573) baseStart_3466573 baseEnd_3466573 := by
    simpa [prefixWord, tailWord_3466573, baseEnd_3466573] using wordTrace_append hprefix tailTrace_3466573
  have hstable : (prefixWord ++ tailWord_3466573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466573).length < 2 ^ (prefixWord ++ tailWord_3466573).sum := by decide
  have hdescent : baseEnd_3466573 < baseStart_3466573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466584 : List Nat := [2, 1, 2, 2, 1, 1, 5, 4, 1, 3]
def baseStart_3466584 : Nat := 118140960795 + 3466584 * 2 ^ 59
def prefixEnd_3466584 : Nat := 4983230072969 + 3 ^ 40 * 3466584 * 2
def baseEnd_3466584 : Nat := 1186682547457180138571651

theorem tailTrace_3466584 : CollatzResearch.WordTrace tailWord_3466584 prefixEnd_3466584 1186682547457180138571651 := by
  unfold tailWord_3466584
  simp only [CollatzResearch.WordTrace]
  refine ⟨63218352836582844128583403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84291137115443792171444537 63218352836582844128583403)
  ·
    refine ⟨94827529254874266192875105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63218352836582844128583403 94827529254874266192875105)
    ·
      refine ⟨71120646941155699644656329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94827529254874266192875105 71120646941155699644656329)
      ·
        refine ⟨53340485205866774733492247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71120646941155699644656329 53340485205866774733492247)
        ·
          refine ⟨80010727808800162100238371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53340485205866774733492247 80010727808800162100238371)
          ·
            refine ⟨120016091713200243150357557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80010727808800162100238371 120016091713200243150357557)
            ·
              refine ⟨11251508598112522795346021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120016091713200243150357557 11251508598112522795346021)
              ·
                refine ⟨2109657862146098024127379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11251508598112522795346021 2109657862146098024127379)
                ·
                  refine ⟨3164486793219147036191069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109657862146098024127379 3164486793219147036191069)
                  ·
                    refine ⟨1186682547457180138571651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3164486793219147036191069 1186682547457180138571651)
                    ·
                      rfl

theorem cell22_3466584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_3466584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466584 prefixEnd_3466584 := by exact prefixLift 3466584
  have htrace : WordTrace (prefixWord ++ tailWord_3466584) baseStart_3466584 baseEnd_3466584 := by
    simpa [prefixWord, tailWord_3466584, baseEnd_3466584] using wordTrace_append hprefix tailTrace_3466584
  have hstable : (prefixWord ++ tailWord_3466584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466584).length < 2 ^ (prefixWord ++ tailWord_3466584).sum := by decide
  have hdescent : baseEnd_3466584 < baseStart_3466584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466595 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 1, 7]
def baseStart_3466595 : Nat := 118140960795 + 3466595 * 2 ^ 59
def prefixEnd_3466595 : Nat := 4983230072969 + 3 ^ 40 * 3466595 * 2
def baseEnd_3466595 : Nat := 1186686312981979776546617

theorem tailTrace_3466595 : CollatzResearch.WordTrace tailWord_3466595 prefixEnd_3466595 1186686312981979776546617 := by
  unfold tailWord_3466595
  simp only [CollatzResearch.WordTrace]
  refine ⟨126437106876125837135817239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84291404584083891423878159 126437106876125837135817239)
  ·
    refine ⟨189655660314188755703725859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126437106876125837135817239 189655660314188755703725859)
    ·
      refine ⟨284483490471283133555588789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189655660314188755703725859 284483490471283133555588789)
      ·
        refine ⟨26670327231682793770836449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 284483490471283133555588789 26670327231682793770836449)
        ·
          refine ⟨20002745423762095328127337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26670327231682793770836449 20002745423762095328127337)
          ·
            refine ⟨15002059067821571496095503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20002745423762095328127337 15002059067821571496095503)
            ·
              refine ⟨22503088601732357244143255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15002059067821571496095503 22503088601732357244143255)
              ·
                refine ⟨33754632902598535866214883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22503088601732357244143255 33754632902598535866214883)
                ·
                  refine ⟨50631949353897803799322325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33754632902598535866214883 50631949353897803799322325)
                  ·
                    refine ⟨1186686312981979776546617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50631949353897803799322325 1186686312981979776546617)
                    ·
                      rfl

theorem cell22_3466595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_3466595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466595 prefixEnd_3466595 := by exact prefixLift 3466595
  have htrace : WordTrace (prefixWord ++ tailWord_3466595) baseStart_3466595 baseEnd_3466595 := by
    simpa [prefixWord, tailWord_3466595, baseEnd_3466595] using wordTrace_append hprefix tailTrace_3466595
  have hstable : (prefixWord ++ tailWord_3466595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466595).length < 2 ^ (prefixWord ++ tailWord_3466595).sum := by decide
  have hdescent : baseEnd_3466595 < baseStart_3466595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466749 : List Nat := [1, 4, 1, 1, 1, 5, 2, 2, 5]
def baseStart_3466749 : Nat := 118140960795 + 3466749 * 2 ^ 59
def prefixEnd_3466749 : Nat := 4983230072969 + 3 ^ 40 * 3466749 * 2
def baseEnd_3466749 : Nat := 395579676776391569398715

theorem tailTrace_3466749 : CollatzResearch.WordTrace tailWord_3466749 prefixEnd_3466749 395579676776391569398715 := by
  unfold tailWord_3466749
  simp only [CollatzResearch.WordTrace]
  refine ⟨126442723717567921436923301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84295149145045280957948867 126442723717567921436923301)
  ·
    refine ⟨23708010697043985269423119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126442723717567921436923301 23708010697043985269423119)
    ·
      refine ⟨35562016045565977904134679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23708010697043985269423119 35562016045565977904134679)
      ·
        refine ⟨53343024068348966856202019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35562016045565977904134679 53343024068348966856202019)
        ·
          refine ⟨80014536102523450284303029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53343024068348966856202019 80014536102523450284303029)
          ·
            refine ⟨7501362759611573464153409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80014536102523450284303029 7501362759611573464153409)
            ·
              refine ⟨5626022069708680098115057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7501362759611573464153409 5626022069708680098115057)
              ·
                refine ⟨4219516552281510073586293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5626022069708680098115057 4219516552281510073586293)
                ·
                  refine ⟨395579676776391569398715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4219516552281510073586293 395579676776391569398715)
                  ·
                    rfl

theorem cell22_3466749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_3466749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466749 prefixEnd_3466749 := by exact prefixLift 3466749
  have htrace : WordTrace (prefixWord ++ tailWord_3466749) baseStart_3466749 baseEnd_3466749 := by
    simpa [prefixWord, tailWord_3466749, baseEnd_3466749] using wordTrace_append hprefix tailTrace_3466749
  have hstable : (prefixWord ++ tailWord_3466749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466749).length < 2 ^ (prefixWord ++ tailWord_3466749).sum := by decide
  have hdescent : baseEnd_3466749 < baseStart_3466749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466753 : List Nat := [1, 2, 4, 1, 4, 1, 1, 4, 1, 3]
def baseStart_3466753 : Nat := 118140960795 + 3466753 * 2 ^ 59
def prefixEnd_3466753 : Nat := 4983230072969 + 3 ^ 40 * 3466753 * 2
def baseEnd_3466753 : Nat := 1186740399610920031096133

theorem tailTrace_3466753 : CollatzResearch.WordTrace tailWord_3466753 prefixEnd_3466753 1186740399610920031096133 := by
  unfold tailWord_3466753
  simp only [CollatzResearch.WordTrace]
  refine ⟨126442869609553430120068913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84295246406368953413379275 126442869609553430120068913)
  ·
    refine ⟨94832152207165072590051685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126442869609553430120068913 94832152207165072590051685)
    ·
      refine ⟨17781028538843451110634691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94832152207165072590051685 17781028538843451110634691)
      ·
        refine ⟨26671542808265176665952037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17781028538843451110634691 26671542808265176665952037)
        ·
          refine ⟨5000914276549720624866007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26671542808265176665952037 5000914276549720624866007)
          ·
            refine ⟨7501371414824580937299011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5000914276549720624866007 7501371414824580937299011)
            ·
              refine ⟨11252057122236871405948517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7501371414824580937299011 11252057122236871405948517)
              ·
                refine ⟨2109760710419413388615347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11252057122236871405948517 2109760710419413388615347)
                ·
                  refine ⟨3164641065629120082923021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109760710419413388615347 3164641065629120082923021)
                  ·
                    refine ⟨1186740399610920031096133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3164641065629120082923021 1186740399610920031096133)
                    ·
                      rfl

theorem cell22_3466753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_3466753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466753 prefixEnd_3466753 := by exact prefixLift 3466753
  have htrace : WordTrace (prefixWord ++ tailWord_3466753) baseStart_3466753 baseEnd_3466753 := by
    simpa [prefixWord, tailWord_3466753, baseEnd_3466753] using wordTrace_append hprefix tailTrace_3466753
  have hstable : (prefixWord ++ tailWord_3466753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466753).length < 2 ^ (prefixWord ++ tailWord_3466753).sum := by decide
  have hdescent : baseEnd_3466753 < baseStart_3466753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466764 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_3466764 : Nat := 118140960795 + 3466764 * 2 ^ 59
def prefixEnd_3466764 : Nat := 4983230072969 + 3 ^ 40 * 3466764 * 2
def baseEnd_3466764 : Nat := 1186744165135719669071099

theorem tailTrace_3466764 : CollatzResearch.WordTrace tailWord_3466764 prefixEnd_3466764 1186744165135719669071099 := by
  unfold tailWord_3466764
  simp only [CollatzResearch.WordTrace]
  refine ⟨63221635406256789499359673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84295513875009052665812897 63221635406256789499359673)
  ·
    refine ⟨47416226554692592124519755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63221635406256789499359673 47416226554692592124519755)
    ·
      refine ⟨71124339832038888186779633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47416226554692592124519755 71124339832038888186779633)
      ·
        refine ⟨53343254874029166140084725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71124339832038888186779633 53343254874029166140084725)
        ·
          refine ⟨5000930144440234325632943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53343254874029166140084725 5000930144440234325632943)
          ·
            refine ⟨7501395216660351488449415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5000930144440234325632943 7501395216660351488449415)
            ·
              refine ⟨11252092824990527232674123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7501395216660351488449415 11252092824990527232674123)
              ·
                refine ⟨16878139237485790849011185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11252092824990527232674123 16878139237485790849011185)
                ·
                  refine ⟨12658604428114343136758389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16878139237485790849011185 12658604428114343136758389)
                  ·
                    refine ⟨1186744165135719669071099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12658604428114343136758389 1186744165135719669071099)
                    ·
                      rfl

theorem cell22_3466764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_3466764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466764 prefixEnd_3466764 := by exact prefixLift 3466764
  have htrace : WordTrace (prefixWord ++ tailWord_3466764) baseStart_3466764 baseEnd_3466764 := by
    simpa [prefixWord, tailWord_3466764, baseEnd_3466764] using wordTrace_append hprefix tailTrace_3466764
  have hstable : (prefixWord ++ tailWord_3466764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466764).length < 2 ^ (prefixWord ++ tailWord_3466764).sum := by decide
  have hdescent : baseEnd_3466764 < baseStart_3466764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466837 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3466837 : Nat := 118140960795 + 3466837 * 2 ^ 59
def prefixEnd_3466837 : Nat := 4983230072969 + 3 ^ 40 * 3466837 * 2
def baseEnd_3466837 : Nat := 1186769154527571811995875

theorem tailTrace_3466837 : CollatzResearch.WordTrace tailWord_3466837 prefixEnd_3466837 1186769154527571811995875 := by
  unfold tailWord_3466837
  simp only [CollatzResearch.WordTrace]
  refine ⟨126445933341249112466126765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84297288894166074977417843 126445933341249112466126765)
  ·
    refine ⟨47417225002968417174797537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126445933341249112466126765 47417225002968417174797537)
    ·
      refine ⟨35562918752226312881098153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47417225002968417174797537 35562918752226312881098153)
      ·
        refine ⟨26672189064169734660823615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35562918752226312881098153 26672189064169734660823615)
        ·
          refine ⟨40008283596254601991235423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26672189064169734660823615 40008283596254601991235423)
          ·
            refine ⟨60012425394381902986853135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40008283596254601991235423 60012425394381902986853135)
            ·
              refine ⟨90018638091572854480279703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60012425394381902986853135 90018638091572854480279703)
              ·
                refine ⟨135027957137359281720419555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90018638091572854480279703 135027957137359281720419555)
                ·
                  refine ⟨202541935706038922580629333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135027957137359281720419555 202541935706038922580629333)
                  ·
                    refine ⟨1186769154527571811995875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 202541935706038922580629333 1186769154527571811995875)
                    ·
                      rfl

theorem cell22_3466837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3466837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466837 prefixEnd_3466837 := by exact prefixLift 3466837
  have htrace : WordTrace (prefixWord ++ tailWord_3466837) baseStart_3466837 baseEnd_3466837 := by
    simpa [prefixWord, tailWord_3466837, baseEnd_3466837] using wordTrace_append hprefix tailTrace_3466837
  have hstable : (prefixWord ++ tailWord_3466837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466837).length < 2 ^ (prefixWord ++ tailWord_3466837).sum := by decide
  have hdescent : baseEnd_3466837 < baseStart_3466837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466839 : List Nat := [1, 1, 3, 2, 2, 3, 4, 6]
def baseStart_3466839 : Nat := 118140960795 + 3466839 * 2 ^ 59
def prefixEnd_3466839 : Nat := 4983230072969 + 3 ^ 40 * 3466839 * 2
def baseEnd_3466839 : Nat := 131863315463160497049541

theorem tailTrace_3466839 : CollatzResearch.WordTrace tailWord_3466839 prefixEnd_3466839 131863315463160497049541 := by
  unfold tailWord_3466839
  simp only [CollatzResearch.WordTrace]
  refine ⟨126446006287241866807699571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84297337524827911205133047 126446006287241866807699571)
  ·
    refine ⟨189669009430862800211549357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126446006287241866807699571 189669009430862800211549357)
    ·
      refine ⟨71125878536573550079331009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189669009430862800211549357 71125878536573550079331009)
      ·
        refine ⟨53344408902430162559498257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71125878536573550079331009 53344408902430162559498257)
        ·
          refine ⟨40008306676822621919623693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53344408902430162559498257 40008306676822621919623693)
          ·
            refine ⟨15003115003808483219858885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40008306676822621919623693 15003115003808483219858885)
            ·
              refine ⟨2813084063214090603723541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15003115003808483219858885 2813084063214090603723541)
              ·
                refine ⟨131863315463160497049541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2813084063214090603723541 131863315463160497049541)
                ·
                  rfl

theorem cell22_3466839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 6].length) (baseStart_3466839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3466839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3466839 prefixEnd_3466839 := by exact prefixLift 3466839
  have htrace : WordTrace (prefixWord ++ tailWord_3466839) baseStart_3466839 baseEnd_3466839 := by
    simpa [prefixWord, tailWord_3466839, baseEnd_3466839] using wordTrace_append hprefix tailTrace_3466839
  have hstable : (prefixWord ++ tailWord_3466839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466839).length < 2 ^ (prefixWord ++ tailWord_3466839).sum := by decide
  have hdescent : baseEnd_3466839 < baseStart_3466839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467019 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 7]
def baseStart_3467019 : Nat := 118140960795 + 3467019 * 2 ^ 59
def prefixEnd_3467019 : Nat := 4983230072969 + 3 ^ 40 * 3467019 * 2
def baseEnd_3467019 : Nat := 395610485615661334648439

theorem tailTrace_3467019 : CollatzResearch.WordTrace tailWord_3467019 prefixEnd_3467019 395610485615661334648439 := by
  unfold tailWord_3467019
  simp only [CollatzResearch.WordTrace]
  refine ⟨126452571426589757549252111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84301714284393171699501407 126452571426589757549252111)
  ·
    refine ⟨189678857139884636323878167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126452571426589757549252111 189678857139884636323878167)
    ·
      refine ⟨284518285709826954485817251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189678857139884636323878167 284518285709826954485817251)
      ·
        refine ⟨426777428564740431728725877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284518285709826954485817251 426777428564740431728725877)
        ·
          refine ⟨40010383927944415474568051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 426777428564740431728725877 40010383927944415474568051)
          ·
            refine ⟨60015575891916623211852077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40010383927944415474568051 60015575891916623211852077)
            ·
              refine ⟨22505840959468733704444529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60015575891916623211852077 22505840959468733704444529)
              ·
                refine ⟨16879380719601550278333397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22505840959468733704444529 16879380719601550278333397)
                ·
                  refine ⟨395610485615661334648439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16879380719601550278333397 395610485615661334648439)
                  ·
                    rfl

theorem cell22_3467019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 7].length) (baseStart_3467019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467019 prefixEnd_3467019 := by exact prefixLift 3467019
  have htrace : WordTrace (prefixWord ++ tailWord_3467019) baseStart_3467019 baseEnd_3467019 := by
    simpa [prefixWord, tailWord_3467019, baseEnd_3467019] using wordTrace_append hprefix tailTrace_3467019
  have hstable : (prefixWord ++ tailWord_3467019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467019).length < 2 ^ (prefixWord ++ tailWord_3467019).sum := by decide
  have hdescent : baseEnd_3467019 < baseStart_3467019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467023 : List Nat := [1, 1, 2, 1, 1, 1, 4, 7, 1, 3]
def baseStart_3467023 : Nat := 118140960795 + 3467023 * 2 ^ 59
def prefixEnd_3467023 : Nat := 4983230072969 + 3 ^ 40 * 3467023 * 2
def baseEnd_3467023 : Nat := 1186832826128729326845305

theorem tailTrace_3467023 : CollatzResearch.WordTrace tailWord_3467023 prefixEnd_3467023 1186832826128729326845305 := by
  unfold tailWord_3467023
  simp only [CollatzResearch.WordTrace]
  refine ⟨126452717318575266232397723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84301811545716844154931815 126452717318575266232397723)
  ·
    refine ⟨189679075977862899348596585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126452717318575266232397723 189679075977862899348596585)
    ·
      refine ⟨142259306983397174511447439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189679075977862899348596585 142259306983397174511447439)
      ·
        refine ⟨213388960475095761767171159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142259306983397174511447439 213388960475095761767171159)
        ·
          refine ⟨320083440712643642650756739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213388960475095761767171159 320083440712643642650756739)
          ·
            refine ⟨480125161068965463976135109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320083440712643642650756739 480125161068965463976135109)
            ·
              refine ⟨90023467700431024495525333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 480125161068965463976135109 90023467700431024495525333)
              ·
                refine ⟨2109925024228852136613875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90023467700431024495525333 2109925024228852136613875)
                ·
                  refine ⟨3164887536343278204920813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109925024228852136613875 3164887536343278204920813)
                  ·
                    refine ⟨1186832826128729326845305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3164887536343278204920813 1186832826128729326845305)
                    ·
                      rfl

theorem cell22_3467023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 1, 3].length) (baseStart_3467023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467023 prefixEnd_3467023 := by exact prefixLift 3467023
  have htrace : WordTrace (prefixWord ++ tailWord_3467023) baseStart_3467023 baseEnd_3467023 := by
    simpa [prefixWord, tailWord_3467023, baseEnd_3467023] using wordTrace_append hprefix tailTrace_3467023
  have hstable : (prefixWord ++ tailWord_3467023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467023).length < 2 ^ (prefixWord ++ tailWord_3467023).sum := by decide
  have hdescent : baseEnd_3467023 < baseStart_3467023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467036 : List Nat := [2, 2, 3, 1, 1, 2, 2, 4, 5]
def baseStart_3467036 : Nat := 118140960795 + 3467036 * 2 ^ 59
def prefixEnd_3467036 : Nat := 4983230072969 + 3 ^ 40 * 3467036 * 2
def baseEnd_3467036 : Nat := 395612425431467208756755

theorem tailTrace_3467036 : CollatzResearch.WordTrace tailWord_3467036 prefixEnd_3467036 395612425431467208756755 := by
  unfold tailWord_3467036
  simp only [CollatzResearch.WordTrace]
  refine ⟨63226595733764084726310481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84302127645018779635080641 63226595733764084726310481)
  ·
    refine ⟨47419946800323063544732861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63226595733764084726310481 47419946800323063544732861)
    ·
      refine ⟨17782480050121148829274823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47419946800323063544732861 17782480050121148829274823)
      ·
        refine ⟨26673720075181723243912235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17782480050121148829274823 26673720075181723243912235)
        ·
          refine ⟨40010580112772584865868353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26673720075181723243912235 40010580112772584865868353)
          ·
            refine ⟨30007935084579438649401265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40010580112772584865868353 30007935084579438649401265)
            ·
              refine ⟨22505951313434578987050949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30007935084579438649401265 22505951313434578987050949)
              ·
                refine ⟨4219865871268983560072053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22505951313434578987050949 4219865871268983560072053)
                ·
                  refine ⟨395612425431467208756755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4219865871268983560072053 395612425431467208756755)
                  ·
                    rfl

theorem cell22_3467036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_3467036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467036 prefixEnd_3467036 := by exact prefixLift 3467036
  have htrace : WordTrace (prefixWord ++ tailWord_3467036) baseStart_3467036 baseEnd_3467036 := by
    simpa [prefixWord, tailWord_3467036, baseEnd_3467036] using wordTrace_append hprefix tailTrace_3467036
  have hstable : (prefixWord ++ tailWord_3467036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467036).length < 2 ^ (prefixWord ++ tailWord_3467036).sum := by decide
  have hdescent : baseEnd_3467036 < baseStart_3467036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467098 : List Nat := [3, 1, 1, 2, 1, 3, 3, 4, 4]
def baseStart_3467098 : Nat := 118140960795 + 3467098 * 2 ^ 59
def prefixEnd_3467098 : Nat := 4983230072969 + 3 ^ 40 * 3467098 * 2
def baseEnd_3467098 : Nat := 395619500053818043740025

theorem tailTrace_3467098 : CollatzResearch.WordTrace tailWord_3467098 prefixEnd_3467098 395619500053818043740025 := by
  unfold tailWord_3467098
  simp only [CollatzResearch.WordTrace]
  refine ⟨31613863198325888510344487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84303635195535702694251965 31613863198325888510344487)
  ·
    refine ⟨47420794797488832765516731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31613863198325888510344487 47420794797488832765516731)
    ·
      refine ⟨71131192196233249148275097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47420794797488832765516731 71131192196233249148275097)
      ·
        refine ⟨53348394147174936861206323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71131192196233249148275097 53348394147174936861206323)
        ·
          refine ⟨80022591220762405291809485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53348394147174936861206323 80022591220762405291809485)
          ·
            refine ⟨30008471707785901984428557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80022591220762405291809485 30008471707785901984428557)
            ·
              refine ⟨11253176890419713244160709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30008471707785901984428557 11253176890419713244160709)
              ·
                refine ⟨2109970666953696233280133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11253176890419713244160709 2109970666953696233280133)
                ·
                  refine ⟨395619500053818043740025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2109970666953696233280133 395619500053818043740025)
                  ·
                    rfl

theorem cell22_3467098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_3467098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467098 prefixEnd_3467098 := by exact prefixLift 3467098
  have htrace : WordTrace (prefixWord ++ tailWord_3467098) baseStart_3467098 baseEnd_3467098 := by
    simpa [prefixWord, tailWord_3467098, baseEnd_3467098] using wordTrace_append hprefix tailTrace_3467098
  have hstable : (prefixWord ++ tailWord_3467098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467098).length < 2 ^ (prefixWord ++ tailWord_3467098).sum := by decide
  have hdescent : baseEnd_3467098 < baseStart_3467098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467111 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 1, 6]
def baseStart_3467111 : Nat := 118140960795 + 3467111 * 2 ^ 59
def prefixEnd_3467111 : Nat := 4983230072969 + 3 ^ 40 * 3467111 * 2
def baseEnd_3467111 : Nat := 1186862950327126430645035

theorem tailTrace_3467111 : CollatzResearch.WordTrace tailWord_3467111 prefixEnd_3467111 1186862950327126430645035 := by
  unfold tailWord_3467111
  simp only [CollatzResearch.WordTrace]
  refine ⟨126455926942256457261601187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84303951294837638174400791 126455926942256457261601187)
  ·
    refine ⟨189683890413384685892401781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126455926942256457261601187 189683890413384685892401781)
    ·
      refine ⟨17782864726254814302412667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189683890413384685892401781 17782864726254814302412667)
      ·
        refine ⟨26674297089382221453619001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17782864726254814302412667 26674297089382221453619001)
        ·
          refine ⟨20005722817036666090214251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26674297089382221453619001 20005722817036666090214251)
          ·
            refine ⟨30008584225554999135321377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20005722817036666090214251 30008584225554999135321377)
            ·
              refine ⟨22506438169166249351491033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30008584225554999135321377 22506438169166249351491033)
              ·
                refine ⟨16879828626874687013618275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22506438169166249351491033 16879828626874687013618275)
                ·
                  refine ⟨25319742940312030520427413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16879828626874687013618275 25319742940312030520427413)
                  ·
                    refine ⟨1186862950327126430645035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25319742940312030520427413 1186862950327126430645035)
                    ·
                      rfl

theorem cell22_3467111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_3467111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467111 prefixEnd_3467111 := by exact prefixLift 3467111
  have htrace : WordTrace (prefixWord ++ tailWord_3467111) baseStart_3467111 baseEnd_3467111 := by
    simpa [prefixWord, tailWord_3467111, baseEnd_3467111] using wordTrace_append hprefix tailTrace_3467111
  have hstable : (prefixWord ++ tailWord_3467111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467111).length < 2 ^ (prefixWord ++ tailWord_3467111).sum := by decide
  have hdescent : baseEnd_3467111 < baseStart_3467111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467134 : List Nat := [4, 2, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3467134 : Nat := 118140960795 + 3467134 * 2 ^ 59
def prefixEnd_3467134 : Nat := 4983230072969 + 3 ^ 40 * 3467134 * 2
def baseEnd_3467134 : Nat := 1186870823697162037319965

theorem tailTrace_3467134 : CollatzResearch.WordTrace tailWord_3467134 prefixEnd_3467134 1186870823697162037319965 := by
  unfold tailWord_3467134
  simp only [CollatzResearch.WordTrace]
  refine ⟨15807095727646641523711057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84304510547448754793125637 15807095727646641523711057)
  ·
    refine ⟨11855321795734981142783293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15807095727646641523711057 11855321795734981142783293)
    ·
      refine ⟨4445745673400617928543735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11855321795734981142783293 4445745673400617928543735)
      ·
        refine ⟨6668618510100926892815603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4445745673400617928543735 6668618510100926892815603)
        ·
          refine ⟨10002927765151390339223405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6668618510100926892815603 10002927765151390339223405)
          ·
            refine ⟨3751097911931771377208777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10002927765151390339223405 3751097911931771377208777)
            ·
              refine ⟨2813323433948828532906583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3751097911931771377208777 2813323433948828532906583)
              ·
                refine ⟨4219985150923242799359875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2813323433948828532906583 4219985150923242799359875)
                ·
                  refine ⟨6329977726384864199039813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219985150923242799359875 6329977726384864199039813)
                  ·
                    refine ⟨1186870823697162037319965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6329977726384864199039813 1186870823697162037319965)
                    ·
                      rfl

theorem cell22_3467134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3467134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467134 prefixEnd_3467134 := by exact prefixLift 3467134
  have htrace : WordTrace (prefixWord ++ tailWord_3467134) baseStart_3467134 baseEnd_3467134 := by
    simpa [prefixWord, tailWord_3467134, baseEnd_3467134] using wordTrace_append hprefix tailTrace_3467134
  have hstable : (prefixWord ++ tailWord_3467134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467134).length < 2 ^ (prefixWord ++ tailWord_3467134).sum := by decide
  have hdescent : baseEnd_3467134 < baseStart_3467134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467175 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 3, 3]
def baseStart_3467175 : Nat := 118140960795 + 3467175 * 2 ^ 59
def prefixEnd_3467175 : Nat := 4983230072969 + 3 ^ 40 * 3467175 * 2
def baseEnd_3467175 : Nat := 1186884858835051597044839

theorem tailTrace_3467175 : CollatzResearch.WordTrace tailWord_3467175 prefixEnd_3467175 1186884858835051597044839 := by
  unfold tailWord_3467175
  simp only [CollatzResearch.WordTrace]
  refine ⟨126458261214024596191930979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84305507476016397461287319 126458261214024596191930979)
  ·
    refine ⟨189687391821036894287896469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126458261214024596191930979 189687391821036894287896469)
    ·
      refine ⟨8891596491611104419745147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 189687391821036894287896469 8891596491611104419745147)
      ·
        refine ⟨13337394737416656629617721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8891596491611104419745147 13337394737416656629617721)
        ·
          refine ⟨10003046053062492472213291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13337394737416656629617721 10003046053062492472213291)
          ·
            refine ⟨15004569079593738708319937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10003046053062492472213291 15004569079593738708319937)
            ·
              refine ⟨11253426809695304031239953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15004569079593738708319937 11253426809695304031239953)
              ·
                refine ⟨8440070107271478023429965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11253426809695304031239953 8440070107271478023429965)
                ·
                  refine ⟨3165026290226804258786237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8440070107271478023429965 3165026290226804258786237)
                  ·
                    refine ⟨1186884858835051597044839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3165026290226804258786237 1186884858835051597044839)
                    ·
                      rfl

theorem cell22_3467175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_3467175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467175 prefixEnd_3467175 := by exact prefixLift 3467175
  have htrace : WordTrace (prefixWord ++ tailWord_3467175) baseStart_3467175 baseEnd_3467175 := by
    simpa [prefixWord, tailWord_3467175, baseEnd_3467175] using wordTrace_append hprefix tailTrace_3467175
  have hstable : (prefixWord ++ tailWord_3467175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467175).length < 2 ^ (prefixWord ++ tailWord_3467175).sum := by decide
  have hdescent : baseEnd_3467175 < baseStart_3467175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467186 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_3467186 : Nat := 118140960795 + 3467186 * 2 ^ 59
def prefixEnd_3467186 : Nat := 4983230072969 + 3 ^ 40 * 3467186 * 2
def baseEnd_3467186 : Nat := 1186888624359851235019805

theorem tailTrace_3467186 : CollatzResearch.WordTrace tailWord_3467186 prefixEnd_3467186 1186888624359851235019805 := by
  unfold tailWord_3467186
  simp only [CollatzResearch.WordTrace]
  refine ⟨31614665604246186267645353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84305774944656496713720941 31614665604246186267645353)
  ·
    refine ⟨23710999203184639700734015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31614665604246186267645353 23710999203184639700734015)
    ·
      refine ⟨35566498804776959551101023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23710999203184639700734015 35566498804776959551101023)
      ·
        refine ⟨53349748207165439326651535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35566498804776959551101023 53349748207165439326651535)
        ·
          refine ⟨80024622310748158989977303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53349748207165439326651535 80024622310748158989977303)
          ·
            refine ⟨120036933466122238484965955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80024622310748158989977303 120036933466122238484965955)
            ·
              refine ⟨180055400199183357727448933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120036933466122238484965955 180055400199183357727448933)
              ·
                refine ⟨33760387537346879573896675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180055400199183357727448933 33760387537346879573896675)
                ·
                  refine ⟨50640581306020319360845013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33760387537346879573896675 50640581306020319360845013)
                  ·
                    refine ⟨1186888624359851235019805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50640581306020319360845013 1186888624359851235019805)
                    ·
                      rfl

theorem cell22_3467186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_3467186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467186 prefixEnd_3467186 := by exact prefixLift 3467186
  have htrace : WordTrace (prefixWord ++ tailWord_3467186) baseStart_3467186 baseEnd_3467186 := by
    simpa [prefixWord, tailWord_3467186, baseEnd_3467186] using wordTrace_append hprefix tailTrace_3467186
  have hstable : (prefixWord ++ tailWord_3467186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467186).length < 2 ^ (prefixWord ++ tailWord_3467186).sum := by decide
  have hdescent : baseEnd_3467186 < baseStart_3467186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467222 : List Nat := [5, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3467222 : Nat := 118140960795 + 3467222 * 2 ^ 59
def prefixEnd_3467222 : Nat := 4983230072969 + 3 ^ 40 * 3467222 * 2
def baseEnd_3467222 : Nat := 395633649298519713706565

theorem tailTrace_3467222 : CollatzResearch.WordTrace tailWord_3467222 prefixEnd_3467222 395633649298519713706565 := by
  unfold tailWord_3467222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7903748465303395201180745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84306650296569548812594613 7903748465303395201180745)
  ·
    refine ⟨5927811348977546400885559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7903748465303395201180745 5927811348977546400885559)
    ·
      refine ⟨8891717023466319601328339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5927811348977546400885559 8891717023466319601328339)
      ·
        refine ⟨13337575535199479401992509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8891717023466319601328339 13337575535199479401992509)
        ·
          refine ⟨5001590825699804775747191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13337575535199479401992509 5001590825699804775747191)
          ·
            refine ⟨7502386238549707163620787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5001590825699804775747191 7502386238549707163620787)
            ·
              refine ⟨11253579357824560745431181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502386238549707163620787 11253579357824560745431181)
              ·
                refine ⟨4220092259184210279536693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11253579357824560745431181 4220092259184210279536693)
                ·
                  refine ⟨395633649298519713706565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4220092259184210279536693 395633649298519713706565)
                  ·
                    rfl

theorem cell22_3467222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3467222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467222 prefixEnd_3467222 := by exact prefixLift 3467222
  have htrace : WordTrace (prefixWord ++ tailWord_3467222) baseStart_3467222 baseEnd_3467222 := by
    simpa [prefixWord, tailWord_3467222, baseEnd_3467222] using wordTrace_append hprefix tailTrace_3467222
  have hstable : (prefixWord ++ tailWord_3467222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467222).length < 2 ^ (prefixWord ++ tailWord_3467222).sum := by decide
  have hdescent : baseEnd_3467222 < baseStart_3467222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467235 : List Nat := [1, 1, 1, 6, 1, 2, 3, 2, 1, 4]
def baseStart_3467235 : Nat := 118140960795 + 3467235 * 2 ^ 59
def prefixEnd_3467235 : Nat := 4983230072969 + 3 ^ 40 * 3467235 * 2
def baseEnd_3467235 : Nat := 1186905398061231440544655

theorem tailTrace_3467235 : CollatzResearch.WordTrace tailWord_3467235 prefixEnd_3467235 1186905398061231440544655 := by
  unfold tailWord_3467235
  simp only [CollatzResearch.WordTrace]
  refine ⟨126460449593807226439115159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84306966395871484292743439 126460449593807226439115159)
  ·
    refine ⟨189690674390710839658672739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126460449593807226439115159 189690674390710839658672739)
    ·
      refine ⟨284536011586066259488009109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189690674390710839658672739 284536011586066259488009109)
      ·
        refine ⟨13337625543096855913500427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 284536011586066259488009109 13337625543096855913500427)
        ·
          refine ⟨20006438314645283870250641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13337625543096855913500427 20006438314645283870250641)
          ·
            refine ⟨15004828735983962902687981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20006438314645283870250641 15004828735983962902687981)
            ·
              refine ⟨5626810775993986088507993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15004828735983962902687981 5626810775993986088507993)
              ·
                refine ⟨4220108081995489566380995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5626810775993986088507993 4220108081995489566380995)
                ·
                  refine ⟨6330162122993234349571493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4220108081995489566380995 6330162122993234349571493)
                  ·
                    refine ⟨1186905398061231440544655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6330162122993234349571493 1186905398061231440544655)
                    ·
                      rfl

theorem cell22_3467235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 4].length) (baseStart_3467235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467235 prefixEnd_3467235 := by exact prefixLift 3467235
  have htrace : WordTrace (prefixWord ++ tailWord_3467235) baseStart_3467235 baseEnd_3467235 := by
    simpa [prefixWord, tailWord_3467235, baseEnd_3467235] using wordTrace_append hprefix tailTrace_3467235
  have hstable : (prefixWord ++ tailWord_3467235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467235).length < 2 ^ (prefixWord ++ tailWord_3467235).sum := by decide
  have hdescent : baseEnd_3467235 < baseStart_3467235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467248 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 6, 3]
def baseStart_3467248 : Nat := 118140960795 + 3467248 * 2 ^ 59
def prefixEnd_3467248 : Nat := 4983230072969 + 3 ^ 40 * 3467248 * 2
def baseEnd_3467248 : Nat := 1186909848226903739969615

theorem tailTrace_3467248 : CollatzResearch.WordTrace tailWord_3467248 prefixEnd_3467248 1186909848226903739969615 := by
  unfold tailWord_3467248
  simp only [CollatzResearch.WordTrace]
  refine ⟨63230461871380064829669199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84307282495173419772892265 63230461871380064829669199)
  ·
    refine ⟨94845692807070097244503799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63230461871380064829669199 94845692807070097244503799)
    ·
      refine ⟨142268539210605145866755699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94845692807070097244503799 142268539210605145866755699)
      ·
        refine ⟨213402808815907718800133549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142268539210605145866755699 213402808815907718800133549)
        ·
          refine ⟨80026053305965394550050081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213402808815907718800133549 80026053305965394550050081)
          ·
            refine ⟨60019539979474045912537561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80026053305965394550050081 60019539979474045912537561)
            ·
              refine ⟨45014654984605534434403171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60019539979474045912537561 45014654984605534434403171)
              ·
                refine ⟨67521982476908301651604757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45014654984605534434403171 67521982476908301651604757)
                ·
                  refine ⟨3165092928605076639918973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67521982476908301651604757 3165092928605076639918973)
                  ·
                    refine ⟨1186909848226903739969615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3165092928605076639918973 1186909848226903739969615)
                    ·
                      rfl

theorem cell22_3467248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 6, 3].length) (baseStart_3467248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467248 prefixEnd_3467248 := by exact prefixLift 3467248
  have htrace : WordTrace (prefixWord ++ tailWord_3467248) baseStart_3467248 baseEnd_3467248 := by
    simpa [prefixWord, tailWord_3467248, baseEnd_3467248] using wordTrace_append hprefix tailTrace_3467248
  have hstable : (prefixWord ++ tailWord_3467248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467248).length < 2 ^ (prefixWord ++ tailWord_3467248).sum := by decide
  have hdescent : baseEnd_3467248 < baseStart_3467248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467297 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 2, 4]
def baseStart_3467297 : Nat := 118140960795 + 3467297 * 2 ^ 59
def prefixEnd_3467297 : Nat := 4983230072969 + 3 ^ 40 * 3467297 * 2
def baseEnd_3467297 : Nat := 1186926621928283945494465

theorem tailTrace_3467297 : CollatzResearch.WordTrace tailWord_3467297 prefixEnd_3467297 1186926621928283945494465 := by
  unfold tailWord_3467297
  simp only [CollatzResearch.WordTrace]
  refine ⟨126462710919582611027872145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84308473946388407351914763 126462710919582611027872145)
  ·
    refine ⟨94847033189686958270904109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126462710919582611027872145 94847033189686958270904109)
    ·
      refine ⟨35567637446132609351589041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94847033189686958270904109 35567637446132609351589041)
      ·
        refine ⟨26675728084599457013691781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35567637446132609351589041 26675728084599457013691781)
        ·
          refine ⟨5001699015862398190067209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26675728084599457013691781 5001699015862398190067209)
          ·
            refine ⟨3751274261896798642550407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5001699015862398190067209 3751274261896798642550407)
            ·
              refine ⟨5626911392845197963825611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3751274261896798642550407 5626911392845197963825611)
              ·
                refine ⟨8440367089267796945738417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5626911392845197963825611 8440367089267796945738417)
                ·
                  refine ⟨6330275316950847709303813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8440367089267796945738417 6330275316950847709303813)
                  ·
                    refine ⟨1186926621928283945494465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6330275316950847709303813 1186926621928283945494465)
                    ·
                      rfl

theorem cell22_3467297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_3467297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467297 prefixEnd_3467297 := by exact prefixLift 3467297
  have htrace : WordTrace (prefixWord ++ tailWord_3467297) baseStart_3467297 baseEnd_3467297 := by
    simpa [prefixWord, tailWord_3467297, baseEnd_3467297] using wordTrace_append hprefix tailTrace_3467297
  have hstable : (prefixWord ++ tailWord_3467297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467297).length < 2 ^ (prefixWord ++ tailWord_3467297).sum := by decide
  have hdescent : baseEnd_3467297 < baseStart_3467297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467316 : List Nat := [2, 5, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_3467316 : Nat := 118140960795 + 3467316 * 2 ^ 59
def prefixEnd_3467316 : Nat := 4983230072969 + 3 ^ 40 * 3467316 * 2
def baseEnd_3467316 : Nat := 1186933126016574229269407

theorem tailTrace_3467316 : CollatzResearch.WordTrace tailWord_3467316 prefixEnd_3467316 1186933126016574229269407 := by
  unfold tailWord_3467316
  simp only [CollatzResearch.WordTrace]
  refine ⟨63231701953256888636406901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84308935937675851515209201 63231701953256888636406901)
  ·
    refine ⟨5927972058117833309663147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63231701953256888636406901 5927972058117833309663147)
    ·
      refine ⟨8891958087176749964494721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5927972058117833309663147 8891958087176749964494721)
      ·
        refine ⟨6668968565382562473371041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8891958087176749964494721 6668968565382562473371041)
        ·
          refine ⟨5001726424036921855028281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6668968565382562473371041 5001726424036921855028281)
          ·
            refine ⟨3751294818027691391271211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5001726424036921855028281 3751294818027691391271211)
            ·
              refine ⟨5626942227041537086906817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3751294818027691391271211 5626942227041537086906817)
              ·
                refine ⟨4220206670281152815180113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5626942227041537086906817 4220206670281152815180113)
                ·
                  refine ⟨3165155002710864611385085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4220206670281152815180113 3165155002710864611385085)
                  ·
                    refine ⟨1186933126016574229269407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3165155002710864611385085 1186933126016574229269407)
                    ·
                      rfl

theorem cell22_3467316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_3467316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467316 prefixEnd_3467316 := by exact prefixLift 3467316
  have htrace : WordTrace (prefixWord ++ tailWord_3467316) baseStart_3467316 baseEnd_3467316 := by
    simpa [prefixWord, tailWord_3467316, baseEnd_3467316] using wordTrace_append hprefix tailTrace_3467316
  have hstable : (prefixWord ++ tailWord_3467316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467316).length < 2 ^ (prefixWord ++ tailWord_3467316).sum := by decide
  have hdescent : baseEnd_3467316 < baseStart_3467316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467327 : List Nat := [1, 1, 2, 2, 3, 1, 4, 4, 1, 3]
def baseStart_3467327 : Nat := 118140960795 + 3467327 * 2 ^ 59
def prefixEnd_3467327 : Nat := 4983230072969 + 3 ^ 40 * 3467327 * 2
def baseEnd_3467327 : Nat := 1186936891541373867244373

theorem tailTrace_3467327 : CollatzResearch.WordTrace tailWord_3467327 prefixEnd_3467327 1186936891541373867244373 := by
  unfold tailWord_3467327
  simp only [CollatzResearch.WordTrace]
  refine ⟨126463805109473926151464235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84309203406315950767642823 126463805109473926151464235)
  ·
    refine ⟨189695707664210889227196353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126463805109473926151464235 189695707664210889227196353)
    ·
      refine ⟨142271780748158166920397265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189695707664210889227196353 142271780748158166920397265)
      ·
        refine ⟨106703835561118625190297949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142271780748158166920397265 106703835561118625190297949)
        ·
          refine ⟨40013938335419484446361731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106703835561118625190297949 40013938335419484446361731)
          ·
            refine ⟨60020907503129226669542597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40013938335419484446361731 60020907503129226669542597)
            ·
              refine ⟨11253920156836730000539237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60020907503129226669542597 11253920156836730000539237)
              ·
                refine ⟨2110110029406886875101107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11253920156836730000539237 2110110029406886875101107)
                ·
                  refine ⟨3165165044110330312651661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110110029406886875101107 3165165044110330312651661)
                  ·
                    refine ⟨1186936891541373867244373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3165165044110330312651661 1186936891541373867244373)
                    ·
                      rfl

theorem cell22_3467327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 1, 3].length) (baseStart_3467327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467327 prefixEnd_3467327 := by exact prefixLift 3467327
  have htrace : WordTrace (prefixWord ++ tailWord_3467327) baseStart_3467327 baseEnd_3467327 := by
    simpa [prefixWord, tailWord_3467327, baseEnd_3467327] using wordTrace_append hprefix tailTrace_3467327
  have hstable : (prefixWord ++ tailWord_3467327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467327).length < 2 ^ (prefixWord ++ tailWord_3467327).sum := by decide
  have hdescent : baseEnd_3467327 < baseStart_3467327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467385 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 6]
def baseStart_3467385 : Nat := 118140960795 + 3467385 * 2 ^ 59
def prefixEnd_3467385 : Nat := 4983230072969 + 3 ^ 40 * 3467385 * 2
def baseEnd_3467385 : Nat := 395652248708893683098065

theorem tailTrace_3467385 : CollatzResearch.WordTrace tailWord_3467385 prefixEnd_3467385 395652248708893683098065 := by
  unfold tailWord_3467385
  simp only [CollatzResearch.WordTrace]
  refine ⟨126465920543263802057075609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84310613695509201371383739 126465920543263802057075609)
  ·
    refine ⟨94849440407447851542806707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126465920543263802057075609 94849440407447851542806707)
    ·
      refine ⟨142274160611171777314210061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94849440407447851542806707 142274160611171777314210061)
      ·
        refine ⟨53352810229189416492828773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142274160611171777314210061 53352810229189416492828773)
        ·
          refine ⟨10003651917973015592405395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53352810229189416492828773 10003651917973015592405395)
          ·
            refine ⟨15005477876959523388608093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10003651917973015592405395 15005477876959523388608093)
            ·
              refine ⟨5627054203859821270728035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15005477876959523388608093 5627054203859821270728035)
              ·
                refine ⟨8440581305789731906092053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5627054203859821270728035 8440581305789731906092053)
                ·
                  refine ⟨395652248708893683098065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8440581305789731906092053 395652248708893683098065)
                  ·
                    rfl

theorem cell22_3467385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_3467385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467385 prefixEnd_3467385 := by exact prefixLift 3467385
  have htrace : WordTrace (prefixWord ++ tailWord_3467385) baseStart_3467385 baseEnd_3467385 := by
    simpa [prefixWord, tailWord_3467385, baseEnd_3467385] using wordTrace_append hprefix tailTrace_3467385
  have hstable : (prefixWord ++ tailWord_3467385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467385).length < 2 ^ (prefixWord ++ tailWord_3467385).sum := by decide
  have hdescent : baseEnd_3467385 < baseStart_3467385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467413 : List Nat := [1, 3, 2, 1, 1, 1, 3, 10]
def baseStart_3467413 : Nat := 118140960795 + 3467413 * 2 ^ 59
def prefixEnd_3467413 : Nat := 4983230072969 + 3 ^ 40 * 3467413 * 2
def baseEnd_3467413 : Nat := 131885147899877589954901

theorem tailTrace_3467413 : CollatzResearch.WordTrace tailWord_3467413 prefixEnd_3467413 131885147899877589954901 := by
  unfold tailWord_3467413
  simp only [CollatzResearch.WordTrace]
  refine ⟨126466941787162362839094893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84311294524774908559396595 126466941787162362839094893)
  ·
    refine ⟨47425103170185886064660585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126466941787162362839094893 47425103170185886064660585)
    ·
      refine ⟨35568827377639414548495439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47425103170185886064660585 35568827377639414548495439)
      ·
        refine ⟨53353241066459121822743159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35568827377639414548495439 53353241066459121822743159)
        ·
          refine ⟨80029861599688682734114739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53353241066459121822743159 80029861599688682734114739)
          ·
            refine ⟨120044792399533024101172109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80029861599688682734114739 120044792399533024101172109)
            ·
              refine ⟨45016797149824884037939541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120044792399533024101172109 45016797149824884037939541)
              ·
                refine ⟨131885147899877589954901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45016797149824884037939541 131885147899877589954901)
                ·
                  rfl

theorem cell22_3467413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 10].length) (baseStart_3467413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467413 prefixEnd_3467413 := by exact prefixLift 3467413
  have htrace : WordTrace (prefixWord ++ tailWord_3467413) baseStart_3467413 baseEnd_3467413 := by
    simpa [prefixWord, tailWord_3467413, baseEnd_3467413] using wordTrace_append hprefix tailTrace_3467413
  have hstable : (prefixWord ++ tailWord_3467413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467413).length < 2 ^ (prefixWord ++ tailWord_3467413).sum := by decide
  have hdescent : baseEnd_3467413 < baseStart_3467413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467505 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 5, 4]
def baseStart_3467505 : Nat := 118140960795 + 3467505 * 2 ^ 59
def prefixEnd_3467505 : Nat := 4983230072969 + 3 ^ 40 * 3467505 * 2
def baseEnd_3467505 : Nat := 1186997824579040736293827

theorem tailTrace_3467505 : CollatzResearch.WordTrace tailWord_3467505 prefixEnd_3467505 1186997824579040736293827 := by
  unfold tailWord_3467505
  simp only [CollatzResearch.WordTrace]
  refine ⟨126470297302829062551443969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84313531535219375034295979 126470297302829062551443969)
  ·
    refine ⟨94852722977121796913582977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126470297302829062551443969 94852722977121796913582977)
    ·
      refine ⟨71139542232841347685187233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94852722977121796913582977 71139542232841347685187233)
      ·
        refine ⟨53354656674631010763890425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71139542232841347685187233 53354656674631010763890425)
        ·
          refine ⟨40015992505973258072917819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53354656674631010763890425 40015992505973258072917819)
          ·
            refine ⟨60023988758959887109376729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40015992505973258072917819 60023988758959887109376729)
            ·
              refine ⟨45017991569219915332032547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60023988758959887109376729 45017991569219915332032547)
              ·
                refine ⟨67526987353829872998048821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45017991569219915332032547 67526987353829872998048821)
                ·
                  refine ⟨6330655064421550593567077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67526987353829872998048821 6330655064421550593567077)
                  ·
                    refine ⟨1186997824579040736293827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6330655064421550593567077 1186997824579040736293827)
                    ·
                      rfl

theorem cell22_3467505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_3467505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467505 prefixEnd_3467505 := by exact prefixLift 3467505
  have htrace : WordTrace (prefixWord ++ tailWord_3467505) baseStart_3467505 baseEnd_3467505 := by
    simpa [prefixWord, tailWord_3467505, baseEnd_3467505] using wordTrace_append hprefix tailTrace_3467505
  have hstable : (prefixWord ++ tailWord_3467505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467505).length < 2 ^ (prefixWord ++ tailWord_3467505).sum := by decide
  have hdescent : baseEnd_3467505 < baseStart_3467505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467520 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 6]
def baseStart_3467520 : Nat := 118140960795 + 3467520 * 2 ^ 59
def prefixEnd_3467520 : Nat := 4983230072969 + 3 ^ 40 * 3467520 * 2
def baseEnd_3467520 : Nat := 395667653128528565722927

theorem tailTrace_3467520 : CollatzResearch.WordTrace tailWord_3467520 prefixEnd_3467520 395667653128528565722927 := by
  unfold tailWord_3467520
  simp only [CollatzResearch.WordTrace]
  refine ⟨63235422198887360056620007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84313896265183146742160009 63235422198887360056620007)
  ·
    refine ⟨94853133298331040084930011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63235422198887360056620007 94853133298331040084930011)
    ·
      refine ⟨142279699947496560127395017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94853133298331040084930011 142279699947496560127395017)
      ·
        refine ⟨106709774960622420095546263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142279699947496560127395017 106709774960622420095546263)
        ·
          refine ⟨160064662440933630143319395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106709774960622420095546263 160064662440933630143319395)
          ·
            refine ⟨240096993661400445214979093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160064662440933630143319395 240096993661400445214979093)
            ·
              refine ⟨11254546577878145869452145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 240096993661400445214979093 11254546577878145869452145)
              ·
                refine ⟨8440909933408609402089109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11254546577878145869452145 8440909933408609402089109)
                ·
                  refine ⟨395667653128528565722927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8440909933408609402089109 395667653128528565722927)
                  ·
                    rfl

theorem cell22_3467520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_3467520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467520 prefixEnd_3467520 := by exact prefixLift 3467520
  have htrace : WordTrace (prefixWord ++ tailWord_3467520) baseStart_3467520 baseEnd_3467520 := by
    simpa [prefixWord, tailWord_3467520, baseEnd_3467520] using wordTrace_append hprefix tailTrace_3467520
  have hstable : (prefixWord ++ tailWord_3467520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467520).length < 2 ^ (prefixWord ++ tailWord_3467520).sum := by decide
  have hdescent : baseEnd_3467520 < baseStart_3467520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467535 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 1, 5]
def baseStart_3467535 : Nat := 118140960795 + 3467535 * 2 ^ 59
def prefixEnd_3467535 : Nat := 4983230072969 + 3 ^ 40 * 3467535 * 2
def baseEnd_3467535 : Nat := 1187008094192130658043735

theorem tailTrace_3467535 : CollatzResearch.WordTrace tailWord_3467535 prefixEnd_3467535 1187008094192130658043735 := by
  unfold tailWord_3467535
  simp only [CollatzResearch.WordTrace]
  refine ⟨126471391492720377675036059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84314260995146918450024039 126471391492720377675036059)
  ·
    refine ⟨189707087239080566512554089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126471391492720377675036059 189707087239080566512554089)
    ·
      refine ⟨142280315429310424884415567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189707087239080566512554089 142280315429310424884415567)
      ·
        refine ⟨213420473143965637326623351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142280315429310424884415567 213420473143965637326623351)
        ·
          refine ⟨320130709715948455989935027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213420473143965637326623351 320130709715948455989935027)
          ·
            refine ⟨480196064573922683984902541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320130709715948455989935027 480196064573922683984902541)
            ·
              refine ⟨180073524215221006494338453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 480196064573922683984902541 180073524215221006494338453)
              ·
                refine ⟨8440946447588484679422115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180073524215221006494338453 8440946447588484679422115)
                ·
                  refine ⟨12661419671382727019133173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8440946447588484679422115 12661419671382727019133173)
                  ·
                    refine ⟨1187008094192130658043735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12661419671382727019133173 1187008094192130658043735)
                    ·
                      rfl

theorem cell22_3467535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_3467535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467535 prefixEnd_3467535 := by exact prefixLift 3467535
  have htrace : WordTrace (prefixWord ++ tailWord_3467535) baseStart_3467535 baseEnd_3467535 := by
    simpa [prefixWord, tailWord_3467535, baseEnd_3467535] using wordTrace_append hprefix tailTrace_3467535
  have hstable : (prefixWord ++ tailWord_3467535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467535).length < 2 ^ (prefixWord ++ tailWord_3467535).sum := by decide
  have hdescent : baseEnd_3467535 < baseStart_3467535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467554 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 6]
def baseStart_3467554 : Nat := 118140960795 + 3467554 * 2 ^ 59
def prefixEnd_3467554 : Nat := 4983230072969 + 3 ^ 40 * 3467554 * 2
def baseEnd_3467554 : Nat := 395671532760140313939559

theorem tailTrace_3467554 : CollatzResearch.WordTrace tailWord_3467554 prefixEnd_3467554 395671532760140313939559 := by
  unfold tailWord_3467554
  simp only [CollatzResearch.WordTrace]
  refine ⟨31618021119912885979994429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84314722986434362613318477 31618021119912885979994429)
  ·
    refine ⟨11856757919967332242497911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31618021119912885979994429 11856757919967332242497911)
    ·
      refine ⟨17785136879950998363746867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11856757919967332242497911 17785136879950998363746867)
      ·
        refine ⟨26677705319926497545620301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17785136879950998363746867 26677705319926497545620301)
        ·
          refine ⟨10004139494972436579607613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26677705319926497545620301 10004139494972436579607613)
          ·
            refine ⟨3751552310614663717352855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10004139494972436579607613 3751552310614663717352855)
            ·
              refine ⟨5627328465921995576029283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3751552310614663717352855 5627328465921995576029283)
              ·
                refine ⟨8440992698882993364043925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5627328465921995576029283 8440992698882993364043925)
                ·
                  refine ⟨395671532760140313939559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8440992698882993364043925 395671532760140313939559)
                  ·
                    rfl

theorem cell22_3467554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_3467554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467554 prefixEnd_3467554 := by exact prefixLift 3467554
  have htrace : WordTrace (prefixWord ++ tailWord_3467554) baseStart_3467554 baseEnd_3467554 := by
    simpa [prefixWord, tailWord_3467554, baseEnd_3467554] using wordTrace_append hprefix tailTrace_3467554
  have hstable : (prefixWord ++ tailWord_3467554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467554).length < 2 ^ (prefixWord ++ tailWord_3467554).sum := by decide
  have hdescent : baseEnd_3467554 < baseStart_3467554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467582 : List Nat := [4, 2, 1, 2, 1, 2, 2, 8]
def baseStart_3467582 : Nat := 118140960795 + 3467582 * 2 ^ 59
def prefixEnd_3467582 : Nat := 4983230072969 + 3 ^ 40 * 3467582 * 2
def baseEnd_3467582 : Nat := 131891575916959800235399

theorem tailTrace_3467582 : CollatzResearch.WordTrace tailWord_3467582 prefixEnd_3467582 131891575916959800235399 := by
  unfold tailWord_3467582
  simp only [CollatzResearch.WordTrace]
  refine ⟨15809138215443763087749625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84315403815700069801331333 15809138215443763087749625)
  ·
    refine ⟨11856853661582822315812219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15809138215443763087749625 11856853661582822315812219)
    ·
      refine ⟨17785280492374233473718329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11856853661582822315812219 17785280492374233473718329)
      ·
        refine ⟨13338960369280675105288747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17785280492374233473718329 13338960369280675105288747)
        ·
          refine ⟨20008440553921012657933121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13338960369280675105288747 20008440553921012657933121)
          ·
            refine ⟨15006330415440759493449841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20008440553921012657933121 15006330415440759493449841)
            ·
              refine ⟨11254747811580569620087381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15006330415440759493449841 11254747811580569620087381)
              ·
                refine ⟨131891575916959800235399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11254747811580569620087381 131891575916959800235399)
                ·
                  rfl

theorem cell22_3467582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_3467582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467582 prefixEnd_3467582 := by exact prefixLift 3467582
  have htrace : WordTrace (prefixWord ++ tailWord_3467582) baseStart_3467582 baseEnd_3467582 := by
    simpa [prefixWord, tailWord_3467582, baseEnd_3467582] using wordTrace_append hprefix tailTrace_3467582
  have hstable : (prefixWord ++ tailWord_3467582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467582).length < 2 ^ (prefixWord ++ tailWord_3467582).sum := by decide
  have hdescent : baseEnd_3467582 < baseStart_3467582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467678 : List Nat := [4, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_3467678 : Nat := 118140960795 + 3467678 * 2 ^ 59
def prefixEnd_3467678 : Nat := 4983230072969 + 3 ^ 40 * 3467678 * 2
def baseEnd_3467678 : Nat := 395685682004841983906099

theorem tailTrace_3467678 : CollatzResearch.WordTrace tailWord_3467678 prefixEnd_3467678 395685682004841983906099 := by
  unfold tailWord_3467678
  simp only [CollatzResearch.WordTrace]
  refine ⟨15809575891400289137186461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84317738087468208731661125 15809575891400289137186461)
  ·
    refine ⟨5928590959275108426444923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15809575891400289137186461 5928590959275108426444923)
    ·
      refine ⟨8892886438912662639667385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5928590959275108426444923 8892886438912662639667385)
      ·
        refine ⟨6669664829184496979750539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8892886438912662639667385 6669664829184496979750539)
        ·
          refine ⟨10004497243776745469625809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6669664829184496979750539 10004497243776745469625809)
          ·
            refine ⟨7503372932832559102219357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10004497243776745469625809 7503372932832559102219357)
            ·
              refine ⟨2813764849812209663332259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7503372932832559102219357 2813764849812209663332259)
              ·
                refine ⟨4220647274718314494998389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2813764849812209663332259 4220647274718314494998389)
                ·
                  refine ⟨395685682004841983906099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4220647274718314494998389 395685682004841983906099)
                  ·
                    rfl

theorem cell22_3467678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_3467678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467678 prefixEnd_3467678 := by exact prefixLift 3467678
  have htrace : WordTrace (prefixWord ++ tailWord_3467678) baseStart_3467678 baseEnd_3467678 := by
    simpa [prefixWord, tailWord_3467678, baseEnd_3467678] using wordTrace_append hprefix tailTrace_3467678
  have hstable : (prefixWord ++ tailWord_3467678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467678).length < 2 ^ (prefixWord ++ tailWord_3467678).sum := by decide
  have hdescent : baseEnd_3467678 < baseStart_3467678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467719 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 2, 4]
def baseStart_3467719 : Nat := 118140960795 + 3467719 * 2 ^ 59
def prefixEnd_3467719 : Nat := 4983230072969 + 3 ^ 40 * 3467719 * 2
def baseEnd_3467719 : Nat := 1187071081152415511443171

theorem tailTrace_3467719 : CollatzResearch.WordTrace tailWord_3467719 prefixEnd_3467719 1187071081152415511443171 := by
  unfold tailWord_3467719
  simp only [CollatzResearch.WordTrace]
  refine ⟨126478102524053777099734211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84318735016035851399822807 126478102524053777099734211)
  ·
    refine ⟨189717153786080665649601317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126478102524053777099734211 189717153786080665649601317)
    ·
      refine ⟨35571966334890124809300247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189717153786080665649601317 35571966334890124809300247)
      ·
        refine ⟨53357949502335187213950371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35571966334890124809300247 53357949502335187213950371)
        ·
          refine ⟨80036924253502780820925557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53357949502335187213950371 80036924253502780820925557)
          ·
            refine ⟨7503461648765885701961771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80036924253502780820925557 7503461648765885701961771)
            ·
              refine ⟨11255192473148828552942657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7503461648765885701961771 11255192473148828552942657)
              ·
                refine ⟨8441394354861621414706993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11255192473148828552942657 8441394354861621414706993)
                ·
                  refine ⟨6331045766146216061030245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8441394354861621414706993 6331045766146216061030245)
                  ·
                    refine ⟨1187071081152415511443171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6331045766146216061030245 1187071081152415511443171)
                    ·
                      rfl

theorem cell22_3467719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_3467719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467719 prefixEnd_3467719 := by exact prefixLift 3467719
  have htrace : WordTrace (prefixWord ++ tailWord_3467719) baseStart_3467719 baseEnd_3467719 := by
    simpa [prefixWord, tailWord_3467719, baseEnd_3467719] using wordTrace_append hprefix tailTrace_3467719
  have hstable : (prefixWord ++ tailWord_3467719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467719).length < 2 ^ (prefixWord ++ tailWord_3467719).sum := by decide
  have hdescent : baseEnd_3467719 < baseStart_3467719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467779 : List Nat := [1, 1, 1, 3, 2, 1, 6, 2, 5]
def baseStart_3467779 : Nat := 118140960795 + 3467779 * 2 ^ 59
def prefixEnd_3467779 : Nat := 4983230072969 + 3 ^ 40 * 3467779 * 2
def baseEnd_3467779 : Nat := 395697206792865118314329

theorem tailTrace_3467779 : CollatzResearch.WordTrace tailWord_3467779 prefixEnd_3467779 395697206792865118314329 := by
  unfold tailWord_3467779
  simp only [CollatzResearch.WordTrace]
  refine ⟨126480290903836407346918391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84320193935890938231278927 126480290903836407346918391)
  ·
    refine ⟨189720436355754611020377587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126480290903836407346918391 189720436355754611020377587)
    ·
      refine ⟨284580654533631916530566381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189720436355754611020377587 284580654533631916530566381)
      ·
        refine ⟨106717745450111968698962393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284580654533631916530566381 106717745450111968698962393)
        ·
          refine ⟨80038309087583976524221795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106717745450111968698962393 80038309087583976524221795)
          ·
            refine ⟨120057463631375964786332693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80038309087583976524221795 120057463631375964786332693)
            ·
              refine ⟨5627693607720748349359345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120057463631375964786332693 5627693607720748349359345)
              ·
                refine ⟨4220770205790561262019509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5627693607720748349359345 4220770205790561262019509)
                ·
                  refine ⟨395697206792865118314329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4220770205790561262019509 395697206792865118314329)
                  ·
                    rfl

theorem cell22_3467779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 5].length) (baseStart_3467779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467779 prefixEnd_3467779 := by exact prefixLift 3467779
  have htrace : WordTrace (prefixWord ++ tailWord_3467779) baseStart_3467779 baseEnd_3467779 := by
    simpa [prefixWord, tailWord_3467779, baseEnd_3467779] using wordTrace_append hprefix tailTrace_3467779
  have hstable : (prefixWord ++ tailWord_3467779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467779).length < 2 ^ (prefixWord ++ tailWord_3467779).sum := by decide
  have hdescent : baseEnd_3467779 < baseStart_3467779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467809 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 3, 4]
def baseStart_3467809 : Nat := 118140960795 + 3467809 * 2 ^ 59
def prefixEnd_3467809 : Nat := 4983230072969 + 3 ^ 40 * 3467809 * 2
def baseEnd_3467809 : Nat := 1187101889991685276692895

theorem tailTrace_3467809 : CollatzResearch.WordTrace tailWord_3467809 prefixEnd_3467809 1187101889991685276692895 := by
  unfold tailWord_3467809
  simp only [CollatzResearch.WordTrace]
  refine ⟨126481385093727722470510481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84320923395818481647006987 126481385093727722470510481)
  ·
    refine ⟨94861038820295791852882861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126481385093727722470510481 94861038820295791852882861)
    ·
      refine ⟨35572889557610921944831073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94861038820295791852882861 35572889557610921944831073)
      ·
        refine ⟨26679667168208191458623305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35572889557610921944831073 26679667168208191458623305)
        ·
          refine ⟨20009750376156143593967479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26679667168208191458623305 20009750376156143593967479)
          ·
            refine ⟨30014625564234215390951219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20009750376156143593967479 30014625564234215390951219)
            ·
              refine ⟨45021938346351323086426829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30014625564234215390951219 45021938346351323086426829)
              ·
                refine ⟨16883226879881746157410061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45021938346351323086426829 16883226879881746157410061)
                ·
                  refine ⟨6331210079955654809028773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16883226879881746157410061 6331210079955654809028773)
                  ·
                    refine ⟨1187101889991685276692895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6331210079955654809028773 1187101889991685276692895)
                    ·
                      rfl

theorem cell22_3467809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_3467809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467809 prefixEnd_3467809 := by exact prefixLift 3467809
  have htrace : WordTrace (prefixWord ++ tailWord_3467809) baseStart_3467809 baseEnd_3467809 := by
    simpa [prefixWord, tailWord_3467809, baseEnd_3467809] using wordTrace_append hprefix tailTrace_3467809
  have hstable : (prefixWord ++ tailWord_3467809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467809).length < 2 ^ (prefixWord ++ tailWord_3467809).sum := by decide
  have hdescent : baseEnd_3467809 < baseStart_3467809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467841 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 6]
def baseStart_3467841 : Nat := 118140960795 + 3467841 * 2 ^ 59
def prefixEnd_3467841 : Nat := 4983230072969 + 3 ^ 40 * 3467841 * 2
def baseEnd_3467841 : Nat := 395704281415215953297599

theorem tailTrace_3467841 : CollatzResearch.WordTrace tailWord_3467841 prefixEnd_3467841 395704281415215953297599 := by
  unfold tailWord_3467841
  simp only [CollatzResearch.WordTrace]
  refine ⟨126482552229611791935675377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84321701486407861290450251 126482552229611791935675377)
  ·
    refine ⟨94861914172208843951756533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126482552229611791935675377 94861914172208843951756533)
    ·
      refine ⟨8893304453644579120477175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94861914172208843951756533 8893304453644579120477175)
      ·
        refine ⟨13339956680466868680715763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8893304453644579120477175 13339956680466868680715763)
        ·
          refine ⟨20009935020700303021073645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13339956680466868680715763 20009935020700303021073645)
          ·
            refine ⟨7503725632762613632902617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20009935020700303021073645 7503725632762613632902617)
            ·
              refine ⟨5627794224571960224676963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7503725632762613632902617 5627794224571960224676963)
              ·
                refine ⟨8441691336857940337015445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5627794224571960224676963 8441691336857940337015445)
                ·
                  refine ⟨395704281415215953297599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8441691336857940337015445 395704281415215953297599)
                  ·
                    rfl

theorem cell22_3467841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_3467841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467841 prefixEnd_3467841 := by exact prefixLift 3467841
  have htrace : WordTrace (prefixWord ++ tailWord_3467841) baseStart_3467841 baseEnd_3467841 := by
    simpa [prefixWord, tailWord_3467841, baseEnd_3467841] using wordTrace_append hprefix tailTrace_3467841
  have hstable : (prefixWord ++ tailWord_3467841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467841).length < 2 ^ (prefixWord ++ tailWord_3467841).sum := by decide
  have hdescent : baseEnd_3467841 < baseStart_3467841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467854 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_3467854 : Nat := 118140960795 + 3467854 * 2 ^ 59
def prefixEnd_3467854 : Nat := 4983230072969 + 3 ^ 40 * 3467854 * 2
def baseEnd_3467854 : Nat := 1187117294411320159317757

theorem tailTrace_3467854 : CollatzResearch.WordTrace tailWord_3467854 prefixEnd_3467854 1187117294411320159317757 := by
  unfold tailWord_3467854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15810378297320586894487327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84322017585709796770599077 15810378297320586894487327)
  ·
    refine ⟨23715567445980880341730991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15810378297320586894487327 23715567445980880341730991)
    ·
      refine ⟨35573351168971320512596487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23715567445980880341730991 35573351168971320512596487)
      ·
        refine ⟨53360026753456980768894731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35573351168971320512596487 53360026753456980768894731)
        ·
          refine ⟨80040040130185471153342097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53360026753456980768894731 80040040130185471153342097)
          ·
            refine ⟨60030030097639103365006573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80040040130185471153342097 60030030097639103365006573)
            ·
              refine ⟨22511261286614663761877465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60030030097639103365006573 22511261286614663761877465)
              ·
                refine ⟨16883445964960997821408099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22511261286614663761877465 16883445964960997821408099)
                ·
                  refine ⟨25325168947441496732112149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16883445964960997821408099 25325168947441496732112149)
                  ·
                    refine ⟨1187117294411320159317757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25325168947441496732112149 1187117294411320159317757)
                    ·
                      rfl

theorem cell22_3467854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_3467854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467854 prefixEnd_3467854 := by exact prefixLift 3467854
  have htrace : WordTrace (prefixWord ++ tailWord_3467854) baseStart_3467854 baseEnd_3467854 := by
    simpa [prefixWord, tailWord_3467854, baseEnd_3467854] using wordTrace_append hprefix tailTrace_3467854
  have hstable : (prefixWord ++ tailWord_3467854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467854).length < 2 ^ (prefixWord ++ tailWord_3467854).sum := by decide
  have hdescent : baseEnd_3467854 < baseStart_3467854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467886 : List Nat := [4, 1, 2, 2, 2, 3, 8]
def baseStart_3467886 : Nat := 118140960795 + 3467886 * 2 ^ 59
def prefixEnd_3467886 : Nat := 4983230072969 + 3 ^ 40 * 3467886 * 2
def baseEnd_3467886 : Nat := 43967712913528990463617

theorem tailTrace_3467886 : CollatzResearch.WordTrace tailWord_3467886 prefixEnd_3467886 43967712913528990463617 := by
  unfold tailWord_3467886
  simp only [CollatzResearch.WordTrace]
  refine ⟨15810524189306095577632939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84322795676299176414042341 15810524189306095577632939)
  ·
    refine ⟨23715786283959143366449409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15810524189306095577632939 23715786283959143366449409)
    ·
      refine ⟨17786839712969357524837057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23715786283959143366449409 17786839712969357524837057)
      ·
        refine ⟨13340129784727018143627793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17786839712969357524837057 13340129784727018143627793)
        ·
          refine ⟨10005097338545263607720845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13340129784727018143627793 10005097338545263607720845)
          ·
            refine ⟨3751911501954473852895317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10005097338545263607720845 3751911501954473852895317)
            ·
              refine ⟨43967712913528990463617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3751911501954473852895317 43967712913528990463617)
              ·
                rfl

theorem cell22_3467886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 8].length) (baseStart_3467886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467886 prefixEnd_3467886 := by exact prefixLift 3467886
  have htrace : WordTrace (prefixWord ++ tailWord_3467886) baseStart_3467886 baseEnd_3467886 := by
    simpa [prefixWord, tailWord_3467886, baseEnd_3467886] using wordTrace_append hprefix tailTrace_3467886
  have hstable : (prefixWord ++ tailWord_3467886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467886).length < 2 ^ (prefixWord ++ tailWord_3467886).sum := by decide
  have hdescent : baseEnd_3467886 < baseStart_3467886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467976 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 6]
def baseStart_3467976 : Nat := 118140960795 + 3467976 * 2 ^ 59
def prefixEnd_3467976 : Nat := 4983230072969 + 3 ^ 40 * 3467976 * 2
def baseEnd_3467976 : Nat := 395719685834850835922461

theorem tailTrace_3467976 : CollatzResearch.WordTrace tailWord_3467976 prefixEnd_3467976 395719685834850835922461 := by
  unfold tailWord_3467976
  simp only [CollatzResearch.WordTrace]
  refine ⟨63243738042061354995919891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84324984056081806661226521 63243738042061354995919891)
  ·
    refine ⟨94865607063092032493879837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63243738042061354995919891 94865607063092032493879837)
    ·
      refine ⟨35574602648659512185204939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94865607063092032493879837 35574602648659512185204939)
      ·
        refine ⟨53361903972989268277807409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35574602648659512185204939 53361903972989268277807409)
        ·
          refine ⟨40021427979741951208355557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53361903972989268277807409 40021427979741951208355557)
          ·
            refine ⟨7504017746201615851566667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40021427979741951208355557 7504017746201615851566667)
            ·
              refine ⟨11256026619302423777350001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7504017746201615851566667 11256026619302423777350001)
              ·
                refine ⟨8442019964476817833012501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11256026619302423777350001 8442019964476817833012501)
                ·
                  refine ⟨395719685834850835922461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8442019964476817833012501 395719685834850835922461)
                  ·
                    rfl

theorem cell22_3467976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_3467976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467976 prefixEnd_3467976 := by exact prefixLift 3467976
  have htrace : WordTrace (prefixWord ++ tailWord_3467976) baseStart_3467976 baseEnd_3467976 := by
    simpa [prefixWord, tailWord_3467976, baseEnd_3467976] using wordTrace_append hprefix tailTrace_3467976
  have hstable : (prefixWord ++ tailWord_3467976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467976).length < 2 ^ (prefixWord ++ tailWord_3467976).sum := by decide
  have hdescent : baseEnd_3467976 < baseStart_3467976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467991 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 1, 5]
def baseStart_3467991 : Nat := 118140960795 + 3467991 * 2 ^ 59
def prefixEnd_3467991 : Nat := 4983230072969 + 3 ^ 40 * 3467991 * 2
def baseEnd_3467991 : Nat := 1187164192311097468642337

theorem tailTrace_3467991 : CollatzResearch.WordTrace tailWord_3467991 prefixEnd_3467991 1187164192311097468642337 := by
  unfold tailWord_3467991
  simp only [CollatzResearch.WordTrace]
  refine ⟨126488023179068367553635827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84325348786045578369090551 126488023179068367553635827)
  ·
    refine ⟨189732034768602551330453741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126488023179068367553635827 189732034768602551330453741)
    ·
      refine ⟨71149513038225956748920153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189732034768602551330453741 71149513038225956748920153)
      ·
        refine ⟨53362134778669467561690115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71149513038225956748920153 53362134778669467561690115)
        ·
          refine ⟨80043202168004201342535173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53362134778669467561690115 80043202168004201342535173)
          ·
            refine ⟨15008100406500787751725345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80043202168004201342535173 15008100406500787751725345)
            ·
              refine ⟨11256075304875590813794009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15008100406500787751725345 11256075304875590813794009)
              ·
                refine ⟨8442056478656693110345507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11256075304875590813794009 8442056478656693110345507)
                ·
                  refine ⟨12663084717985039665518261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8442056478656693110345507 12663084717985039665518261)
                  ·
                    refine ⟨1187164192311097468642337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12663084717985039665518261 1187164192311097468642337)
                    ·
                      rfl

theorem cell22_3467991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_3467991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467991 prefixEnd_3467991 := by exact prefixLift 3467991
  have htrace : WordTrace (prefixWord ++ tailWord_3467991) baseStart_3467991 baseEnd_3467991 := by
    simpa [prefixWord, tailWord_3467991, baseEnd_3467991] using wordTrace_append hprefix tailTrace_3467991
  have hstable : (prefixWord ++ tailWord_3467991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467991).length < 2 ^ (prefixWord ++ tailWord_3467991).sum := by decide
  have hdescent : baseEnd_3467991 < baseStart_3467991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467993 : List Nat := [1, 2, 1, 2, 3, 2, 4, 3, 4]
def baseStart_3467993 : Nat := 118140960795 + 3467993 * 2 ^ 59
def prefixEnd_3467993 : Nat := 4983230072969 + 3 ^ 40 * 3467993 * 2
def baseEnd_3467993 : Nat := 395721625650656710030777

theorem tailTrace_3467993 : CollatzResearch.WordTrace tailWord_3467993 prefixEnd_3467993 395721625650656710030777 := by
  unfold tailWord_3467993
  simp only [CollatzResearch.WordTrace]
  refine ⟨126488096125061121895208633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84325397416707414596805755 126488096125061121895208633)
  ·
    refine ⟨94866072093795841421406475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126488096125061121895208633 94866072093795841421406475)
    ·
      refine ⟨142299108140693762132109713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94866072093795841421406475 142299108140693762132109713)
      ·
        refine ⟨106724331105520321599082285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142299108140693762132109713 106724331105520321599082285)
        ·
          refine ⟨40021624164570120599655857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106724331105520321599082285 40021624164570120599655857)
          ·
            refine ⟨30016218123427590449741893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40021624164570120599655857 30016218123427590449741893)
            ·
              refine ⟨5628040898142673209326605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30016218123427590449741893 5628040898142673209326605)
              ·
                refine ⟨2110515336803502453497477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5628040898142673209326605 2110515336803502453497477)
                ·
                  refine ⟨395721625650656710030777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110515336803502453497477 395721625650656710030777)
                  ·
                    rfl

theorem cell22_3467993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 4].length) (baseStart_3467993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3467993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3467993 prefixEnd_3467993 := by exact prefixLift 3467993
  have htrace : WordTrace (prefixWord ++ tailWord_3467993) baseStart_3467993 baseEnd_3467993 := by
    simpa [prefixWord, tailWord_3467993, baseEnd_3467993] using wordTrace_append hprefix tailTrace_3467993
  have hstable : (prefixWord ++ tailWord_3467993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467993).length < 2 ^ (prefixWord ++ tailWord_3467993).sum := by decide
  have hdescent : baseEnd_3467993 < baseStart_3467993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468036 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_3468036 : Nat := 118140960795 + 3468036 * 2 ^ 59
def prefixEnd_3468036 : Nat := 4983230072969 + 3 ^ 40 * 3468036 * 2
def baseEnd_3468036 : Nat := 1187179596730732351267199

theorem tailTrace_3468036 : CollatzResearch.WordTrace tailWord_3468036 prefixEnd_3468036 1187179596730732351267199 := by
  unfold tailWord_3468036
  simp only [CollatzResearch.WordTrace]
  refine ⟨63244832231952670119511981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84326442975936893492682641 63244832231952670119511981)
  ·
    refine ⟨23716812086982251294816993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63244832231952670119511981 23716812086982251294816993)
    ·
      refine ⟨17787609065236688471112745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23716812086982251294816993 17787609065236688471112745)
      ·
        refine ⟨13340706798927516353334559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17787609065236688471112745 13340706798927516353334559)
        ·
          refine ⟨20011060198391274530001839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13340706798927516353334559 20011060198391274530001839)
          ·
            refine ⟨30016590297586911795002759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20011060198391274530001839 30016590297586911795002759)
            ·
              refine ⟨45024885446380367692504139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30016590297586911795002759 45024885446380367692504139)
              ·
                refine ⟨67537328169570551538756209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45024885446380367692504139 67537328169570551538756209)
                ·
                  refine ⟨50652996127177913654067157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67537328169570551538756209 50652996127177913654067157)
                  ·
                    refine ⟨1187179596730732351267199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50652996127177913654067157 1187179596730732351267199)
                    ·
                      rfl

theorem cell22_3468036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_3468036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468036 prefixEnd_3468036 := by exact prefixLift 3468036
  have htrace : WordTrace (prefixWord ++ tailWord_3468036) baseStart_3468036 baseEnd_3468036 := by
    simpa [prefixWord, tailWord_3468036, baseEnd_3468036] using wordTrace_append hprefix tailTrace_3468036
  have hstable : (prefixWord ++ tailWord_3468036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468036).length < 2 ^ (prefixWord ++ tailWord_3468036).sum := by decide
  have hdescent : baseEnd_3468036 < baseStart_3468036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468081 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 1, 7]
def baseStart_3468081 : Nat := 118140960795 + 3468081 * 2 ^ 59
def prefixEnd_3468081 : Nat := 4983230072969 + 3 ^ 40 * 3468081 * 2
def baseEnd_3468081 : Nat := 1187195001150367233892061

theorem tailTrace_3468081 : CollatzResearch.WordTrace tailWord_3468081 prefixEnd_3468081 1187195001150367233892061 := by
  unfold tailWord_3468081
  simp only [CollatzResearch.WordTrace]
  refine ⟨126491305748742312924412097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84327537165828208616274731 126491305748742312924412097)
  ·
    refine ⟨94868479311556734693309073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126491305748742312924412097 94868479311556734693309073)
    ·
      refine ⟨71151359483667551019981805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94868479311556734693309073 71151359483667551019981805)
      ·
        refine ⟨26681759806375331632493177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71151359483667551019981805 26681759806375331632493177)
        ·
          refine ⟨20011319854781498724369883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26681759806375331632493177 20011319854781498724369883)
          ·
            refine ⟨30016979782172248086554825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20011319854781498724369883 30016979782172248086554825)
            ·
              refine ⟨22512734836629186064916119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30016979782172248086554825 22512734836629186064916119)
              ·
                refine ⟨33769102254943779097374179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22512734836629186064916119 33769102254943779097374179)
                ·
                  refine ⟨50653653382415668646061269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33769102254943779097374179 50653653382415668646061269)
                  ·
                    refine ⟨1187195001150367233892061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50653653382415668646061269 1187195001150367233892061)
                    ·
                      rfl

theorem cell22_3468081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_3468081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468081 prefixEnd_3468081 := by exact prefixLift 3468081
  have htrace : WordTrace (prefixWord ++ tailWord_3468081) baseStart_3468081 baseEnd_3468081 := by
    simpa [prefixWord, tailWord_3468081, baseEnd_3468081] using wordTrace_append hprefix tailTrace_3468081
  have hstable : (prefixWord ++ tailWord_3468081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468081).length < 2 ^ (prefixWord ++ tailWord_3468081).sum := by decide
  have hdescent : baseEnd_3468081 < baseStart_3468081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468083 : List Nat := [1, 1, 1, 2, 6, 2, 1, 3, 5]
def baseStart_3468083 : Nat := 118140960795 + 3468083 * 2 ^ 59
def prefixEnd_3468083 : Nat := 4983230072969 + 3 ^ 40 * 3468083 * 2
def baseEnd_3468083 : Nat := 395731895263746631780685

theorem tailTrace_3468083 : CollatzResearch.WordTrace tailWord_3468083 prefixEnd_3468083 395731895263746631780685 := by
  unfold tailWord_3468083
  simp only [CollatzResearch.WordTrace]
  refine ⟨126491378694735067265984903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84327585796490044843989935 126491378694735067265984903)
  ·
    refine ⟨189737068042102600898977355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126491378694735067265984903 189737068042102600898977355)
    ·
      refine ⟨284605602063153901348466033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189737068042102600898977355 284605602063153901348466033)
      ·
        refine ⟨213454201547365426011349525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284605602063153901348466033 213454201547365426011349525)
        ·
          refine ⟨10005665697532754344282009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 213454201547365426011349525 10005665697532754344282009)
          ·
            refine ⟨7504249273149565758211507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10005665697532754344282009 7504249273149565758211507)
            ·
              refine ⟨11256373909724348637317261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7504249273149565758211507 11256373909724348637317261)
              ·
                refine ⟨4221140216146630738993973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11256373909724348637317261 4221140216146630738993973)
                ·
                  refine ⟨395731895263746631780685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4221140216146630738993973 395731895263746631780685)
                  ·
                    rfl

theorem cell22_3468083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 5].length) (baseStart_3468083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468083 prefixEnd_3468083 := by exact prefixLift 3468083
  have htrace : WordTrace (prefixWord ++ tailWord_3468083) baseStart_3468083 baseEnd_3468083 := by
    simpa [prefixWord, tailWord_3468083, baseEnd_3468083] using wordTrace_append hprefix tailTrace_3468083
  have hstable : (prefixWord ++ tailWord_3468083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468083).length < 2 ^ (prefixWord ++ tailWord_3468083).sum := by decide
  have hdescent : baseEnd_3468083 < baseStart_3468083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468156 : List Nat := [2, 2, 2, 1, 1, 1, 1, 12]
def baseStart_3468156 : Nat := 118140960795 + 3468156 * 2 ^ 59
def prefixEnd_3468156 : Nat := 4983230072969 + 3 ^ 40 * 3468156 * 2
def baseEnd_3468156 : Nat := 131913408353676893140759

theorem tailTrace_3468156 : CollatzResearch.WordTrace tailWord_3468156 prefixEnd_3468156 131913408353676893140759 := by
  unfold tailWord_3468156
  simp only [CollatzResearch.WordTrace]
  refine ⟨63247020611735300366696161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84329360815647067155594881 63247020611735300366696161)
  ·
    refine ⟨47435265458801475275022121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63247020611735300366696161 47435265458801475275022121)
    ·
      refine ⟨35576449094101106456266591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47435265458801475275022121 35576449094101106456266591)
      ·
        refine ⟨53364673641151659684399887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35576449094101106456266591 53364673641151659684399887)
        ·
          refine ⟨80047010461727489526599831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53364673641151659684399887 80047010461727489526599831)
          ·
            refine ⟨120070515692591234289899747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80047010461727489526599831 120070515692591234289899747)
            ·
              refine ⟨180105773538886851434849621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120070515692591234289899747 180105773538886851434849621)
              ·
                refine ⟨131913408353676893140759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 180105773538886851434849621 131913408353676893140759)
                ·
                  rfl

theorem cell22_3468156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 12].length) (baseStart_3468156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468156 prefixEnd_3468156 := by exact prefixLift 3468156
  have htrace : WordTrace (prefixWord ++ tailWord_3468156) baseStart_3468156 baseEnd_3468156 := by
    simpa [prefixWord, tailWord_3468156, baseEnd_3468156] using wordTrace_append hprefix tailTrace_3468156
  have hstable : (prefixWord ++ tailWord_3468156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468156).length < 2 ^ (prefixWord ++ tailWord_3468156).sum := by decide
  have hdescent : baseEnd_3468156 < baseStart_3468156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468194 : List Nat := [3, 3, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3468194 : Nat := 118140960795 + 3468194 * 2 ^ 59
def prefixEnd_3468194 : Nat := 4983230072969 + 3 ^ 40 * 3468194 * 2
def baseEnd_3468194 : Nat := 1187233683359672605816715

theorem tailTrace_3468194 : CollatzResearch.WordTrace tailWord_3468194 prefixEnd_3468194 1187233683359672605816715 := by
  unfold tailWord_3468194
  simp only [CollatzResearch.WordTrace]
  refine ⟨31623856799333233305818909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84330284798221955482183757 31623856799333233305818909)
  ·
    refine ⟨11858946299749962489682091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31623856799333233305818909 11858946299749962489682091)
    ·
      refine ⟨17788419449624943734523137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11858946299749962489682091 17788419449624943734523137)
      ·
        refine ⟨13341314587218707800892353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17788419449624943734523137 13341314587218707800892353)
        ·
          refine ⟨10005985940414030850669265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13341314587218707800892353 10005985940414030850669265)
          ·
            refine ⟨7504489455310523138001949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10005985940414030850669265 7504489455310523138001949)
            ·
              refine ⟨2814183545741446176750731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7504489455310523138001949 2814183545741446176750731)
              ·
                refine ⟨4221275318612169265126097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814183545741446176750731 4221275318612169265126097)
                ·
                  refine ⟨3165956488959126948844573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4221275318612169265126097 3165956488959126948844573)
                  ·
                    refine ⟨1187233683359672605816715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3165956488959126948844573 1187233683359672605816715)
                    ·
                      rfl

theorem cell22_3468194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3468194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468194 prefixEnd_3468194 := by exact prefixLift 3468194
  have htrace : WordTrace (prefixWord ++ tailWord_3468194) baseStart_3468194 baseEnd_3468194 := by
    simpa [prefixWord, tailWord_3468194, baseEnd_3468194] using wordTrace_append hprefix tailTrace_3468194
  have hstable : (prefixWord ++ tailWord_3468194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468194).length < 2 ^ (prefixWord ++ tailWord_3468194).sum := by decide
  have hdescent : baseEnd_3468194 < baseStart_3468194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468230 : List Nat := [6, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_3468230 : Nat := 118140960795 + 3468230 * 2 ^ 59
def prefixEnd_3468230 : Nat := 4983230072969 + 3 ^ 40 * 3468230 * 2
def baseEnd_3468230 : Nat := 395748668965126837305535

theorem tailTrace_3468230 : CollatzResearch.WordTrace tailWord_3468230 prefixEnd_3468230 395748668965126837305535 := by
  unfold tailWord_3468230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3953023132037578480362067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84331160150135007581057429 3953023132037578480362067)
  ·
    refine ⟨5929534698056367720543101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3953023132037578480362067 5929534698056367720543101)
    ·
      refine ⟨2223575511771137895203663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5929534698056367720543101 2223575511771137895203663)
      ·
        refine ⟨3335363267656706842805495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2223575511771137895203663 3335363267656706842805495)
        ·
          refine ⟨5003044901485060264208243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3335363267656706842805495 5003044901485060264208243)
          ·
            refine ⟨7504567352227590396312365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003044901485060264208243 7504567352227590396312365)
            ·
              refine ⟨2814212757085346398617137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7504567352227590396312365 2814212757085346398617137)
              ·
                refine ⟨2110659567814009798962853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814212757085346398617137 2110659567814009798962853)
                ·
                  refine ⟨395748668965126837305535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110659567814009798962853 395748668965126837305535)
                  ·
                    rfl

theorem cell22_3468230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_3468230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468230 prefixEnd_3468230 := by exact prefixLift 3468230
  have htrace : WordTrace (prefixWord ++ tailWord_3468230) baseStart_3468230 baseEnd_3468230 := by
    simpa [prefixWord, tailWord_3468230, baseEnd_3468230] using wordTrace_append hprefix tailTrace_3468230
  have hstable : (prefixWord ++ tailWord_3468230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468230).length < 2 ^ (prefixWord ++ tailWord_3468230).sum := by decide
  have hdescent : baseEnd_3468230 < baseStart_3468230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468239 : List Nat := [1, 1, 2, 1, 1, 7, 3, 2, 1, 3]
def baseStart_3468239 : Nat := 118140960795 + 3468239 * 2 ^ 59
def prefixEnd_3468239 : Nat := 4983230072969 + 3 ^ 40 * 3468239 * 2
def baseEnd_3468239 : Nat := 1187249087779307488441577

theorem tailTrace_3468239 : CollatzResearch.WordTrace tailWord_3468239 prefixEnd_3468239 1187249087779307488441577 := by
  unfold tailWord_3468239
  simp only [CollatzResearch.WordTrace]
  refine ⟨126497068482169905908663771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84331378988113270605775847 126497068482169905908663771)
  ·
    refine ⟨189745602723254858862995657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126497068482169905908663771 189745602723254858862995657)
    ·
      refine ⟨142309202042441144147246743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189745602723254858862995657 142309202042441144147246743)
      ·
        refine ⟨213463803063661716220870115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142309202042441144147246743 213463803063661716220870115)
        ·
          refine ⟨320195704595492574331305173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213463803063661716220870115 320195704595492574331305173)
          ·
            refine ⟨7504586826456857210889965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 320195704595492574331305173 7504586826456857210889965)
            ·
              refine ⟨2814220059921321454083737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7504586826456857210889965 2814220059921321454083737)
              ·
                refine ⟨2110665044940991090562803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814220059921321454083737 2110665044940991090562803)
                ·
                  refine ⟨3165997567411486635844205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110665044940991090562803 3165997567411486635844205)
                  ·
                    refine ⟨1187249087779307488441577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3165997567411486635844205 1187249087779307488441577)
                    ·
                      rfl

theorem cell22_3468239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 1, 3].length) (baseStart_3468239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468239 prefixEnd_3468239 := by exact prefixLift 3468239
  have htrace : WordTrace (prefixWord ++ tailWord_3468239) baseStart_3468239 baseEnd_3468239 := by
    simpa [prefixWord, tailWord_3468239, baseEnd_3468239] using wordTrace_append hprefix tailTrace_3468239
  have hstable : (prefixWord ++ tailWord_3468239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468239).length < 2 ^ (prefixWord ++ tailWord_3468239).sum := by decide
  have hdescent : baseEnd_3468239 < baseStart_3468239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468280 : List Nat := [2, 1, 2, 1, 1, 3, 1, 7, 4]
def baseStart_3468280 : Nat := 118140960795 + 3468280 * 2 ^ 59
def prefixEnd_3468280 : Nat := 4983230072969 + 3 ^ 40 * 3468280 * 2
def baseEnd_3468280 : Nat := 395754374305732349388817

theorem tailTrace_3468280 : CollatzResearch.WordTrace tailWord_3468280 prefixEnd_3468280 395754374305732349388817 := by
  unfold tailWord_3468280
  simp only [CollatzResearch.WordTrace]
  refine ⟨63249281937510684955453147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84332375916680913273937529 63249281937510684955453147)
  ·
    refine ⟨94873922906266027433179721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63249281937510684955453147 94873922906266027433179721)
    ·
      refine ⟨71155442179699520574884791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94873922906266027433179721 71155442179699520574884791)
      ·
        refine ⟨106733163269549280862327187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71155442179699520574884791 106733163269549280862327187)
        ·
          refine ⟨160099744904323921293490781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106733163269549280862327187 160099744904323921293490781)
          ·
            refine ⟨60037404339121470485059043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160099744904323921293490781 60037404339121470485059043)
            ·
              refine ⟨90056106508682205727588565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60037404339121470485059043 90056106508682205727588565)
              ·
                refine ⟨2110689996297239196740357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90056106508682205727588565 2110689996297239196740357)
                ·
                  refine ⟨395754374305732349388817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110689996297239196740357 395754374305732349388817)
                  ·
                    rfl

theorem cell22_3468280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 4].length) (baseStart_3468280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468280 prefixEnd_3468280 := by exact prefixLift 3468280
  have htrace : WordTrace (prefixWord ++ tailWord_3468280) baseStart_3468280 baseEnd_3468280 := by
    simpa [prefixWord, tailWord_3468280, baseEnd_3468280] using wordTrace_append hprefix tailTrace_3468280
  have hstable : (prefixWord ++ tailWord_3468280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468280).length < 2 ^ (prefixWord ++ tailWord_3468280).sum := by decide
  have hdescent : baseEnd_3468280 < baseStart_3468280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468290 : List Nat := [3, 4, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_3468290 : Nat := 118140960795 + 3468290 * 2 ^ 59
def prefixEnd_3468290 : Nat := 4983230072969 + 3 ^ 40 * 3468290 * 2
def baseEnd_3468290 : Nat := 1187266546121560355416421

theorem tailTrace_3468290 : CollatzResearch.WordTrace tailWord_3468290 prefixEnd_3468290 1187266546121560355416421 := by
  unfold tailWord_3468290
  simp only [CollatzResearch.WordTrace]
  refine ⟨31624732151246285404692581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84332619069990094412513549 31624732151246285404692581)
  ·
    refine ⟨5929637278358678513379859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31624732151246285404692581 5929637278358678513379859)
    ·
      refine ⟨8894455917538017770069789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5929637278358678513379859 8894455917538017770069789)
      ·
        refine ⟨3335420969076756663776171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8894455917538017770069789 3335420969076756663776171)
        ·
          refine ⟨5003131453615134995664257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3335420969076756663776171 5003131453615134995664257)
          ·
            refine ⟨3752348590211351246748193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5003131453615134995664257 3752348590211351246748193)
            ·
              refine ⟨2814261442658513435061145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3752348590211351246748193 2814261442658513435061145)
              ·
                refine ⟨2110696081993885076295859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814261442658513435061145 2110696081993885076295859)
                ·
                  refine ⟨3166044122990827614443789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110696081993885076295859 3166044122990827614443789)
                  ·
                    refine ⟨1187266546121560355416421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3166044122990827614443789 1187266546121560355416421)
                    ·
                      rfl

theorem cell22_3468290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_3468290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468290 prefixEnd_3468290 := by exact prefixLift 3468290
  have htrace : WordTrace (prefixWord ++ tailWord_3468290) baseStart_3468290 baseEnd_3468290 := by
    simpa [prefixWord, tailWord_3468290, baseEnd_3468290] using wordTrace_append hprefix tailTrace_3468290
  have hstable : (prefixWord ++ tailWord_3468290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468290).length < 2 ^ (prefixWord ++ tailWord_3468290).sum := by decide
  have hdescent : baseEnd_3468290 < baseStart_3468290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468312 : List Nat := [2, 1, 2, 3, 2, 2, 2, 3, 2, 3]
def baseStart_3468312 : Nat := 118140960795 + 3468312 * 2 ^ 59
def prefixEnd_3468312 : Nat := 4983230072969 + 3 ^ 40 * 3468312 * 2
def baseEnd_3468312 : Nat := 1187274077171159631366353

theorem tailTrace_3468312 : CollatzResearch.WordTrace tailWord_3468312 prefixEnd_3468312 1187274077171159631366353 := by
  unfold tailWord_3468312
  simp only [CollatzResearch.WordTrace]
  refine ⟨63249865505452719688035595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84333154007270292917380793 63249865505452719688035595)
  ·
    refine ⟨94874798258179079532053393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63249865505452719688035595 94874798258179079532053393)
    ·
      refine ⟨71156098693634309649040045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94874798258179079532053393 71156098693634309649040045)
      ·
        refine ⟨26683537010112866118390017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71156098693634309649040045 26683537010112866118390017)
        ·
          refine ⟨20012652757584649588792513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26683537010112866118390017 20012652757584649588792513)
          ·
            refine ⟨15009489568188487191594385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20012652757584649588792513 15009489568188487191594385)
            ·
              refine ⟨11257117176141365393695789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15009489568188487191594385 11257117176141365393695789)
              ·
                refine ⟨4221418941053012022635921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11257117176141365393695789 4221418941053012022635921)
                ·
                  refine ⟨3166064205789759016976941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4221418941053012022635921 3166064205789759016976941)
                  ·
                    refine ⟨1187274077171159631366353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3166064205789759016976941 1187274077171159631366353)
                    ·
                      rfl

theorem cell22_3468312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_3468312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468312 prefixEnd_3468312 := by exact prefixLift 3468312
  have htrace : WordTrace (prefixWord ++ tailWord_3468312) baseStart_3468312 baseEnd_3468312 := by
    simpa [prefixWord, tailWord_3468312, baseEnd_3468312] using wordTrace_append hprefix tailTrace_3468312
  have hstable : (prefixWord ++ tailWord_3468312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468312).length < 2 ^ (prefixWord ++ tailWord_3468312).sum := by decide
  have hdescent : baseEnd_3468312 < baseStart_3468312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468325 : List Nat := [1, 3, 1, 2, 2, 2, 5, 6]
def baseStart_3468325 : Nat := 118140960795 + 3468325 * 2 ^ 59
def prefixEnd_3468325 : Nat := 4983230072969 + 3 ^ 40 * 3468325 * 2
def baseEnd_3468325 : Nat := 131919836370759103421257

theorem tailTrace_3468325 : CollatzResearch.WordTrace tailWord_3468325 prefixEnd_3468325 131919836370759103421257 := by
  unfold tailWord_3468325
  simp only [CollatzResearch.WordTrace]
  refine ⟨126500205159858342596294429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84333470106572228397529619 126500205159858342596294429)
  ·
    refine ⟨47437576934946878473610411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126500205159858342596294429 47437576934946878473610411)
    ·
      refine ⟨71156365402420317710415617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47437576934946878473610411 71156365402420317710415617)
      ·
        refine ⟨53367274051815238282811713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71156365402420317710415617 53367274051815238282811713)
        ·
          refine ⟨40025455538861428712108785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53367274051815238282811713 40025455538861428712108785)
          ·
            refine ⟨30019091654146071534081589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40025455538861428712108785 30019091654146071534081589)
            ·
              refine ⟨2814289842576194206320149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30019091654146071534081589 2814289842576194206320149)
              ·
                refine ⟨131919836370759103421257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2814289842576194206320149 131919836370759103421257)
                ·
                  rfl

theorem cell22_3468325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 6].length) (baseStart_3468325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468325 prefixEnd_3468325 := by exact prefixLift 3468325
  have htrace : WordTrace (prefixWord ++ tailWord_3468325) baseStart_3468325 baseEnd_3468325 := by
    simpa [prefixWord, tailWord_3468325, baseEnd_3468325] using wordTrace_append hprefix tailTrace_3468325
  have hstable : (prefixWord ++ tailWord_3468325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468325).length < 2 ^ (prefixWord ++ tailWord_3468325).sum := by decide
  have hdescent : baseEnd_3468325 < baseStart_3468325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468327 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3468327 : Nat := 118140960795 + 3468327 * 2 ^ 59
def prefixEnd_3468327 : Nat := 4983230072969 + 3 ^ 40 * 3468327 * 2
def baseEnd_3468327 : Nat := 1187279211977704592241307

theorem tailTrace_3468327 : CollatzResearch.WordTrace tailWord_3468327 prefixEnd_3468327 1187279211977704592241307 := by
  unfold tailWord_3468327
  simp only [CollatzResearch.WordTrace]
  refine ⟨126500278105851096937867235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84333518737234064625244823 126500278105851096937867235)
  ·
    refine ⟨189750417158776645406800853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126500278105851096937867235 189750417158776645406800853)
    ·
      refine ⟨4447275402158827626721895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 189750417158776645406800853 4447275402158827626721895)
      ·
        refine ⟨6670913103238241440082843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4447275402158827626721895 6670913103238241440082843)
        ·
          refine ⟨10006369654857362160124265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6670913103238241440082843 10006369654857362160124265)
          ·
            refine ⟨7504777241143021620093199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10006369654857362160124265 7504777241143021620093199)
            ·
              refine ⟨11257165861714532430139799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7504777241143021620093199 11257165861714532430139799)
              ·
                refine ⟨16885748792571798645209699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11257165861714532430139799 16885748792571798645209699)
                ·
                  refine ⟨25328623188857697967814549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16885748792571798645209699 25328623188857697967814549)
                  ·
                    refine ⟨1187279211977704592241307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25328623188857697967814549 1187279211977704592241307)
                    ·
                      rfl

theorem cell22_3468327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3468327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468327 prefixEnd_3468327 := by exact prefixLift 3468327
  have htrace : WordTrace (prefixWord ++ tailWord_3468327) baseStart_3468327 baseEnd_3468327 := by
    simpa [prefixWord, tailWord_3468327, baseEnd_3468327] using wordTrace_append hprefix tailTrace_3468327
  have hstable : (prefixWord ++ tailWord_3468327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468327).length < 2 ^ (prefixWord ++ tailWord_3468327).sum := by decide
  have hdescent : baseEnd_3468327 < baseStart_3468327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468391 : List Nat := [1, 1, 5, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3468391 : Nat := 118140960795 + 3468391 * 2 ^ 59
def prefixEnd_3468391 : Nat := 4983230072969 + 3 ^ 40 * 3468391 * 2
def baseEnd_3468391 : Nat := 1187301120485629758641111

theorem tailTrace_3468391 : CollatzResearch.WordTrace tailWord_3468391 prefixEnd_3468391 1187301120485629758641111 := by
  unfold tailWord_3468391
  simp only [CollatzResearch.WordTrace]
  refine ⟨126502612377619235868197027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84335074918412823912131351 126502612377619235868197027)
  ·
    refine ⟨189753918566428853802295541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126502612377619235868197027 189753918566428853802295541)
    ·
      refine ⟨17789429865602705043965207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189753918566428853802295541 17789429865602705043965207)
      ·
        refine ⟨26684144798404057565947811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17789429865602705043965207 26684144798404057565947811)
        ·
          refine ⟨40026217197606086348921717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26684144798404057565947811 40026217197606086348921717)
          ·
            refine ⟨3752457862275570595211411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40026217197606086348921717 3752457862275570595211411)
            ·
              refine ⟨5628686793413355892817117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3752457862275570595211411 5628686793413355892817117)
              ·
                refine ⟨2110757547530008459806419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5628686793413355892817117 2110757547530008459806419)
                ·
                  refine ⟨3166136321295012689709629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110757547530008459806419 3166136321295012689709629)
                  ·
                    refine ⟨1187301120485629758641111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3166136321295012689709629 1187301120485629758641111)
                    ·
                      rfl

theorem cell22_3468391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3468391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468391 prefixEnd_3468391 := by exact prefixLift 3468391
  have htrace : WordTrace (prefixWord ++ tailWord_3468391) baseStart_3468391 baseEnd_3468391 := by
    simpa [prefixWord, tailWord_3468391, baseEnd_3468391] using wordTrace_append hprefix tailTrace_3468391
  have hstable : (prefixWord ++ tailWord_3468391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468391).length < 2 ^ (prefixWord ++ tailWord_3468391).sum := by decide
  have hdescent : baseEnd_3468391 < baseStart_3468391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468421 : List Nat := [1, 3, 1, 1, 7, 1, 2, 1, 5]
def baseStart_3468421 : Nat := 118140960795 + 3468421 * 2 ^ 59
def prefixEnd_3468421 : Nat := 4983230072969 + 3 ^ 40 * 3468421 * 2
def baseEnd_3468421 : Nat := 395770463366239893463673

theorem tailTrace_3468421 : CollatzResearch.WordTrace tailWord_3468421 prefixEnd_3468421 395770463366239893463673 := by
  unfold tailWord_3468421
  simp only [CollatzResearch.WordTrace]
  refine ⟨126503706567510550991789117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84335804378340367327859411 126503706567510550991789117)
  ·
    refine ⟨47438889962816456621920919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126503706567510550991789117 47438889962816456621920919)
    ·
      refine ⟨71158334944224684932881379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47438889962816456621920919 71158334944224684932881379)
      ·
        refine ⟨106737502416337027399322069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71158334944224684932881379 106737502416337027399322069)
        ·
          refine ⟨2501660212882899079671611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 106737502416337027399322069 2501660212882899079671611)
          ·
            refine ⟨3752490319324348619507417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501660212882899079671611 3752490319324348619507417)
            ·
              refine ⟨2814367739493261464630563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3752490319324348619507417 2814367739493261464630563)
              ·
                refine ⟨4221551609239892196945845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814367739493261464630563 4221551609239892196945845)
                ·
                  refine ⟨395770463366239893463673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4221551609239892196945845 395770463366239893463673)
                  ·
                    rfl

theorem cell22_3468421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_3468421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468421 prefixEnd_3468421 := by exact prefixLift 3468421
  have htrace : WordTrace (prefixWord ++ tailWord_3468421) baseStart_3468421 baseEnd_3468421 := by
    simpa [prefixWord, tailWord_3468421, baseEnd_3468421] using wordTrace_append hprefix tailTrace_3468421
  have hstable : (prefixWord ++ tailWord_3468421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468421).length < 2 ^ (prefixWord ++ tailWord_3468421).sum := by decide
  have hdescent : baseEnd_3468421 < baseStart_3468421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
