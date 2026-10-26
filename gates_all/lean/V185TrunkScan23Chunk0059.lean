import V185TrunkScan23Chunk0058

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_348848 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 5]
def baseStart_348848 : Nat := 118140960795 + 348848 * 2 ^ 59
def prefixEnd_348848 : Nat := 4983230072969 + 3 ^ 40 * 348848 * 2
def baseEnd_348848 : Nat := 179126699359756364295683

theorem tailTrace_348848 : CollatzResearch.WordTrace tailWord_348848 prefixEnd_348848 179126699359756364295683 := by
  unfold tailWord_348848
  simp only [CollatzResearch.WordTrace]
  refine ⟨6361765920095374670111599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8482354560127166226815465 6361765920095374670111599)
  ·
    refine ⟨9542648880143062005167399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6361765920095374670111599 9542648880143062005167399)
    ·
      refine ⟨14313973320214593007751099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9542648880143062005167399 14313973320214593007751099)
      ·
        refine ⟨21470959980321889511626649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14313973320214593007751099 21470959980321889511626649)
        ·
          refine ⟨16103219985241417133719987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21470959980321889511626649 16103219985241417133719987)
          ·
            refine ⟨24154829977862125700579981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16103219985241417133719987 24154829977862125700579981)
            ·
              refine ⟨9058061241698297137717493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24154829977862125700579981 9058061241698297137717493)
              ·
                refine ⟨849193241409215356661015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9058061241698297137717493 849193241409215356661015)
                ·
                  refine ⟨1273789862113823034991523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849193241409215356661015 1273789862113823034991523)
                  ·
                    refine ⟨1910684793170734552487285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1273789862113823034991523 1910684793170734552487285)
                    ·
                      refine ⟨179126699359756364295683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1910684793170734552487285 179126699359756364295683)
                      ·
                        rfl

theorem cell23_348848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_348848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348848 prefixEnd_348848 := by exact prefixLift 348848
  have htrace : WordTrace (prefixWord ++ tailWord_348848) baseStart_348848 baseEnd_348848 := by
    simpa [prefixWord, tailWord_348848, baseEnd_348848] using wordTrace_append hprefix tailTrace_348848
  have hstable : (prefixWord ++ tailWord_348848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348848).length < 2 ^ (prefixWord ++ tailWord_348848).sum := by decide
  have hdescent : baseEnd_348848 < baseStart_348848 := by decide
  rcases family_descends (prefixWord ++ tailWord_348848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348858 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_348858 : Nat := 118140960795 + 348858 * 2 ^ 59
def prefixEnd_348858 : Nat := 4983230072969 + 3 ^ 40 * 348858 * 2
def baseEnd_348858 : Nat := 179131834166301325170637

theorem tailTrace_348858 : CollatzResearch.WordTrace tailWord_348858 prefixEnd_348858 179131834166301325170637 := by
  unfold tailWord_348858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3180974142538630262021807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8482597713436347365391485 3180974142538630262021807)
  ·
    refine ⟨4771461213807945393032711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3180974142538630262021807 4771461213807945393032711)
    ·
      refine ⟨7157191820711918089549067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4771461213807945393032711 7157191820711918089549067)
      ·
        refine ⟨10735787731067877134323601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7157191820711918089549067 10735787731067877134323601)
        ·
          refine ⟨8051840798300907850742701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10735787731067877134323601 8051840798300907850742701)
          ·
            refine ⟨3019440299362840444028513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8051840798300907850742701 3019440299362840444028513)
            ·
              refine ⟨2264580224522130333021385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3019440299362840444028513 2264580224522130333021385)
              ·
                refine ⟨1698435168391597749766039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2264580224522130333021385 1698435168391597749766039)
                ·
                  refine ⟨2547652752587396624649059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698435168391597749766039 2547652752587396624649059)
                  ·
                    refine ⟨3821479128881094936973589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2547652752587396624649059 3821479128881094936973589)
                    ·
                      refine ⟨179131834166301325170637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3821479128881094936973589 179131834166301325170637)
                      ·
                        rfl

theorem cell23_348858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_348858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348858 prefixEnd_348858 := by exact prefixLift 348858
  have htrace : WordTrace (prefixWord ++ tailWord_348858) baseStart_348858 baseEnd_348858 := by
    simpa [prefixWord, tailWord_348858, baseEnd_348858] using wordTrace_append hprefix tailTrace_348858
  have hstable : (prefixWord ++ tailWord_348858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348858).length < 2 ^ (prefixWord ++ tailWord_348858).sum := by decide
  have hdescent : baseEnd_348858 < baseStart_348858 := by decide
  rcases family_descends (prefixWord ++ tailWord_348858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348908 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_348908 : Nat := 118140960795 + 348908 * 2 ^ 59
def prefixEnd_348908 : Nat := 4983230072969 + 3 ^ 40 * 348908 * 2
def baseEnd_348908 : Nat := 179157508199026129545407

theorem tailTrace_348908 : CollatzResearch.WordTrace tailWord_348908 prefixEnd_348908 179157508199026129545407 := by
  unfold tailWord_348908
  simp only [CollatzResearch.WordTrace]
  refine ⟨6362860109986689793703689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8483813479982253058271585 6362860109986689793703689)
  ·
    refine ⟨4772145082490017345277767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6362860109986689793703689 4772145082490017345277767)
    ·
      refine ⟨7158217623735026017916651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4772145082490017345277767 7158217623735026017916651)
      ·
        refine ⟨10737326435602539026874977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7158217623735026017916651 10737326435602539026874977)
        ·
          refine ⟨8052994826701904270156233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10737326435602539026874977 8052994826701904270156233)
          ·
            refine ⟨6039746120026428202617175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8052994826701904270156233 6039746120026428202617175)
            ·
              refine ⟨9059619180039642303925763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6039746120026428202617175 9059619180039642303925763)
              ·
                refine ⟨13589428770059463455888645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9059619180039642303925763 13589428770059463455888645)
                ·
                  refine ⟨2548017894386149397979121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13589428770059463455888645 2548017894386149397979121)
                  ·
                    refine ⟨1911013420789612048484341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2548017894386149397979121 1911013420789612048484341)
                    ·
                      refine ⟨179157508199026129545407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1911013420789612048484341 179157508199026129545407)
                      ·
                        rfl

theorem cell23_348908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_348908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348908 prefixEnd_348908 := by exact prefixLift 348908
  have htrace : WordTrace (prefixWord ++ tailWord_348908) baseStart_348908 baseEnd_348908 := by
    simpa [prefixWord, tailWord_348908, baseEnd_348908] using wordTrace_append hprefix tailTrace_348908
  have hstable : (prefixWord ++ tailWord_348908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348908).length < 2 ^ (prefixWord ++ tailWord_348908).sum := by decide
  have hdescent : baseEnd_348908 < baseStart_348908 := by decide
  rcases family_descends (prefixWord ++ tailWord_348908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348912 : List Nat := [2, 1, 1, 1, 3, 1, 4, 4, 2, 1, 3]
def baseStart_348912 : Nat := 118140960795 + 348912 * 2 ^ 59
def prefixEnd_348912 : Nat := 4983230072969 + 3 ^ 40 * 348912 * 2
def baseEnd_348912 : Nat := 179159562121644113895389

theorem tailTrace_348912 : CollatzResearch.WordTrace tailWord_348912 prefixEnd_348912 179159562121644113895389 := by
  unfold tailWord_348912
  simp only [CollatzResearch.WordTrace]
  refine ⟨6362933055979444135276495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8483910741305925513701993 6362933055979444135276495)
  ·
    refine ⟨9544399583969166202914743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6362933055979444135276495 9544399583969166202914743)
    ·
      refine ⟨14316599375953749304372115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9544399583969166202914743 14316599375953749304372115)
      ·
        refine ⟨21474899063930623956558173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14316599375953749304372115 21474899063930623956558173)
        ·
          refine ⟨8053087148973983983709315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21474899063930623956558173 8053087148973983983709315)
          ·
            refine ⟨12079630723460975975563973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8053087148973983983709315 12079630723460975975563973)
            ·
              refine ⟨2264930760648932995418245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12079630723460975975563973 2264930760648932995418245)
              ·
                refine ⟨424674517621674936640921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2264930760648932995418245 424674517621674936640921)
                ·
                  refine ⟨318505888216256202480691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424674517621674936640921 318505888216256202480691)
                  ·
                    refine ⟨477758832324384303721037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 318505888216256202480691 477758832324384303721037)
                    ·
                      refine ⟨179159562121644113895389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 477758832324384303721037 179159562121644113895389)
                      ·
                        rfl

theorem cell23_348912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 2, 1, 3].length) (baseStart_348912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348912 prefixEnd_348912 := by exact prefixLift 348912
  have htrace : WordTrace (prefixWord ++ tailWord_348912) baseStart_348912 baseEnd_348912 := by
    simpa [prefixWord, tailWord_348912, baseEnd_348912] using wordTrace_append hprefix tailTrace_348912
  have hstable : (prefixWord ++ tailWord_348912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348912).length < 2 ^ (prefixWord ++ tailWord_348912).sum := by decide
  have hdescent : baseEnd_348912 < baseStart_348912 := by decide
  rcases family_descends (prefixWord ++ tailWord_348912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348956 : List Nat := [2, 2, 3, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_348956 : Nat := 118140960795 + 348956 * 2 ^ 59
def prefixEnd_348956 : Nat := 4983230072969 + 3 ^ 40 * 348956 * 2
def baseEnd_348956 : Nat := 179182155270441941745187

theorem tailTrace_348956 : CollatzResearch.WordTrace tailWord_348956 prefixEnd_348956 179182155270441941745187 := by
  unfold tailWord_348956
  simp only [CollatzResearch.WordTrace]
  refine ⟨6363735461899741892577361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8484980615866322523436481 6363735461899741892577361)
  ·
    refine ⟨4772801596424806419433021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6363735461899741892577361 4772801596424806419433021)
    ·
      refine ⟨1789800598659302407287383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4772801596424806419433021 1789800598659302407287383)
      ·
        refine ⟨2684700897988953610931075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1789800598659302407287383 2684700897988953610931075)
        ·
          refine ⟨4027051346983430416396613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2684700897988953610931075 4027051346983430416396613)
          ·
            refine ⟨755072127559393203074365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4027051346983430416396613 755072127559393203074365)
            ·
              refine ⟨283152047834772451152887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 755072127559393203074365 283152047834772451152887)
              ·
                refine ⟨424728071752158676729331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283152047834772451152887 424728071752158676729331)
                ·
                  refine ⟨637092107628238015093997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424728071752158676729331 637092107628238015093997)
                  ·
                    refine ⟨238909540360589255660249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 637092107628238015093997 238909540360589255660249)
                    ·
                      refine ⟨179182155270441941745187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 238909540360589255660249 179182155270441941745187)
                      ·
                        rfl

theorem cell23_348956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_348956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348956 prefixEnd_348956 := by exact prefixLift 348956
  have htrace : WordTrace (prefixWord ++ tailWord_348956) baseStart_348956 baseEnd_348956 := by
    simpa [prefixWord, tailWord_348956, baseEnd_348956] using wordTrace_append hprefix tailTrace_348956
  have hstable : (prefixWord ++ tailWord_348956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348956).length < 2 ^ (prefixWord ++ tailWord_348956).sum := by decide
  have hdescent : baseEnd_348956 < baseStart_348956 := by decide
  rcases family_descends (prefixWord ++ tailWord_348956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348965 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_348965 : Nat := 118140960795 + 348965 * 2 ^ 59
def prefixEnd_348965 : Nat := 4983230072969 + 3 ^ 40 * 348965 * 2
def baseEnd_348965 : Nat := 179186776596332406532645

theorem tailTrace_348965 : CollatzResearch.WordTrace tailWord_348965 prefixEnd_348965 179186776596332406532645 := by
  unfold tailWord_348965
  simp only [CollatzResearch.WordTrace]
  refine ⟨12727799180766878322232349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8485199453844585548154899 12727799180766878322232349)
  ·
    refine ⟨4772924692787579370837131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12727799180766878322232349 4772924692787579370837131)
    ·
      refine ⟨7159387039181369056255697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4772924692787579370837131 7159387039181369056255697)
      ·
        refine ⟨5369540279386026792191773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7159387039181369056255697 5369540279386026792191773)
        ·
          refine ⟨2013577604769760047071915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5369540279386026792191773 2013577604769760047071915)
          ·
            refine ⟨3020366407154640070607873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013577604769760047071915 3020366407154640070607873)
            ·
              refine ⟨2265274805365980052955905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3020366407154640070607873 2265274805365980052955905)
              ·
                refine ⟨1698956104024485039716929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2265274805365980052955905 1698956104024485039716929)
                ·
                  refine ⟨1274217078018363779787697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698956104024485039716929 1274217078018363779787697)
                  ·
                    refine ⟨955662808513772834840773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1274217078018363779787697 955662808513772834840773)
                    ·
                      refine ⟨179186776596332406532645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 955662808513772834840773 179186776596332406532645)
                      ·
                        rfl

theorem cell23_348965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_348965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348965 prefixEnd_348965 := by exact prefixLift 348965
  have htrace : WordTrace (prefixWord ++ tailWord_348965) baseStart_348965 baseEnd_348965 := by
    simpa [prefixWord, tailWord_348965, baseEnd_348965] using wordTrace_append hprefix tailTrace_348965
  have hstable : (prefixWord ++ tailWord_348965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348965).length < 2 ^ (prefixWord ++ tailWord_348965).sum := by decide
  have hdescent : baseEnd_348965 < baseStart_348965 := by decide
  rcases family_descends (prefixWord ++ tailWord_348965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349009 : List Nat := [1, 2, 2, 1, 6, 1, 2, 3, 5]
def baseStart_349009 : Nat := 118140960795 + 349009 * 2 ^ 59
def prefixEnd_349009 : Nat := 4983230072969 + 3 ^ 40 * 349009 * 2
def baseEnd_349009 : Nat := 19912152193903359375827

theorem tailTrace_349009 : CollatzResearch.WordTrace tailWord_349009 prefixEnd_349009 19912152193903359375827 := by
  unfold tailWord_349009
  simp only [CollatzResearch.WordTrace]
  refine ⟨12729403992607473836834081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8486269328404982557889387 12729403992607473836834081)
  ·
    refine ⟨9547052994455605377625561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12729403992607473836834081 9547052994455605377625561)
    ·
      refine ⟨7160289745841704033219171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9547052994455605377625561 7160289745841704033219171)
      ·
        refine ⟨10740434618762556049828757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7160289745841704033219171 10740434618762556049828757)
        ·
          refine ⟨503457872754494814835723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10740434618762556049828757 503457872754494814835723)
          ·
            refine ⟨755186809131742222253585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503457872754494814835723 755186809131742222253585)
            ·
              refine ⟨566390106848806666690189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755186809131742222253585 566390106848806666690189)
              ·
                refine ⟨212396290068302500008821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 566390106848806666690189 212396290068302500008821)
                ·
                  refine ⟨19912152193903359375827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212396290068302500008821 19912152193903359375827)
                  ·
                    rfl

theorem cell23_349009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 5].length) (baseStart_349009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349009 prefixEnd_349009 := by exact prefixLift 349009
  have htrace : WordTrace (prefixWord ++ tailWord_349009) baseStart_349009 baseEnd_349009 := by
    simpa [prefixWord, tailWord_349009, baseEnd_349009] using wordTrace_append hprefix tailTrace_349009
  have hstable : (prefixWord ++ tailWord_349009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349009).length < 2 ^ (prefixWord ++ tailWord_349009).sum := by decide
  have hdescent : baseEnd_349009 < baseStart_349009 := by decide
  rcases family_descends (prefixWord ++ tailWord_349009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349065 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 8]
def baseStart_349065 : Nat := 118140960795 + 349065 * 2 ^ 59
def prefixEnd_349065 : Nat := 4983230072969 + 3 ^ 40 * 349065 * 2
def baseEnd_349065 : Nat := 19915347184642446142465

theorem tailTrace_349065 : CollatzResearch.WordTrace tailWord_349065 prefixEnd_349065 19915347184642446142465 := by
  unfold tailWord_349065
  simp only [CollatzResearch.WordTrace]
  refine ⟨12731446480404595400872649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8487630986936396933915099 12731446480404595400872649)
  ·
    refine ⟨9548584860303446550654487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12731446480404595400872649 9548584860303446550654487)
    ·
      refine ⟨14322877290455169825981731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9548584860303446550654487 14322877290455169825981731)
      ·
        refine ⟨21484315935682754738972597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14322877290455169825981731 21484315935682754738972597)
        ·
          refine ⟨2014154618970258256778681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21484315935682754738972597 2014154618970258256778681)
          ·
            refine ⟨1510615964227693692584011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2014154618970258256778681 1510615964227693692584011)
            ·
              refine ⟨2265923946341540538876017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510615964227693692584011 2265923946341540538876017)
              ·
                refine ⟨1699442959756155404157013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2265923946341540538876017 1699442959756155404157013)
                ·
                  refine ⟨19915347184642446142465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1699442959756155404157013 19915347184642446142465)
                  ·
                    rfl

theorem cell23_349065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 8].length) (baseStart_349065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349065 prefixEnd_349065 := by exact prefixLift 349065
  have htrace : WordTrace (prefixWord ++ tailWord_349065) baseStart_349065 baseEnd_349065 := by
    simpa [prefixWord, tailWord_349065, baseEnd_349065] using wordTrace_append hprefix tailTrace_349065
  have hstable : (prefixWord ++ tailWord_349065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349065).length < 2 ^ (prefixWord ++ tailWord_349065).sum := by decide
  have hdescent : baseEnd_349065 < baseStart_349065 := by decide
  rcases family_descends (prefixWord ++ tailWord_349065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349109 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_349109 : Nat := 118140960795 + 349109 * 2 ^ 59
def prefixEnd_349109 : Nat := 4983230072969 + 3 ^ 40 * 349109 * 2
def baseEnd_349109 : Nat := 179260717810579843131983

theorem tailTrace_349109 : CollatzResearch.WordTrace tailWord_349109 prefixEnd_349109 179260717810579843131983 := by
  unfold tailWord_349109
  simp only [CollatzResearch.WordTrace]
  refine ⟨12733051292245190915474381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8488700861496793943649587 12733051292245190915474381)
  ·
    refine ⟨4774894234591946593302893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12733051292245190915474381 4774894234591946593302893)
    ·
      refine ⟨1790585337971979972488585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4774894234591946593302893 1790585337971979972488585)
      ·
        refine ⟨1342939003478984979366439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1790585337971979972488585 1342939003478984979366439)
        ·
          refine ⟨2014408505218477469049659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1342939003478984979366439 2014408505218477469049659)
          ·
            refine ⟨3021612757827716203574489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014408505218477469049659 3021612757827716203574489)
            ·
              refine ⟨2266209568370787152680867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3021612757827716203574489 2266209568370787152680867)
              ·
                refine ⟨3399314352556180729021301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2266209568370787152680867 3399314352556180729021301)
                ·
                  refine ⟨318685720552141943345747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3399314352556180729021301 318685720552141943345747)
                  ·
                    refine ⟨478028580828212915018621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 318685720552141943345747 478028580828212915018621)
                    ·
                      refine ⟨179260717810579843131983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 478028580828212915018621 179260717810579843131983)
                      ·
                        rfl

theorem cell23_349109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_349109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349109 prefixEnd_349109 := by exact prefixLift 349109
  have htrace : WordTrace (prefixWord ++ tailWord_349109) baseStart_349109 baseEnd_349109 := by
    simpa [prefixWord, tailWord_349109, baseEnd_349109] using wordTrace_append hprefix tailTrace_349109
  have hstable : (prefixWord ++ tailWord_349109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349109).length < 2 ^ (prefixWord ++ tailWord_349109).sum := by decide
  have hdescent : baseEnd_349109 < baseStart_349109 := by decide
  rcases family_descends (prefixWord ++ tailWord_349109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349110 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_349110 : Nat := 118140960795 + 349110 * 2 ^ 59
def prefixEnd_349110 : Nat := 4983230072969 + 3 ^ 40 * 349110 * 2
def baseEnd_349110 : Nat := 179261231291234339219479

theorem tailTrace_349110 : CollatzResearch.WordTrace tailWord_349110 prefixEnd_349110 179261231291234339219479 := by
  unfold tailWord_349110
  simp only [CollatzResearch.WordTrace]
  refine ⟨795817985327598005391299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8488725176827712057507189 795817985327598005391299)
  ·
    refine ⟨1193726977991397008086949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 795817985327598005391299 1193726977991397008086949)
    ·
      refine ⟨223823808373386939016303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1193726977991397008086949 223823808373386939016303)
      ·
        refine ⟨335735712560080408524455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223823808373386939016303 335735712560080408524455)
        ·
          refine ⟨503603568840120612786683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335735712560080408524455 503603568840120612786683)
          ·
            refine ⟨755405353260180919180025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503603568840120612786683 755405353260180919180025)
            ·
              refine ⟨566554014945135689385019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755405353260180919180025 566554014945135689385019)
              ·
                refine ⟨849831022417703534077529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566554014945135689385019 849831022417703534077529)
                ·
                  refine ⟨637373266813277650558147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 849831022417703534077529 637373266813277650558147)
                  ·
                    refine ⟨956059900219916475837221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 637373266813277650558147 956059900219916475837221)
                    ·
                      refine ⟨179261231291234339219479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 956059900219916475837221 179261231291234339219479)
                      ·
                        rfl

theorem cell23_349110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_349110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349110 prefixEnd_349110 := by exact prefixLift 349110
  have htrace : WordTrace (prefixWord ++ tailWord_349110) baseStart_349110 baseEnd_349110 := by
    simpa [prefixWord, tailWord_349110, baseEnd_349110] using wordTrace_append hprefix tailTrace_349110
  have hstable : (prefixWord ++ tailWord_349110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349110).length < 2 ^ (prefixWord ++ tailWord_349110).sum := by decide
  have hdescent : baseEnd_349110 < baseStart_349110 := by decide
  rcases family_descends (prefixWord ++ tailWord_349110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349112 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 3, 5]
def baseStart_349112 : Nat := 118140960795 + 349112 * 2 ^ 59
def prefixEnd_349112 : Nat := 4983230072969 + 3 ^ 40 * 349112 * 2
def baseEnd_349112 : Nat := 59754086084181110464823

theorem tailTrace_349112 : CollatzResearch.WordTrace tailWord_349112 prefixEnd_349112 59754086084181110464823 := by
  unfold tailWord_349112
  simp only [CollatzResearch.WordTrace]
  refine ⟨6366580355617161213916795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8488773807489548285222393 6366580355617161213916795)
  ·
    refine ⟨9549870533425741820875193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6366580355617161213916795 9549870533425741820875193)
    ·
      refine ⟨7162402900069306365656395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9549870533425741820875193 7162402900069306365656395)
      ·
        refine ⟨10743604350103959548484593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7162402900069306365656395 10743604350103959548484593)
        ·
          refine ⟨8057703262577969661363445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10743604350103959548484593 8057703262577969661363445)
          ·
            refine ⟨755409680866684655752823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8057703262577969661363445 755409680866684655752823)
            ·
              refine ⟨1133114521300026983629235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755409680866684655752823 1133114521300026983629235)
              ·
                refine ⟨1699671781950040475443853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133114521300026983629235 1699671781950040475443853)
                ·
                  refine ⟨637376918231265178291445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1699671781950040475443853 637376918231265178291445)
                  ·
                    refine ⟨59754086084181110464823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 637376918231265178291445 59754086084181110464823)
                    ·
                      rfl

theorem cell23_349112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_349112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349112 prefixEnd_349112 := by exact prefixLift 349112
  have htrace : WordTrace (prefixWord ++ tailWord_349112) baseStart_349112 baseEnd_349112 := by
    simpa [prefixWord, tailWord_349112, baseEnd_349112] using wordTrace_append hprefix tailTrace_349112
  have hstable : (prefixWord ++ tailWord_349112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349112).length < 2 ^ (prefixWord ++ tailWord_349112).sum := by decide
  have hdescent : baseEnd_349112 < baseStart_349112 := by decide
  rcases family_descends (prefixWord ++ tailWord_349112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349149 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_349149 : Nat := 118140960795 + 349149 * 2 ^ 59
def prefixEnd_349149 : Nat := 4983230072969 + 3 ^ 40 * 349149 * 2
def baseEnd_349149 : Nat := 179281257036759686631799

theorem tailTrace_349149 : CollatzResearch.WordTrace tailWord_349149 prefixEnd_349149 179281257036759686631799 := by
  unfold tailWord_349149
  simp only [CollatzResearch.WordTrace]
  refine ⟨12734510212100277746930501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8489673474733518497953667 12734510212100277746930501)
  ·
    refine ⟨2387720664768802077549469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12734510212100277746930501 2387720664768802077549469)
    ·
      refine ⟨895395249288300779081051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2387720664768802077549469 895395249288300779081051)
      ·
        refine ⟨1343092873932451168621577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 895395249288300779081051 1343092873932451168621577)
        ·
          refine ⟨1007319655449338376466183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1343092873932451168621577 1007319655449338376466183)
          ·
            refine ⟨1510979483174007564699275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007319655449338376466183 1510979483174007564699275)
            ·
              refine ⟨2266469224761011347048913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510979483174007564699275 2266469224761011347048913)
              ·
                refine ⟨1699851918570758510286685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2266469224761011347048913 1699851918570758510286685)
                ·
                  refine ⟨637444469464034441357507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1699851918570758510286685 637444469464034441357507)
                  ·
                    refine ⟨956166704196051662036261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 637444469464034441357507 956166704196051662036261)
                    ·
                      refine ⟨179281257036759686631799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 956166704196051662036261 179281257036759686631799)
                      ·
                        rfl

theorem cell23_349149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_349149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349149 prefixEnd_349149 := by exact prefixLift 349149
  have htrace : WordTrace (prefixWord ++ tailWord_349149) baseStart_349149 baseEnd_349149 := by
    simpa [prefixWord, tailWord_349149, baseEnd_349149] using wordTrace_append hprefix tailTrace_349149
  have hstable : (prefixWord ++ tailWord_349149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349149).length < 2 ^ (prefixWord ++ tailWord_349149).sum := by decide
  have hdescent : baseEnd_349149 < baseStart_349149 := by decide
  rcases family_descends (prefixWord ++ tailWord_349149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349159 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 1, 6]
def baseStart_349159 : Nat := 118140960795 + 349159 * 2 ^ 59
def prefixEnd_349159 : Nat := 4983230072969 + 3 ^ 40 * 349159 * 2
def baseEnd_349159 : Nat := 59762130614434882502251

theorem tailTrace_349159 : CollatzResearch.WordTrace tailWord_349159 prefixEnd_349159 59762130614434882502251 := by
  unfold tailWord_349159
  simp only [CollatzResearch.WordTrace]
  refine ⟨12734874942064049454794531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8489916628042699636529687 12734874942064049454794531)
  ·
    refine ⟨19102312413096074182191797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12734874942064049454794531 19102312413096074182191797)
    ·
      refine ⟨1790841788727756954580481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19102312413096074182191797 1790841788727756954580481)
      ·
        refine ⟨1343131341545817715935361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1790841788727756954580481 1343131341545817715935361)
        ·
          refine ⟨1007348506159363286951521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1343131341545817715935361 1007348506159363286951521)
          ·
            refine ⟨755511379619522465213641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1007348506159363286951521 755511379619522465213641)
            ·
              refine ⟨566633534714641848910231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755511379619522465213641 566633534714641848910231)
              ·
                refine ⟨849950302071962773365347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566633534714641848910231 849950302071962773365347)
                ·
                  refine ⟨1274925453107944160048021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849950302071962773365347 1274925453107944160048021)
                  ·
                    refine ⟨59762130614434882502251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1274925453107944160048021 59762130614434882502251)
                    ·
                      rfl

theorem cell23_349159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_349159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349159 prefixEnd_349159 := by exact prefixLift 349159
  have htrace : WordTrace (prefixWord ++ tailWord_349159) baseStart_349159 baseEnd_349159 := by
    simpa [prefixWord, tailWord_349159, baseEnd_349159] using wordTrace_append hprefix tailTrace_349159
  have hstable : (prefixWord ++ tailWord_349159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349159).length < 2 ^ (prefixWord ++ tailWord_349159).sum := by decide
  have hdescent : baseEnd_349159 < baseStart_349159 := by decide
  rcases family_descends (prefixWord ++ tailWord_349159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349169 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 3, 2, 3]
def baseStart_349169 : Nat := 118140960795 + 349169 * 2 ^ 59
def prefixEnd_349169 : Nat := 4983230072969 + 3 ^ 40 * 349169 * 2
def baseEnd_349169 : Nat := 179291526649849608381707

theorem tailTrace_349169 : CollatzResearch.WordTrace tailWord_349169 prefixEnd_349169 179291526649849608381707 := by
  unfold tailWord_349169
  simp only [CollatzResearch.WordTrace]
  refine ⟨12735239672027821162658561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8490159781351880775105707 12735239672027821162658561)
  ·
    refine ⟨9551429754020865871993921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12735239672027821162658561 9551429754020865871993921)
    ·
      refine ⟨7163572315515649403995441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9551429754020865871993921 7163572315515649403995441)
      ·
        refine ⟨5372679236636737052996581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7163572315515649403995441 5372679236636737052996581)
        ·
          refine ⟨1007377356869388197436859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5372679236636737052996581 1007377356869388197436859)
          ·
            refine ⟨1511066035304082296155289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007377356869388197436859 1511066035304082296155289)
            ·
              refine ⟨1133299526478061722116467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511066035304082296155289 1133299526478061722116467)
              ·
                refine ⟨1699949289717092583174701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133299526478061722116467 1699949289717092583174701)
                ·
                  refine ⟨637480983643909718690513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1699949289717092583174701 637480983643909718690513)
                  ·
                    refine ⟨478110737732932289017885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 637480983643909718690513 478110737732932289017885)
                    ·
                      refine ⟨179291526649849608381707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 478110737732932289017885 179291526649849608381707)
                      ·
                        rfl

theorem cell23_349169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_349169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349169 prefixEnd_349169 := by exact prefixLift 349169
  have htrace : WordTrace (prefixWord ++ tailWord_349169) baseStart_349169 baseEnd_349169 := by
    simpa [prefixWord, tailWord_349169, baseEnd_349169] using wordTrace_append hprefix tailTrace_349169
  have hstable : (prefixWord ++ tailWord_349169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349169).length < 2 ^ (prefixWord ++ tailWord_349169).sum := by decide
  have hdescent : baseEnd_349169 < baseStart_349169 := by decide
  rcases family_descends (prefixWord ++ tailWord_349169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349170 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 2, 3, 2]
def baseStart_349170 : Nat := 118140960795 + 349170 * 2 ^ 59
def prefixEnd_349170 : Nat := 4983230072969 + 3 ^ 40 * 349170 * 2
def baseEnd_349170 : Nat := 179292040130504104469203

theorem tailTrace_349170 : CollatzResearch.WordTrace tailWord_349170 prefixEnd_349170 179292040130504104469203 := by
  unfold tailWord_349170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3183819036256049583361241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8490184096682798888963309 3183819036256049583361241)
  ·
    refine ⟨2387864277192037187520931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3183819036256049583361241 2387864277192037187520931)
    ·
      refine ⟨3581796415788055781281397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2387864277192037187520931 3581796415788055781281397)
      ·
        refine ⟨335793413980130229495131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3581796415788055781281397 335793413980130229495131)
        ·
          refine ⟨503690120970195344242697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335793413980130229495131 503690120970195344242697)
          ·
            refine ⟨377767590727646508182023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503690120970195344242697 377767590727646508182023)
            ·
              refine ⟨566651386091469762273035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377767590727646508182023 566651386091469762273035)
              ·
                refine ⟨849977079137204643409553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566651386091469762273035 849977079137204643409553)
                ·
                  refine ⟨637482809352903482557165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 849977079137204643409553 637482809352903482557165)
                  ·
                    refine ⟨239056053507338805958937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 637482809352903482557165 239056053507338805958937)
                    ·
                      refine ⟨179292040130504104469203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239056053507338805958937 179292040130504104469203)
                      ·
                        rfl

theorem cell23_349170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_349170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349170 prefixEnd_349170 := by exact prefixLift 349170
  have htrace : WordTrace (prefixWord ++ tailWord_349170) baseStart_349170 baseEnd_349170 := by
    simpa [prefixWord, tailWord_349170, baseEnd_349170] using wordTrace_append hprefix tailTrace_349170
  have hstable : (prefixWord ++ tailWord_349170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349170).length < 2 ^ (prefixWord ++ tailWord_349170).sum := by decide
  have hdescent : baseEnd_349170 < baseStart_349170 := by decide
  rcases family_descends (prefixWord ++ tailWord_349170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349209 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 5, 3, 2]
def baseStart_349209 : Nat := 118140960795 + 349209 * 2 ^ 59
def prefixEnd_349209 : Nat := 4983230072969 + 3 ^ 40 * 349209 * 2
def baseEnd_349209 : Nat := 179312065876029451881523

theorem tailTrace_349209 : CollatzResearch.WordTrace tailWord_349209 prefixEnd_349209 179312065876029451881523 := by
  unfold tailWord_349209
  simp only [CollatzResearch.WordTrace]
  refine ⟨12736698591882907994114681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8491132394588605329409787 12736698591882907994114681)
  ·
    refine ⟨9552523943912180995586011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12736698591882907994114681 9552523943912180995586011)
    ·
      refine ⟨14328785915868271493379017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9552523943912180995586011 14328785915868271493379017)
      ·
        refine ⟨10746589436901203620034263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14328785915868271493379017 10746589436901203620034263)
        ·
          refine ⟨16119884155351805430051395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10746589436901203620034263 16119884155351805430051395)
          ·
            refine ⟨24179826233027708145077093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16119884155351805430051395 24179826233027708145077093)
            ·
              refine ⟨4533717418692695277201955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24179826233027708145077093 4533717418692695277201955)
              ·
                refine ⟨6800576128039042915802933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4533717418692695277201955 6800576128039042915802933)
                ·
                  refine ⟨637554012003660273356525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6800576128039042915802933 637554012003660273356525)
                  ·
                    refine ⟨239082754501372602508697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 637554012003660273356525 239082754501372602508697)
                    ·
                      refine ⟨179312065876029451881523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239082754501372602508697 179312065876029451881523)
                      ·
                        rfl

theorem cell23_349209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 3, 2].length) (baseStart_349209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349209 prefixEnd_349209 := by exact prefixLift 349209
  have htrace : WordTrace (prefixWord ++ tailWord_349209) baseStart_349209 baseEnd_349209 := by
    simpa [prefixWord, tailWord_349209, baseEnd_349209] using wordTrace_append hprefix tailTrace_349209
  have hstable : (prefixWord ++ tailWord_349209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349209).length < 2 ^ (prefixWord ++ tailWord_349209).sum := by decide
  have hdescent : baseEnd_349209 < baseStart_349209 := by decide
  rcases family_descends (prefixWord ++ tailWord_349209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349213 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_349213 : Nat := 118140960795 + 349213 * 2 ^ 59
def prefixEnd_349213 : Nat := 4983230072969 + 3 ^ 40 * 349213 * 2
def baseEnd_349213 : Nat := 179314119798647436231505

theorem tailTrace_349213 : CollatzResearch.WordTrace tailWord_349213 prefixEnd_349213 179314119798647436231505 := by
  unfold tailWord_349213
  simp only [CollatzResearch.WordTrace]
  refine ⟨12736844483868416677260293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8491229655912277784840195 12736844483868416677260293)
  ·
    refine ⟨2388158340725328126986305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12736844483868416677260293 2388158340725328126986305)
    ·
      refine ⟨1791118755543996095239729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2388158340725328126986305 1791118755543996095239729)
      ·
        refine ⟨1343339066657997071429797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1791118755543996095239729 1343339066657997071429797)
        ·
          refine ⟨251876074998374450893087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1343339066657997071429797 251876074998374450893087)
          ·
            refine ⟨377814112497561676339631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251876074998374450893087 377814112497561676339631)
            ·
              refine ⟨566721168746342514509447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377814112497561676339631 566721168746342514509447)
              ·
                refine ⟨850081753119513771764171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566721168746342514509447 850081753119513771764171)
                ·
                  refine ⟨1275122629679270657646257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850081753119513771764171 1275122629679270657646257)
                  ·
                    refine ⟨956341972259452993234693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1275122629679270657646257 956341972259452993234693)
                    ·
                      refine ⟨179314119798647436231505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 956341972259452993234693 179314119798647436231505)
                      ·
                        rfl

theorem cell23_349213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_349213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349213 prefixEnd_349213 := by exact prefixLift 349213
  have htrace : WordTrace (prefixWord ++ tailWord_349213) baseStart_349213 baseEnd_349213 := by
    simpa [prefixWord, tailWord_349213, baseEnd_349213] using wordTrace_append hprefix tailTrace_349213
  have hstable : (prefixWord ++ tailWord_349213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349213).length < 2 ^ (prefixWord ++ tailWord_349213).sum := by decide
  have hdescent : baseEnd_349213 < baseStart_349213 := by decide
  rcases family_descends (prefixWord ++ tailWord_349213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349239 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 3, 4, 2]
def baseStart_349239 : Nat := 118140960795 + 349239 * 2 ^ 59
def prefixEnd_349239 : Nat := 4983230072969 + 3 ^ 40 * 349239 * 2
def baseEnd_349239 : Nat := 179327470295664334506385

theorem tailTrace_349239 : CollatzResearch.WordTrace tailWord_349239 prefixEnd_349239 179327470295664334506385 := by
  unfold tailWord_349239
  simp only [CollatzResearch.WordTrace]
  refine ⟨12737792781774223117706771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8491861854516148745137847 12737792781774223117706771)
  ·
    refine ⟨19106689172661334676560157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12737792781774223117706771 19106689172661334676560157)
    ·
      refine ⟨7165008439748000503710059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19106689172661334676560157 7165008439748000503710059)
      ·
        refine ⟨10747512659622000755565089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7165008439748000503710059 10747512659622000755565089)
        ·
          refine ⟨8060634494716500566673817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10747512659622000755565089 8060634494716500566673817)
          ·
            refine ⟨6045475871037375425005363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8060634494716500566673817 6045475871037375425005363)
            ·
              refine ⟨9068213806556063137508045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6045475871037375425005363 9068213806556063137508045)
              ·
                refine ⟨3400580177458523676565517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9068213806556063137508045 3400580177458523676565517)
                ·
                  refine ⟨1275217566546946378712069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3400580177458523676565517 1275217566546946378712069)
                  ·
                    refine ⟨239103293727552446008513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1275217566546946378712069 239103293727552446008513)
                    ·
                      refine ⟨179327470295664334506385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239103293727552446008513 179327470295664334506385)
                      ·
                        rfl

theorem cell23_349239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 4, 2].length) (baseStart_349239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349239 prefixEnd_349239 := by exact prefixLift 349239
  have htrace : WordTrace (prefixWord ++ tailWord_349239) baseStart_349239 baseEnd_349239 := by
    simpa [prefixWord, tailWord_349239, baseEnd_349239] using wordTrace_append hprefix tailTrace_349239
  have hstable : (prefixWord ++ tailWord_349239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349239).length < 2 ^ (prefixWord ++ tailWord_349239).sum := by decide
  have hdescent : baseEnd_349239 < baseStart_349239 := by decide
  rcases family_descends (prefixWord ++ tailWord_349239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349242 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_349242 : Nat := 118140960795 + 349242 * 2 ^ 59
def prefixEnd_349242 : Nat := 4983230072969 + 3 ^ 40 * 349242 * 2
def baseEnd_349242 : Nat := 179329010737627822768871

theorem tailTrace_349242 : CollatzResearch.WordTrace tailWord_349242 prefixEnd_349242 179329010737627822768871 := by
  unfold tailWord_349242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3184475550190838657516495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8491934800508903086710653 3184475550190838657516495)
  ·
    refine ⟨4776713325286257986274743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3184475550190838657516495 4776713325286257986274743)
    ·
      refine ⟨7165069987929386979412115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4776713325286257986274743 7165069987929386979412115)
      ·
        refine ⟨10747604981894080469118173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7165069987929386979412115 10747604981894080469118173)
        ·
          refine ⟨4030351868210280175919315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10747604981894080469118173 4030351868210280175919315)
          ·
            refine ⟨6045527802315420263878973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4030351868210280175919315 6045527802315420263878973)
            ·
              refine ⟨2267072925868282598954615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6045527802315420263878973 2267072925868282598954615)
              ·
                refine ⟨3400609388802423898431923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267072925868282598954615 3400609388802423898431923)
                ·
                  refine ⟨5100914083203635847647885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400609388802423898431923 5100914083203635847647885)
                  ·
                    refine ⟨1912842781201363442867957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5100914083203635847647885 1912842781201363442867957)
                    ·
                      refine ⟨179329010737627822768871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1912842781201363442867957 179329010737627822768871)
                      ·
                        rfl

theorem cell23_349242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_349242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349242 prefixEnd_349242 := by exact prefixLift 349242
  have htrace : WordTrace (prefixWord ++ tailWord_349242) baseStart_349242 baseEnd_349242 := by
    simpa [prefixWord, tailWord_349242, baseEnd_349242] using wordTrace_append hprefix tailTrace_349242
  have hstable : (prefixWord ++ tailWord_349242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349242).length < 2 ^ (prefixWord ++ tailWord_349242).sum := by decide
  have hdescent : baseEnd_349242 < baseStart_349242 := by decide
  rcases family_descends (prefixWord ++ tailWord_349242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349256 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 4, 2, 2]
def baseStart_349256 : Nat := 118140960795 + 349256 * 2 ^ 59
def prefixEnd_349256 : Nat := 4983230072969 + 3 ^ 40 * 349256 * 2
def baseEnd_349256 : Nat := 179336199466790767993807

theorem tailTrace_349256 : CollatzResearch.WordTrace tailWord_349256 prefixEnd_349256 179336199466790767993807 := by
  unfold tailWord_349256
  simp only [CollatzResearch.WordTrace]
  refine ⟨6369206411356317510537811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8492275215141756680717081 6369206411356317510537811)
  ·
    refine ⟨9553809617034476265806717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6369206411356317510537811 9553809617034476265806717)
    ·
      refine ⟨3582678606387928599677519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9553809617034476265806717 3582678606387928599677519)
      ·
        refine ⟨5374017909581892899516279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3582678606387928599677519 5374017909581892899516279)
        ·
          refine ⟨8061026864372839349274419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5374017909581892899516279 8061026864372839349274419)
          ·
            refine ⟨12091540296559259023911629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8061026864372839349274419 12091540296559259023911629)
            ·
              refine ⟨4534327611209722133966861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12091540296559259023911629 4534327611209722133966861)
              ·
                refine ⟨1700372854203645800237573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4534327611209722133966861 1700372854203645800237573)
                ·
                  refine ⟨318819910163183587544545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1700372854203645800237573 318819910163183587544545)
                  ·
                    refine ⟨239114932622387690658409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 318819910163183587544545 239114932622387690658409)
                    ·
                      refine ⟨179336199466790767993807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239114932622387690658409 179336199466790767993807)
                      ·
                        rfl

theorem cell23_349256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_349256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349256 prefixEnd_349256 := by exact prefixLift 349256
  have htrace : WordTrace (prefixWord ++ tailWord_349256) baseStart_349256 baseEnd_349256 := by
    simpa [prefixWord, tailWord_349256, baseEnd_349256] using wordTrace_append hprefix tailTrace_349256
  have hstable : (prefixWord ++ tailWord_349256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349256).length < 2 ^ (prefixWord ++ tailWord_349256).sum := by decide
  have hdescent : baseEnd_349256 < baseStart_349256 := by decide
  rcases family_descends (prefixWord ++ tailWord_349256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349277 : List Nat := [1, 4, 4, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_349277 : Nat := 118140960795 + 349277 * 2 ^ 59
def prefixEnd_349277 : Nat := 4983230072969 + 3 ^ 40 * 349277 * 2
def baseEnd_349277 : Nat := 179346982560535185831211

theorem tailTrace_349277 : CollatzResearch.WordTrace tailWord_349277 prefixEnd_349277 179346982560535185831211 := by
  unfold tailWord_349277
  simp only [CollatzResearch.WordTrace]
  refine ⟨12739178755636555607590085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8492785837091037071726723 12739178755636555607590085)
  ·
    refine ⟨2388596016681854176423141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12739178755636555607590085 2388596016681854176423141)
    ·
      refine ⟨447861753127847658079339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2388596016681854176423141 447861753127847658079339)
      ·
        refine ⟨671792629691771487119009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447861753127847658079339 671792629691771487119009)
        ·
          refine ⟨503844472268828615339257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671792629691771487119009 503844472268828615339257)
          ·
            refine ⟨377883354201621461504443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503844472268828615339257 377883354201621461504443)
            ·
              refine ⟨566825031302432192256665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377883354201621461504443 566825031302432192256665)
              ·
                refine ⟨425118773476824144192499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566825031302432192256665 425118773476824144192499)
                ·
                  refine ⟨637678160215236216288749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425118773476824144192499 637678160215236216288749)
                  ·
                    refine ⟨239129310080713581108281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 637678160215236216288749 239129310080713581108281)
                    ·
                      refine ⟨179346982560535185831211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239129310080713581108281 179346982560535185831211)
                      ·
                        rfl

theorem cell23_349277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_349277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349277 prefixEnd_349277 := by exact prefixLift 349277
  have htrace : WordTrace (prefixWord ++ tailWord_349277) baseStart_349277 baseEnd_349277 := by
    simpa [prefixWord, tailWord_349277, baseEnd_349277] using wordTrace_append hprefix tailTrace_349277
  have hstable : (prefixWord ++ tailWord_349277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349277).length < 2 ^ (prefixWord ++ tailWord_349277).sum := by decide
  have hdescent : baseEnd_349277 < baseStart_349277 := by decide
  rcases family_descends (prefixWord ++ tailWord_349277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349299 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 6, 5, 2]
def baseStart_349299 : Nat := 118140960795 + 349299 * 2 ^ 59
def prefixEnd_349299 : Nat := 4983230072969 + 3 ^ 40 * 349299 * 2
def baseEnd_349299 : Nat := 179358279134934099756109

theorem tailTrace_349299 : CollatzResearch.WordTrace tailWord_349299 prefixEnd_349299 179358279134934099756109 := by
  unfold tailWord_349299
  simp only [CollatzResearch.WordTrace]
  refine ⟨12739981161556853364890951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8493320774371235576593967 12739981161556853364890951)
  ·
    refine ⟨19109971742335280047336427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12739981161556853364890951 19109971742335280047336427)
    ·
      refine ⟨28664957613502920071004641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19109971742335280047336427 28664957613502920071004641)
      ·
        refine ⟨21498718210127190053253481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28664957613502920071004641 21498718210127190053253481)
        ·
          refine ⟨16124038657595392539940111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21498718210127190053253481 16124038657595392539940111)
          ·
            refine ⟨24186057986393088809910167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16124038657595392539940111 24186057986393088809910167)
            ·
              refine ⟨36279086979589633214865251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24186057986393088809910167 36279086979589633214865251)
              ·
                refine ⟨54418630469384449822297877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36279086979589633214865251 54418630469384449822297877)
                ·
                  refine ⟨2550873303252396085420213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54418630469384449822297877 2550873303252396085420213)
                  ·
                    refine ⟨239144372179912133008145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2550873303252396085420213 239144372179912133008145)
                    ·
                      refine ⟨179358279134934099756109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239144372179912133008145 179358279134934099756109)
                      ·
                        rfl

theorem cell23_349299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 5, 2].length) (baseStart_349299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349299 prefixEnd_349299 := by exact prefixLift 349299
  have htrace : WordTrace (prefixWord ++ tailWord_349299) baseStart_349299 baseEnd_349299 := by
    simpa [prefixWord, tailWord_349299, baseEnd_349299] using wordTrace_append hprefix tailTrace_349299
  have hstable : (prefixWord ++ tailWord_349299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349299).length < 2 ^ (prefixWord ++ tailWord_349299).sum := by decide
  have hdescent : baseEnd_349299 < baseStart_349299 := by decide
  rcases family_descends (prefixWord ++ tailWord_349299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349309 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_349309 : Nat := 118140960795 + 349309 * 2 ^ 59
def prefixEnd_349309 : Nat := 4983230072969 + 3 ^ 40 * 349309 * 2
def baseEnd_349309 : Nat := 59787804647159686877021

theorem tailTrace_349309 : CollatzResearch.WordTrace tailWord_349309 prefixEnd_349309 59787804647159686877021 := by
  unfold tailWord_349309
  simp only [CollatzResearch.WordTrace]
  refine ⟨12740345891520625072754981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8493563927680416715169987 12740345891520625072754981)
  ·
    refine ⟨2388814854660117201141559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12740345891520625072754981 2388814854660117201141559)
    ·
      refine ⟨3583222281990175801712339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2388814854660117201141559 3583222281990175801712339)
      ·
        refine ⟨5374833422985263702568509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583222281990175801712339 5374833422985263702568509)
        ·
          refine ⟨2015562533619473888463191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5374833422985263702568509 2015562533619473888463191)
          ·
            refine ⟨3023343800429210832694787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015562533619473888463191 3023343800429210832694787)
            ·
              refine ⟨4535015700643816249042181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023343800429210832694787 4535015700643816249042181)
              ·
                refine ⟨850315443870715546695409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4535015700643816249042181 850315443870715546695409)
                ·
                  refine ⟨637736582903036660021557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 850315443870715546695409 637736582903036660021557)
                  ·
                    refine ⟨59787804647159686877021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 637736582903036660021557 59787804647159686877021)
                    ·
                      rfl

theorem cell23_349309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_349309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349309 prefixEnd_349309 := by exact prefixLift 349309
  have htrace : WordTrace (prefixWord ++ tailWord_349309) baseStart_349309 baseEnd_349309 := by
    simpa [prefixWord, tailWord_349309, baseEnd_349309] using wordTrace_append hprefix tailTrace_349309
  have hstable : (prefixWord ++ tailWord_349309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349309).length < 2 ^ (prefixWord ++ tailWord_349309).sum := by decide
  have hdescent : baseEnd_349309 < baseStart_349309 := by decide
  rcases family_descends (prefixWord ++ tailWord_349309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349313 : List Nat := [1, 2, 4, 2, 2, 1, 4, 2, 5]
def baseStart_349313 : Nat := 118140960795 + 349313 * 2 ^ 59
def prefixEnd_349313 : Nat := 4983230072969 + 3 ^ 40 * 349313 * 2
def baseEnd_349313 : Nat := 19929496429344116109005

theorem tailTrace_349313 : CollatzResearch.WordTrace tailWord_349313 prefixEnd_349313 19929496429344116109005 := by
  unfold tailWord_349313
  simp only [CollatzResearch.WordTrace]
  refine ⟨12740491783506133755900593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8493661189004089170600395 12740491783506133755900593)
  ·
    refine ⟨9555368837629600316925445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12740491783506133755900593 9555368837629600316925445)
    ·
      refine ⟨1791631657055550059423521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9555368837629600316925445 1791631657055550059423521)
      ·
        refine ⟨1343723742791662544567641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1791631657055550059423521 1343723742791662544567641)
        ·
          refine ⟨1007792807093746908425731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1343723742791662544567641 1007792807093746908425731)
          ·
            refine ⟨1511689210640620362638597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007792807093746908425731 1511689210640620362638597)
            ·
              refine ⟨283441726995116317994737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1511689210640620362638597 283441726995116317994737)
              ·
                refine ⟨212581295246337238496053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283441726995116317994737 212581295246337238496053)
                ·
                  refine ⟨19929496429344116109005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212581295246337238496053 19929496429344116109005)
                  ·
                    rfl

theorem cell23_349313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 5].length) (baseStart_349313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349313 prefixEnd_349313 := by exact prefixLift 349313
  have htrace : WordTrace (prefixWord ++ tailWord_349313) baseStart_349313 baseEnd_349313 := by
    simpa [prefixWord, tailWord_349313, baseEnd_349313] using wordTrace_append hprefix tailTrace_349313
  have hstable : (prefixWord ++ tailWord_349313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349313).length < 2 ^ (prefixWord ++ tailWord_349313).sum := by decide
  have hdescent : baseEnd_349313 < baseStart_349313 := by decide
  rcases family_descends (prefixWord ++ tailWord_349313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349316 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_349316 : Nat := 118140960795 + 349316 * 2 ^ 59
def prefixEnd_349316 : Nat := 4983230072969 + 3 ^ 40 * 349316 * 2
def baseEnd_349316 : Nat := 179367008306060533243531

theorem tailTrace_349316 : CollatzResearch.WordTrace tailWord_349316 prefixEnd_349316 179367008306060533243531 := by
  unfold tailWord_349316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370300601247632634129901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8493734134996843512173201 6370300601247632634129901)
  ·
    refine ⟨2388862725467862237798713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6370300601247632634129901 2388862725467862237798713)
    ·
      refine ⟨1791647044100896678349035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2388862725467862237798713 1791647044100896678349035)
      ·
        refine ⟨2687470566151345017523553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1791647044100896678349035 2687470566151345017523553)
        ·
          refine ⟨2015602924613508763142665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2687470566151345017523553 2015602924613508763142665)
          ·
            refine ⟨1511702193460131572356999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2015602924613508763142665 1511702193460131572356999)
            ·
              refine ⟨2267553290190197358535499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1511702193460131572356999 2267553290190197358535499)
              ·
                refine ⟨3401329935285296037803249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267553290190197358535499 3401329935285296037803249)
                ·
                  refine ⟨2550997451463972028352437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3401329935285296037803249 2550997451463972028352437)
                  ·
                    refine ⟨239156011074747377658041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2550997451463972028352437 239156011074747377658041)
                    ·
                      refine ⟨179367008306060533243531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239156011074747377658041 179367008306060533243531)
                      ·
                        rfl

theorem cell23_349316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_349316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349316 prefixEnd_349316 := by exact prefixLift 349316
  have htrace : WordTrace (prefixWord ++ tailWord_349316) baseStart_349316 baseEnd_349316 := by
    simpa [prefixWord, tailWord_349316, baseEnd_349316] using wordTrace_append hprefix tailTrace_349316
  have hstable : (prefixWord ++ tailWord_349316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349316).length < 2 ^ (prefixWord ++ tailWord_349316).sum := by decide
  have hdescent : baseEnd_349316 < baseStart_349316 := by decide
  rcases family_descends (prefixWord ++ tailWord_349316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349343 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 2, 5]
def baseStart_349343 : Nat := 118140960795 + 349343 * 2 ^ 59
def prefixEnd_349343 : Nat := 4983230072969 + 3 ^ 40 * 349343 * 2
def baseEnd_349343 : Nat := 59793624094577309201969

theorem tailTrace_349343 : CollatzResearch.WordTrace tailWord_349343 prefixEnd_349343 59793624094577309201969 := by
  unfold tailWord_349343
  simp only [CollatzResearch.WordTrace]
  refine ⟨12741585973397448879492683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8494390648931632586328455 12741585973397448879492683)
  ·
    refine ⟨19112378960096173319239025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12741585973397448879492683 19112378960096173319239025)
    ·
      refine ⟨14334284220072129989429269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19112378960096173319239025 14334284220072129989429269)
      ·
        refine ⟨671919572815881093254497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14334284220072129989429269 671919572815881093254497)
        ·
          refine ⟨503939679611910819940873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671919572815881093254497 503939679611910819940873)
          ·
            refine ⟨377954759708933114955655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503939679611910819940873 377954759708933114955655)
            ·
              refine ⟨566932139563399672433483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377954759708933114955655 566932139563399672433483)
              ·
                refine ⟨850398209345099508650225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566932139563399672433483 850398209345099508650225)
                ·
                  refine ⟨637798657008824631487669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 850398209345099508650225 637798657008824631487669)
                  ·
                    refine ⟨59793624094577309201969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 637798657008824631487669 59793624094577309201969)
                    ·
                      rfl

theorem cell23_349343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 5].length) (baseStart_349343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349343 prefixEnd_349343 := by exact prefixLift 349343
  have htrace : WordTrace (prefixWord ++ tailWord_349343) baseStart_349343 baseEnd_349343 := by
    simpa [prefixWord, tailWord_349343, baseEnd_349343] using wordTrace_append hprefix tailTrace_349343
  have hstable : (prefixWord ++ tailWord_349343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349343).length < 2 ^ (prefixWord ++ tailWord_349343).sum := by decide
  have hdescent : baseEnd_349343 < baseStart_349343 := by decide
  rcases family_descends (prefixWord ++ tailWord_349343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349369 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 8]
def baseStart_349369 : Nat := 118140960795 + 349369 * 2 ^ 59
def prefixEnd_349369 : Nat := 4983230072969 + 3 ^ 40 * 349369 * 2
def baseEnd_349369 : Nat := 19932691420083202875643

theorem tailTrace_349369 : CollatzResearch.WordTrace tailWord_349369 prefixEnd_349369 19932691420083202875643 := by
  unfold tailWord_349369
  simp only [CollatzResearch.WordTrace]
  refine ⟨12742534271303255319939161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8495022847535503546626107 12742534271303255319939161)
  ·
    refine ⟨9556900703477441489954371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12742534271303255319939161 9556900703477441489954371)
    ·
      refine ⟨14335351055216162234931557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9556900703477441489954371 14335351055216162234931557)
      ·
        refine ⟨2687878322853030419049667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14335351055216162234931557 2687878322853030419049667)
        ·
          refine ⟨4031817484279545628574501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687878322853030419049667 4031817484279545628574501)
          ·
            refine ⟨755965778302414805357719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4031817484279545628574501 755965778302414805357719)
            ·
              refine ⟨1133948667453622208036579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755965778302414805357719 1133948667453622208036579)
              ·
                refine ⟨1700923001180433312054869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133948667453622208036579 1700923001180433312054869)
                ·
                  refine ⟨19932691420083202875643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1700923001180433312054869 19932691420083202875643)
                  ·
                    rfl

theorem cell23_349369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 8].length) (baseStart_349369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349369 prefixEnd_349369 := by exact prefixLift 349369
  have htrace : WordTrace (prefixWord ++ tailWord_349369) baseStart_349369 baseEnd_349369 := by
    simpa [prefixWord, tailWord_349369, baseEnd_349369] using wordTrace_append hprefix tailTrace_349369
  have hstable : (prefixWord ++ tailWord_349369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349369).length < 2 ^ (prefixWord ++ tailWord_349369).sum := by decide
  have hdescent : baseEnd_349369 < baseStart_349369 := by decide
  rcases family_descends (prefixWord ++ tailWord_349369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349373 : List Nat := [1, 4, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_349373 : Nat := 118140960795 + 349373 * 2 ^ 59
def prefixEnd_349373 : Nat := 4983230072969 + 3 ^ 40 * 349373 * 2
def baseEnd_349373 : Nat := 59798758901122270076923

theorem tailTrace_349373 : CollatzResearch.WordTrace tailWord_349373 prefixEnd_349373 59798758901122270076923 := by
  unfold tailWord_349373
  simp only [CollatzResearch.WordTrace]
  refine ⟨12742680163288764003084773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8495120108859176002056515 12742680163288764003084773)
  ·
    refine ⟨2389252530616643250578395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12742680163288764003084773 2389252530616643250578395)
    ·
      refine ⟨3583878795924964875867593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2389252530616643250578395 3583878795924964875867593)
      ·
        refine ⟨2687909096943723656900695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3583878795924964875867593 2687909096943723656900695)
        ·
          refine ⟨4031863645415585485351043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687909096943723656900695 4031863645415585485351043)
          ·
            refine ⟨6047795468123378228026565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4031863645415585485351043 6047795468123378228026565)
            ·
              refine ⟨1133961650273133417754981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6047795468123378228026565 1133961650273133417754981)
              ·
                refine ⟨212617809426212515829059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1133961650273133417754981 212617809426212515829059)
                ·
                  refine ⟨318926714139318773743589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212617809426212515829059 318926714139318773743589)
                  ·
                    refine ⟨59798758901122270076923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 318926714139318773743589 59798758901122270076923)
                    ·
                      rfl

theorem cell23_349373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_349373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349373 prefixEnd_349373 := by exact prefixLift 349373
  have htrace : WordTrace (prefixWord ++ tailWord_349373) baseStart_349373 baseEnd_349373 := by
    simpa [prefixWord, tailWord_349373, baseEnd_349373] using wordTrace_append hprefix tailTrace_349373
  have hstable : (prefixWord ++ tailWord_349373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349373).length < 2 ^ (prefixWord ++ tailWord_349373).sum := by decide
  have hdescent : baseEnd_349373 < baseStart_349373 := by decide
  rcases family_descends (prefixWord ++ tailWord_349373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349399 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 3, 5]
def baseStart_349399 : Nat := 118140960795 + 349399 * 2 ^ 59
def prefixEnd_349399 : Nat := 4983230072969 + 3 ^ 40 * 349399 * 2
def baseEnd_349399 : Nat := 59803209066794569501883

theorem tailTrace_349399 : CollatzResearch.WordTrace tailWord_349399 prefixEnd_349399 59803209066794569501883 := by
  unfold tailWord_349399
  simp only [CollatzResearch.WordTrace]
  refine ⟨12743628461194570443531251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8495752307463046962354167 12743628461194570443531251)
  ·
    refine ⟨19115442691791855665296877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12743628461194570443531251 19115442691791855665296877)
    ·
      refine ⟨7168291009421945874486329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19115442691791855665296877 7168291009421945874486329)
      ·
        refine ⟨5376218257066459405864747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7168291009421945874486329 5376218257066459405864747)
        ·
          refine ⟨8064327385599689108797121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5376218257066459405864747 8064327385599689108797121)
          ·
            refine ⟨6048245539199766831597841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8064327385599689108797121 6048245539199766831597841)
            ·
              refine ⟨4536184154399825123698381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6048245539199766831597841 4536184154399825123698381)
              ·
                refine ⟨1701069057899934421386893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4536184154399825123698381 1701069057899934421386893)
                ·
                  refine ⟨637900896712475408020085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1701069057899934421386893 637900896712475408020085)
                  ·
                    refine ⟨59803209066794569501883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 637900896712475408020085 59803209066794569501883)
                    ·
                      rfl

theorem cell23_349399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_349399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349399 prefixEnd_349399 := by exact prefixLift 349399
  have htrace : WordTrace (prefixWord ++ tailWord_349399) baseStart_349399 baseEnd_349399 := by
    simpa [prefixWord, tailWord_349399, baseEnd_349399] using wordTrace_append hprefix tailTrace_349399
  have hstable : (prefixWord ++ tailWord_349399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349399).length < 2 ^ (prefixWord ++ tailWord_349399).sum := by decide
  have hdescent : baseEnd_349399 < baseStart_349399 := by decide
  rcases family_descends (prefixWord ++ tailWord_349399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349416 : List Nat := [2, 1, 4, 1, 2, 1, 1, 5, 1, 5]
def baseStart_349416 : Nat := 118140960795 + 349416 * 2 ^ 59
def prefixEnd_349416 : Nat := 4983230072969 + 3 ^ 40 * 349416 * 2
def baseEnd_349416 : Nat := 59806118790503380664357

theorem tailTrace_349416 : CollatzResearch.WordTrace tailWord_349416 prefixEnd_349416 59806118790503380664357 := by
  unfold tailWord_349416
  simp only [CollatzResearch.WordTrace]
  refine ⟨6372124251066491173450051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8496165668088654897933401 6372124251066491173450051)
  ·
    refine ⟨9558186376599736760175077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6372124251066491173450051 9558186376599736760175077)
    ·
      refine ⟨1792159945612450642532827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9558186376599736760175077 1792159945612450642532827)
      ·
        refine ⟨2688239918418675963799241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792159945612450642532827 2688239918418675963799241)
        ·
          refine ⟨2016179938814006972849431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2688239918418675963799241 2016179938814006972849431)
          ·
            refine ⟨3024269908221010459274147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016179938814006972849431 3024269908221010459274147)
            ·
              refine ⟨4536404862331515688911221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024269908221010459274147 4536404862331515688911221)
              ·
                refine ⟨425287955843579595835427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4536404862331515688911221 425287955843579595835427)
                ·
                  refine ⟨637931933765369393753141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425287955843579595835427 637931933765369393753141)
                  ·
                    refine ⟨59806118790503380664357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 637931933765369393753141 59806118790503380664357)
                    ·
                      rfl

theorem cell23_349416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_349416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349416 prefixEnd_349416 := by exact prefixLift 349416
  have htrace : WordTrace (prefixWord ++ tailWord_349416) baseStart_349416 baseEnd_349416 := by
    simpa [prefixWord, tailWord_349416, baseEnd_349416] using wordTrace_append hprefix tailTrace_349416
  have hstable : (prefixWord ++ tailWord_349416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349416).length < 2 ^ (prefixWord ++ tailWord_349416).sum := by decide
  have hdescent : baseEnd_349416 < baseStart_349416 := by decide
  rcases family_descends (prefixWord ++ tailWord_349416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349449 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 6]
def baseStart_349449 : Nat := 118140960795 + 349449 * 2 ^ 59
def prefixEnd_349449 : Nat := 4983230072969 + 3 ^ 40 * 349449 * 2
def baseEnd_349449 : Nat := 179435301233108512880419

theorem tailTrace_349449 : CollatzResearch.WordTrace tailWord_349449 prefixEnd_349449 179435301233108512880419 := by
  unfold tailWord_349449
  simp only [CollatzResearch.WordTrace]
  refine ⟨12745452111013428982851401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8496968074008952655234267 12745452111013428982851401)
  ·
    refine ⟨9559089083260071737138551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12745452111013428982851401 9559089083260071737138551)
    ·
      refine ⟨14338633624890107605707827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9559089083260071737138551 14338633624890107605707827)
      ·
        refine ⟨21507950437335161408561741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14338633624890107605707827 21507950437335161408561741)
        ·
          refine ⟨8065481414000685528210653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21507950437335161408561741 8065481414000685528210653)
          ·
            refine ⟨3024555530250257073078995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8065481414000685528210653 3024555530250257073078995)
            ·
              refine ⟨4536833295375385609618493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024555530250257073078995 4536833295375385609618493)
              ·
                refine ⟨1701312485765769603606935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4536833295375385609618493 1701312485765769603606935)
                ·
                  refine ⟨2551968728648654405410403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1701312485765769603606935 2551968728648654405410403)
                  ·
                    refine ⟨3827953092972981608115605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2551968728648654405410403 3827953092972981608115605)
                    ·
                      refine ⟨179435301233108512880419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3827953092972981608115605 179435301233108512880419)
                      ·
                        rfl

theorem cell23_349449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_349449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349449 prefixEnd_349449 := by exact prefixLift 349449
  have htrace : WordTrace (prefixWord ++ tailWord_349449) baseStart_349449 baseEnd_349449 := by
    simpa [prefixWord, tailWord_349449, baseEnd_349449] using wordTrace_append hprefix tailTrace_349449
  have hstable : (prefixWord ++ tailWord_349449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349449).length < 2 ^ (prefixWord ++ tailWord_349449).sum := by decide
  have hdescent : baseEnd_349449 < baseStart_349449 := by decide
  rcases family_descends (prefixWord ++ tailWord_349449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349466 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_349466 : Nat := 118140960795 + 349466 * 2 ^ 59
def prefixEnd_349466 : Nat := 4983230072969 + 3 ^ 40 * 349466 * 2
def baseEnd_349466 : Nat := 179444030404234946367841

theorem tailTrace_349466 : CollatzResearch.WordTrace tailWord_349466 prefixEnd_349466 179444030404234946367841 := by
  unfold tailWord_349466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3186518037987960221555063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8497381434634560590813501 3186518037987960221555063)
  ·
    refine ⟨4779777056981940332332595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3186518037987960221555063 4779777056981940332332595)
    ·
      refine ⟨7169665585472910498498893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4779777056981940332332595 7169665585472910498498893)
      ·
        refine ⟨2688624594552341436937085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7169665585472910498498893 2688624594552341436937085)
        ·
          refine ⟨1008234222957128038851407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2688624594552341436937085 1008234222957128038851407)
          ·
            refine ⟨1512351334435692058277111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008234222957128038851407 1512351334435692058277111)
            ·
              refine ⟨2268527001653538087415667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512351334435692058277111 2268527001653538087415667)
              ·
                refine ⟨3402790502480307131123501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268527001653538087415667 3402790502480307131123501)
                ·
                  refine ⟨1276046438430115174171313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3402790502480307131123501 1276046438430115174171313)
                  ·
                    refine ⟨957034828822586380628485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1276046438430115174171313 957034828822586380628485)
                    ·
                      refine ⟨179444030404234946367841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 957034828822586380628485 179444030404234946367841)
                      ·
                        rfl

theorem cell23_349466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_349466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349466 prefixEnd_349466 := by exact prefixLift 349466
  have htrace : WordTrace (prefixWord ++ tailWord_349466) baseStart_349466 baseEnd_349466 := by
    simpa [prefixWord, tailWord_349466, baseEnd_349466] using wordTrace_append hprefix tailTrace_349466
  have hstable : (prefixWord ++ tailWord_349466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349466).length < 2 ^ (prefixWord ++ tailWord_349466).sum := by decide
  have hdescent : baseEnd_349466 < baseStart_349466 := by decide
  rcases family_descends (prefixWord ++ tailWord_349466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349480 : List Nat := [2, 1, 5, 1, 2, 2, 2, 2, 2, 4]
def baseStart_349480 : Nat := 118140960795 + 349480 * 2 ^ 59
def prefixEnd_349480 : Nat := 4983230072969 + 3 ^ 40 * 349480 * 2
def baseEnd_349480 : Nat := 59817073044465963864259

theorem tailTrace_349480 : CollatzResearch.WordTrace tailWord_349480 prefixEnd_349480 59817073044465963864259 := by
  unfold tailWord_349480
  simp only [CollatzResearch.WordTrace]
  refine ⟨6373291386950560638614947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8497721849267414184819929 6373291386950560638614947)
  ·
    refine ⟨9559937080425840957922421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6373291386950560638614947 9559937080425840957922421)
    ·
      refine ⟨896244101289922589805227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9559937080425840957922421 896244101289922589805227)
      ·
        refine ⟨1344366151934883884707841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896244101289922589805227 1344366151934883884707841)
        ·
          refine ⟨1008274613951162913530881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1344366151934883884707841 1008274613951162913530881)
          ·
            refine ⟨756205960463372185148161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1008274613951162913530881 756205960463372185148161)
            ·
              refine ⟨567154470347529138861121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756205960463372185148161 567154470347529138861121)
              ·
                refine ⟨425365852760646854145841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567154470347529138861121 425365852760646854145841)
                ·
                  refine ⟨319024389570485140609381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425365852760646854145841 319024389570485140609381)
                  ·
                    refine ⟨59817073044465963864259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 319024389570485140609381 59817073044465963864259)
                    ·
                      rfl

theorem cell23_349480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_349480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349480 prefixEnd_349480 := by exact prefixLift 349480
  have htrace : WordTrace (prefixWord ++ tailWord_349480) baseStart_349480 baseEnd_349480 := by
    simpa [prefixWord, tailWord_349480, baseEnd_349480] using wordTrace_append hprefix tailTrace_349480
  have hstable : (prefixWord ++ tailWord_349480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349480).length < 2 ^ (prefixWord ++ tailWord_349480).sum := by decide
  have hdescent : baseEnd_349480 < baseStart_349480 := by decide
  rcases family_descends (prefixWord ++ tailWord_349480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349503 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 3]
def baseStart_349503 : Nat := 118140960795 + 349503 * 2 ^ 59
def prefixEnd_349503 : Nat := 4983230072969 + 3 ^ 40 * 349503 * 2
def baseEnd_349503 : Nat := 179463029188451301605171

theorem tailTrace_349503 : CollatzResearch.WordTrace tailWord_349503 prefixEnd_349503 179463029188451301605171 := by
  unfold tailWord_349503
  simp only [CollatzResearch.WordTrace]
  refine ⟨12747421652817796205317163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8498281101878530803544775 12747421652817796205317163)
  ·
    refine ⟨19121132479226694307975745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12747421652817796205317163 19121132479226694307975745)
    ·
      refine ⟨14340849359420020730981809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19121132479226694307975745 14340849359420020730981809)
      ·
        refine ⟨10755637019565015548236357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14340849359420020730981809 10755637019565015548236357)
        ·
          refine ⟨2016681941168440415294317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10755637019565015548236357 2016681941168440415294317)
          ·
            refine ⟨756255727938165155735369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2016681941168440415294317 756255727938165155735369)
            ·
              refine ⟨567191795953623866801527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756255727938165155735369 567191795953623866801527)
              ·
                refine ⟨850787693930435800202291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567191795953623866801527 850787693930435800202291)
                ·
                  refine ⟨1276181540895653700303437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850787693930435800202291 1276181540895653700303437)
                  ·
                    refine ⟨478568077835870137613789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1276181540895653700303437 478568077835870137613789)
                    ·
                      refine ⟨179463029188451301605171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 478568077835870137613789 179463029188451301605171)
                      ·
                        rfl

theorem cell23_349503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_349503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349503 prefixEnd_349503 := by exact prefixLift 349503
  have htrace : WordTrace (prefixWord ++ tailWord_349503) baseStart_349503 baseEnd_349503 := by
    simpa [prefixWord, tailWord_349503, baseEnd_349503] using wordTrace_append hprefix tailTrace_349503
  have hstable : (prefixWord ++ tailWord_349503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349503).length < 2 ^ (prefixWord ++ tailWord_349503).sum := by decide
  have hdescent : baseEnd_349503 < baseStart_349503 := by decide
  rcases family_descends (prefixWord ++ tailWord_349503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349513 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 3, 3, 2]
def baseStart_349513 : Nat := 118140960795 + 349513 * 2 ^ 59
def prefixEnd_349513 : Nat := 4983230072969 + 3 ^ 40 * 349513 * 2
def baseEnd_349513 : Nat := 179468163994996262480125

theorem tailTrace_349513 : CollatzResearch.WordTrace tailWord_349513 prefixEnd_349513 179468163994996262480125 := by
  unfold tailWord_349513
  simp only [CollatzResearch.WordTrace]
  refine ⟨12747786382781567913181193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8498524255187711942120795 12747786382781567913181193)
  ·
    refine ⟨9560839787086175934885895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12747786382781567913181193 9560839787086175934885895)
    ·
      refine ⟨14341259680629263902328843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9560839787086175934885895 14341259680629263902328843)
      ·
        refine ⟨21511889520943895853493265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14341259680629263902328843 21511889520943895853493265)
        ·
          refine ⟨16133917140707921890119949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21511889520943895853493265 16133917140707921890119949)
          ·
            refine ⟨6050218927765470708794981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16133917140707921890119949 6050218927765470708794981)
            ·
              refine ⟨1134416048956025757899059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6050218927765470708794981 1134416048956025757899059)
              ·
                refine ⟨1701624073434038636848589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1134416048956025757899059 1701624073434038636848589)
                ·
                  refine ⟨638109027537764488818221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1701624073434038636848589 638109027537764488818221)
                  ·
                    refine ⟨239290885326661683306833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 638109027537764488818221 239290885326661683306833)
                    ·
                      refine ⟨179468163994996262480125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239290885326661683306833 179468163994996262480125)
                      ·
                        rfl

theorem cell23_349513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 3, 2].length) (baseStart_349513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349513 prefixEnd_349513 := by exact prefixLift 349513
  have htrace : WordTrace (prefixWord ++ tailWord_349513) baseStart_349513 baseEnd_349513 := by
    simpa [prefixWord, tailWord_349513, baseEnd_349513] using wordTrace_append hprefix tailTrace_349513
  have hstable : (prefixWord ++ tailWord_349513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349513).length < 2 ^ (prefixWord ++ tailWord_349513).sum := by decide
  have hdescent : baseEnd_349513 < baseStart_349513 := by decide
  rcases family_descends (prefixWord ++ tailWord_349513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349536 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 2, 6]
def baseStart_349536 : Nat := 118140960795 + 349536 * 2 ^ 59
def prefixEnd_349536 : Nat := 4983230072969 + 3 ^ 40 * 349536 * 2
def baseEnd_349536 : Nat := 59826658016683224164173

theorem tailTrace_349536 : CollatzResearch.WordTrace tailWord_349536 prefixEnd_349536 59826658016683224164173 := by
  unfold tailWord_349536
  simp only [CollatzResearch.WordTrace]
  refine ⟨6374312630849121420634231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8499083507798828560845641 6374312630849121420634231)
  ·
    refine ⟨9561468946273682130951347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6374312630849121420634231 9561468946273682130951347)
    ·
      refine ⟨14342203419410523196427021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9561468946273682130951347 14342203419410523196427021)
      ·
        refine ⟨5378326282278946198660133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14342203419410523196427021 5378326282278946198660133)
        ·
          refine ⟨1008436177927302412248775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5378326282278946198660133 1008436177927302412248775)
          ·
            refine ⟨1512654266890953618373163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008436177927302412248775 1512654266890953618373163)
            ·
              refine ⟨2268981400336430427559745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512654266890953618373163 2268981400336430427559745)
              ·
                refine ⟨1701736050252322820669809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2268981400336430427559745 1701736050252322820669809)
                ·
                  refine ⟨1276302037689242115502357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1701736050252322820669809 1276302037689242115502357)
                  ·
                    refine ⟨59826658016683224164173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1276302037689242115502357 59826658016683224164173)
                    ·
                      rfl

theorem cell23_349536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_349536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349536 prefixEnd_349536 := by exact prefixLift 349536
  have htrace : WordTrace (prefixWord ++ tailWord_349536) baseStart_349536 baseEnd_349536 := by
    simpa [prefixWord, tailWord_349536, baseEnd_349536] using wordTrace_append hprefix tailTrace_349536
  have hstable : (prefixWord ++ tailWord_349536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349536).length < 2 ^ (prefixWord ++ tailWord_349536).sum := by decide
  have hdescent : baseEnd_349536 < baseStart_349536 := by decide
  rcases family_descends (prefixWord ++ tailWord_349536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349600 : List Nat := [2, 1, 1, 4, 1, 2, 5, 2, 5]
def baseStart_349600 : Nat := 118140960795 + 349600 * 2 ^ 59
def prefixEnd_349600 : Nat := 4983230072969 + 3 ^ 40 * 349600 * 2
def baseEnd_349600 : Nat := 19945870756881935788025

theorem tailTrace_349600 : CollatzResearch.WordTrace tailWord_349600 prefixEnd_349600 19945870756881935788025 := by
  unfold tailWord_349600
  simp only [CollatzResearch.WordTrace]
  refine ⟨6375479766733190885799127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8500639688977587847732169 6375479766733190885799127)
  ·
    refine ⟨9563219650099786328698691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6375479766733190885799127 9563219650099786328698691)
    ·
      refine ⟨14344829475149679493048037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9563219650099786328698691 14344829475149679493048037)
      ·
        refine ⟨2689655526590564904946507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14344829475149679493048037 2689655526590564904946507)
        ·
          refine ⟨4034483289885847357419761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689655526590564904946507 4034483289885847357419761)
          ·
            refine ⟨3025862467414385518064821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4034483289885847357419761 3025862467414385518064821)
            ·
              refine ⟨283674606320098642318577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3025862467414385518064821 283674606320098642318577)
              ·
                refine ⟨212755954740073981738933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283674606320098642318577 212755954740073981738933)
                ·
                  refine ⟨19945870756881935788025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212755954740073981738933 19945870756881935788025)
                  ·
                    rfl

theorem cell23_349600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 5].length) (baseStart_349600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349600 prefixEnd_349600 := by exact prefixLift 349600
  have htrace : WordTrace (prefixWord ++ tailWord_349600) baseStart_349600 baseEnd_349600 := by
    simpa [prefixWord, tailWord_349600, baseEnd_349600] using wordTrace_append hprefix tailTrace_349600
  have hstable : (prefixWord ++ tailWord_349600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349600).length < 2 ^ (prefixWord ++ tailWord_349600).sum := by decide
  have hdescent : baseEnd_349600 < baseStart_349600 := by decide
  rcases family_descends (prefixWord ++ tailWord_349600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349603 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 2, 5, 2]
def baseStart_349603 : Nat := 118140960795 + 349603 * 2 ^ 59
def prefixEnd_349603 : Nat := 4983230072969 + 3 ^ 40 * 349603 * 2
def baseEnd_349603 : Nat := 179514377253900910354711

theorem tailTrace_349603 : CollatzResearch.WordTrace tailWord_349603 prefixEnd_349603 179514377253900910354711 := by
  unfold tailWord_349603
  simp only [CollatzResearch.WordTrace]
  refine ⟨12751068952455513283957463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8500712634970342189304975 12751068952455513283957463)
  ·
    refine ⟨19126603428683269925936195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12751068952455513283957463 19126603428683269925936195)
    ·
      refine ⟨28689905143024904888904293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19126603428683269925936195 28689905143024904888904293)
      ·
        refine ⟨5379357214317169666669555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28689905143024904888904293 5379357214317169666669555)
        ·
          refine ⟨8069035821475754500004333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5379357214317169666669555 8069035821475754500004333)
          ·
            refine ⟨3025888433053407937501625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8069035821475754500004333 3025888433053407937501625)
            ·
              refine ⟨2269416324790055953126219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3025888433053407937501625 2269416324790055953126219)
              ·
                refine ⟨3404124487185083929689329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269416324790055953126219 3404124487185083929689329)
                ·
                  refine ⟨2553093365388812947266997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3404124487185083929689329 2553093365388812947266997)
                  ·
                    refine ⟨239352503005201213806281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2553093365388812947266997 239352503005201213806281)
                    ·
                      refine ⟨179514377253900910354711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239352503005201213806281 179514377253900910354711)
                      ·
                        rfl

theorem cell23_349603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_349603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349603 prefixEnd_349603 := by exact prefixLift 349603
  have htrace : WordTrace (prefixWord ++ tailWord_349603) baseStart_349603 baseEnd_349603 := by
    simpa [prefixWord, tailWord_349603, baseEnd_349603] using wordTrace_append hprefix tailTrace_349603
  have hstable : (prefixWord ++ tailWord_349603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349603).length < 2 ^ (prefixWord ++ tailWord_349603).sum := by decide
  have hdescent : baseEnd_349603 < baseStart_349603 := by decide
  rcases family_descends (prefixWord ++ tailWord_349603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349616 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 4]
def baseStart_349616 : Nat := 118140960795 + 349616 * 2 ^ 59
def prefixEnd_349616 : Nat := 4983230072969 + 3 ^ 40 * 349616 * 2
def baseEnd_349616 : Nat := 179521052502409359492151

theorem tailTrace_349616 : CollatzResearch.WordTrace tailWord_349616 prefixEnd_349616 179521052502409359492151 := by
  unfold tailWord_349616
  simp only [CollatzResearch.WordTrace]
  refine ⟨6375771550704208252090351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8501028734272277669453801 6375771550704208252090351)
  ·
    refine ⟨9563657326056312378135527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6375771550704208252090351 9563657326056312378135527)
    ·
      refine ⟨14345485989084468567203291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9563657326056312378135527 14345485989084468567203291)
      ·
        refine ⟨21518228983626702850804937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14345485989084468567203291 21518228983626702850804937)
        ·
          refine ⟨16138671737720027138103703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21518228983626702850804937 16138671737720027138103703)
          ·
            refine ⟨24208007606580040707155555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16138671737720027138103703 24208007606580040707155555)
            ·
              refine ⟨36312011409870061060733333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24208007606580040707155555 36312011409870061060733333)
              ·
                refine ⟨1702125534837659112221875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36312011409870061060733333 1702125534837659112221875)
                ·
                  refine ⟨2553188302256488668332813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702125534837659112221875 2553188302256488668332813)
                  ·
                    refine ⟨957445613346183250624805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2553188302256488668332813 957445613346183250624805)
                    ·
                      refine ⟨179521052502409359492151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 957445613346183250624805 179521052502409359492151)
                      ·
                        rfl

theorem cell23_349616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_349616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349616 prefixEnd_349616 := by exact prefixLift 349616
  have htrace : WordTrace (prefixWord ++ tailWord_349616) baseStart_349616 baseEnd_349616 := by
    simpa [prefixWord, tailWord_349616, baseEnd_349616] using wordTrace_append hprefix tailTrace_349616
  have hstable : (prefixWord ++ tailWord_349616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349616).length < 2 ^ (prefixWord ++ tailWord_349616).sum := by decide
  have hdescent : baseEnd_349616 < baseStart_349616 := by decide
  rcases family_descends (prefixWord ++ tailWord_349616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349656 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 8]
def baseStart_349656 : Nat := 118140960795 + 349656 * 2 ^ 59
def prefixEnd_349656 : Nat := 4983230072969 + 3 ^ 40 * 349656 * 2
def baseEnd_349656 : Nat := 19949065747621022554663

theorem tailTrace_349656 : CollatzResearch.WordTrace tailWord_349656 prefixEnd_349656 19949065747621022554663 := by
  unfold tailWord_349656
  simp only [CollatzResearch.WordTrace]
  refine ⟨6376501010631751667818411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8502001347509002223757881 6376501010631751667818411)
  ·
    refine ⟨9564751515947627501727617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6376501010631751667818411 9564751515947627501727617)
    ·
      refine ⟨7173563636960720626295713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9564751515947627501727617 7173563636960720626295713)
      ·
        refine ⟨5380172727720540469721785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7173563636960720626295713 5380172727720540469721785)
        ·
          refine ⟨4035129545790405352291339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5380172727720540469721785 4035129545790405352291339)
          ·
            refine ⟨6052694318685608028437009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4035129545790405352291339 6052694318685608028437009)
            ·
              refine ⟨4539520739014206021327757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6052694318685608028437009 4539520739014206021327757)
              ·
                refine ⟨1702320277130327257997909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4539520739014206021327757 1702320277130327257997909)
                ·
                  refine ⟨19949065747621022554663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1702320277130327257997909 19949065747621022554663)
                  ·
                    rfl

theorem cell23_349656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 8].length) (baseStart_349656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349656 prefixEnd_349656 := by exact prefixLift 349656
  have htrace : WordTrace (prefixWord ++ tailWord_349656) baseStart_349656 baseEnd_349656 := by
    simpa [prefixWord, tailWord_349656, baseEnd_349656] using wordTrace_append hprefix tailTrace_349656
  have hstable : (prefixWord ++ tailWord_349656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349656).length < 2 ^ (prefixWord ++ tailWord_349656).sum := by decide
  have hdescent : baseEnd_349656 < baseStart_349656 := by decide
  rcases family_descends (prefixWord ++ tailWord_349656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349676 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_349676 : Nat := 118140960795 + 349676 * 2 ^ 59
def prefixEnd_349676 : Nat := 4983230072969 + 3 ^ 40 * 349676 * 2
def baseEnd_349676 : Nat := 179551861341679124741875

theorem tailTrace_349676 : CollatzResearch.WordTrace tailWord_349676 prefixEnd_349676 179551861341679124741875 := by
  unfold tailWord_349676
  simp only [CollatzResearch.WordTrace]
  refine ⟨6376865740595523375682441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8502487654127364500909921 6376865740595523375682441)
  ·
    refine ⟨4782649305446642531761831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6376865740595523375682441 4782649305446642531761831)
    ·
      refine ⟨7173973958169963797642747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4782649305446642531761831 7173973958169963797642747)
      ·
        refine ⟨10760960937254945696464121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7173973958169963797642747 10760960937254945696464121)
        ·
          refine ⟨8070720702941209272348091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10760960937254945696464121 8070720702941209272348091)
          ·
            refine ⟨12106081054411813908522137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8070720702941209272348091 12106081054411813908522137)
            ·
              refine ⟨9079560790808860431391603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12106081054411813908522137 9079560790808860431391603)
              ·
                refine ⟨13619341186213290647087405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9079560790808860431391603 13619341186213290647087405)
                ·
                  refine ⟨5107252944829983992657777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13619341186213290647087405 5107252944829983992657777)
                  ·
                    refine ⟨3830439708622487994493333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5107252944829983992657777 3830439708622487994493333)
                    ·
                      refine ⟨179551861341679124741875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3830439708622487994493333 179551861341679124741875)
                      ·
                        rfl

theorem cell23_349676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_349676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349676 prefixEnd_349676 := by exact prefixLift 349676
  have htrace : WordTrace (prefixWord ++ tailWord_349676) baseStart_349676 baseEnd_349676 := by
    simpa [prefixWord, tailWord_349676, baseEnd_349676] using wordTrace_append hprefix tailTrace_349676
  have hstable : (prefixWord ++ tailWord_349676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349676).length < 2 ^ (prefixWord ++ tailWord_349676).sum := by decide
  have hdescent : baseEnd_349676 < baseStart_349676 := by decide
  rcases family_descends (prefixWord ++ tailWord_349676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349677 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_349677 : Nat := 118140960795 + 349677 * 2 ^ 59
def prefixEnd_349677 : Nat := 4983230072969 + 3 ^ 40 * 349677 * 2
def baseEnd_349677 : Nat := 59850791607444540276457

theorem tailTrace_349677 : CollatzResearch.WordTrace tailWord_349677 prefixEnd_349677 59850791607444540276457 := by
  unfold tailWord_349677
  simp only [CollatzResearch.WordTrace]
  refine ⟨12753767954187423922151285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8502511969458282614767523 12753767954187423922151285)
  ·
    refine ⟨1195665745705070992701683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12753767954187423922151285 1195665745705070992701683)
    ·
      refine ⟨1793498618557606489052525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195665745705070992701683 1793498618557606489052525)
      ·
        refine ⟨672561981959102433394697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1793498618557606489052525 672561981959102433394697)
        ·
          refine ⟨504421486469326825046023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 672561981959102433394697 504421486469326825046023)
          ·
            refine ⟨756632229703990237569035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504421486469326825046023 756632229703990237569035)
            ·
              refine ⟨1134948344555985356353553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756632229703990237569035 1134948344555985356353553)
              ·
                refine ⟨851211258416989017265165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134948344555985356353553 851211258416989017265165)
                ·
                  refine ⟨319204221906370881474437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851211258416989017265165 319204221906370881474437)
                  ·
                    refine ⟨59850791607444540276457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 319204221906370881474437 59850791607444540276457)
                    ·
                      rfl

theorem cell23_349677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_349677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349677 prefixEnd_349677 := by exact prefixLift 349677
  have htrace : WordTrace (prefixWord ++ tailWord_349677) baseStart_349677 baseEnd_349677 := by
    simpa [prefixWord, tailWord_349677, baseEnd_349677] using wordTrace_append hprefix tailTrace_349677
  have hstable : (prefixWord ++ tailWord_349677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349677).length < 2 ^ (prefixWord ++ tailWord_349677).sum := by decide
  have hdescent : baseEnd_349677 < baseStart_349677 := by decide
  rcases family_descends (prefixWord ++ tailWord_349677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349707 : List Nat := [1, 1, 1, 1, 9, 1, 1, 2, 6]
def baseStart_349707 : Nat := 118140960795 + 349707 * 2 ^ 59
def prefixEnd_349707 : Nat := 4983230072969 + 3 ^ 40 * 349707 * 2
def baseEnd_349707 : Nat := 19951975471329833717137

theorem tailTrace_349707 : CollatzResearch.WordTrace tailWord_349707 prefixEnd_349707 19951975471329833717137 := by
  unfold tailWord_349707
  simp only [CollatzResearch.WordTrace]
  refine ⟨12754862144078739045743375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8503241429385826030495583 12754862144078739045743375)
  ·
    refine ⟨19132293216118108568615063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12754862144078739045743375 19132293216118108568615063)
    ·
      refine ⟨28698439824177162852922595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19132293216118108568615063 28698439824177162852922595)
      ·
        refine ⟨43047659736265744279383893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28698439824177162852922595 43047659736265744279383893)
        ·
          refine ⟨252232381267182095387015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 43047659736265744279383893 252232381267182095387015)
          ·
            refine ⟨378348571900773143080523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252232381267182095387015 378348571900773143080523)
            ·
              refine ⟨567522857851159714620785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378348571900773143080523 567522857851159714620785)
              ·
                refine ⟨425642143388369785965589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567522857851159714620785 425642143388369785965589)
                ·
                  refine ⟨19951975471329833717137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 425642143388369785965589 19951975471329833717137)
                  ·
                    rfl

theorem cell23_349707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 6].length) (baseStart_349707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349707 prefixEnd_349707 := by exact prefixLift 349707
  have htrace : WordTrace (prefixWord ++ tailWord_349707) baseStart_349707 baseEnd_349707 := by
    simpa [prefixWord, tailWord_349707, baseEnd_349707] using wordTrace_append hprefix tailTrace_349707
  have hstable : (prefixWord ++ tailWord_349707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349707).length < 2 ^ (prefixWord ++ tailWord_349707).sum := by decide
  have hdescent : baseEnd_349707 < baseStart_349707 := by decide
  rcases family_descends (prefixWord ++ tailWord_349707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349717 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_349717 : Nat := 118140960795 + 349717 * 2 ^ 59
def prefixEnd_349717 : Nat := 4983230072969 + 3 ^ 40 * 349717 * 2
def baseEnd_349717 : Nat := 179572914048513464329187

theorem tailTrace_349717 : CollatzResearch.WordTrace tailWord_349717 prefixEnd_349717 179572914048513464329187 := by
  unfold tailWord_349717
  simp only [CollatzResearch.WordTrace]
  refine ⟨12755226874042510753607405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8503484582695007169071603 12755226874042510753607405)
  ·
    refine ⟨4783210077765941532602777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12755226874042510753607405 4783210077765941532602777)
    ·
      refine ⟨3587407558324456149452083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4783210077765941532602777 3587407558324456149452083)
      ·
        refine ⟨5381111337486684224178125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3587407558324456149452083 5381111337486684224178125)
        ·
          refine ⟨2017916751557506584066797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5381111337486684224178125 2017916751557506584066797)
          ·
            refine ⟨756718781834064969025049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2017916751557506584066797 756718781834064969025049)
            ·
              refine ⟨567539086375548726768787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756718781834064969025049 567539086375548726768787)
              ·
                refine ⟨851308629563323090153181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567539086375548726768787 851308629563323090153181)
                ·
                  refine ⟨319240736086246158807443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851308629563323090153181 319240736086246158807443)
                  ·
                    refine ⟨478861104129369238211165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 319240736086246158807443 478861104129369238211165)
                    ·
                      refine ⟨179572914048513464329187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 478861104129369238211165 179572914048513464329187)
                      ·
                        rfl

theorem cell23_349717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_349717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349717 prefixEnd_349717 := by exact prefixLift 349717
  have htrace : WordTrace (prefixWord ++ tailWord_349717) baseStart_349717 baseEnd_349717 := by
    simpa [prefixWord, tailWord_349717, baseEnd_349717] using wordTrace_append hprefix tailTrace_349717
  have hstable : (prefixWord ++ tailWord_349717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349717).length < 2 ^ (prefixWord ++ tailWord_349717).sum := by decide
  have hdescent : baseEnd_349717 < baseStart_349717 := by decide
  rcases family_descends (prefixWord ++ tailWord_349717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349833 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 5]
def baseStart_349833 : Nat := 118140960795 + 349833 * 2 ^ 59
def prefixEnd_349833 : Nat := 4983230072969 + 3 ^ 40 * 349833 * 2
def baseEnd_349833 : Nat := 179632477804435010478653

theorem tailTrace_349833 : CollatzResearch.WordTrace tailWord_349833 prefixEnd_349833 179632477804435010478653 := by
  unfold tailWord_349833
  simp only [CollatzResearch.WordTrace]
  refine ⟨12759457741622262564830153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8506305161081508376553435 12759457741622262564830153)
  ·
    refine ⟨9569593306216696923622615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12759457741622262564830153 9569593306216696923622615)
    ·
      refine ⟨14354389959325045385433923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9569593306216696923622615 14354389959325045385433923)
      ·
        refine ⟨21531584938987568078150885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14354389959325045385433923 21531584938987568078150885)
        ·
          refine ⟨4037172176060169014653291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21531584938987568078150885 4037172176060169014653291)
          ·
            refine ⟨6055758264090253521979937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4037172176060169014653291 6055758264090253521979937)
            ·
              refine ⟨4541818698067690141484953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6055758264090253521979937 4541818698067690141484953)
              ·
                refine ⟨3406364023550767606113715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4541818698067690141484953 3406364023550767606113715)
                ·
                  refine ⟨5109546035326151409170573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406364023550767606113715 5109546035326151409170573)
                  ·
                    refine ⟨1916079763247306778438965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5109546035326151409170573 1916079763247306778438965)
                    ·
                      refine ⟨179632477804435010478653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1916079763247306778438965 179632477804435010478653)
                      ·
                        rfl

theorem cell23_349833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_349833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349833 prefixEnd_349833 := by exact prefixLift 349833
  have htrace : WordTrace (prefixWord ++ tailWord_349833) baseStart_349833 baseEnd_349833 := by
    simpa [prefixWord, tailWord_349833, baseEnd_349833] using wordTrace_append hprefix tailTrace_349833
  have hstable : (prefixWord ++ tailWord_349833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349833).length < 2 ^ (prefixWord ++ tailWord_349833).sum := by decide
  have hdescent : baseEnd_349833 < baseStart_349833 := by decide
  rcases family_descends (prefixWord ++ tailWord_349833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349847 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 1, 4, 2]
def baseStart_349847 : Nat := 118140960795 + 349847 * 2 ^ 59
def prefixEnd_349847 : Nat := 4983230072969 + 3 ^ 40 * 349847 * 2
def baseEnd_349847 : Nat := 179639666533597955703589

theorem tailTrace_349847 : CollatzResearch.WordTrace tailWord_349847 prefixEnd_349847 179639666533597955703589 := by
  unfold tailWord_349847
  simp only [CollatzResearch.WordTrace]
  refine ⟨12759968363571542955839795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8506645575714361970559863 12759968363571542955839795)
  ·
    refine ⟨19139952545357314433759693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12759968363571542955839795 19139952545357314433759693)
    ·
      refine ⟨7177482204508992912659885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19139952545357314433759693 7177482204508992912659885)
      ·
        refine ⟨2691555826690872342247457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7177482204508992912659885 2691555826690872342247457)
        ·
          refine ⟨2018666870018154256685593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2691555826690872342247457 2018666870018154256685593)
          ·
            refine ⟨1514000152513615692514195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2018666870018154256685593 1514000152513615692514195)
            ·
              refine ⟨2271000228770423538771293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514000152513615692514195 2271000228770423538771293)
              ·
                refine ⟨851625085788908827039235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2271000228770423538771293 851625085788908827039235)
                ·
                  refine ⟨1277437628683363240558853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 851625085788908827039235 1277437628683363240558853)
                  ·
                    refine ⟨239519555378130607604785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1277437628683363240558853 239519555378130607604785)
                    ·
                      refine ⟨179639666533597955703589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239519555378130607604785 179639666533597955703589)
                      ·
                        rfl

theorem cell23_349847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_349847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349847 prefixEnd_349847 := by exact prefixLift 349847
  have htrace : WordTrace (prefixWord ++ tailWord_349847) baseStart_349847 baseEnd_349847 := by
    simpa [prefixWord, tailWord_349847, baseEnd_349847] using wordTrace_append hprefix tailTrace_349847
  have hstable : (prefixWord ++ tailWord_349847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349847).length < 2 ^ (prefixWord ++ tailWord_349847).sum := by decide
  have hdescent : baseEnd_349847 < baseStart_349847 := by decide
  rcases family_descends (prefixWord ++ tailWord_349847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349898 : List Nat := [3, 1, 2, 1, 5, 1, 3, 1, 2, 2, 2]
def baseStart_349898 : Nat := 118140960795 + 349898 * 2 ^ 59
def prefixEnd_349898 : Nat := 4983230072969 + 3 ^ 40 * 349898 * 2
def baseEnd_349898 : Nat := 179665854046977256165855

theorem tailTrace_349898 : CollatzResearch.WordTrace tailWord_349898 prefixEnd_349898 179665854046977256165855 := by
  unfold tailWord_349898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190457121596694666486587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8507885657591185777297565 3190457121596694666486587)
  ·
    refine ⟨4785685682395041999729881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3190457121596694666486587 4785685682395041999729881)
    ·
      refine ⟨3589264261796281499797411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4785685682395041999729881 3589264261796281499797411)
      ·
        refine ⟨5383896392694422249696117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3589264261796281499797411 5383896392694422249696117)
        ·
          refine ⟨504740286815102085909011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5383896392694422249696117 504740286815102085909011)
          ·
            refine ⟨757110430222653128863517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504740286815102085909011 757110430222653128863517)
            ·
              refine ⟨283916411333494923323819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 757110430222653128863517 283916411333494923323819)
              ·
                refine ⟨425874617000242384985729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283916411333494923323819 425874617000242384985729)
                ·
                  refine ⟨319405962750181788739297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425874617000242384985729 319405962750181788739297)
                  ·
                    refine ⟨239554472062636341554473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 319405962750181788739297 239554472062636341554473)
                    ·
                      refine ⟨179665854046977256165855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239554472062636341554473 179665854046977256165855)
                      ·
                        rfl

theorem cell23_349898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_349898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349898 prefixEnd_349898 := by exact prefixLift 349898
  have htrace : WordTrace (prefixWord ++ tailWord_349898) baseStart_349898 baseEnd_349898 := by
    simpa [prefixWord, tailWord_349898, baseEnd_349898] using wordTrace_append hprefix tailTrace_349898
  have hstable : (prefixWord ++ tailWord_349898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349898).length < 2 ^ (prefixWord ++ tailWord_349898).sum := by decide
  have hdescent : baseEnd_349898 < baseStart_349898 := by decide
  rcases family_descends (prefixWord ++ tailWord_349898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349920 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 4]
def baseStart_349920 : Nat := 118140960795 + 349920 * 2 ^ 59
def prefixEnd_349920 : Nat := 4983230072969 + 3 ^ 40 * 349920 * 2
def baseEnd_349920 : Nat := 179677150621376170090753

theorem tailTrace_349920 : CollatzResearch.WordTrace tailWord_349920 prefixEnd_349920 179677150621376170090753 := by
  unfold tailWord_349920
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381315446153538211623607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8508420594871384282164809 6381315446153538211623607)
  ·
    refine ⟨9571973169230307317435411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6381315446153538211623607 9571973169230307317435411)
    ·
      refine ⟨14357959753845460976153117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9571973169230307317435411 14357959753845460976153117)
      ·
        refine ⟨5384234907692047866057419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14357959753845460976153117 5384234907692047866057419)
        ·
          refine ⟨8076352361538071799086129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5384234907692047866057419 8076352361538071799086129)
          ·
            refine ⟨6057264271153553849314597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8076352361538071799086129 6057264271153553849314597)
            ·
              refine ⟨1135737050841291346746487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6057264271153553849314597 1135737050841291346746487)
              ·
                refine ⟨1703605576261937020119731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135737050841291346746487 1703605576261937020119731)
                ·
                  refine ⟨2555408364392905530179597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703605576261937020119731 2555408364392905530179597)
                  ·
                    refine ⟨958278136647339573817349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2555408364392905530179597 958278136647339573817349)
                    ·
                      refine ⟨179677150621376170090753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 958278136647339573817349 179677150621376170090753)
                      ·
                        rfl

theorem cell23_349920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_349920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349920 prefixEnd_349920 := by exact prefixLift 349920
  have htrace : WordTrace (prefixWord ++ tailWord_349920) baseStart_349920 baseEnd_349920 := by
    simpa [prefixWord, tailWord_349920, baseEnd_349920] using wordTrace_append hprefix tailTrace_349920
  have hstable : (prefixWord ++ tailWord_349920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349920).length < 2 ^ (prefixWord ++ tailWord_349920).sum := by decide
  have hdescent : baseEnd_349920 < baseStart_349920 := by decide
  rcases family_descends (prefixWord ++ tailWord_349920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349921 : List Nat := [1, 2, 3, 1, 6, 1, 1, 3, 5]
def baseStart_349921 : Nat := 118140960795 + 349921 * 2 ^ 59
def prefixEnd_349921 : Nat := 4983230072969 + 3 ^ 40 * 349921 * 2
def baseEnd_349921 : Nat := 19964184900225629575361

theorem tailTrace_349921 : CollatzResearch.WordTrace tailWord_349921 prefixEnd_349921 19964184900225629575361 := by
  unfold tailWord_349921
  simp only [CollatzResearch.WordTrace]
  refine ⟨12762667365303453594033617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8508444910202302396022411 12762667365303453594033617)
  ·
    refine ⟨9572000523977590195525213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12762667365303453594033617 9572000523977590195525213)
    ·
      refine ⟨3589500196491596323321955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9572000523977590195525213 3589500196491596323321955)
      ·
        refine ⟨5384250294737394484982933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3589500196491596323321955 5384250294737394484982933)
        ·
          refine ⟨252386732565815366483575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5384250294737394484982933 252386732565815366483575)
          ·
            refine ⟨378580098848723049725363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252386732565815366483575 378580098848723049725363)
            ·
              refine ⟨567870148273084574588045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378580098848723049725363 567870148273084574588045)
              ·
                refine ⟨212951305602406715470517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 567870148273084574588045 212951305602406715470517)
                ·
                  refine ⟨19964184900225629575361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212951305602406715470517 19964184900225629575361)
                  ·
                    rfl

theorem cell23_349921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 5].length) (baseStart_349921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349921 prefixEnd_349921 := by exact prefixLift 349921
  have htrace : WordTrace (prefixWord ++ tailWord_349921) baseStart_349921 baseEnd_349921 := by
    simpa [prefixWord, tailWord_349921, baseEnd_349921] using wordTrace_append hprefix tailTrace_349921
  have hstable : (prefixWord ++ tailWord_349921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349921).length < 2 ^ (prefixWord ++ tailWord_349921).sum := by decide
  have hdescent : baseEnd_349921 < baseStart_349921 := by decide
  rcases family_descends (prefixWord ++ tailWord_349921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349937 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_349937 : Nat := 118140960795 + 349937 * 2 ^ 59
def prefixEnd_349937 : Nat := 4983230072969 + 3 ^ 40 * 349937 * 2
def baseEnd_349937 : Nat := 179685879792502603578175

theorem tailTrace_349937 : CollatzResearch.WordTrace tailWord_349937 prefixEnd_349937 179685879792502603578175 := by
  unfold tailWord_349937
  simp only [CollatzResearch.WordTrace]
  refine ⟨12763250933245488326616065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8508833955496992217744043 12763250933245488326616065)
  ·
    refine ⟨9572438199934116244962049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12763250933245488326616065 9572438199934116244962049)
    ·
      refine ⟨7179328649950587183721537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9572438199934116244962049 7179328649950587183721537)
      ·
        refine ⟨5384496487462940387791153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7179328649950587183721537 5384496487462940387791153)
        ·
          refine ⟨4038372365597205290843365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5384496487462940387791153 4038372365597205290843365)
          ·
            refine ⟨757194818549475992033131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4038372365597205290843365 757194818549475992033131)
            ·
              refine ⟨1135792227824213988049697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757194818549475992033131 1135792227824213988049697)
              ·
                refine ⟨851844170868160491037273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1135792227824213988049697 851844170868160491037273)
                ·
                  refine ⟨638883128151120368277955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 851844170868160491037273 638883128151120368277955)
                  ·
                    refine ⟨958324692226680552416933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 638883128151120368277955 958324692226680552416933)
                    ·
                      refine ⟨179685879792502603578175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 958324692226680552416933 179685879792502603578175)
                      ·
                        rfl

theorem cell23_349937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_349937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349937 prefixEnd_349937 := by exact prefixLift 349937
  have htrace : WordTrace (prefixWord ++ tailWord_349937) baseStart_349937 baseEnd_349937 := by
    simpa [prefixWord, tailWord_349937, baseEnd_349937] using wordTrace_append hprefix tailTrace_349937
  have hstable : (prefixWord ++ tailWord_349937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349937).length < 2 ^ (prefixWord ++ tailWord_349937).sum := by decide
  have hdescent : baseEnd_349937 < baseStart_349937 := by decide
  rcases family_descends (prefixWord ++ tailWord_349937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349954 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_349954 : Nat := 118140960795 + 349954 * 2 ^ 59
def prefixEnd_349954 : Nat := 4983230072969 + 3 ^ 40 * 349954 * 2
def baseEnd_349954 : Nat := 179694608963629037065597

theorem tailTrace_349954 : CollatzResearch.WordTrace tailWord_349954 prefixEnd_349954 179694608963629037065597 := by
  unfold tailWord_349954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190967743545975057496229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8509247316122600153323277 3190967743545975057496229)
  ·
    refine ⟨598306451914870323280543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3190967743545975057496229 598306451914870323280543)
    ·
      refine ⟨897459677872305484920815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 598306451914870323280543 897459677872305484920815)
      ·
        refine ⟨1346189516808458227381223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897459677872305484920815 1346189516808458227381223)
        ·
          refine ⟨2019284275212687341071835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346189516808458227381223 2019284275212687341071835)
          ·
            refine ⟨3028926412819031011607753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019284275212687341071835 3028926412819031011607753)
            ·
              refine ⟨2271694809614273258705815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3028926412819031011607753 2271694809614273258705815)
              ·
                refine ⟨3407542214421409888058723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271694809614273258705815 3407542214421409888058723)
                ·
                  refine ⟨5111313321632114832088085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407542214421409888058723 5111313321632114832088085)
                  ·
                    refine ⟨239592811951505382754129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5111313321632114832088085 239592811951505382754129)
                    ·
                      refine ⟨179694608963629037065597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239592811951505382754129 179694608963629037065597)
                      ·
                        rfl

theorem cell23_349954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_349954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349954 prefixEnd_349954 := by exact prefixLift 349954
  have htrace : WordTrace (prefixWord ++ tailWord_349954) baseStart_349954 baseEnd_349954 := by
    simpa [prefixWord, tailWord_349954, baseEnd_349954] using wordTrace_append hprefix tailTrace_349954
  have hstable : (prefixWord ++ tailWord_349954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349954).length < 2 ^ (prefixWord ++ tailWord_349954).sum := by decide
  have hdescent : baseEnd_349954 < baseStart_349954 := by decide
  rcases family_descends (prefixWord ++ tailWord_349954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349998 : List Nat := [4, 1, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_349998 : Nat := 118140960795 + 349998 * 2 ^ 59
def prefixEnd_349998 : Nat := 4983230072969 + 3 ^ 40 * 349998 * 2
def baseEnd_349998 : Nat := 59905734037475621638465

theorem tailTrace_349998 : CollatzResearch.WordTrace tailWord_349998 prefixEnd_349998 59905734037475621638465 := by
  unfold tailWord_349998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595684473253061968073331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8510317190682997163057765 1595684473253061968073331)
  ·
    refine ⟨2393526709879592952109997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1595684473253061968073331 2393526709879592952109997)
    ·
      refine ⟨897572516204847357041249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2393526709879592952109997 897572516204847357041249)
      ·
        refine ⟨673179387153635517780937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 897572516204847357041249 673179387153635517780937)
        ·
          refine ⟨504884540365226638335703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 673179387153635517780937 504884540365226638335703)
          ·
            refine ⟨757326810547839957503555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504884540365226638335703 757326810547839957503555)
            ·
              refine ⟨1135990215821759936255333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757326810547839957503555 1135990215821759936255333)
              ·
                refine ⟨212998165466579988047875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1135990215821759936255333 212998165466579988047875)
                ·
                  refine ⟨319497248199869982071813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212998165466579988047875 319497248199869982071813)
                  ·
                    refine ⟨59905734037475621638465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 319497248199869982071813 59905734037475621638465)
                    ·
                      rfl

theorem cell23_349998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_349998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_349998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_349998 prefixEnd_349998 := by exact prefixLift 349998
  have htrace : WordTrace (prefixWord ++ tailWord_349998) baseStart_349998 baseEnd_349998 := by
    simpa [prefixWord, tailWord_349998, baseEnd_349998] using wordTrace_append hprefix tailTrace_349998
  have hstable : (prefixWord ++ tailWord_349998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349998).length < 2 ^ (prefixWord ++ tailWord_349998).sum := by decide
  have hdescent : baseEnd_349998 < baseStart_349998 := by decide
  rcases family_descends (prefixWord ++ tailWord_349998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350037 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 1, 6]
def baseStart_350037 : Nat := 118140960795 + 350037 * 2 ^ 59
def prefixEnd_350037 : Nat := 4983230072969 + 3 ^ 40 * 350037 * 2
def baseEnd_350037 : Nat := 59912409285984070775905

theorem tailTrace_350037 : CollatzResearch.WordTrace tailWord_350037 prefixEnd_350037 59912409285984070775905 := by
  unfold tailWord_350037
  simp only [CollatzResearch.WordTrace]
  refine ⟨12766898232883205405256365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8511265488588803603504243 12766898232883205405256365)
  ·
    refine ⟨4787586837331202026971137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12766898232883205405256365 4787586837331202026971137)
    ·
      refine ⟨3590690127998401520228353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4787586837331202026971137 3590690127998401520228353)
      ·
        refine ⟨2693017595998801140171265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3590690127998401520228353 2693017595998801140171265)
        ·
          refine ⟨2019763196999100855128449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2693017595998801140171265 2019763196999100855128449)
          ·
            refine ⟨1514822397749325641346337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2019763196999100855128449 1514822397749325641346337)
            ·
              refine ⟨1136116798311994231009753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1514822397749325641346337 1136116798311994231009753)
              ·
                refine ⟨852087598733995673257315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1136116798311994231009753 852087598733995673257315)
                ·
                  refine ⟨1278131398100993509885973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852087598733995673257315 1278131398100993509885973)
                  ·
                    refine ⟨59912409285984070775905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1278131398100993509885973 59912409285984070775905)
                    ·
                      rfl

theorem cell23_350037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_350037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350037 prefixEnd_350037 := by exact prefixLift 350037
  have htrace : WordTrace (prefixWord ++ tailWord_350037) baseStart_350037 baseEnd_350037 := by
    simpa [prefixWord, tailWord_350037, baseEnd_350037] using wordTrace_append hprefix tailTrace_350037
  have hstable : (prefixWord ++ tailWord_350037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350037).length < 2 ^ (prefixWord ++ tailWord_350037).sum := by decide
  have hdescent : baseEnd_350037 < baseStart_350037 := by decide
  rcases family_descends (prefixWord ++ tailWord_350037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350040 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_350040 : Nat := 118140960795 + 350040 * 2 ^ 59
def prefixEnd_350040 : Nat := 4983230072969 + 3 ^ 40 * 350040 * 2
def baseEnd_350040 : Nat := 179738768299915700590201

theorem tailTrace_350040 : CollatzResearch.WordTrace tailWord_350040 prefixEnd_350040 179738768299915700590201 := by
  unfold tailWord_350040
  simp only [CollatzResearch.WordTrace]
  refine ⟨6383503825936168458807787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8511338434581557945077049 6383503825936168458807787)
  ·
    refine ⟨9575255738904252688211681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6383503825936168458807787 9575255738904252688211681)
    ·
      refine ⟨7181441804178189516158761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9575255738904252688211681 7181441804178189516158761)
      ·
        refine ⟨5386081353133642137119071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7181441804178189516158761 5386081353133642137119071)
        ·
          refine ⟨8079122029700463205678607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386081353133642137119071 8079122029700463205678607)
          ·
            refine ⟨12118683044550694808517911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8079122029700463205678607 12118683044550694808517911)
            ·
              refine ⟨18178024566826042212776867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12118683044550694808517911 18178024566826042212776867)
              ·
                refine ⟨27267036850239063319165301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18178024566826042212776867 27267036850239063319165301)
                ·
                  refine ⟨2556284704709912186171747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27267036850239063319165301 2556284704709912186171747)
                  ·
                    refine ⟨3834427057064868279257621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2556284704709912186171747 3834427057064868279257621)
                    ·
                      refine ⟨179738768299915700590201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3834427057064868279257621 179738768299915700590201)
                      ·
                        rfl

theorem cell23_350040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_350040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350040 prefixEnd_350040 := by exact prefixLift 350040
  have htrace : WordTrace (prefixWord ++ tailWord_350040) baseStart_350040 baseEnd_350040 := by
    simpa [prefixWord, tailWord_350040, baseEnd_350040] using wordTrace_append hprefix tailTrace_350040
  have hstable : (prefixWord ++ tailWord_350040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350040).length < 2 ^ (prefixWord ++ tailWord_350040).sum := by decide
  have hdescent : baseEnd_350040 < baseStart_350040 := by decide
  rcases family_descends (prefixWord ++ tailWord_350040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350061 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_350061 : Nat := 118140960795 + 350061 * 2 ^ 59
def prefixEnd_350061 : Nat := 4983230072969 + 3 ^ 40 * 350061 * 2
def baseEnd_350061 : Nat := 179749551393660118427605

theorem tailTrace_350061 : CollatzResearch.WordTrace tailWord_350061 prefixEnd_350061 179749551393660118427605 := by
  unfold tailWord_350061
  simp only [CollatzResearch.WordTrace]
  refine ⟨12767773584796257504130037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8511849056530838336086691 12767773584796257504130037)
  ·
    refine ⟨1196978773574649141012191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12767773584796257504130037 1196978773574649141012191)
    ·
      refine ⟨1795468160361973711518287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196978773574649141012191 1795468160361973711518287)
      ·
        refine ⟨2693202240542960567277431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795468160361973711518287 2693202240542960567277431)
        ·
          refine ⟨4039803360814440850916147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2693202240542960567277431 4039803360814440850916147)
          ·
            refine ⟨6059705041221661276374221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039803360814440850916147 6059705041221661276374221)
            ·
              refine ⟨2272389390458122978640333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6059705041221661276374221 2272389390458122978640333)
              ·
                refine ⟨852146021421796116990125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2272389390458122978640333 852146021421796116990125)
                ·
                  refine ⟨319554758033173543871297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 852146021421796116990125 319554758033173543871297)
                  ·
                    refine ⟨239666068524880157903473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 319554758033173543871297 239666068524880157903473)
                    ·
                      refine ⟨179749551393660118427605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239666068524880157903473 179749551393660118427605)
                      ·
                        rfl

theorem cell23_350061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_350061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350061 prefixEnd_350061 := by exact prefixLift 350061
  have htrace : WordTrace (prefixWord ++ tailWord_350061) baseStart_350061 baseEnd_350061 := by
    simpa [prefixWord, tailWord_350061, baseEnd_350061] using wordTrace_append hprefix tailTrace_350061
  have hstable : (prefixWord ++ tailWord_350061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350061).length < 2 ^ (prefixWord ++ tailWord_350061).sum := by decide
  have hdescent : baseEnd_350061 < baseStart_350061 := by decide
  rcases family_descends (prefixWord ++ tailWord_350061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350078 : List Nat := [4, 2, 3, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_350078 : Nat := 118140960795 + 350078 * 2 ^ 59
def prefixEnd_350078 : Nat := 4983230072969 + 3 ^ 40 * 350078 * 2
def baseEnd_350078 : Nat := 179758280564786551915027

theorem tailTrace_350078 : CollatzResearch.WordTrace tailWord_350078 prefixEnd_350078 179758280564786551915027 := by
  unfold tailWord_350078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1596049203216833675937361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8512262417156446271665925 1596049203216833675937361)
  ·
    refine ⟨1197036902412625256953021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1596049203216833675937361 1197036902412625256953021)
    ·
      refine ⟨448888838404734471357383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1197036902412625256953021 448888838404734471357383)
      ·
        refine ⟨673333257607101707036075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448888838404734471357383 673333257607101707036075)
        ·
          refine ⟨1009999886410652560554113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673333257607101707036075 1009999886410652560554113)
          ·
            refine ⟨757499914807989420415585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1009999886410652560554113 757499914807989420415585)
            ·
              refine ⟨568124936105992065311689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757499914807989420415585 568124936105992065311689)
              ·
                refine ⟨426093702079494048983767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568124936105992065311689 426093702079494048983767)
                ·
                  refine ⟨639140553119241073475651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426093702079494048983767 639140553119241073475651)
                  ·
                    refine ⟨958710829678861610213477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 639140553119241073475651 958710829678861610213477)
                    ·
                      refine ⟨179758280564786551915027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 958710829678861610213477 179758280564786551915027)
                      ·
                        rfl

theorem cell23_350078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_350078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350078 prefixEnd_350078 := by exact prefixLift 350078
  have htrace : WordTrace (prefixWord ++ tailWord_350078) baseStart_350078 baseEnd_350078 := by
    simpa [prefixWord, tailWord_350078, baseEnd_350078] using wordTrace_append hprefix tailTrace_350078
  have hstable : (prefixWord ++ tailWord_350078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350078).length < 2 ^ (prefixWord ++ tailWord_350078).sum := by decide
  have hdescent : baseEnd_350078 < baseStart_350078 := by decide
  rcases family_descends (prefixWord ++ tailWord_350078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350132 : List Nat := [2, 5, 2, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_350132 : Nat := 118140960795 + 350132 * 2 ^ 59
def prefixEnd_350132 : Nat := 4983230072969 + 3 ^ 40 * 350132 * 2
def baseEnd_350132 : Nat := 179786008520129340639779

theorem tailTrace_350132 : CollatzResearch.WordTrace tailWord_350132 prefixEnd_350132 179786008520129340639779 := by
  unfold tailWord_350132
  simp only [CollatzResearch.WordTrace]
  refine ⟨6385181583769518314982325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8513575445026024419976433 6385181583769518314982325)
  ·
    refine ⟨598610773478392342029593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6385181583769518314982325 598610773478392342029593)
    ·
      refine ⟨448958080108794256522195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 598610773478392342029593 448958080108794256522195)
      ·
        refine ⟨673437120163191384783293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448958080108794256522195 673437120163191384783293)
        ·
          refine ⟨252538920061196769293735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 673437120163191384783293 252538920061196769293735)
          ·
            refine ⟨378808380091795153940603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252538920061196769293735 378808380091795153940603)
            ·
              refine ⟨568212570137692730910905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378808380091795153940603 568212570137692730910905)
              ·
                refine ⟨426159427603269548183179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568212570137692730910905 426159427603269548183179)
                ·
                  refine ⟨639239141404904322274769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426159427603269548183179 639239141404904322274769)
                  ·
                    refine ⟨479429356053678241706077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 639239141404904322274769 479429356053678241706077)
                    ·
                      refine ⟨179786008520129340639779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 479429356053678241706077 179786008520129340639779)
                      ·
                        rfl

theorem cell23_350132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_350132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350132 prefixEnd_350132 := by exact prefixLift 350132
  have htrace : WordTrace (prefixWord ++ tailWord_350132) baseStart_350132 baseEnd_350132 := by
    simpa [prefixWord, tailWord_350132, baseEnd_350132] using wordTrace_append hprefix tailTrace_350132
  have hstable : (prefixWord ++ tailWord_350132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350132).length < 2 ^ (prefixWord ++ tailWord_350132).sum := by decide
  have hdescent : baseEnd_350132 < baseStart_350132 := by decide
  rcases family_descends (prefixWord ++ tailWord_350132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350137 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 5]
def baseStart_350137 : Nat := 118140960795 + 350137 * 2 ^ 59
def prefixEnd_350137 : Nat := 4983230072969 + 3 ^ 40 * 350137 * 2
def baseEnd_350137 : Nat := 179788575923401821077255

theorem tailTrace_350137 : CollatzResearch.WordTrace tailWord_350137 prefixEnd_350137 179788575923401821077255 := by
  unfold tailWord_350137
  simp only [CollatzResearch.WordTrace]
  refine ⟨12770545532520922483896665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8513697021680614989264443 12770545532520922483896665)
  ·
    refine ⟨9577909149390691862922499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12770545532520922483896665 9577909149390691862922499)
    ·
      refine ⟨14366863724086037794383749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9577909149390691862922499 14366863724086037794383749)
      ·
        refine ⟨2693786948266132086446953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14366863724086037794383749 2693786948266132086446953)
        ·
          refine ⟨2020340211199599064835215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2693786948266132086446953 2020340211199599064835215)
          ·
            refine ⟨3030510316799398597252823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020340211199599064835215 3030510316799398597252823)
            ·
              refine ⟨4545765475199097895879235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3030510316799398597252823 4545765475199097895879235)
              ·
                refine ⟨6818648212798646843818853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4545765475199097895879235 6818648212798646843818853)
                ·
                  refine ⟨1278496539899746283216035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6818648212798646843818853 1278496539899746283216035)
                  ·
                    refine ⟨1917744809849619424824053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1278496539899746283216035 1917744809849619424824053)
                    ·
                      refine ⟨179788575923401821077255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1917744809849619424824053 179788575923401821077255)
                      ·
                        rfl

theorem cell23_350137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_350137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350137 prefixEnd_350137 := by exact prefixLift 350137
  have htrace : WordTrace (prefixWord ++ tailWord_350137) baseStart_350137 baseEnd_350137 := by
    simpa [prefixWord, tailWord_350137, baseEnd_350137] using wordTrace_append hprefix tailTrace_350137
  have hstable : (prefixWord ++ tailWord_350137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350137).length < 2 ^ (prefixWord ++ tailWord_350137).sum := by decide
  have hdescent : baseEnd_350137 < baseStart_350137 := by decide
  rcases family_descends (prefixWord ++ tailWord_350137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350164 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_350164 : Nat := 118140960795 + 350164 * 2 ^ 59
def prefixEnd_350164 : Nat := 4983230072969 + 3 ^ 40 * 350164 * 2
def baseEnd_350164 : Nat := 179802439901073215439631

theorem tailTrace_350164 : CollatzResearch.WordTrace tailWord_350164 prefixEnd_350164 179802439901073215439631 := by
  unfold tailWord_350164
  simp only [CollatzResearch.WordTrace]
  refine ⟨6385765151711553047564773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8514353535615404063419697 6385765151711553047564773)
  ·
    refine ⟨1197330965945916196418395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6385765151711553047564773 1197330965945916196418395)
    ·
      refine ⟨1795996448918874294627593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197330965945916196418395 1795996448918874294627593)
      ·
        refine ⟨1346997336689155720970695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1795996448918874294627593 1346997336689155720970695)
        ·
          refine ⟨2020496005033733581456043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346997336689155720970695 2020496005033733581456043)
          ·
            refine ⟨3030744007550600372184065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020496005033733581456043 3030744007550600372184065)
            ·
              refine ⟨2273058005662950279138049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3030744007550600372184065 2273058005662950279138049)
              ·
                refine ⟨1704793504247212709353537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2273058005662950279138049 1704793504247212709353537)
                ·
                  refine ⟨1278595128185409532015153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1704793504247212709353537 1278595128185409532015153)
                  ·
                    refine ⟨958946346139057149011365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1278595128185409532015153 958946346139057149011365)
                    ·
                      refine ⟨179802439901073215439631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 958946346139057149011365 179802439901073215439631)
                      ·
                        rfl

theorem cell23_350164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_350164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350164 prefixEnd_350164 := by exact prefixLift 350164
  have htrace : WordTrace (prefixWord ++ tailWord_350164) baseStart_350164 baseEnd_350164 := by
    simpa [prefixWord, tailWord_350164, baseEnd_350164] using wordTrace_append hprefix tailTrace_350164
  have hstable : (prefixWord ++ tailWord_350164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350164).length < 2 ^ (prefixWord ++ tailWord_350164).sum := by decide
  have hdescent : baseEnd_350164 < baseStart_350164 := by decide
  rcases family_descends (prefixWord ++ tailWord_350164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350168 : List Nat := [2, 1, 2, 2, 2, 2, 4, 2, 2, 2, 2]
def baseStart_350168 : Nat := 118140960795 + 350168 * 2 ^ 59
def prefixEnd_350168 : Nat := 4983230072969 + 3 ^ 40 * 350168 * 2
def baseEnd_350168 : Nat := 179804493823691199789613

theorem tailTrace_350168 : CollatzResearch.WordTrace tailWord_350168 prefixEnd_350168 179804493823691199789613 := by
  unfold tailWord_350168
  simp only [CollatzResearch.WordTrace]
  refine ⟨6385838097704307389137579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8514450796939076518850105 6385838097704307389137579)
  ·
    refine ⟨9578757146556461083706369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6385838097704307389137579 9578757146556461083706369)
    ·
      refine ⟨7184067859917345812779777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9578757146556461083706369 7184067859917345812779777)
      ·
        refine ⟨5388050894938009359584833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7184067859917345812779777 5388050894938009359584833)
        ·
          refine ⟨4041038171203507019688625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5388050894938009359584833 4041038171203507019688625)
          ·
            refine ⟨3030778628402630264766469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4041038171203507019688625 3030778628402630264766469)
            ·
              refine ⟨568270992825493174643713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3030778628402630264766469 568270992825493174643713)
              ·
                refine ⟨426203244619119880982785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568270992825493174643713 426203244619119880982785)
                ·
                  refine ⟨319652433464339910737089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426203244619119880982785 319652433464339910737089)
                  ·
                    refine ⟨239739325098254933052817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 319652433464339910737089 239739325098254933052817)
                    ·
                      refine ⟨179804493823691199789613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239739325098254933052817 179804493823691199789613)
                      ·
                        rfl

theorem cell23_350168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_350168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350168 prefixEnd_350168 := by exact prefixLift 350168
  have htrace : WordTrace (prefixWord ++ tailWord_350168) baseStart_350168 baseEnd_350168 := by
    simpa [prefixWord, tailWord_350168, baseEnd_350168] using wordTrace_append hprefix tailTrace_350168
  have hstable : (prefixWord ++ tailWord_350168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350168).length < 2 ^ (prefixWord ++ tailWord_350168).sum := by decide
  have hdescent : baseEnd_350168 < baseStart_350168 := by decide
  rcases family_descends (prefixWord ++ tailWord_350168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350187 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 4, 5]
def baseStart_350187 : Nat := 118140960795 + 350187 * 2 ^ 59
def prefixEnd_350187 : Nat := 4983230072969 + 3 ^ 40 * 350187 * 2
def baseEnd_350187 : Nat := 59938083318708875150675

theorem tailTrace_350187 : CollatzResearch.WordTrace tailWord_350187 prefixEnd_350187 59938083318708875150675 := by
  unfold tailWord_350187
  simp only [CollatzResearch.WordTrace]
  refine ⟨12772369182339781023216815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8514912788226520682144543 12772369182339781023216815)
  ·
    refine ⟨19158553773509671534825223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12772369182339781023216815 19158553773509671534825223)
    ·
      refine ⟨28737830660264507302237835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19158553773509671534825223 28737830660264507302237835)
      ·
        refine ⟨43106745990396760953356753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28737830660264507302237835 43106745990396760953356753)
        ·
          refine ⟨32330059492797570715017565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43106745990396760953356753 32330059492797570715017565)
          ·
            refine ⟨12123772309799089018131587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32330059492797570715017565 12123772309799089018131587)
            ·
              refine ⟨18185658464698633527197381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12123772309799089018131587 18185658464698633527197381)
              ·
                refine ⟨3409810962130993786349509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18185658464698633527197381 3409810962130993786349509)
                ·
                  refine ⟨639339555399561334940533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3409810962130993786349509 639339555399561334940533)
                  ·
                    refine ⟨59938083318708875150675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 639339555399561334940533 59938083318708875150675)
                    ·
                      rfl

theorem cell23_350187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 5].length) (baseStart_350187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350187 prefixEnd_350187 := by exact prefixLift 350187
  have htrace : WordTrace (prefixWord ++ tailWord_350187) baseStart_350187 baseEnd_350187 := by
    simpa [prefixWord, tailWord_350187, baseEnd_350187] using wordTrace_append hprefix tailTrace_350187
  have hstable : (prefixWord ++ tailWord_350187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350187).length < 2 ^ (prefixWord ++ tailWord_350187).sum := by decide
  have hdescent : baseEnd_350187 < baseStart_350187 := by decide
  rcases family_descends (prefixWord ++ tailWord_350187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350224 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 3, 6, 2]
def baseStart_350224 : Nat := 118140960795 + 350224 * 2 ^ 59
def prefixEnd_350224 : Nat := 4983230072969 + 3 ^ 40 * 350224 * 2
def baseEnd_350224 : Nat := 179833248740342980689355

theorem tailTrace_350224 : CollatzResearch.WordTrace tailWord_350224 prefixEnd_350224 179833248740342980689355 := by
  unfold tailWord_350224
  simp only [CollatzResearch.WordTrace]
  refine ⟨6386859341602868171156863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8515812455470490894875817 6386859341602868171156863)
  ·
    refine ⟨9580289012404302256735295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6386859341602868171156863 9580289012404302256735295)
    ·
      refine ⟨14370433518606453385102943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9580289012404302256735295 14370433518606453385102943)
      ·
        refine ⟨21555650277909680077654415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14370433518606453385102943 21555650277909680077654415)
        ·
          refine ⟨32333475416864520116481623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21555650277909680077654415 32333475416864520116481623)
          ·
            refine ⟨48500213125296780174722435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32333475416864520116481623 48500213125296780174722435)
            ·
              refine ⟨72750319687945170262083653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48500213125296780174722435 72750319687945170262083653)
              ·
                refine ⟨13640684941489719424140685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72750319687945170262083653 13640684941489719424140685)
                ·
                  refine ⟨5115256853058644784052757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13640684941489719424140685 5115256853058644784052757)
                  ·
                    refine ⟨239777664987123974252473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5115256853058644784052757 239777664987123974252473)
                    ·
                      refine ⟨179833248740342980689355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239777664987123974252473 179833248740342980689355)
                      ·
                        rfl

theorem cell23_350224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 6, 2].length) (baseStart_350224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350224 prefixEnd_350224 := by exact prefixLift 350224
  have htrace : WordTrace (prefixWord ++ tailWord_350224) baseStart_350224 baseEnd_350224 := by
    simpa [prefixWord, tailWord_350224, baseEnd_350224] using wordTrace_append hprefix tailTrace_350224
  have hstable : (prefixWord ++ tailWord_350224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350224).length < 2 ^ (prefixWord ++ tailWord_350224).sum := by decide
  have hdescent : baseEnd_350224 < baseStart_350224 := by decide
  rcases family_descends (prefixWord ++ tailWord_350224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350227 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 5]
def baseStart_350227 : Nat := 118140960795 + 350227 * 2 ^ 59
def prefixEnd_350227 : Nat := 4983230072969 + 3 ^ 40 * 350227 * 2
def baseEnd_350227 : Nat := 179834789182306468951841

theorem tailTrace_350227 : CollatzResearch.WordTrace tailWord_350227 prefixEnd_350227 179834789182306468951841 := by
  unfold tailWord_350227
  simp only [CollatzResearch.WordTrace]
  refine ⟨12773828102194867854672935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8515885401463245236448623 12773828102194867854672935)
  ·
    refine ⟨19160742153292301782009403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12773828102194867854672935 19160742153292301782009403)
    ·
      refine ⟨28741113229938452673014105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19160742153292301782009403 28741113229938452673014105)
      ·
        refine ⟨21555834922453839504760579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28741113229938452673014105 21555834922453839504760579)
        ·
          refine ⟨32333752383680759257140869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21555834922453839504760579 32333752383680759257140869)
          ·
            refine ⟨6062578571940142360713913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32333752383680759257140869 6062578571940142360713913)
            ·
              refine ⟨4546933928955106770535435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6062578571940142360713913 4546933928955106770535435)
              ·
                refine ⟨6820400893432660155803153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546933928955106770535435 6820400893432660155803153)
                ·
                  refine ⟨5115300670074495116852365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6820400893432660155803153 5115300670074495116852365)
                  ·
                    refine ⟨1918237751277935668819637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5115300670074495116852365 1918237751277935668819637)
                    ·
                      refine ⟨179834789182306468951841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1918237751277935668819637 179834789182306468951841)
                      ·
                        rfl

theorem cell23_350227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_350227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350227 prefixEnd_350227 := by exact prefixLift 350227
  have htrace : WordTrace (prefixWord ++ tailWord_350227) baseStart_350227 baseEnd_350227 := by
    simpa [prefixWord, tailWord_350227, baseEnd_350227] using wordTrace_append hprefix tailTrace_350227
  have hstable : (prefixWord ++ tailWord_350227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350227).length < 2 ^ (prefixWord ++ tailWord_350227).sum := by decide
  have hdescent : baseEnd_350227 < baseStart_350227 := by decide
  rcases family_descends (prefixWord ++ tailWord_350227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350267 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 6]
def baseStart_350267 : Nat := 118140960795 + 350267 * 2 ^ 59
def prefixEnd_350267 : Nat := 4983230072969 + 3 ^ 40 * 350267 * 2
def baseEnd_350267 : Nat := 179855328408486312451657

theorem tailTrace_350267 : CollatzResearch.WordTrace tailWord_350267 prefixEnd_350267 179855328408486312451657 := by
  unfold tailWord_350267
  simp only [CollatzResearch.WordTrace]
  refine ⟨12775287022049954686129055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8516858014699969790752703 12775287022049954686129055)
  ·
    refine ⟨19162930533074932029193583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12775287022049954686129055 19162930533074932029193583)
    ·
      refine ⟨28744395799612398043790375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19162930533074932029193583 28744395799612398043790375)
      ·
        refine ⟨43116593699418597065685563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28744395799612398043790375 43116593699418597065685563)
        ·
          refine ⟨64674890549127895598528345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43116593699418597065685563 64674890549127895598528345)
          ·
            refine ⟨48506167911845921698896259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64674890549127895598528345 48506167911845921698896259)
            ·
              refine ⟨72759251867768882548344389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48506167911845921698896259 72759251867768882548344389)
              ·
                refine ⟨13642359725206665477814573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72759251867768882548344389 13642359725206665477814573)
                ·
                  refine ⟨5115884896952499554180465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13642359725206665477814573 5115884896952499554180465)
                  ·
                    refine ⟨3836913672714374665635349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5115884896952499554180465 3836913672714374665635349)
                    ·
                      refine ⟨179855328408486312451657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3836913672714374665635349 179855328408486312451657)
                      ·
                        rfl

theorem cell23_350267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_350267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350267 prefixEnd_350267 := by exact prefixLift 350267
  have htrace : WordTrace (prefixWord ++ tailWord_350267) baseStart_350267 baseEnd_350267 := by
    simpa [prefixWord, tailWord_350267, baseEnd_350267] using wordTrace_append hprefix tailTrace_350267
  have hstable : (prefixWord ++ tailWord_350267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350267).length < 2 ^ (prefixWord ++ tailWord_350267).sum := by decide
  have hdescent : baseEnd_350267 < baseStart_350267 := by decide
  rcases family_descends (prefixWord ++ tailWord_350267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350365 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_350365 : Nat := 118140960795 + 350365 * 2 ^ 59
def prefixEnd_350365 : Nat := 4983230072969 + 3 ^ 40 * 350365 * 2
def baseEnd_350365 : Nat := 179905649512626929026207

theorem tailTrace_350365 : CollatzResearch.WordTrace tailWord_350365 prefixEnd_350365 179905649512626929026207 := by
  unfold tailWord_350365
  simp only [CollatzResearch.WordTrace]
  refine ⟨12778861375694917423196549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8519240917129944948797699 12778861375694917423196549)
  ·
    refine ⟨2396036507942797016849353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12778861375694917423196549 2396036507942797016849353)
    ·
      refine ⟨1797027380957097762637015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2396036507942797016849353 1797027380957097762637015)
      ·
        refine ⟨2695541071435646643955523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797027380957097762637015 2695541071435646643955523)
        ·
          refine ⟨4043311607153469965933285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695541071435646643955523 4043311607153469965933285)
          ·
            refine ⟨758120926341275618612491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4043311607153469965933285 758120926341275618612491)
            ·
              refine ⟨1137181389511913427918737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758120926341275618612491 1137181389511913427918737)
              ·
                refine ⟨852886042133935070939053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1137181389511913427918737 852886042133935070939053)
                ·
                  refine ⟨319832265800225651602145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 852886042133935070939053 319832265800225651602145)
                  ·
                    refine ⟨239874199350169238701609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 319832265800225651602145 239874199350169238701609)
                    ·
                      refine ⟨179905649512626929026207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239874199350169238701609 179905649512626929026207)
                      ·
                        rfl

theorem cell23_350365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_350365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350365 prefixEnd_350365 := by exact prefixLift 350365
  have htrace : WordTrace (prefixWord ++ tailWord_350365) baseStart_350365 baseEnd_350365 := by
    simpa [prefixWord, tailWord_350365, baseEnd_350365] using wordTrace_append hprefix tailTrace_350365
  have hstable : (prefixWord ++ tailWord_350365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350365).length < 2 ^ (prefixWord ++ tailWord_350365).sum := by decide
  have hdescent : baseEnd_350365 < baseStart_350365 := by decide
  rcases family_descends (prefixWord ++ tailWord_350365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350382 : List Nat := [4, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_350382 : Nat := 118140960795 + 350382 * 2 ^ 59
def prefixEnd_350382 : Nat := 4983230072969 + 3 ^ 40 * 350382 * 2
def baseEnd_350382 : Nat := 179914378683753362513629

theorem tailTrace_350382 : CollatzResearch.WordTrace tailWord_350382 prefixEnd_350382 179914378683753362513629 := by
  unfold tailWord_350382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1597435177079166165820675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8519654277755552884376933 1597435177079166165820675)
  ·
    refine ⟨2396152765618749248731013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1597435177079166165820675 2396152765618749248731013)
    ·
      refine ⟨449278643553515484137065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2396152765618749248731013 449278643553515484137065)
      ·
        refine ⟨336958982665136613102799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449278643553515484137065 336958982665136613102799)
        ·
          refine ⟨505438473997704919654199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336958982665136613102799 505438473997704919654199)
          ·
            refine ⟨758157710996557379481299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505438473997704919654199 758157710996557379481299)
            ·
              refine ⟨1137236566494836069221949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758157710996557379481299 1137236566494836069221949)
              ·
                refine ⟨426463712435563525958231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1137236566494836069221949 426463712435563525958231)
                ·
                  refine ⟨639695568653345288937347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426463712435563525958231 639695568653345288937347)
                  ·
                    refine ⟨959543352980017933406021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 639695568653345288937347 959543352980017933406021)
                    ·
                      refine ⟨179914378683753362513629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 959543352980017933406021 179914378683753362513629)
                      ·
                        rfl

theorem cell23_350382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_350382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350382 prefixEnd_350382 := by exact prefixLift 350382
  have htrace : WordTrace (prefixWord ++ tailWord_350382) baseStart_350382 baseEnd_350382 := by
    simpa [prefixWord, tailWord_350382, baseEnd_350382] using wordTrace_append hprefix tailTrace_350382
  have hstable : (prefixWord ++ tailWord_350382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350382).length < 2 ^ (prefixWord ++ tailWord_350382).sum := by decide
  have hdescent : baseEnd_350382 < baseStart_350382 := by decide
  rcases family_descends (prefixWord ++ tailWord_350382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350385 : List Nat := [1, 2, 2, 5, 2, 1, 1, 3, 1, 2, 3]
def baseStart_350385 : Nat := 118140960795 + 350385 * 2 ^ 59
def prefixEnd_350385 : Nat := 4983230072969 + 3 ^ 40 * 350385 * 2
def baseEnd_350385 : Nat := 179915919125716850776115

theorem tailTrace_350385 : CollatzResearch.WordTrace tailWord_350385 prefixEnd_350385 179915919125716850776115 := by
  unfold tailWord_350385
  simp only [CollatzResearch.WordTrace]
  refine ⟨12779590835622460838924609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8519727223748307225949739 12779590835622460838924609)
  ·
    refine ⟨9584693126716845629193457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12779590835622460838924609 9584693126716845629193457)
    ·
      refine ⟨7188519845037634221895093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9584693126716845629193457 7188519845037634221895093)
      ·
        refine ⟨673923735472278208302665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7188519845037634221895093 673923735472278208302665)
        ·
          refine ⟨505442801604208656226999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 673923735472278208302665 505442801604208656226999)
          ·
            refine ⟨758164202406312984340499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505442801604208656226999 758164202406312984340499)
            ·
              refine ⟨1137246303609469476510749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758164202406312984340499 1137246303609469476510749)
              ·
                refine ⟨426467363853551053691531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1137246303609469476510749 426467363853551053691531)
                ·
                  refine ⟨639701045780326580537297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426467363853551053691531 639701045780326580537297)
                  ·
                    refine ⟨479775784335244935402973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 639701045780326580537297 479775784335244935402973)
                    ·
                      refine ⟨179915919125716850776115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 479775784335244935402973 179915919125716850776115)
                      ·
                        rfl

theorem cell23_350385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_350385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350385 prefixEnd_350385 := by exact prefixLift 350385
  have htrace : WordTrace (prefixWord ++ tailWord_350385) baseStart_350385 baseEnd_350385 := by
    simpa [prefixWord, tailWord_350385, baseEnd_350385] using wordTrace_append hprefix tailTrace_350385
  have hstable : (prefixWord ++ tailWord_350385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350385).length < 2 ^ (prefixWord ++ tailWord_350385).sum := by decide
  have hdescent : baseEnd_350385 < baseStart_350385 := by decide
  rcases family_descends (prefixWord ++ tailWord_350385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350412 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 1, 2, 4]
def baseStart_350412 : Nat := 118140960795 + 350412 * 2 ^ 59
def prefixEnd_350412 : Nat := 4983230072969 + 3 ^ 40 * 350412 * 2
def baseEnd_350412 : Nat := 179929783103388245138491

theorem tailTrace_350412 : CollatzResearch.WordTrace tailWord_350412 prefixEnd_350412 179929783103388245138491 := by
  unfold tailWord_350412
  simp only [CollatzResearch.WordTrace]
  refine ⟨6390287803262322225078745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8520383737683096300104993 6390287803262322225078745)
  ·
    refine ⟨4792715852446741668809059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6390287803262322225078745 4792715852446741668809059)
    ·
      refine ⟨7189073778670112503213589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4792715852446741668809059 7189073778670112503213589)
      ·
        refine ⟨336987833375161523588137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7189073778670112503213589 336987833375161523588137)
        ·
          refine ⟨252740875031371142691103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336987833375161523588137 252740875031371142691103)
          ·
            refine ⟨379111312547056714036655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252740875031371142691103 379111312547056714036655)
            ·
              refine ⟨568666968820585071054983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379111312547056714036655 568666968820585071054983)
              ·
                refine ⟨853000453230877606582475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568666968820585071054983 853000453230877606582475)
                ·
                  refine ⟨1279500679846316409873713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853000453230877606582475 1279500679846316409873713)
                  ·
                    refine ⟨959625509884737307405285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1279500679846316409873713 959625509884737307405285)
                    ·
                      refine ⟨179929783103388245138491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 959625509884737307405285 179929783103388245138491)
                      ·
                        rfl

theorem cell23_350412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_350412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350412 prefixEnd_350412 := by exact prefixLift 350412
  have htrace : WordTrace (prefixWord ++ tailWord_350412) baseStart_350412 baseEnd_350412 := by
    simpa [prefixWord, tailWord_350412, baseEnd_350412] using wordTrace_append hprefix tailTrace_350412
  have hstable : (prefixWord ++ tailWord_350412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350412).length < 2 ^ (prefixWord ++ tailWord_350412).sum := by decide
  have hdescent : baseEnd_350412 < baseStart_350412 := by decide
  rcases family_descends (prefixWord ++ tailWord_350412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350415 : List Nat := [1, 1, 2, 1, 1, 3, 7, 1, 2, 1, 3]
def baseStart_350415 : Nat := 118140960795 + 350415 * 2 ^ 59
def prefixEnd_350415 : Nat := 4983230072969 + 3 ^ 40 * 350415 * 2
def baseEnd_350415 : Nat := 179931323545351733400977

theorem tailTrace_350415 : CollatzResearch.WordTrace tailWord_350415 prefixEnd_350415 179931323545351733400977 := by
  unfold tailWord_350415
  simp only [CollatzResearch.WordTrace]
  refine ⟨12780685025513775962516699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8520456683675850641677799 12780685025513775962516699)
  ·
    refine ⟨19171027538270663943775049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12780685025513775962516699 19171027538270663943775049)
    ·
      refine ⟨14378270653702997957831287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19171027538270663943775049 14378270653702997957831287)
      ·
        refine ⟨21567405980554496936746931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14378270653702997957831287 21567405980554496936746931)
        ·
          refine ⟨32351108970831745405120397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21567405980554496936746931 32351108970831745405120397)
          ·
            refine ⟨12131665864061904526920149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32351108970831745405120397 12131665864061904526920149)
            ·
              refine ⟨284335918688950887349691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12131665864061904526920149 284335918688950887349691)
              ·
                refine ⟨426503878033426331024537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284335918688950887349691 426503878033426331024537)
                ·
                  refine ⟨319877908525069748268403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426503878033426331024537 319877908525069748268403)
                  ·
                    refine ⟨479816862787604622402605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 319877908525069748268403 479816862787604622402605)
                    ·
                      refine ⟨179931323545351733400977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 479816862787604622402605 179931323545351733400977)
                      ·
                        rfl

theorem cell23_350415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 2, 1, 3].length) (baseStart_350415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350415 prefixEnd_350415 := by exact prefixLift 350415
  have htrace : WordTrace (prefixWord ++ tailWord_350415) baseStart_350415 baseEnd_350415 := by
    simpa [prefixWord, tailWord_350415, baseEnd_350415] using wordTrace_append hprefix tailTrace_350415
  have hstable : (prefixWord ++ tailWord_350415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350415).length < 2 ^ (prefixWord ++ tailWord_350415).sum := by decide
  have hdescent : baseEnd_350415 < baseStart_350415 := by decide
  rcases family_descends (prefixWord ++ tailWord_350415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350472 : List Nat := [2, 1, 3, 2, 3, 2, 1, 3, 2, 2, 2]
def baseStart_350472 : Nat := 118140960795 + 350472 * 2 ^ 59
def prefixEnd_350472 : Nat := 4983230072969 + 3 ^ 40 * 350472 * 2
def baseEnd_350472 : Nat := 179960591942658010388215

theorem tailTrace_350472 : CollatzResearch.WordTrace tailWord_350472 prefixEnd_350472 179960591942658010388215 := by
  unfold tailWord_350472
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391381993153637348670835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8521842657538183131561113 6391381993153637348670835)
  ·
    refine ⟨9587072989730456023006253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6391381993153637348670835 9587072989730456023006253)
    ·
      refine ⟨3595152371148921008627345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9587072989730456023006253 3595152371148921008627345)
      ·
        refine ⟨2696364278361690756470509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3595152371148921008627345 2696364278361690756470509)
        ·
          refine ⟨1011136604385634033676441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2696364278361690756470509 1011136604385634033676441)
          ·
            refine ⟨758352453289225525257331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1011136604385634033676441 758352453289225525257331)
            ·
              refine ⟨1137528679933838287885997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758352453289225525257331 1137528679933838287885997)
              ·
                refine ⟨426573254975189357957249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1137528679933838287885997 426573254975189357957249)
                ·
                  refine ⟨319929941231392018467937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426573254975189357957249 319929941231392018467937)
                  ·
                    refine ⟨239947455923544013850953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 319929941231392018467937 239947455923544013850953)
                    ·
                      refine ⟨179960591942658010388215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 239947455923544013850953 179960591942658010388215)
                      ·
                        rfl

theorem cell23_350472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_350472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350472 prefixEnd_350472 := by exact prefixLift 350472
  have htrace : WordTrace (prefixWord ++ tailWord_350472) baseStart_350472 baseEnd_350472 := by
    simpa [prefixWord, tailWord_350472, baseEnd_350472] using wordTrace_append hprefix tailTrace_350472
  have hstable : (prefixWord ++ tailWord_350472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350472).length < 2 ^ (prefixWord ++ tailWord_350472).sum := by decide
  have hdescent : baseEnd_350472 < baseStart_350472 := by decide
  rcases family_descends (prefixWord ++ tailWord_350472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350491 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 2, 5]
def baseStart_350491 : Nat := 118140960795 + 350491 * 2 ^ 59
def prefixEnd_350491 : Nat := 4983230072969 + 3 ^ 40 * 350491 * 2
def baseEnd_350491 : Nat := 59990116025031145350209

theorem tailTrace_350491 : CollatzResearch.WordTrace tailWord_350491 prefixEnd_350491 59990116025031145350209 := by
  unfold tailWord_350491
  simp only [CollatzResearch.WordTrace]
  refine ⟨12783456973238440942283327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8522304648825627294855551 12783456973238440942283327)
  ·
    refine ⟨19175185459857661413424991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12783456973238440942283327 19175185459857661413424991)
    ·
      refine ⟨28762778189786492120137487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19175185459857661413424991 28762778189786492120137487)
      ·
        refine ⟨43144167284679738180206231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28762778189786492120137487 43144167284679738180206231)
        ·
          refine ⟨64716250927019607270309347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43144167284679738180206231 64716250927019607270309347)
          ·
            refine ⟨97074376390529410905464021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64716250927019607270309347 97074376390529410905464021)
            ·
              refine ⟨2275180696653033068096813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 97074376390529410905464021 2275180696653033068096813)
              ·
                refine ⟨853192761244887400536305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2275180696653033068096813 853192761244887400536305)
                ·
                  refine ⟨639894570933665550402229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 853192761244887400536305 639894570933665550402229)
                  ·
                    refine ⟨59990116025031145350209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 639894570933665550402229 59990116025031145350209)
                    ·
                      rfl

theorem cell23_350491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 5].length) (baseStart_350491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350491 prefixEnd_350491 := by exact prefixLift 350491
  have htrace : WordTrace (prefixWord ++ tailWord_350491) baseStart_350491 baseEnd_350491 := by
    simpa [prefixWord, tailWord_350491, baseEnd_350491] using wordTrace_append hprefix tailTrace_350491
  have hstable : (prefixWord ++ tailWord_350491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350491).length < 2 ^ (prefixWord ++ tailWord_350491).sum := by decide
  have hdescent : baseEnd_350491 < baseStart_350491 := by decide
  rcases family_descends (prefixWord ++ tailWord_350491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350545 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 2, 1, 4]
def baseStart_350545 : Nat := 118140960795 + 350545 * 2 ^ 59
def prefixEnd_350545 : Nat := 4983230072969 + 3 ^ 40 * 350545 * 2
def baseEnd_350545 : Nat := 179998076030436224775379

theorem tailTrace_350545 : CollatzResearch.WordTrace tailWord_350545 prefixEnd_350545 179998076030436224775379 := by
  unfold tailWord_350545
  simp only [CollatzResearch.WordTrace]
  refine ⟨12785426515042808164749089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8523617676695205443166059 12785426515042808164749089)
  ·
    refine ⟨9589069886282106123561817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12785426515042808164749089 9589069886282106123561817)
    ·
      refine ⟨7191802414711579592671363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9589069886282106123561817 7191802414711579592671363)
      ·
        refine ⟨10787703622067369389007045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7191802414711579592671363 10787703622067369389007045)
        ·
          refine ⟨2022694429137631760438821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10787703622067369389007045 2022694429137631760438821)
          ·
            refine ⟨379255205463305955082279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2022694429137631760438821 379255205463305955082279)
            ·
              refine ⟨568882808194958932623419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379255205463305955082279 568882808194958932623419)
              ·
                refine ⟨853324212292438398935129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568882808194958932623419 853324212292438398935129)
                ·
                  refine ⟨639993159219328799201347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 853324212292438398935129 639993159219328799201347)
                  ·
                    refine ⟨959989738828993198802021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 639993159219328799201347 959989738828993198802021)
                    ·
                      refine ⟨179998076030436224775379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 959989738828993198802021 179998076030436224775379)
                      ·
                        rfl

theorem cell23_350545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_350545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350545 prefixEnd_350545 := by exact prefixLift 350545
  have htrace : WordTrace (prefixWord ++ tailWord_350545) baseStart_350545 baseEnd_350545 := by
    simpa [prefixWord, tailWord_350545, baseEnd_350545] using wordTrace_append hprefix tailTrace_350545
  have hstable : (prefixWord ++ tailWord_350545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350545).length < 2 ^ (prefixWord ++ tailWord_350545).sum := by decide
  have hdescent : baseEnd_350545 < baseStart_350545 := by decide
  rcases family_descends (prefixWord ++ tailWord_350545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350551 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 8]
def baseStart_350551 : Nat := 118140960795 + 350551 * 2 ^ 59
def prefixEnd_350551 : Nat := 4983230072969 + 3 ^ 40 * 350551 * 2
def baseEnd_350551 : Nat := 20000128546040355700039

theorem tailTrace_350551 : CollatzResearch.WordTrace tailWord_350551 prefixEnd_350551 20000128546040355700039 := by
  unfold tailWord_350551
  simp only [CollatzResearch.WordTrace]
  refine ⟨12785645353021071189467507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8523763568680714126311671 12785645353021071189467507)
  ·
    refine ⟨19178468029531606784201261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12785645353021071189467507 19178468029531606784201261)
    ·
      refine ⟨7191925511074352544075473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19178468029531606784201261 7191925511074352544075473)
      ·
        refine ⟨5393944133305764408056605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7191925511074352544075473 5393944133305764408056605)
        ·
          refine ⟨2022729049989661653021227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5393944133305764408056605 2022729049989661653021227)
          ·
            refine ⟨3034093574984492479531841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022729049989661653021227 3034093574984492479531841)
            ·
              refine ⟨2275570181238369359648881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3034093574984492479531841 2275570181238369359648881)
              ·
                refine ⟨1706677635928777019736661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275570181238369359648881 1706677635928777019736661)
                ·
                  refine ⟨20000128546040355700039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1706677635928777019736661 20000128546040355700039)
                  ·
                    rfl

theorem cell23_350551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 8].length) (baseStart_350551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350551 prefixEnd_350551 := by exact prefixLift 350551
  have htrace : WordTrace (prefixWord ++ tailWord_350551) baseStart_350551 baseEnd_350551 := by
    simpa [prefixWord, tailWord_350551, baseEnd_350551] using wordTrace_append hprefix tailTrace_350551
  have hstable : (prefixWord ++ tailWord_350551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350551).length < 2 ^ (prefixWord ++ tailWord_350551).sum := by decide
  have hdescent : baseEnd_350551 < baseStart_350551 := by decide
  rcases family_descends (prefixWord ++ tailWord_350551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350568 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 8]
def baseStart_350568 : Nat := 118140960795 + 350568 * 2 ^ 59
def prefixEnd_350568 : Nat := 4983230072969 + 3 ^ 40 * 350568 * 2
def baseEnd_350568 : Nat := 20001098453943292754197

theorem tailTrace_350568 : CollatzResearch.WordTrace tailWord_350568 prefixEnd_350568 20001098453943292754197 := by
  unfold tailWord_350568
  simp only [CollatzResearch.WordTrace]
  refine ⟨6393132696979741546418179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8524176929306322061890905 6393132696979741546418179)
  ·
    refine ⟨9589699045469612319627269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6393132696979741546418179 9589699045469612319627269)
    ·
      refine ⟨1798068571025552309930113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9589699045469612319627269 1798068571025552309930113)
      ·
        refine ⟨1348551428269164232447585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1798068571025552309930113 1348551428269164232447585)
        ·
          refine ⟨1011413571201873174335689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1348551428269164232447585 1011413571201873174335689)
          ·
            refine ⟨758560178401404880751767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1011413571201873174335689 758560178401404880751767)
            ·
              refine ⟨1137840267602107321127651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758560178401404880751767 1137840267602107321127651)
              ·
                refine ⟨1706760401403160981691477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137840267602107321127651 1706760401403160981691477)
                ·
                  refine ⟨20001098453943292754197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1706760401403160981691477 20001098453943292754197)
                  ·
                    rfl

theorem cell23_350568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 8].length) (baseStart_350568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350568 prefixEnd_350568 := by exact prefixLift 350568
  have htrace : WordTrace (prefixWord ++ tailWord_350568) baseStart_350568 baseEnd_350568 := by
    simpa [prefixWord, tailWord_350568, baseEnd_350568] using wordTrace_append hprefix tailTrace_350568
  have hstable : (prefixWord ++ tailWord_350568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350568).length < 2 ^ (prefixWord ++ tailWord_350568).sum := by decide
  have hdescent : baseEnd_350568 < baseStart_350568 := by decide
  rcases family_descends (prefixWord ++ tailWord_350568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350629 : List Nat := [1, 3, 1, 2, 1, 1, 7, 2, 1, 1, 3]
def baseStart_350629 : Nat := 118140960795 + 350629 * 2 ^ 59
def prefixEnd_350629 : Nat := 4983230072969 + 3 ^ 40 * 350629 * 2
def baseEnd_350629 : Nat := 180041208405413896124993

theorem tailTrace_350629 : CollatzResearch.WordTrace tailWord_350629 prefixEnd_350629 180041208405413896124993 := by
  unfold tailWord_350629
  simp only [CollatzResearch.WordTrace]
  refine ⟨12788490246738490510806941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8525660164492327007204627 12788490246738490510806941)
  ·
    refine ⟨4795683842526933941552603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12788490246738490510806941 4795683842526933941552603)
    ·
      refine ⟨7193525763790400912328905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4795683842526933941552603 7193525763790400912328905)
      ·
        refine ⟨5395144322842800684246679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7193525763790400912328905 5395144322842800684246679)
        ·
          refine ⟨8092716484264201026370019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5395144322842800684246679 8092716484264201026370019)
          ·
            refine ⟨12139074726396301539555029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8092716484264201026370019 12139074726396301539555029)
            ·
              refine ⟨284509563899913317333321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12139074726396301539555029 284509563899913317333321)
              ·
                refine ⟨213382172924934987999991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284509563899913317333321 213382172924934987999991)
                ·
                  refine ⟨320073259387402481999987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213382172924934987999991 320073259387402481999987)
                  ·
                    refine ⟨480109889081103722999981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 320073259387402481999987 480109889081103722999981)
                    ·
                      refine ⟨180041208405413896124993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 480109889081103722999981 180041208405413896124993)
                      ·
                        rfl

theorem cell23_350629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_350629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350629 prefixEnd_350629 := by exact prefixLift 350629
  have htrace : WordTrace (prefixWord ++ tailWord_350629) baseStart_350629 baseEnd_350629 := by
    simpa [prefixWord, tailWord_350629, baseEnd_350629] using wordTrace_append hprefix tailTrace_350629
  have hstable : (prefixWord ++ tailWord_350629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350629).length < 2 ^ (prefixWord ++ tailWord_350629).sum := by decide
  have hdescent : baseEnd_350629 < baseStart_350629 := by decide
  rcases family_descends (prefixWord ++ tailWord_350629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350648 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_350648 : Nat := 118140960795 + 350648 * 2 ^ 59
def prefixEnd_350648 : Nat := 4983230072969 + 3 ^ 40 * 350648 * 2
def baseEnd_350648 : Nat := 180050964537849321787405

theorem tailTrace_350648 : CollatzResearch.WordTrace tailWord_350648 prefixEnd_350648 180050964537849321787405 := by
  unfold tailWord_350648
  simp only [CollatzResearch.WordTrace]
  refine ⟨6394591616834828377874299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8526122155779771170499065 6394591616834828377874299)
  ·
    refine ⟨9591887425252242566811449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6394591616834828377874299 9591887425252242566811449)
    ·
      refine ⟨7193915568939181925108587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9591887425252242566811449 7193915568939181925108587)
      ·
        refine ⟨10790873353408772887662881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7193915568939181925108587 10790873353408772887662881)
        ·
          refine ⟨8093155015056579665747161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10790873353408772887662881 8093155015056579665747161)
          ·
            refine ⟨6069866261292434749310371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8093155015056579665747161 6069866261292434749310371)
            ·
              refine ⟨9104799391938652123965557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6069866261292434749310371 9104799391938652123965557)
              ·
                refine ⟨853574942994248636621771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9104799391938652123965557 853574942994248636621771)
                ·
                  refine ⟨1280362414491372954932657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853574942994248636621771 1280362414491372954932657)
                  ·
                    refine ⟨960271810868529716199493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1280362414491372954932657 960271810868529716199493)
                    ·
                      refine ⟨180050964537849321787405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 960271810868529716199493 180050964537849321787405)
                      ·
                        rfl

theorem cell23_350648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_350648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350648 prefixEnd_350648 := by exact prefixLift 350648
  have htrace : WordTrace (prefixWord ++ tailWord_350648) baseStart_350648 baseEnd_350648 := by
    simpa [prefixWord, tailWord_350648, baseEnd_350648] using wordTrace_append hprefix tailTrace_350648
  have hstable : (prefixWord ++ tailWord_350648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350648).length < 2 ^ (prefixWord ++ tailWord_350648).sum := by decide
  have hdescent : baseEnd_350648 < baseStart_350648 := by decide
  rcases family_descends (prefixWord ++ tailWord_350648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350651 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 7]
def baseStart_350651 : Nat := 118140960795 + 350651 * 2 ^ 59
def prefixEnd_350651 : Nat := 4983230072969 + 3 ^ 40 * 350651 * 2
def baseEnd_350651 : Nat := 180052504979812810049891

theorem tailTrace_350651 : CollatzResearch.WordTrace tailWord_350651 prefixEnd_350651 180052504979812810049891 := by
  unfold tailWord_350651
  simp only [CollatzResearch.WordTrace]
  refine ⟨12789292652658788268107807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8526195101772525512071871 12789292652658788268107807)
  ·
    refine ⟨19183938978988182402161711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12789292652658788268107807 19183938978988182402161711)
    ·
      refine ⟨28775908468482273603242567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19183938978988182402161711 28775908468482273603242567)
      ·
        refine ⟨43163862702723410404863851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28775908468482273603242567 43163862702723410404863851)
        ·
          refine ⟨64745794054085115607295777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43163862702723410404863851 64745794054085115607295777)
          ·
            refine ⟨48559345540563836705471833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64745794054085115607295777 48559345540563836705471833)
            ·
              refine ⟨36419509155422877529103875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48559345540563836705471833 36419509155422877529103875)
              ·
                refine ⟨54629263733134316293655813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36419509155422877529103875 54629263733134316293655813)
                ·
                  refine ⟨10242986949962684305060465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54629263733134316293655813 10242986949962684305060465)
                  ·
                    refine ⟨7682240212472013228795349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10242986949962684305060465 7682240212472013228795349)
                    ·
                      refine ⟨180052504979812810049891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7682240212472013228795349 180052504979812810049891)
                      ·
                        rfl

theorem cell23_350651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_350651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350651 prefixEnd_350651 := by exact prefixLift 350651
  have htrace : WordTrace (prefixWord ++ tailWord_350651) baseStart_350651 baseEnd_350651 := by
    simpa [prefixWord, tailWord_350651, baseEnd_350651] using wordTrace_append hprefix tailTrace_350651
  have hstable : (prefixWord ++ tailWord_350651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350651).length < 2 ^ (prefixWord ++ tailWord_350651).sum := by decide
  have hdescent : baseEnd_350651 < baseStart_350651 := by decide
  rcases family_descends (prefixWord ++ tailWord_350651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350652 : List Nat := [2, 2, 2, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_350652 : Nat := 118140960795 + 350652 * 2 ^ 59
def prefixEnd_350652 : Nat := 4983230072969 + 3 ^ 40 * 350652 * 2
def baseEnd_350652 : Nat := 180053018460467306137387

theorem tailTrace_350652 : CollatzResearch.WordTrace tailWord_350652 prefixEnd_350652 180053018460467306137387 := by
  unfold tailWord_350652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6394664562827582719447105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8526219417103443625929473 6394664562827582719447105)
  ·
    refine ⟨4795998422120687039585329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6394664562827582719447105 4795998422120687039585329)
    ·
      refine ⟨3596998816590515279688997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4795998422120687039585329 3596998816590515279688997)
      ·
        refine ⟨674437278110721614941687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3596998816590515279688997 674437278110721614941687)
        ·
          refine ⟨1011655917166082422412531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 674437278110721614941687 1011655917166082422412531)
          ·
            refine ⟨1517483875749123633618797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011655917166082422412531 1517483875749123633618797)
            ·
              refine ⟨569056453405921362607049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1517483875749123633618797 569056453405921362607049)
              ·
                refine ⟨426792340054441021955287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569056453405921362607049 426792340054441021955287)
                ·
                  refine ⟨640188510081661532932931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426792340054441021955287 640188510081661532932931)
                  ·
                    refine ⟨960282765122492299399397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 640188510081661532932931 960282765122492299399397)
                    ·
                      refine ⟨180053018460467306137387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 960282765122492299399397 180053018460467306137387)
                      ·
                        rfl

theorem cell23_350652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_350652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350652 prefixEnd_350652 := by exact prefixLift 350652
  have htrace : WordTrace (prefixWord ++ tailWord_350652) baseStart_350652 baseEnd_350652 := by
    simpa [prefixWord, tailWord_350652, baseEnd_350652] using wordTrace_append hprefix tailTrace_350652
  have hstable : (prefixWord ++ tailWord_350652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350652).length < 2 ^ (prefixWord ++ tailWord_350652).sum := by decide
  have hdescent : baseEnd_350652 < baseStart_350652 := by decide
  rcases family_descends (prefixWord ++ tailWord_350652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350685 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_350685 : Nat := 118140960795 + 350685 * 2 ^ 59
def prefixEnd_350685 : Nat := 4983230072969 + 3 ^ 40 * 350685 * 2
def baseEnd_350685 : Nat := 180069963322065677024735

theorem tailTrace_350685 : CollatzResearch.WordTrace tailWord_350685 prefixEnd_350685 180069963322065677024735 := by
  unfold tailWord_350685
  simp only [CollatzResearch.WordTrace]
  refine ⟨12790532734535612074845509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8527021823023741383230339 12790532734535612074845509)
  ·
    refine ⟨2398224887725427264033533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12790532734535612074845509 2398224887725427264033533)
    ·
      refine ⟨899334332897035224012575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2398224887725427264033533 899334332897035224012575)
      ·
        refine ⟨1349001499345552836018863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899334332897035224012575 1349001499345552836018863)
        ·
          refine ⟨2023502249018329254028295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349001499345552836018863 2023502249018329254028295)
          ·
            refine ⟨3035253373527493881042443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023502249018329254028295 3035253373527493881042443)
            ·
              refine ⟨4552880060291240821563665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3035253373527493881042443 4552880060291240821563665)
              ·
                refine ⟨3414660045218430616172749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4552880060291240821563665 3414660045218430616172749)
                ·
                  refine ⟨1280497516956911481064781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3414660045218430616172749 1280497516956911481064781)
                  ·
                    refine ⟨480186568858841805399293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1280497516956911481064781 480186568858841805399293)
                    ·
                      refine ⟨180069963322065677024735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 480186568858841805399293 180069963322065677024735)
                      ·
                        rfl

theorem cell23_350685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_350685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350685 prefixEnd_350685 := by exact prefixLift 350685
  have htrace : WordTrace (prefixWord ++ tailWord_350685) baseStart_350685 baseEnd_350685 := by
    simpa [prefixWord, tailWord_350685, baseEnd_350685] using wordTrace_append hprefix tailTrace_350685
  have hstable : (prefixWord ++ tailWord_350685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350685).length < 2 ^ (prefixWord ++ tailWord_350685).sum := by decide
  have hdescent : baseEnd_350685 < baseStart_350685 := by decide
  rcases family_descends (prefixWord ++ tailWord_350685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350702 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_350702 : Nat := 118140960795 + 350702 * 2 ^ 59
def prefixEnd_350702 : Nat := 4983230072969 + 3 ^ 40 * 350702 * 2
def baseEnd_350702 : Nat := 180078692493192110512157

theorem tailTrace_350702 : CollatzResearch.WordTrace tailWord_350702 prefixEnd_350702 180078692493192110512157 := by
  unfold tailWord_350702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1598894096934252997276795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8527435183649349318809573 1598894096934252997276795)
  ·
    refine ⟨2398341145401379495915193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1598894096934252997276795 2398341145401379495915193)
    ·
      refine ⟨1798755859051034621936395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2398341145401379495915193 1798755859051034621936395)
      ·
        refine ⟨2698133788576551932904593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1798755859051034621936395 2698133788576551932904593)
        ·
          refine ⟨2023600341432413949678445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2698133788576551932904593 2023600341432413949678445)
          ·
            refine ⟨758850128037155231129417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2023600341432413949678445 758850128037155231129417)
            ·
              refine ⟨569137596027866423347063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 758850128037155231129417 569137596027866423347063)
              ·
                refine ⟨853706394041799635020595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569137596027866423347063 853706394041799635020595)
                ·
                  refine ⟨1280559591062699452530893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853706394041799635020595 1280559591062699452530893)
                  ·
                    refine ⟨480209846648512294699085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1280559591062699452530893 480209846648512294699085)
                    ·
                      refine ⟨180078692493192110512157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 480209846648512294699085 180078692493192110512157)
                      ·
                        rfl

theorem cell23_350702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_350702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350702 prefixEnd_350702 := by exact prefixLift 350702
  have htrace : WordTrace (prefixWord ++ tailWord_350702) baseStart_350702 baseEnd_350702 := by
    simpa [prefixWord, tailWord_350702, baseEnd_350702] using wordTrace_append hprefix tailTrace_350702
  have hstable : (prefixWord ++ tailWord_350702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350702).length < 2 ^ (prefixWord ++ tailWord_350702).sum := by decide
  have hdescent : baseEnd_350702 < baseStart_350702 := by decide
  rcases family_descends (prefixWord ++ tailWord_350702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350712 : List Nat := [2, 1, 2, 1, 1, 4, 2, 4, 1, 3, 2]
def baseStart_350712 : Nat := 118140960795 + 350712 * 2 ^ 59
def prefixEnd_350712 : Nat := 4983230072969 + 3 ^ 40 * 350712 * 2
def baseEnd_350712 : Nat := 180083827299737071387111

theorem tailTrace_350712 : CollatzResearch.WordTrace tailWord_350712 prefixEnd_350712 180083827299737071387111 := by
  unfold tailWord_350712
  simp only [CollatzResearch.WordTrace]
  refine ⟨6395758752718897843039195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8527678336958530457385593 6395758752718897843039195)
  ·
    refine ⟨9593638129078346764558793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6395758752718897843039195 9593638129078346764558793)
    ·
      refine ⟨7195228596808760073419095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9593638129078346764558793 7195228596808760073419095)
      ·
        refine ⟨10792842895213140110128643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7195228596808760073419095 10792842895213140110128643)
        ·
          refine ⟨16189264342819710165192965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10792842895213140110128643 16189264342819710165192965)
          ·
            refine ⟨3035487064278695655973681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16189264342819710165192965 3035487064278695655973681)
            ·
              refine ⟨2276615298209021741980261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3035487064278695655973681 2276615298209021741980261)
              ·
                refine ⟨426865368414191576621299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2276615298209021741980261 426865368414191576621299)
                ·
                  refine ⟨640298052621287364931949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426865368414191576621299 640298052621287364931949)
                  ·
                    refine ⟨240111769732982761849481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 640298052621287364931949 240111769732982761849481)
                    ·
                      refine ⟨180083827299737071387111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 240111769732982761849481 180083827299737071387111)
                      ·
                        rfl

theorem cell23_350712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 1, 3, 2].length) (baseStart_350712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350712 prefixEnd_350712 := by exact prefixLift 350712
  have htrace : WordTrace (prefixWord ++ tailWord_350712) baseStart_350712 baseEnd_350712 := by
    simpa [prefixWord, tailWord_350712, baseEnd_350712] using wordTrace_append hprefix tailTrace_350712
  have hstable : (prefixWord ++ tailWord_350712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350712).length < 2 ^ (prefixWord ++ tailWord_350712).sum := by decide
  have hdescent : baseEnd_350712 < baseStart_350712 := by decide
  rcases family_descends (prefixWord ++ tailWord_350712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350728 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_350728 : Nat := 118140960795 + 350728 * 2 ^ 59
def prefixEnd_350728 : Nat := 4983230072969 + 3 ^ 40 * 350728 * 2
def baseEnd_350728 : Nat := 180092042990209008787037

theorem tailTrace_350728 : CollatzResearch.WordTrace tailWord_350728 prefixEnd_350728 180092042990209008787037 := by
  unfold tailWord_350728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6396050536689915209330419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8528067382253220279107225 6396050536689915209330419)
  ·
    refine ⟨9594075805034872813995629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6396050536689915209330419 9594075805034872813995629)
    ·
      refine ⟨3597778426888077305248361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9594075805034872813995629 3597778426888077305248361)
      ·
        refine ⟨2698333820166057978936271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3597778426888077305248361 2698333820166057978936271)
        ·
          refine ⟨4047500730249086968404407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698333820166057978936271 4047500730249086968404407)
          ·
            refine ⟨6071251095373630452606611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4047500730249086968404407 6071251095373630452606611)
            ·
              refine ⟨9106876643060445678909917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6071251095373630452606611 9106876643060445678909917)
              ·
                refine ⟨3415078741147667129591219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9106876643060445678909917 3415078741147667129591219)
                ·
                  refine ⟨5122618111721500694386829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415078741147667129591219 5122618111721500694386829)
                  ·
                    refine ⟨1920981791895562760395061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5122618111721500694386829 1920981791895562760395061)
                    ·
                      refine ⟨180092042990209008787037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1920981791895562760395061 180092042990209008787037)
                      ·
                        rfl

theorem cell23_350728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_350728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350728 prefixEnd_350728 := by exact prefixLift 350728
  have htrace : WordTrace (prefixWord ++ tailWord_350728) baseStart_350728 baseEnd_350728 := by
    simpa [prefixWord, tailWord_350728, baseEnd_350728] using wordTrace_append hprefix tailTrace_350728
  have hstable : (prefixWord ++ tailWord_350728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350728).length < 2 ^ (prefixWord ++ tailWord_350728).sum := by decide
  have hdescent : baseEnd_350728 < baseStart_350728 := by decide
  rcases family_descends (prefixWord ++ tailWord_350728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350755 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 4]
def baseStart_350755 : Nat := 118140960795 + 350755 * 2 ^ 59
def prefixEnd_350755 : Nat := 4983230072969 + 3 ^ 40 * 350755 * 2
def baseEnd_350755 : Nat := 180105906967880403149413

theorem tailTrace_350755 : CollatzResearch.WordTrace tailWord_350755 prefixEnd_350755 180105906967880403149413 := by
  unfold tailWord_350755
  simp only [CollatzResearch.WordTrace]
  refine ⟨12793085844282014029893719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8528723896188009353262479 12793085844282014029893719)
  ·
    refine ⟨19189628766423021044840579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12793085844282014029893719 19189628766423021044840579)
    ·
      refine ⟨28784443149634531567260869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19189628766423021044840579 28784443149634531567260869)
      ·
        refine ⟨5397083090556474668861413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28784443149634531567260869 5397083090556474668861413)
        ·
          refine ⟨1011953079479339000411515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5397083090556474668861413 1011953079479339000411515)
          ·
            refine ⟨1517929619219008500617273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011953079479339000411515 1517929619219008500617273)
            ·
              refine ⟨1138447214414256375462955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1517929619219008500617273 1138447214414256375462955)
              ·
                refine ⟨1707670821621384563194433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138447214414256375462955 1707670821621384563194433)
                ·
                  refine ⟨1280753116216038422395825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1707670821621384563194433 1280753116216038422395825)
                  ·
                    refine ⟨960564837162028816796869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1280753116216038422395825 960564837162028816796869)
                    ·
                      refine ⟨180105906967880403149413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 960564837162028816796869 180105906967880403149413)
                      ·
                        rfl

theorem cell23_350755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_350755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350755 prefixEnd_350755 := by exact prefixLift 350755
  have htrace : WordTrace (prefixWord ++ tailWord_350755) baseStart_350755 baseEnd_350755 := by
    simpa [prefixWord, tailWord_350755, baseEnd_350755] using wordTrace_append hprefix tailTrace_350755
  have hstable : (prefixWord ++ tailWord_350755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350755).length < 2 ^ (prefixWord ++ tailWord_350755).sum := by decide
  have hdescent : baseEnd_350755 < baseStart_350755 := by decide
  rcases family_descends (prefixWord ++ tailWord_350755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350802 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_350802 : Nat := 118140960795 + 350802 * 2 ^ 59
def prefixEnd_350802 : Nat := 4983230072969 + 3 ^ 40 * 350802 * 2
def baseEnd_350802 : Nat := 180130040558641719261697

theorem tailTrace_350802 : CollatzResearch.WordTrace tailWord_350802 prefixEnd_350802 180130040558641719261697 := by
  unfold tailWord_350802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3198700018777935264213665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8529866716741160704569773 3198700018777935264213665)
  ·
    refine ⟨2399025014083451448160249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3198700018777935264213665 2399025014083451448160249)
    ·
      refine ⟨1799268760562588586120187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2399025014083451448160249 1799268760562588586120187)
      ·
        refine ⟨2698903140843882879180281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799268760562588586120187 2698903140843882879180281)
        ·
          refine ⟨2024177355632912159385211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2698903140843882879180281 2024177355632912159385211)
          ·
            refine ⟨3036266033449368239077817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024177355632912159385211 3036266033449368239077817)
            ·
              refine ⟨2277199525087026179308363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3036266033449368239077817 2277199525087026179308363)
              ·
                refine ⟨3415799287630539268962545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277199525087026179308363 3415799287630539268962545)
                ·
                  refine ⟨2561849465722904451721909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3415799287630539268962545 2561849465722904451721909)
                  ·
                    refine ⟨240173387411522292348929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2561849465722904451721909 240173387411522292348929)
                    ·
                      refine ⟨180130040558641719261697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 240173387411522292348929 180130040558641719261697)
                      ·
                        rfl

theorem cell23_350802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_350802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350802 prefixEnd_350802 := by exact prefixLift 350802
  have htrace : WordTrace (prefixWord ++ tailWord_350802) baseStart_350802 baseEnd_350802 := by
    simpa [prefixWord, tailWord_350802, baseEnd_350802] using wordTrace_append hprefix tailTrace_350802
  have hstable : (prefixWord ++ tailWord_350802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350802).length < 2 ^ (prefixWord ++ tailWord_350802).sum := by decide
  have hdescent : baseEnd_350802 < baseStart_350802 := by decide
  rcases family_descends (prefixWord ++ tailWord_350802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350825 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 5, 4]
def baseStart_350825 : Nat := 118140960795 + 350825 * 2 ^ 59
def prefixEnd_350825 : Nat := 4983230072969 + 3 ^ 40 * 350825 * 2
def baseEnd_350825 : Nat := 60047283537898376424697

theorem tailTrace_350825 : CollatzResearch.WordTrace tailWord_350825 prefixEnd_350825 60047283537898376424697 := by
  unfold tailWord_350825
  simp only [CollatzResearch.WordTrace]
  refine ⟨12795638954028415984941929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8530425969352277323294619 12795638954028415984941929)
  ·
    refine ⟨9596729215521311988706447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12795638954028415984941929 9596729215521311988706447)
    ·
      refine ⟨14395093823281967983059671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9596729215521311988706447 14395093823281967983059671)
      ·
        refine ⟨21592640734922951974589507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14395093823281967983059671 21592640734922951974589507)
        ·
          refine ⟨32388961102384427961884261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21592640734922951974589507 32388961102384427961884261)
          ·
            refine ⟨6072930206697080242853299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32388961102384427961884261 6072930206697080242853299)
            ·
              refine ⟨9109395310045620364279949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6072930206697080242853299 9109395310045620364279949)
              ·
                refine ⟨3416023241267107636604981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9109395310045620364279949 3416023241267107636604981)
                ·
                  refine ⟨320252178868791340931717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3416023241267107636604981 320252178868791340931717)
                  ·
                    refine ⟨60047283537898376424697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 320252178868791340931717 60047283537898376424697)
                    ·
                      rfl

theorem cell23_350825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 4].length) (baseStart_350825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350825 prefixEnd_350825 := by exact prefixLift 350825
  have htrace : WordTrace (prefixWord ++ tailWord_350825) baseStart_350825 baseEnd_350825 := by
    simpa [prefixWord, tailWord_350825, baseEnd_350825] using wordTrace_append hprefix tailTrace_350825
  have hstable : (prefixWord ++ tailWord_350825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350825).length < 2 ^ (prefixWord ++ tailWord_350825).sum := by decide
  have hdescent : baseEnd_350825 < baseStart_350825 := by decide
  rcases family_descends (prefixWord ++ tailWord_350825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350916 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_350916 : Nat := 118140960795 + 350916 * 2 ^ 59
def prefixEnd_350916 : Nat := 4983230072969 + 3 ^ 40 * 350916 * 2
def baseEnd_350916 : Nat := 180188577353254273236173

theorem tailTrace_350916 : CollatzResearch.WordTrace tailWord_350916 prefixEnd_350916 180188577353254273236173 := by
  unfold tailWord_350916
  simp only [CollatzResearch.WordTrace]
  refine ⟨6399478998349369263252301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8532638664465825684336401 6399478998349369263252301)
  ·
    refine ⟨2399804624381013473719613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6399478998349369263252301 2399804624381013473719613)
    ·
      refine ⟨899926734142880052644855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2399804624381013473719613 899926734142880052644855)
      ·
        refine ⟨1349890101214320078967283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899926734142880052644855 1349890101214320078967283)
        ·
          refine ⟨2024835151821480118450925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349890101214320078967283 2024835151821480118450925)
          ·
            refine ⟨759313181933055044419097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2024835151821480118450925 759313181933055044419097)
            ·
              refine ⟨569484886449791283314323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759313181933055044419097 569484886449791283314323)
              ·
                refine ⟨854227329674686924971485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569484886449791283314323 854227329674686924971485)
                ·
                  refine ⟨320335248628007596864307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854227329674686924971485 320335248628007596864307)
                  ·
                    refine ⟨480502872942011395296461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 320335248628007596864307 480502872942011395296461)
                    ·
                      refine ⟨180188577353254273236173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 480502872942011395296461 180188577353254273236173)
                      ·
                        rfl

theorem cell23_350916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_350916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350916 prefixEnd_350916 := by exact prefixLift 350916
  have htrace : WordTrace (prefixWord ++ tailWord_350916) baseStart_350916 baseEnd_350916 := by
    simpa [prefixWord, tailWord_350916, baseEnd_350916] using wordTrace_append hprefix tailTrace_350916
  have hstable : (prefixWord ++ tailWord_350916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350916).length < 2 ^ (prefixWord ++ tailWord_350916).sum := by decide
  have hdescent : baseEnd_350916 < baseStart_350916 := by decide
  rcases family_descends (prefixWord ++ tailWord_350916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350959 : List Nat := [1, 1, 2, 1, 5, 2, 2, 3, 1, 2, 3]
def baseStart_350959 : Nat := 118140960795 + 350959 * 2 ^ 59
def prefixEnd_350959 : Nat := 4983230072969 + 3 ^ 40 * 350959 * 2
def baseEnd_350959 : Nat := 180210657021397604998475

theorem tailTrace_350959 : CollatzResearch.WordTrace tailWord_350959 prefixEnd_350959 180210657021397604998475 := by
  unfold tailWord_350959
  simp only [CollatzResearch.WordTrace]
  refine ⟨12800526335542956870319931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8533684223695304580213287 12800526335542956870319931)
  ·
    refine ⟨19200789503314435305479897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12800526335542956870319931 19200789503314435305479897)
    ·
      refine ⟨14400592127485826479109923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19200789503314435305479897 14400592127485826479109923)
      ·
        refine ⟨21600888191228739718664885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14400592127485826479109923 21600888191228739718664885)
        ·
          refine ⟨2025083267927694348624833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21600888191228739718664885 2025083267927694348624833)
          ·
            refine ⟨1518812450945770761468625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2025083267927694348624833 1518812450945770761468625)
            ·
              refine ⟨1139109338209328071101469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518812450945770761468625 1139109338209328071101469)
              ·
                refine ⟨427166001828498026663051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1139109338209328071101469 427166001828498026663051)
                ·
                  refine ⟨640749002742747039994577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427166001828498026663051 640749002742747039994577)
                  ·
                    refine ⟨480561752057060279995933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 640749002742747039994577 480561752057060279995933)
                    ·
                      refine ⟨180210657021397604998475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 480561752057060279995933 180210657021397604998475)
                      ·
                        rfl

theorem cell23_350959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 2, 3].length) (baseStart_350959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350959 prefixEnd_350959 := by exact prefixLift 350959
  have htrace : WordTrace (prefixWord ++ tailWord_350959) baseStart_350959 baseEnd_350959 := by
    simpa [prefixWord, tailWord_350959, baseEnd_350959] using wordTrace_append hprefix tailTrace_350959
  have hstable : (prefixWord ++ tailWord_350959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350959).length < 2 ^ (prefixWord ++ tailWord_350959).sum := by decide
  have hdescent : baseEnd_350959 < baseStart_350959 := by decide
  rcases family_descends (prefixWord ++ tailWord_350959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350962 : List Nat := [3, 2, 1, 3, 1, 4, 9]
def baseStart_350962 : Nat := 118140960795 + 350962 * 2 ^ 59
def prefixEnd_350962 : Nat := 4983230072969 + 3 ^ 40 * 350962 * 2
def baseEnd_350962 : Nat := 2224841943992112262481

theorem tailTrace_350962 : CollatzResearch.WordTrace tailWord_350962 prefixEnd_350962 2224841943992112262481 := by
  unfold tailWord_350962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3200158938633022095669785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8533757169688058921786093 3200158938633022095669785)
  ·
    refine ⟨2400119203974766571752339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3200158938633022095669785 2400119203974766571752339)
    ·
      refine ⟨3600178805962149857628509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2400119203974766571752339 3600178805962149857628509)
      ·
        refine ⟨1350067052235806196610691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3600178805962149857628509 1350067052235806196610691)
        ·
          refine ⟨2025100578353709294916037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350067052235806196610691 2025100578353709294916037)
          ·
            refine ⟨379706358441320492796757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2025100578353709294916037 379706358441320492796757)
            ·
              refine ⟨2224841943992112262481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 379706358441320492796757 2224841943992112262481)
              ·
                rfl

theorem cell23_350962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 9].length) (baseStart_350962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350962 prefixEnd_350962 := by exact prefixLift 350962
  have htrace : WordTrace (prefixWord ++ tailWord_350962) baseStart_350962 baseEnd_350962 := by
    simpa [prefixWord, tailWord_350962, baseEnd_350962] using wordTrace_append hprefix tailTrace_350962
  have hstable : (prefixWord ++ tailWord_350962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350962).length < 2 ^ (prefixWord ++ tailWord_350962).sum := by decide
  have hdescent : baseEnd_350962 < baseStart_350962 := by decide
  rcases family_descends (prefixWord ++ tailWord_350962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350975 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 2, 7]
def baseStart_350975 : Nat := 118140960795 + 350975 * 2 ^ 59
def prefixEnd_350975 : Nat := 4983230072969 + 3 ^ 40 * 350975 * 2
def baseEnd_350975 : Nat := 60072957570623180799467

theorem tailTrace_350975 : CollatzResearch.WordTrace tailWord_350975 prefixEnd_350975 60072957570623180799467 := by
  unfold tailWord_350975
  simp only [CollatzResearch.WordTrace]
  refine ⟨12801109903484991602902379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8534073268989994401934919 12801109903484991602902379)
  ·
    refine ⟨19201664855227487404353569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12801109903484991602902379 19201664855227487404353569)
    ·
      refine ⟨14401248641420615553265177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19201664855227487404353569 14401248641420615553265177)
      ·
        refine ⟨10800936481065461664948883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14401248641420615553265177 10800936481065461664948883)
        ·
          refine ⟨16201404721598192497423325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10800936481065461664948883 16201404721598192497423325)
          ·
            refine ⟨6075526770599322186533747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16201404721598192497423325 6075526770599322186533747)
            ·
              refine ⟨9113290155898983279800621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6075526770599322186533747 9113290155898983279800621)
              ·
                refine ⟨3417483808462118729925233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9113290155898983279800621 3417483808462118729925233)
                ·
                  refine ⟨2563112856346589047443925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3417483808462118729925233 2563112856346589047443925)
                  ·
                    refine ⟨60072957570623180799467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2563112856346589047443925 60072957570623180799467)
                    ·
                      rfl

theorem cell23_350975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_350975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350975 prefixEnd_350975 := by exact prefixLift 350975
  have htrace : WordTrace (prefixWord ++ tailWord_350975) baseStart_350975 baseEnd_350975 := by
    simpa [prefixWord, tailWord_350975, baseEnd_350975] using wordTrace_append hprefix tailTrace_350975
  have hstable : (prefixWord ++ tailWord_350975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350975).length < 2 ^ (prefixWord ++ tailWord_350975).sum := by decide
  have hdescent : baseEnd_350975 < baseStart_350975 := by decide
  rcases family_descends (prefixWord ++ tailWord_350975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350983 : List Nat := [1, 1, 4, 4, 1, 3, 2, 1, 2, 4]
def baseStart_350983 : Nat := 118140960795 + 350983 * 2 ^ 59
def prefixEnd_350983 : Nat := 4983230072969 + 3 ^ 40 * 350983 * 2
def baseEnd_350983 : Nat := 60074326852368503699455

theorem tailTrace_350983 : CollatzResearch.WordTrace tailWord_350983 prefixEnd_350983 60074326852368503699455 := by
  unfold tailWord_350983
  simp only [CollatzResearch.WordTrace]
  refine ⟨12801401687456008969193603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8534267791637339312795735 12801401687456008969193603)
  ·
    refine ⟨19202102531184013453790405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12801401687456008969193603 19202102531184013453790405)
    ·
      refine ⟨3600394224597002522585701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19202102531184013453790405 3600394224597002522585701)
      ·
        refine ⟨675073917111937972984819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3600394224597002522585701 675073917111937972984819)
        ·
          refine ⟨1012610875667906959477229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675073917111937972984819 1012610875667906959477229)
          ·
            refine ⟨379729078375465109803961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1012610875667906959477229 379729078375465109803961)
            ·
              refine ⟨284796808781598832352971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379729078375465109803961 284796808781598832352971)
              ·
                refine ⟨427195213172398248529457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284796808781598832352971 427195213172398248529457)
                ·
                  refine ⟨320396409879298686397093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427195213172398248529457 320396409879298686397093)
                  ·
                    refine ⟨60074326852368503699455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 320396409879298686397093 60074326852368503699455)
                    ·
                      rfl

theorem cell23_350983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_350983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_350983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_350983 prefixEnd_350983 := by exact prefixLift 350983
  have htrace : WordTrace (prefixWord ++ tailWord_350983) baseStart_350983 baseEnd_350983 := by
    simpa [prefixWord, tailWord_350983, baseEnd_350983] using wordTrace_append hprefix tailTrace_350983
  have hstable : (prefixWord ++ tailWord_350983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350983).length < 2 ^ (prefixWord ++ tailWord_350983).sum := by decide
  have hdescent : baseEnd_350983 < baseStart_350983 := by decide
  rcases family_descends (prefixWord ++ tailWord_350983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351032 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 1, 6, 3]
def baseStart_351032 : Nat := 118140960795 + 351032 * 2 ^ 59
def prefixEnd_351032 : Nat := 4983230072969 + 3 ^ 40 * 351032 * 2
def baseEnd_351032 : Nat := 180248141109175819385639

theorem tailTrace_351032 : CollatzResearch.WordTrace tailWord_351032 prefixEnd_351032 180248141109175819385639 := by
  unfold tailWord_351032
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401594432139245168863675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8535459242852326891818233 6401594432139245168863675)
  ·
    refine ⟨9602391648208867753295513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6401594432139245168863675 9602391648208867753295513)
    ·
      refine ⟨7201793736156650814971635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9602391648208867753295513 7201793736156650814971635)
      ·
        refine ⟨10802690604234976222457453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7201793736156650814971635 10802690604234976222457453)
        ·
          refine ⟨4051008976588116083421545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10802690604234976222457453 4051008976588116083421545)
          ·
            refine ⟨3038256732441087062566159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4051008976588116083421545 3038256732441087062566159)
            ·
              refine ⟨4557385098661630593849239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3038256732441087062566159 4557385098661630593849239)
              ·
                refine ⟨6836077647992445890773859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4557385098661630593849239 6836077647992445890773859)
                ·
                  refine ⟨10254116471988668836160789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6836077647992445890773859 10254116471988668836160789)
                  ·
                    refine ⟨480661709624468851695037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10254116471988668836160789 480661709624468851695037)
                    ·
                      refine ⟨180248141109175819385639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 480661709624468851695037 180248141109175819385639)
                      ·
                        rfl

theorem cell23_351032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_351032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351032 prefixEnd_351032 := by exact prefixLift 351032
  have htrace : WordTrace (prefixWord ++ tailWord_351032) baseStart_351032 baseEnd_351032 := by
    simpa [prefixWord, tailWord_351032, baseEnd_351032] using wordTrace_append hprefix tailTrace_351032
  have hstable : (prefixWord ++ tailWord_351032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351032).length < 2 ^ (prefixWord ++ tailWord_351032).sum := by decide
  have hdescent : baseEnd_351032 < baseStart_351032 := by decide
  rcases family_descends (prefixWord ++ tailWord_351032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351052 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 9]
def baseStart_351052 : Nat := 118140960795 + 351052 * 2 ^ 59
def prefixEnd_351052 : Nat := 4983230072969 + 3 ^ 40 * 351052 * 2
def baseEnd_351052 : Nat := 20028712302473971237283

theorem tailTrace_351052 : CollatzResearch.WordTrace tailWord_351052 prefixEnd_351052 20028712302473971237283 := by
  unfold tailWord_351052
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401959162103016876727705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8535945549470689168970273 6401959162103016876727705)
  ·
    refine ⟨4801469371577262657545779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6401959162103016876727705 4801469371577262657545779)
    ·
      refine ⟨7202204057365893986318669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4801469371577262657545779 7202204057365893986318669)
      ·
        refine ⟨2700826521512210244869501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7202204057365893986318669 2700826521512210244869501)
        ·
          refine ⟨1012809945567078841826063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2700826521512210244869501 1012809945567078841826063)
          ·
            refine ⟨1519214918350618262739095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012809945567078841826063 1519214918350618262739095)
            ·
              refine ⟨2278822377525927394108643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519214918350618262739095 2278822377525927394108643)
              ·
                refine ⟨3418233566288891091162965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278822377525927394108643 3418233566288891091162965)
                ·
                  refine ⟨20028712302473971237283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3418233566288891091162965 20028712302473971237283)
                  ·
                    rfl

theorem cell23_351052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_351052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351052 prefixEnd_351052 := by exact prefixLift 351052
  have htrace : WordTrace (prefixWord ++ tailWord_351052) baseStart_351052 baseEnd_351052 := by
    simpa [prefixWord, tailWord_351052, baseEnd_351052] using wordTrace_append hprefix tailTrace_351052
  have hstable : (prefixWord ++ tailWord_351052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351052).length < 2 ^ (prefixWord ++ tailWord_351052).sum := by decide
  have hdescent : baseEnd_351052 < baseStart_351052 := by decide
  rcases family_descends (prefixWord ++ tailWord_351052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351079 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_351079 : Nat := 118140960795 + 351079 * 2 ^ 59
def prefixEnd_351079 : Nat := 4983230072969 + 3 ^ 40 * 351079 * 2
def baseEnd_351079 : Nat := 180272274699937135497923

theorem tailTrace_351079 : CollatzResearch.WordTrace tailWord_351079 prefixEnd_351079 180272274699937135497923 := by
  unfold tailWord_351079
  simp only [CollatzResearch.WordTrace]
  refine ⟨12804903095108217364688291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8536602063405478243125527 12804903095108217364688291)
  ·
    refine ⟨19207354642662326047032437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12804903095108217364688291 19207354642662326047032437)
    ·
      refine ⟨1800689497749593066909291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19207354642662326047032437 1800689497749593066909291)
      ·
        refine ⟨2701034246624389600363937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800689497749593066909291 2701034246624389600363937)
        ·
          refine ⟨2025775684968292200272953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2701034246624389600363937 2025775684968292200272953)
          ·
            refine ⟨1519331763726219150204715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2025775684968292200272953 1519331763726219150204715)
            ·
              refine ⟨2278997645589328725307073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519331763726219150204715 2278997645589328725307073)
              ·
                refine ⟨1709248234191996543980305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2278997645589328725307073 1709248234191996543980305)
                ·
                  refine ⟨1281936175643997407985229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1709248234191996543980305 1281936175643997407985229)
                  ·
                    refine ⟨480726065866499027994461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1281936175643997407985229 480726065866499027994461)
                    ·
                      refine ⟨180272274699937135497923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 480726065866499027994461 180272274699937135497923)
                      ·
                        rfl

theorem cell23_351079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_351079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351079 prefixEnd_351079 := by exact prefixLift 351079
  have htrace : WordTrace (prefixWord ++ tailWord_351079) baseStart_351079 baseEnd_351079 := by
    simpa [prefixWord, tailWord_351079, baseEnd_351079] using wordTrace_append hprefix tailTrace_351079
  have hstable : (prefixWord ++ tailWord_351079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351079).length < 2 ^ (prefixWord ++ tailWord_351079).sum := by decide
  have hdescent : baseEnd_351079 < baseStart_351079 := by decide
  rcases family_descends (prefixWord ++ tailWord_351079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351080 : List Nat := [2, 1, 4, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_351080 : Nat := 118140960795 + 351080 * 2 ^ 59
def prefixEnd_351080 : Nat := 4983230072969 + 3 ^ 40 * 351080 * 2
def baseEnd_351080 : Nat := 180272788180591631585419

theorem tailTrace_351080 : CollatzResearch.WordTrace tailWord_351080 prefixEnd_351080 180272788180591631585419 := by
  unfold tailWord_351080
  simp only [CollatzResearch.WordTrace]
  refine ⟨6402469784052297267737347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8536626378736396356983129 6402469784052297267737347)
  ·
    refine ⟨9603704676078445901606021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6402469784052297267737347 9603704676078445901606021)
    ·
      refine ⟨1800694626764708606551129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9603704676078445901606021 1800694626764708606551129)
      ·
        refine ⟨1350520970073531454913347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1800694626764708606551129 1350520970073531454913347)
        ·
          refine ⟨2025781455110297182370021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350520970073531454913347 2025781455110297182370021)
          ·
            refine ⟨379834022833180721694379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2025781455110297182370021 379834022833180721694379)
            ·
              refine ⟨569751034249771082541569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379834022833180721694379 569751034249771082541569)
              ·
                refine ⟨427313275687328311906177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569751034249771082541569 427313275687328311906177)
                ·
                  refine ⟨320484956765496233929633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427313275687328311906177 320484956765496233929633)
                  ·
                    refine ⟨240363717574122175447225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 320484956765496233929633 240363717574122175447225)
                    ·
                      refine ⟨180272788180591631585419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 240363717574122175447225 180272788180591631585419)
                      ·
                        rfl

theorem cell23_351080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_351080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351080 prefixEnd_351080 := by exact prefixLift 351080
  have htrace : WordTrace (prefixWord ++ tailWord_351080) baseStart_351080 baseEnd_351080 := by
    simpa [prefixWord, tailWord_351080, baseEnd_351080] using wordTrace_append hprefix tailTrace_351080
  have hstable : (prefixWord ++ tailWord_351080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351080).length < 2 ^ (prefixWord ++ tailWord_351080).sum := by decide
  have hdescent : baseEnd_351080 < baseStart_351080 := by decide
  rcases family_descends (prefixWord ++ tailWord_351080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351086 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 7]
def baseStart_351086 : Nat := 118140960795 + 351086 * 2 ^ 59
def prefixEnd_351086 : Nat := 4983230072969 + 3 ^ 40 * 351086 * 2
def baseEnd_351086 : Nat := 20030652118279845345599

theorem tailTrace_351086 : CollatzResearch.WordTrace tailWord_351086 prefixEnd_351086 20030652118279845345599 := by
  unfold tailWord_351086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1600644800760357195024139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8536772270721905040128741 1600644800760357195024139)
  ·
    refine ⟨2400967201140535792536209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1600644800760357195024139 2400967201140535792536209)
    ·
      refine ⟨1800725400855401844402157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2400967201140535792536209 1800725400855401844402157)
      ·
        refine ⟨675272025320775691650809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1800725400855401844402157 675272025320775691650809)
        ·
          refine ⟨506454018990581768738107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675272025320775691650809 506454018990581768738107)
          ·
            refine ⟨759681028485872653107161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506454018990581768738107 759681028485872653107161)
            ·
              refine ⟨569760771364404489830371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759681028485872653107161 569760771364404489830371)
              ·
                refine ⟨854641157046606734745557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569760771364404489830371 854641157046606734745557)
                ·
                  refine ⟨20030652118279845345599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 854641157046606734745557 20030652118279845345599)
                  ·
                    rfl

theorem cell23_351086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_351086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351086 prefixEnd_351086 := by exact prefixLift 351086
  have htrace : WordTrace (prefixWord ++ tailWord_351086) baseStart_351086 baseEnd_351086 := by
    simpa [prefixWord, tailWord_351086, baseEnd_351086] using wordTrace_append hprefix tailTrace_351086
  have hstable : (prefixWord ++ tailWord_351086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351086).length < 2 ^ (prefixWord ++ tailWord_351086).sum := by decide
  have hdescent : baseEnd_351086 < baseStart_351086 := by decide
  rcases family_descends (prefixWord ++ tailWord_351086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351139 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 3]
def baseStart_351139 : Nat := 118140960795 + 351139 * 2 ^ 59
def prefixEnd_351139 : Nat := 4983230072969 + 3 ^ 40 * 351139 * 2
def baseEnd_351139 : Nat := 180303083539206900747647

theorem tailTrace_351139 : CollatzResearch.WordTrace tailWord_351139 prefixEnd_351139 180303083539206900747647 := by
  unfold tailWord_351139
  simp only [CollatzResearch.WordTrace]
  refine ⟨12807091474890847611872471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8538060983260565074581647 12807091474890847611872471)
  ·
    refine ⟨19210637212336271417808707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12807091474890847611872471 19210637212336271417808707)
    ·
      refine ⟨28815955818504407126713061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19210637212336271417808707 28815955818504407126713061)
      ·
        refine ⟨5402991715969576336258699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28815955818504407126713061 5402991715969576336258699)
        ·
          refine ⟨8104487573954364504388049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5402991715969576336258699 8104487573954364504388049)
          ·
            refine ⟨6078365680465773378291037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8104487573954364504388049 6078365680465773378291037)
            ·
              refine ⟨2279387130174665016859139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6078365680465773378291037 2279387130174665016859139)
              ·
                refine ⟨3419080695261997525288709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279387130174665016859139 3419080695261997525288709)
                ·
                  refine ⟨641077630361624535991633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3419080695261997525288709 641077630361624535991633)
                  ·
                    refine ⟨480808222771218401993725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 641077630361624535991633 480808222771218401993725)
                    ·
                      refine ⟨180303083539206900747647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 480808222771218401993725 180303083539206900747647)
                      ·
                        rfl

theorem cell23_351139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_351139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351139 prefixEnd_351139 := by exact prefixLift 351139
  have htrace : WordTrace (prefixWord ++ tailWord_351139) baseStart_351139 baseEnd_351139 := by
    simpa [prefixWord, tailWord_351139, baseEnd_351139] using wordTrace_append hprefix tailTrace_351139
  have hstable : (prefixWord ++ tailWord_351139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351139).length < 2 ^ (prefixWord ++ tailWord_351139).sum := by decide
  have hdescent : baseEnd_351139 < baseStart_351139 := by decide
  rcases family_descends (prefixWord ++ tailWord_351139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351197 : List Nat := [1, 4, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_351197 : Nat := 118140960795 + 351197 * 2 ^ 59
def prefixEnd_351197 : Nat := 4983230072969 + 3 ^ 40 * 351197 * 2
def baseEnd_351197 : Nat := 60110955139055891274127

theorem tailTrace_351197 : CollatzResearch.WordTrace tailWord_351197 prefixEnd_351197 60110955139055891274127 := by
  unfold tailWord_351197
  simp only [CollatzResearch.WordTrace]
  refine ⟨12809206908680723517483845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8539471272453815678322563 12809206908680723517483845)
  ·
    refine ⟨2401726295377635659528221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12809206908680723517483845 2401726295377635659528221)
    ·
      refine ⟨900647360766613372323083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2401726295377635659528221 900647360766613372323083)
      ·
        refine ⟨1350971041149920058484625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900647360766613372323083 1350971041149920058484625)
        ·
          refine ⟨1013228280862440043863469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1350971041149920058484625 1013228280862440043863469)
          ·
            refine ⟨379960605323415016448801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1013228280862440043863469 379960605323415016448801)
            ·
              refine ⟨284970453992561262336601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379960605323415016448801 284970453992561262336601)
              ·
                refine ⟨213727840494420946752451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284970453992561262336601 213727840494420946752451)
                ·
                  refine ⟨320591760741631420128677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213727840494420946752451 320591760741631420128677)
                  ·
                    refine ⟨60110955139055891274127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 320591760741631420128677 60110955139055891274127)
                    ·
                      rfl

theorem cell23_351197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_351197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351197 prefixEnd_351197 := by exact prefixLift 351197
  have htrace : WordTrace (prefixWord ++ tailWord_351197) baseStart_351197 baseEnd_351197 := by
    simpa [prefixWord, tailWord_351197, baseEnd_351197] using wordTrace_append hprefix tailTrace_351197
  have hstable : (prefixWord ++ tailWord_351197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351197).length < 2 ^ (prefixWord ++ tailWord_351197).sum := by decide
  have hdescent : baseEnd_351197 < baseStart_351197 := by decide
  rcases family_descends (prefixWord ++ tailWord_351197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351219 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 8, 4]
def baseStart_351219 : Nat := 118140960795 + 351219 * 2 ^ 59
def prefixEnd_351219 : Nat := 4983230072969 + 3 ^ 40 * 351219 * 2
def baseEnd_351219 : Nat := 60114720663855529249093

theorem tailTrace_351219 : CollatzResearch.WordTrace tailWord_351219 prefixEnd_351219 60114720663855529249093 := by
  unfold tailWord_351219
  simp only [CollatzResearch.WordTrace]
  refine ⟨12810009314601021274784711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8540006209734014183189807 12810009314601021274784711)
  ·
    refine ⟨19215013971901531912177067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12810009314601021274784711 19215013971901531912177067)
    ·
      refine ⟨28822520957852297868265601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19215013971901531912177067 28822520957852297868265601)
      ·
        refine ⟨21616890718389223401199201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28822520957852297868265601 21616890718389223401199201)
        ·
          refine ⟨16212668038791917550899401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21616890718389223401199201 16212668038791917550899401)
          ·
            refine ⟨12159501029093938163174551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16212668038791917550899401 12159501029093938163174551)
            ·
              refine ⟨18239251543640907244761827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12159501029093938163174551 18239251543640907244761827)
              ·
                refine ⟨27358877315461360867142741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18239251543640907244761827 27358877315461360867142741)
                ·
                  refine ⟨320611843540562822661829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27358877315461360867142741 320611843540562822661829)
                  ·
                    refine ⟨60114720663855529249093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 320611843540562822661829 60114720663855529249093)
                    ·
                      rfl

theorem cell23_351219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 4].length) (baseStart_351219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351219 prefixEnd_351219 := by exact prefixLift 351219
  have htrace : WordTrace (prefixWord ++ tailWord_351219) baseStart_351219 baseEnd_351219 := by
    simpa [prefixWord, tailWord_351219, baseEnd_351219] using wordTrace_append hprefix tailTrace_351219
  have hstable : (prefixWord ++ tailWord_351219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351219).length < 2 ^ (prefixWord ++ tailWord_351219).sum := by decide
  have hdescent : baseEnd_351219 < baseStart_351219 := by decide
  rcases family_descends (prefixWord ++ tailWord_351219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351230 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_351230 : Nat := 118140960795 + 351230 * 2 ^ 59
def prefixEnd_351230 : Nat := 4983230072969 + 3 ^ 40 * 351230 * 2
def baseEnd_351230 : Nat := 180349810278766044709729

theorem tailTrace_351230 : CollatzResearch.WordTrace tailWord_351230 prefixEnd_351230 180349810278766044709729 := by
  unfold tailWord_351230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601301314695146269179393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8540273678374113435623429 1601301314695146269179393)
  ·
    refine ⟨1200975986021359701884545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1601301314695146269179393 1200975986021359701884545)
    ·
      refine ⟨900731989516019776413409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1200975986021359701884545 900731989516019776413409)
      ·
        refine ⟨675548992137014832310057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 900731989516019776413409 675548992137014832310057)
        ·
          refine ⟨506661744102761124232543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675548992137014832310057 506661744102761124232543)
          ·
            refine ⟨759992616154141686348815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506661744102761124232543 759992616154141686348815)
            ·
              refine ⟨1139988924231212529523223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759992616154141686348815 1139988924231212529523223)
              ·
                refine ⟨1709983386346818794284835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139988924231212529523223 1709983386346818794284835)
                ·
                  refine ⟨2564975079520228191427253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709983386346818794284835 2564975079520228191427253)
                  ·
                    refine ⟨240466413705021392946305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2564975079520228191427253 240466413705021392946305)
                    ·
                      refine ⟨180349810278766044709729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 240466413705021392946305 180349810278766044709729)
                      ·
                        rfl

theorem cell23_351230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_351230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351230 prefixEnd_351230 := by exact prefixLift 351230
  have htrace : WordTrace (prefixWord ++ tailWord_351230) baseStart_351230 baseEnd_351230 := by
    simpa [prefixWord, tailWord_351230, baseEnd_351230] using wordTrace_append hprefix tailTrace_351230
  have hstable : (prefixWord ++ tailWord_351230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351230).length < 2 ^ (prefixWord ++ tailWord_351230).sum := by decide
  have hdescent : baseEnd_351230 < baseStart_351230 := by decide
  rcases family_descends (prefixWord ++ tailWord_351230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351243 : List Nat := [1, 1, 1, 1, 6, 2, 4, 1, 1, 1, 4]
def baseStart_351243 : Nat := 118140960795 + 351243 * 2 ^ 59
def prefixEnd_351243 : Nat := 4983230072969 + 3 ^ 40 * 351243 * 2
def baseEnd_351243 : Nat := 180356485527274493847169

theorem tailTrace_351243 : CollatzResearch.WordTrace tailWord_351243 prefixEnd_351243 180356485527274493847169 := by
  unfold tailWord_351243
  simp only [CollatzResearch.WordTrace]
  refine ⟨12810884666514073373658383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8540589777676048915772255 12810884666514073373658383)
  ·
    refine ⟨19216326999771110060487575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12810884666514073373658383 19216326999771110060487575)
    ·
      refine ⟨28824490499656665090731363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19216326999771110060487575 28824490499656665090731363)
      ·
        refine ⟨43236735749484997636097045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28824490499656665090731363 43236735749484997636097045)
        ·
          refine ⟨2026721988257109264192049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43236735749484997636097045 2026721988257109264192049)
          ·
            refine ⟨1520041491192831948144037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2026721988257109264192049 1520041491192831948144037)
            ·
              refine ⟨285007779598655990277007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1520041491192831948144037 285007779598655990277007)
              ·
                refine ⟨427511669397983985415511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285007779598655990277007 427511669397983985415511)
                ·
                  refine ⟨641267504096975978123267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427511669397983985415511 641267504096975978123267)
                  ·
                    refine ⟨961901256145463967184901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 641267504096975978123267 961901256145463967184901)
                    ·
                      refine ⟨180356485527274493847169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 961901256145463967184901 180356485527274493847169)
                      ·
                        rfl

theorem cell23_351243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 1, 1, 4].length) (baseStart_351243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351243 prefixEnd_351243 := by exact prefixLift 351243
  have htrace : WordTrace (prefixWord ++ tailWord_351243) baseStart_351243 baseEnd_351243 := by
    simpa [prefixWord, tailWord_351243, baseEnd_351243] using wordTrace_append hprefix tailTrace_351243
  have hstable : (prefixWord ++ tailWord_351243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351243).length < 2 ^ (prefixWord ++ tailWord_351243).sum := by decide
  have hdescent : baseEnd_351243 < baseStart_351243 := by decide
  rcases family_descends (prefixWord ++ tailWord_351243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351253 : List Nat := [1, 3, 2, 1, 4, 1, 3, 2, 2, 4]
def baseStart_351253 : Nat := 118140960795 + 351253 * 2 ^ 59
def prefixEnd_351253 : Nat := 4983230072969 + 3 ^ 40 * 351253 * 2
def baseEnd_351253 : Nat := 60120540111273151574041

theorem tailTrace_351253 : CollatzResearch.WordTrace tailWord_351253 prefixEnd_351253 60120540111273151574041 := by
  unfold tailWord_351253
  simp only [CollatzResearch.WordTrace]
  refine ⟨12811249396477845081522413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8540832930985230054348275 12811249396477845081522413)
  ·
    refine ⟨4804218523679191905570905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12811249396477845081522413 4804218523679191905570905)
    ·
      refine ⟨3603163892759393929178179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4804218523679191905570905 3603163892759393929178179)
      ·
        refine ⟨5404745839139090893767269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3603163892759393929178179 5404745839139090893767269)
        ·
          refine ⟨1013389844838579542581363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5404745839139090893767269 1013389844838579542581363)
          ·
            refine ⟨1520084767257869313872045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013389844838579542581363 1520084767257869313872045)
            ·
              refine ⟨570031787721700992702017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1520084767257869313872045 570031787721700992702017)
              ·
                refine ⟨427523840791275744526513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570031787721700992702017 427523840791275744526513)
                ·
                  refine ⟨320642880593456808394885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427523840791275744526513 320642880593456808394885)
                  ·
                    refine ⟨60120540111273151574041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 320642880593456808394885 60120540111273151574041)
                    ·
                      rfl

theorem cell23_351253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_351253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351253 prefixEnd_351253 := by exact prefixLift 351253
  have htrace : WordTrace (prefixWord ++ tailWord_351253) baseStart_351253 baseEnd_351253 := by
    simpa [prefixWord, tailWord_351253, baseEnd_351253] using wordTrace_append hprefix tailTrace_351253
  have hstable : (prefixWord ++ tailWord_351253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351253).length < 2 ^ (prefixWord ++ tailWord_351253).sum := by decide
  have hdescent : baseEnd_351253 < baseStart_351253 := by decide
  rcases family_descends (prefixWord ++ tailWord_351253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351293 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_351293 : Nat := 118140960795 + 351293 * 2 ^ 59
def prefixEnd_351293 : Nat := 4983230072969 + 3 ^ 40 * 351293 * 2
def baseEnd_351293 : Nat := 180382159559999298221939

theorem tailTrace_351293 : CollatzResearch.WordTrace tailWord_351293 prefixEnd_351293 180382159559999298221939 := by
  unfold tailWord_351293
  simp only [CollatzResearch.WordTrace]
  refine ⟨12812708316332931912978533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8541805544221954608652355 12812708316332931912978533)
  ·
    refine ⟨2402382809312424733683475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12812708316332931912978533 2402382809312424733683475)
    ·
      refine ⟨3603574213968637100525213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2402382809312424733683475 3603574213968637100525213)
      ·
        refine ⟨1351340330238238912696955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3603574213968637100525213 1351340330238238912696955)
        ·
          refine ⟨2027010495357358369045433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351340330238238912696955 2027010495357358369045433)
          ·
            refine ⟨1520257871518018776784075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2027010495357358369045433 1520257871518018776784075)
            ·
              refine ⟨2280386807277028165176113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520257871518018776784075 2280386807277028165176113)
              ·
                refine ⟨1710290105457771123882085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2280386807277028165176113 1710290105457771123882085)
                ·
                  refine ⟨320679394773332085727891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1710290105457771123882085 320679394773332085727891)
                  ·
                    refine ⟨481019092159998128591837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 320679394773332085727891 481019092159998128591837)
                    ·
                      refine ⟨180382159559999298221939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 481019092159998128591837 180382159559999298221939)
                      ·
                        rfl

theorem cell23_351293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_351293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351293 prefixEnd_351293 := by exact prefixLift 351293
  have htrace : WordTrace (prefixWord ++ tailWord_351293) baseStart_351293 baseEnd_351293 := by
    simpa [prefixWord, tailWord_351293, baseEnd_351293] using wordTrace_append hprefix tailTrace_351293
  have hstable : (prefixWord ++ tailWord_351293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351293).length < 2 ^ (prefixWord ++ tailWord_351293).sum := by decide
  have hdescent : baseEnd_351293 < baseStart_351293 := by decide
  rcases family_descends (prefixWord ++ tailWord_351293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351294 : List Nat := [4, 2, 1, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_351294 : Nat := 118140960795 + 351294 * 2 ^ 59
def prefixEnd_351294 : Nat := 4983230072969 + 3 ^ 40 * 351294 * 2
def baseEnd_351294 : Nat := 180382673040653794309435

theorem tailTrace_351294 : CollatzResearch.WordTrace tailWord_351294 prefixEnd_351294 180382673040653794309435 := by
  unfold tailWord_351294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601593098666163635470617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8541829859552872722509957 1601593098666163635470617)
  ·
    refine ⟨1201194823999622726602963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1601593098666163635470617 1201194823999622726602963)
    ·
      refine ⟨1801792235999434089904445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1201194823999622726602963 1801792235999434089904445)
      ·
        refine ⟨675672088499787783714167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1801792235999434089904445 675672088499787783714167)
        ·
          refine ⟨1013508132749681675571251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675672088499787783714167 1013508132749681675571251)
          ·
            refine ⟨1520262199124522513356877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013508132749681675571251 1520262199124522513356877)
            ·
              refine ⟨570098324671695942508829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1520262199124522513356877 570098324671695942508829)
              ·
                refine ⟨213786871751885978440811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570098324671695942508829 213786871751885978440811)
                ·
                  refine ⟨320680307627828967661217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213786871751885978440811 320680307627828967661217)
                  ·
                    refine ⟨240510230720871725745913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 320680307627828967661217 240510230720871725745913)
                    ·
                      refine ⟨180382673040653794309435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 240510230720871725745913 180382673040653794309435)
                      ·
                        rfl

theorem cell23_351294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_351294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351294 prefixEnd_351294 := by exact prefixLift 351294
  have htrace : WordTrace (prefixWord ++ tailWord_351294) baseStart_351294 baseEnd_351294 := by
    simpa [prefixWord, tailWord_351294, baseEnd_351294] using wordTrace_append hprefix tailTrace_351294
  have hstable : (prefixWord ++ tailWord_351294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351294).length < 2 ^ (prefixWord ++ tailWord_351294).sum := by decide
  have hdescent : baseEnd_351294 < baseStart_351294 := by decide
  rcases family_descends (prefixWord ++ tailWord_351294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351319 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_351319 : Nat := 118140960795 + 351319 * 2 ^ 59
def prefixEnd_351319 : Nat := 4983230072969 + 3 ^ 40 * 351319 * 2
def baseEnd_351319 : Nat := 180395510057016196496819

theorem tailTrace_351319 : CollatzResearch.WordTrace tailWord_351319 prefixEnd_351319 180395510057016196496819 := by
  unfold tailWord_351319
  simp only [CollatzResearch.WordTrace]
  refine ⟨12813656614238738353425011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8542437742825825568950007 12813656614238738353425011)
  ·
    refine ⟨19220484921358107530137517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12813656614238738353425011 19220484921358107530137517)
    ·
      refine ⟨7207681845509290323801569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19220484921358107530137517 7207681845509290323801569)
      ·
        refine ⟨5405761384131967742851177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7207681845509290323801569 5405761384131967742851177)
        ·
          refine ⟨4054321038098975807138383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5405761384131967742851177 4054321038098975807138383)
          ·
            refine ⟨6081481557148463710707575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4054321038098975807138383 6081481557148463710707575)
            ·
              refine ⟨9122222335722695566061363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6081481557148463710707575 9122222335722695566061363)
              ·
                refine ⟨13683333503584043349092045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9122222335722695566061363 13683333503584043349092045)
                ·
                  refine ⟨5131250063844016255909517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13683333503584043349092045 5131250063844016255909517)
                  ·
                    refine ⟨1924218773941506095966069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5131250063844016255909517 1924218773941506095966069)
                    ·
                      refine ⟨180395510057016196496819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1924218773941506095966069 180395510057016196496819)
                      ·
                        rfl

theorem cell23_351319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_351319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351319 prefixEnd_351319 := by exact prefixLift 351319
  have htrace : WordTrace (prefixWord ++ tailWord_351319) baseStart_351319 baseEnd_351319 := by
    simpa [prefixWord, tailWord_351319, baseEnd_351319] using wordTrace_append hprefix tailTrace_351319
  have hstable : (prefixWord ++ tailWord_351319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351319).length < 2 ^ (prefixWord ++ tailWord_351319).sum := by decide
  have hdescent : baseEnd_351319 < baseStart_351319 := by decide
  rcases family_descends (prefixWord ++ tailWord_351319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351333 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 1, 4, 2]
def baseStart_351333 : Nat := 118140960795 + 351333 * 2 ^ 59
def prefixEnd_351333 : Nat := 4983230072969 + 3 ^ 40 * 351333 * 2
def baseEnd_351333 : Nat := 180402698786179141721755

theorem tailTrace_351333 : CollatzResearch.WordTrace tailWord_351333 prefixEnd_351333 180402698786179141721755 := by
  unfold tailWord_351333
  simp only [CollatzResearch.WordTrace]
  refine ⟨12814167236188018744434653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8542778157458679162956435 12814167236188018744434653)
  ·
    refine ⟨4805312713570507029162995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12814167236188018744434653 4805312713570507029162995)
    ·
      refine ⟨7207969070355760543744493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4805312713570507029162995 7207969070355760543744493)
      ·
        refine ⟨2702988401383410203904185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7207969070355760543744493 2702988401383410203904185)
        ·
          refine ⟨2027241301037557652928139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2702988401383410203904185 2027241301037557652928139)
          ·
            refine ⟨3040861951556336479392209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027241301037557652928139 3040861951556336479392209)
            ·
              refine ⟨2280646463667252359544157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3040861951556336479392209 2280646463667252359544157)
              ·
                refine ⟨855242423875219634829059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2280646463667252359544157 855242423875219634829059)
                ·
                  refine ⟨1282863635812829452243589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855242423875219634829059 1282863635812829452243589)
                  ·
                    refine ⟨240536931714905522295673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1282863635812829452243589 240536931714905522295673)
                    ·
                      refine ⟨180402698786179141721755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 240536931714905522295673 180402698786179141721755)
                      ·
                        rfl

theorem cell23_351333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_351333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351333 prefixEnd_351333 := by exact prefixLift 351333
  have htrace : WordTrace (prefixWord ++ tailWord_351333) baseStart_351333 baseEnd_351333 := by
    simpa [prefixWord, tailWord_351333, baseEnd_351333] using wordTrace_append hprefix tailTrace_351333
  have hstable : (prefixWord ++ tailWord_351333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351333).length < 2 ^ (prefixWord ++ tailWord_351333).sum := by decide
  have hdescent : baseEnd_351333 < baseStart_351333 := by decide
  rcases family_descends (prefixWord ++ tailWord_351333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351350 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_351350 : Nat := 118140960795 + 351350 * 2 ^ 59
def prefixEnd_351350 : Nat := 4983230072969 + 3 ^ 40 * 351350 * 2
def baseEnd_351350 : Nat := 180411427957305575209177

theorem tailTrace_351350 : CollatzResearch.WordTrace tailWord_351350 prefixEnd_351350 180411427957305575209177 := by
  unfold tailWord_351350
  simp only [CollatzResearch.WordTrace]
  refine ⟨800924204820401915487719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8543191518084287098535669 800924204820401915487719)
  ·
    refine ⟨1201386307230602873231579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 800924204820401915487719 1201386307230602873231579)
    ·
      refine ⟨1802079460845904309847369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1201386307230602873231579 1802079460845904309847369)
      ·
        refine ⟨1351559595634428232385527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1802079460845904309847369 1351559595634428232385527)
        ·
          refine ⟨2027339393451642348578291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351559595634428232385527 2027339393451642348578291)
          ·
            refine ⟨3041009090177463522867437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027339393451642348578291 3041009090177463522867437)
            ·
              refine ⟨1140378408816548821075289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3041009090177463522867437 1140378408816548821075289)
              ·
                refine ⟨855283806612411615806467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1140378408816548821075289 855283806612411615806467)
                ·
                  refine ⟨1282925709918617423709701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855283806612411615806467 1282925709918617423709701)
                  ·
                    refine ⟨240548570609740766945569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1282925709918617423709701 240548570609740766945569)
                    ·
                      refine ⟨180411427957305575209177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 240548570609740766945569 180411427957305575209177)
                      ·
                        rfl

theorem cell23_351350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_351350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351350 prefixEnd_351350 := by exact prefixLift 351350
  have htrace : WordTrace (prefixWord ++ tailWord_351350) baseStart_351350 baseEnd_351350 := by
    simpa [prefixWord, tailWord_351350, baseEnd_351350] using wordTrace_append hprefix tailTrace_351350
  have hstable : (prefixWord ++ tailWord_351350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351350).length < 2 ^ (prefixWord ++ tailWord_351350).sum := by decide
  have hdescent : baseEnd_351350 < baseStart_351350 := by decide
  rcases family_descends (prefixWord ++ tailWord_351350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351383 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 3]
def baseStart_351383 : Nat := 118140960795 + 351383 * 2 ^ 59
def prefixEnd_351383 : Nat := 4983230072969 + 3 ^ 40 * 351383 * 2
def baseEnd_351383 : Nat := 180428372818903946096525

theorem tailTrace_351383 : CollatzResearch.WordTrace tailWord_351383 prefixEnd_351383 180428372818903946096525 := by
  unfold tailWord_351383
  simp only [CollatzResearch.WordTrace]
  refine ⟨12815990886006877283754803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8543993924004584855836535 12815990886006877283754803)
  ·
    refine ⟨19223986329010315925632205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12815990886006877283754803 19223986329010315925632205)
    ·
      refine ⟨7208994873378868472112077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19223986329010315925632205 7208994873378868472112077)
      ·
        refine ⟨2703373077517075677042029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7208994873378868472112077 2703373077517075677042029)
        ·
          refine ⟨1013764904068903378890761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2703373077517075677042029 1013764904068903378890761)
          ·
            refine ⟨760323678051677534168071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1013764904068903378890761 760323678051677534168071)
            ·
              refine ⟨1140485517077516301252107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760323678051677534168071 1140485517077516301252107)
              ·
                refine ⟨1710728275616274451878161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140485517077516301252107 1710728275616274451878161)
                ·
                  refine ⟨1283046206712205838908621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710728275616274451878161 1283046206712205838908621)
                  ·
                    refine ⟨481142327517077189590733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1283046206712205838908621 481142327517077189590733)
                    ·
                      refine ⟨180428372818903946096525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 481142327517077189590733 180428372818903946096525)
                      ·
                        rfl

theorem cell23_351383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_351383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351383 prefixEnd_351383 := by exact prefixLift 351383
  have htrace : WordTrace (prefixWord ++ tailWord_351383) baseStart_351383 baseEnd_351383 := by
    simpa [prefixWord, tailWord_351383, baseEnd_351383] using wordTrace_append hprefix tailTrace_351383
  have hstable : (prefixWord ++ tailWord_351383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351383).length < 2 ^ (prefixWord ++ tailWord_351383).sum := by decide
  have hdescent : baseEnd_351383 < baseStart_351383 := by decide
  rcases family_descends (prefixWord ++ tailWord_351383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351393 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 2, 5, 2]
def baseStart_351393 : Nat := 118140960795 + 351393 * 2 ^ 59
def prefixEnd_351393 : Nat := 4983230072969 + 3 ^ 40 * 351393 * 2
def baseEnd_351393 : Nat := 180433507625448906971479

theorem tailTrace_351393 : CollatzResearch.WordTrace tailWord_351393 prefixEnd_351393 180433507625448906971479 := by
  unfold tailWord_351393
  simp only [CollatzResearch.WordTrace]
  refine ⟨12816355615970648991618833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8544237077313765994412555 12816355615970648991618833)
  ·
    refine ⟨9612266711977986743714125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12816355615970648991618833 9612266711977986743714125)
    ·
      refine ⟨3604600016991745028892797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9612266711977986743714125 3604600016991745028892797)
      ·
        refine ⟨1351725006371904385834799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3604600016991745028892797 1351725006371904385834799)
        ·
          refine ⟨2027587509557856578752199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351725006371904385834799 2027587509557856578752199)
          ·
            refine ⟨3041381264336784868128299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027587509557856578752199 3041381264336784868128299)
            ·
              refine ⟨4562071896505177302192449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041381264336784868128299 4562071896505177302192449)
              ·
                refine ⟨3421553922378882976644337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4562071896505177302192449 3421553922378882976644337)
                ·
                  refine ⟨2566165441784162232483253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3421553922378882976644337 2566165441784162232483253)
                  ·
                    refine ⟨240578010167265209295305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2566165441784162232483253 240578010167265209295305)
                    ·
                      refine ⟨180433507625448906971479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 240578010167265209295305 180433507625448906971479)
                      ·
                        rfl

theorem cell23_351393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_351393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351393 prefixEnd_351393 := by exact prefixLift 351393
  have htrace : WordTrace (prefixWord ++ tailWord_351393) baseStart_351393 baseEnd_351393 := by
    simpa [prefixWord, tailWord_351393, baseEnd_351393] using wordTrace_append hprefix tailTrace_351393
  have hstable : (prefixWord ++ tailWord_351393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351393).length < 2 ^ (prefixWord ++ tailWord_351393).sum := by decide
  have hdescent : baseEnd_351393 < baseStart_351393 := by decide
  rcases family_descends (prefixWord ++ tailWord_351393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351423 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 2, 4, 2]
def baseStart_351423 : Nat := 118140960795 + 351423 * 2 ^ 59
def prefixEnd_351423 : Nat := 4983230072969 + 3 ^ 40 * 351423 * 2
def baseEnd_351423 : Nat := 180448912045083789596341

theorem tailTrace_351423 : CollatzResearch.WordTrace tailWord_351423 prefixEnd_351423 180448912045083789596341 := by
  unfold tailWord_351423
  simp only [CollatzResearch.WordTrace]
  refine ⟨12817449805861964115210923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8544966537241309410140615 12817449805861964115210923)
  ·
    refine ⟨19226174708792946172816385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12817449805861964115210923 19226174708792946172816385)
    ·
      refine ⟨14419631031594709629612289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19226174708792946172816385 14419631031594709629612289)
      ·
        refine ⟨10814723273696032222209217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14419631031594709629612289 10814723273696032222209217)
        ·
          refine ⟨8111042455272024166656913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10814723273696032222209217 8111042455272024166656913)
          ·
            refine ⟨6083281841454018124992685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8111042455272024166656913 6083281841454018124992685)
            ·
              refine ⟨2281230690545256796872257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6083281841454018124992685 2281230690545256796872257)
              ·
                refine ⟨1710923017908942597654193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281230690545256796872257 1710923017908942597654193)
                ·
                  refine ⟨1283192263431706948240645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710923017908942597654193 1283192263431706948240645)
                  ·
                    refine ⟨240598549393445052795121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1283192263431706948240645 240598549393445052795121)
                    ·
                      refine ⟨180448912045083789596341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 240598549393445052795121 180448912045083789596341)
                      ·
                        rfl

theorem cell23_351423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 4, 2].length) (baseStart_351423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351423 prefixEnd_351423 := by exact prefixLift 351423
  have htrace : WordTrace (prefixWord ++ tailWord_351423) baseStart_351423 baseEnd_351423 := by
    simpa [prefixWord, tailWord_351423, baseEnd_351423] using wordTrace_append hprefix tailTrace_351423
  have hstable : (prefixWord ++ tailWord_351423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351423).length < 2 ^ (prefixWord ++ tailWord_351423).sum := by decide
  have hdescent : baseEnd_351423 < baseStart_351423 := by decide
  rcases family_descends (prefixWord ++ tailWord_351423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351467 : List Nat := [1, 1, 1, 1, 2, 8, 1, 3, 1, 4]
def baseStart_351467 : Nat := 118140960795 + 351467 * 2 ^ 59
def prefixEnd_351467 : Nat := 4983230072969 + 3 ^ 40 * 351467 * 2
def baseEnd_351467 : Nat := 60157168397960539148713

theorem tailTrace_351467 : CollatzResearch.WordTrace tailWord_351467 prefixEnd_351467 60157168397960539148713 := by
  unfold tailWord_351467
  simp only [CollatzResearch.WordTrace]
  refine ⟨12819054617702559629812655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8546036411801706419875103 12819054617702559629812655)
  ·
    refine ⟨19228581926553839444718983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12819054617702559629812655 19228581926553839444718983)
    ·
      refine ⟨28842872889830759167078475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19228581926553839444718983 28842872889830759167078475)
      ·
        refine ⟨43264309334746138750617713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28842872889830759167078475 43264309334746138750617713)
        ·
          refine ⟨32448232001059604062963285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43264309334746138750617713 32448232001059604062963285)
          ·
            refine ⟨380252718762417235112851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 32448232001059604062963285 380252718762417235112851)
            ·
              refine ⟨570379078143625852669277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380252718762417235112851 570379078143625852669277)
              ·
                refine ⟨213892154303859694750979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570379078143625852669277 213892154303859694750979)
                ·
                  refine ⟨320838231455789542126469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213892154303859694750979 320838231455789542126469)
                  ·
                    refine ⟨60157168397960539148713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 320838231455789542126469 60157168397960539148713)
                    ·
                      rfl

theorem cell23_351467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 1, 4].length) (baseStart_351467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351467 prefixEnd_351467 := by exact prefixLift 351467
  have htrace : WordTrace (prefixWord ++ tailWord_351467) baseStart_351467 baseEnd_351467 := by
    simpa [prefixWord, tailWord_351467, baseEnd_351467] using wordTrace_append hprefix tailTrace_351467
  have hstable : (prefixWord ++ tailWord_351467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351467).length < 2 ^ (prefixWord ++ tailWord_351467).sum := by decide
  have hdescent : baseEnd_351467 < baseStart_351467 := by decide
  rcases family_descends (prefixWord ++ tailWord_351467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351484 : List Nat := [2, 2, 2, 1, 5, 1, 3, 2, 1, 4]
def baseStart_351484 : Nat := 118140960795 + 351484 * 2 ^ 59
def prefixEnd_351484 : Nat := 4983230072969 + 3 ^ 40 * 351484 * 2
def baseEnd_351484 : Nat := 60160078121669350311187

theorem tailTrace_351484 : CollatzResearch.WordTrace tailWord_351484 prefixEnd_351484 60160078121669350311187 := by
  unfold tailWord_351484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6409837329320485766590753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8546449772427314355454337 6409837329320485766590753)
  ·
    refine ⟨4807377996990364324943065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6409837329320485766590753 4807377996990364324943065)
    ·
      refine ⟨3605533497742773243707299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4807377996990364324943065 3605533497742773243707299)
      ·
        refine ⟨5408300246614159865560949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605533497742773243707299 5408300246614159865560949)
        ·
          refine ⟨507028148120077487396339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5408300246614159865560949 507028148120077487396339)
          ·
            refine ⟨760542222180116231094509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507028148120077487396339 760542222180116231094509)
            ·
              refine ⟨285203333317543586660441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 760542222180116231094509 285203333317543586660441)
              ·
                refine ⟨213902499988157689995331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285203333317543586660441 213902499988157689995331)
                ·
                  refine ⟨320853749982236534992997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213902499988157689995331 320853749982236534992997)
                  ·
                    refine ⟨60160078121669350311187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 320853749982236534992997 60160078121669350311187)
                    ·
                      rfl

theorem cell23_351484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_351484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351484 prefixEnd_351484 := by exact prefixLift 351484
  have htrace : WordTrace (prefixWord ++ tailWord_351484) baseStart_351484 baseEnd_351484 := by
    simpa [prefixWord, tailWord_351484, baseEnd_351484] using wordTrace_append hprefix tailTrace_351484
  have hstable : (prefixWord ++ tailWord_351484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351484).length < 2 ^ (prefixWord ++ tailWord_351484).sum := by decide
  have hdescent : baseEnd_351484 < baseStart_351484 := by decide
  rcases family_descends (prefixWord ++ tailWord_351484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351517 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_351517 : Nat := 118140960795 + 351517 * 2 ^ 59
def prefixEnd_351517 : Nat := 4983230072969 + 3 ^ 40 * 351517 * 2
def baseEnd_351517 : Nat := 180497179226606421820909

theorem tailTrace_351517 : CollatzResearch.WordTrace tailWord_351517 prefixEnd_351517 180497179226606421820909 := by
  unfold tailWord_351517
  simp only [CollatzResearch.WordTrace]
  refine ⟨12820878267521418169132805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8547252178347612112755203 12820878267521418169132805)
  ·
    refine ⟨2403914675160265906712401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12820878267521418169132805 2403914675160265906712401)
    ·
      refine ⟨1802936006370199430034301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2403914675160265906712401 1802936006370199430034301)
      ·
        refine ⟨676101002388824786262863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1802936006370199430034301 676101002388824786262863)
        ·
          refine ⟨1014151503583237179394295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676101002388824786262863 1014151503583237179394295)
          ·
            refine ⟨1521227255374855769091443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014151503583237179394295 1521227255374855769091443)
            ·
              refine ⟨2281840883062283653637165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521227255374855769091443 2281840883062283653637165)
              ·
                refine ⟨855690331148356370113937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2281840883062283653637165 855690331148356370113937)
                ·
                  refine ⟨641767748361267277585453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 855690331148356370113937 641767748361267277585453)
                  ·
                    refine ⟨240662905635475229094545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 641767748361267277585453 240662905635475229094545)
                    ·
                      refine ⟨180497179226606421820909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 240662905635475229094545 180497179226606421820909)
                      ·
                        rfl

theorem cell23_351517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_351517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351517 prefixEnd_351517 := by exact prefixLift 351517
  have htrace : WordTrace (prefixWord ++ tailWord_351517) baseStart_351517 baseEnd_351517 := by
    simpa [prefixWord, tailWord_351517, baseEnd_351517] using wordTrace_append hprefix tailTrace_351517
  have hstable : (prefixWord ++ tailWord_351517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351517).length < 2 ^ (prefixWord ++ tailWord_351517).sum := by decide
  have hdescent : baseEnd_351517 < baseStart_351517 := by decide
  rcases family_descends (prefixWord ++ tailWord_351517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351523 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 1, 6]
def baseStart_351523 : Nat := 118140960795 + 351523 * 2 ^ 59
def prefixEnd_351523 : Nat := 4983230072969 + 3 ^ 40 * 351523 * 2
def baseEnd_351523 : Nat := 60166753370177799448627

theorem tailTrace_351523 : CollatzResearch.WordTrace tailWord_351523 prefixEnd_351523 60166753370177799448627 := by
  unfold tailWord_351523
  simp only [CollatzResearch.WordTrace]
  refine ⟨12821097105499681193851223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8547398070333120795900815 12821097105499681193851223)
  ·
    refine ⟨19231645658249521790776835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12821097105499681193851223 19231645658249521790776835)
    ·
      refine ⟨28847468487374282686165253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19231645658249521790776835 28847468487374282686165253)
      ·
        refine ⟨5408900341382678003655985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28847468487374282686165253 5408900341382678003655985)
        ·
          refine ⟨4056675256037008502741989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5408900341382678003655985 4056675256037008502741989)
          ·
            refine ⟨760626610506939094264123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4056675256037008502741989 760626610506939094264123)
            ·
              refine ⟨1140939915760408641396185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760626610506939094264123 1140939915760408641396185)
              ·
                refine ⟨855704936820306481047139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1140939915760408641396185 855704936820306481047139)
                ·
                  refine ⟨1283557405230459721570709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855704936820306481047139 1283557405230459721570709)
                  ·
                    refine ⟨60166753370177799448627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1283557405230459721570709 60166753370177799448627)
                    ·
                      rfl

theorem cell23_351523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 6].length) (baseStart_351523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351523 prefixEnd_351523 := by exact prefixLift 351523
  have htrace : WordTrace (prefixWord ++ tailWord_351523) baseStart_351523 baseEnd_351523 := by
    simpa [prefixWord, tailWord_351523, baseEnd_351523] using wordTrace_append hprefix tailTrace_351523
  have hstable : (prefixWord ++ tailWord_351523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351523).length < 2 ^ (prefixWord ++ tailWord_351523).sum := by decide
  have hdescent : baseEnd_351523 < baseStart_351523 := by decide
  rcases family_descends (prefixWord ++ tailWord_351523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351541 : List Nat := [1, 3, 3, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_351541 : Nat := 118140960795 + 351541 * 2 ^ 59
def prefixEnd_351541 : Nat := 4983230072969 + 3 ^ 40 * 351541 * 2
def baseEnd_351541 : Nat := 180509502762314327920799

theorem tailTrace_351541 : CollatzResearch.WordTrace tailWord_351541 prefixEnd_351541 180509502762314327920799 := by
  unfold tailWord_351541
  simp only [CollatzResearch.WordTrace]
  refine ⟨12821753619434470268006477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8547835746289646845337651 12821753619434470268006477)
  ·
    refine ⟨4808157607287926350502429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12821753619434470268006477 4808157607287926350502429)
    ·
      refine ⟨1803059102732972381438411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4808157607287926350502429 1803059102732972381438411)
      ·
        refine ⟨2704588654099458572157617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803059102732972381438411 2704588654099458572157617)
        ·
          refine ⟨2028441490574593929118213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2704588654099458572157617 2028441490574593929118213)
          ·
            refine ⟨380332779482736361709665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2028441490574593929118213 380332779482736361709665)
            ·
              refine ⟨285249584612052271282249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380332779482736361709665 285249584612052271282249)
              ·
                refine ⟨213937188459039203461687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285249584612052271282249 213937188459039203461687)
                ·
                  refine ⟨320905782688558805192531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213937188459039203461687 320905782688558805192531)
                  ·
                    refine ⟨481358674032838207788797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 320905782688558805192531 481358674032838207788797)
                    ·
                      refine ⟨180509502762314327920799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 481358674032838207788797 180509502762314327920799)
                      ·
                        rfl

theorem cell23_351541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_351541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351541 prefixEnd_351541 := by exact prefixLift 351541
  have htrace : WordTrace (prefixWord ++ tailWord_351541) baseStart_351541 baseEnd_351541 := by
    simpa [prefixWord, tailWord_351541, baseEnd_351541] using wordTrace_append hprefix tailTrace_351541
  have hstable : (prefixWord ++ tailWord_351541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351541).length < 2 ^ (prefixWord ++ tailWord_351541).sum := by decide
  have hdescent : baseEnd_351541 < baseStart_351541 := by decide
  rcases family_descends (prefixWord ++ tailWord_351541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351550 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_351550 : Nat := 118140960795 + 351550 * 2 ^ 59
def prefixEnd_351550 : Nat := 4983230072969 + 3 ^ 40 * 351550 * 2
def baseEnd_351550 : Nat := 180514124088204792708257

theorem tailTrace_351550 : CollatzResearch.WordTrace tailWord_351550 prefixEnd_351550 180514124088204792708257 := by
  unfold tailWord_351550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1602760234550233100635513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8548054584267909870056069 1602760234550233100635513)
  ·
    refine ⟨1202070175912674825476635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1602760234550233100635513 1202070175912674825476635)
    ·
      refine ⟨1803105263869012238214953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1202070175912674825476635 1803105263869012238214953)
      ·
        refine ⟨1352328947901759178661215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1803105263869012238214953 1352328947901759178661215)
        ·
          refine ⟨2028493421852638767991823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352328947901759178661215 2028493421852638767991823)
          ·
            refine ⟨3042740132778958151987735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028493421852638767991823 3042740132778958151987735)
            ·
              refine ⟨4564110199168437227981603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3042740132778958151987735 4564110199168437227981603)
              ·
                refine ⟨6846165298752655841972405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4564110199168437227981603 6846165298752655841972405)
                ·
                  refine ⟨641827996758061485184913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6846165298752655841972405 641827996758061485184913)
                  ·
                    refine ⟨481370997568546113888685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 641827996758061485184913 481370997568546113888685)
                    ·
                      refine ⟨180514124088204792708257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 481370997568546113888685 180514124088204792708257)
                      ·
                        rfl

theorem cell23_351550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_351550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351550 prefixEnd_351550 := by exact prefixLift 351550
  have htrace : WordTrace (prefixWord ++ tailWord_351550) baseStart_351550 baseEnd_351550 := by
    simpa [prefixWord, tailWord_351550, baseEnd_351550] using wordTrace_append hprefix tailTrace_351550
  have hstable : (prefixWord ++ tailWord_351550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351550).length < 2 ^ (prefixWord ++ tailWord_351550).sum := by decide
  have hdescent : baseEnd_351550 < baseStart_351550 := by decide
  rcases family_descends (prefixWord ++ tailWord_351550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351581 : List Nat := [1, 4, 5, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_351581 : Nat := 118140960795 + 351581 * 2 ^ 59
def prefixEnd_351581 : Nat := 4983230072969 + 3 ^ 40 * 351581 * 2
def baseEnd_351581 : Nat := 180530041988494171420615

theorem tailTrace_351581 : CollatzResearch.WordTrace tailWord_351581 prefixEnd_351581 180530041988494171420615 := by
  unfold tailWord_351581
  simp only [CollatzResearch.WordTrace]
  refine ⟨12823212539289557099462597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8548808359526371399641731 12823212539289557099462597)
  ·
    refine ⟨2404352351116791956149237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12823212539289557099462597 2404352351116791956149237)
    ·
      refine ⟨225408032917199245888991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2404352351116791956149237 225408032917199245888991)
      ·
        refine ⟨338112049375798868833487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225408032917199245888991 338112049375798868833487)
        ·
          refine ⟨507168074063698303250231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338112049375798868833487 507168074063698303250231)
          ·
            refine ⟨760752111095547454875347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507168074063698303250231 760752111095547454875347)
            ·
              refine ⟨1141128166643321182313021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760752111095547454875347 1141128166643321182313021)
              ·
                refine ⟨427923062491245443367383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1141128166643321182313021 427923062491245443367383)
                ·
                  refine ⟨641884593736868165051075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427923062491245443367383 641884593736868165051075)
                  ·
                    refine ⟨962826890605302247576613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 641884593736868165051075 962826890605302247576613)
                    ·
                      refine ⟨180530041988494171420615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 962826890605302247576613 180530041988494171420615)
                      ·
                        rfl

theorem cell23_351581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_351581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351581 prefixEnd_351581 := by exact prefixLift 351581
  have htrace : WordTrace (prefixWord ++ tailWord_351581) baseStart_351581 baseEnd_351581 := by
    simpa [prefixWord, tailWord_351581, baseEnd_351581] using wordTrace_append hprefix tailTrace_351581
  have hstable : (prefixWord ++ tailWord_351581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351581).length < 2 ^ (prefixWord ++ tailWord_351581).sum := by decide
  have hdescent : baseEnd_351581 < baseStart_351581 := by decide
  rcases family_descends (prefixWord ++ tailWord_351581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351584 : List Nat := [2, 1, 1, 3, 4, 3, 2, 1, 1, 2, 3]
def baseStart_351584 : Nat := 118140960795 + 351584 * 2 ^ 59
def prefixEnd_351584 : Nat := 4983230072969 + 3 ^ 40 * 351584 * 2
def baseEnd_351584 : Nat := 180531582430457659683101

theorem tailTrace_351584 : CollatzResearch.WordTrace tailWord_351584 prefixEnd_351584 180531582430457659683101 := by
  unfold tailWord_351584
  simp only [CollatzResearch.WordTrace]
  refine ⟨6411660979139344305910903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8548881305519125741214537 6411660979139344305910903)
  ·
    refine ⟨9617491468709016458866355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6411660979139344305910903 9617491468709016458866355)
    ·
      refine ⟨14426237203063524688299533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9617491468709016458866355 14426237203063524688299533)
      ·
        refine ⟨5409838951148821758112325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14426237203063524688299533 5409838951148821758112325)
        ·
          refine ⟨1014344803340404079646061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5409838951148821758112325 1014344803340404079646061)
          ·
            refine ⟨380379301252651529867273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1014344803340404079646061 380379301252651529867273)
            ·
              refine ⟨285284475939488647400455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380379301252651529867273 285284475939488647400455)
              ·
                refine ⟨427926713909232971100683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285284475939488647400455 427926713909232971100683)
                ·
                  refine ⟨641890070863849456651025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427926713909232971100683 641890070863849456651025)
                  ·
                    refine ⟨481417553147887092488269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 641890070863849456651025 481417553147887092488269)
                    ·
                      refine ⟨180531582430457659683101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 481417553147887092488269 180531582430457659683101)
                      ·
                        rfl

theorem cell23_351584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_351584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351584 prefixEnd_351584 := by exact prefixLift 351584
  have htrace : WordTrace (prefixWord ++ tailWord_351584) baseStart_351584 baseEnd_351584 := by
    simpa [prefixWord, tailWord_351584, baseEnd_351584] using wordTrace_append hprefix tailTrace_351584
  have hstable : (prefixWord ++ tailWord_351584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351584).length < 2 ^ (prefixWord ++ tailWord_351584).sum := by decide
  have hdescent : baseEnd_351584 < baseStart_351584 := by decide
  rcases family_descends (prefixWord ++ tailWord_351584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351597 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_351597 : Nat := 118140960795 + 351597 * 2 ^ 59
def prefixEnd_351597 : Nat := 4983230072969 + 3 ^ 40 * 351597 * 2
def baseEnd_351597 : Nat := 180538257678966108820541

theorem tailTrace_351597 : CollatzResearch.WordTrace tailWord_351597 prefixEnd_351597 180538257678966108820541 := by
  unfold tailWord_351597
  simp only [CollatzResearch.WordTrace]
  refine ⟨12823796107231591832045045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8549197404821061221363363 12823796107231591832045045)
  ·
    refine ⟨1202230885052961734254223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12823796107231591832045045 1202230885052961734254223)
    ·
      refine ⟨1803346327579442601381335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1202230885052961734254223 1803346327579442601381335)
      ·
        refine ⟨2705019491369163902072003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803346327579442601381335 2705019491369163902072003)
        ·
          refine ⟨4057529237053745853108005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705019491369163902072003 4057529237053745853108005)
          ·
            refine ⟨760786731947577347457751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4057529237053745853108005 760786731947577347457751)
            ·
              refine ⟨1141180097921366021186627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760786731947577347457751 1141180097921366021186627)
              ·
                refine ⟨1711770146882049031779941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141180097921366021186627 1711770146882049031779941)
                ·
                  refine ⟨320956902540384193458739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1711770146882049031779941 320956902540384193458739)
                  ·
                    refine ⟨481435353810576290188109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 320956902540384193458739 481435353810576290188109)
                    ·
                      refine ⟨180538257678966108820541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 481435353810576290188109 180538257678966108820541)
                      ·
                        rfl

theorem cell23_351597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_351597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351597 prefixEnd_351597 := by exact prefixLift 351597
  have htrace : WordTrace (prefixWord ++ tailWord_351597) baseStart_351597 baseEnd_351597 := by
    simpa [prefixWord, tailWord_351597, baseEnd_351597] using wordTrace_append hprefix tailTrace_351597
  have hstable : (prefixWord ++ tailWord_351597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351597).length < 2 ^ (prefixWord ++ tailWord_351597).sum := by decide
  have hdescent : baseEnd_351597 < baseStart_351597 := by decide
  rcases family_descends (prefixWord ++ tailWord_351597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351613 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_351613 : Nat := 118140960795 + 351613 * 2 ^ 59
def prefixEnd_351613 : Nat := 4983230072969 + 3 ^ 40 * 351613 * 2
def baseEnd_351613 : Nat := 60182157789812682073489

theorem tailTrace_351613 : CollatzResearch.WordTrace tailWord_351613 prefixEnd_351613 60182157789812682073489 := by
  unfold tailWord_351613
  simp only [CollatzResearch.WordTrace]
  refine ⟨12824379675173626564627493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8549586450115751043084995 12824379675173626564627493)
  ·
    refine ⟨2404571189095054980867655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12824379675173626564627493 2404571189095054980867655)
    ·
      refine ⟨3606856783642582471301483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2404571189095054980867655 3606856783642582471301483)
      ·
        refine ⟨5410285175463873706952225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3606856783642582471301483 5410285175463873706952225)
        ·
          refine ⟨4057713881597905280214169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5410285175463873706952225 4057713881597905280214169)
          ·
            refine ⟨3043285411198428960160627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4057713881597905280214169 3043285411198428960160627)
            ·
              refine ⟨4564928116797643440240941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3043285411198428960160627 4564928116797643440240941)
              ·
                refine ⟨1711848043799116290090353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4564928116797643440240941 1711848043799116290090353)
                ·
                  refine ⟨1283886032849337217567765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1711848043799116290090353 1283886032849337217567765)
                  ·
                    refine ⟨60182157789812682073489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1283886032849337217567765 60182157789812682073489)
                    ·
                      rfl

theorem cell23_351613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_351613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351613 prefixEnd_351613 := by exact prefixLift 351613
  have htrace : WordTrace (prefixWord ++ tailWord_351613) baseStart_351613 baseEnd_351613 := by
    simpa [prefixWord, tailWord_351613, baseEnd_351613] using wordTrace_append hprefix tailTrace_351613
  have hstable : (prefixWord ++ tailWord_351613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351613).length < 2 ^ (prefixWord ++ tailWord_351613).sum := by decide
  have hdescent : baseEnd_351613 < baseStart_351613 := by decide
  rcases family_descends (prefixWord ++ tailWord_351613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351624 : List Nat := [2, 1, 3, 3, 1, 3, 2, 2, 1, 3, 2]
def baseStart_351624 : Nat := 118140960795 + 351624 * 2 ^ 59
def prefixEnd_351624 : Nat := 4983230072969 + 3 ^ 40 * 351624 * 2
def baseEnd_351624 : Nat := 180552121656637503182917

theorem tailTrace_351624 : CollatzResearch.WordTrace tailWord_351624 prefixEnd_351624 180552121656637503182917 := by
  unfold tailWord_351624
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412390439066887721638963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8549853918755850295518617 6412390439066887721638963)
  ·
    refine ⟨9618585658600331582458445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6412390439066887721638963 9618585658600331582458445)
    ·
      refine ⟨3606969621975124343421917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9618585658600331582458445 3606969621975124343421917)
      ·
        refine ⟨1352613608240671628783219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3606969621975124343421917 1352613608240671628783219)
        ·
          refine ⟨2028920412361007443174829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352613608240671628783219 2028920412361007443174829)
          ·
            refine ⟨760845154635377791190561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2028920412361007443174829 760845154635377791190561)
            ·
              refine ⟨570633865976533343392921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760845154635377791190561 570633865976533343392921)
              ·
                refine ⟨427975399482400007544691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570633865976533343392921 427975399482400007544691)
                ·
                  refine ⟨641963099223600011317037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427975399482400007544691 641963099223600011317037)
                  ·
                    refine ⟨240736162208850004243889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 641963099223600011317037 240736162208850004243889)
                    ·
                      refine ⟨180552121656637503182917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 240736162208850004243889 180552121656637503182917)
                      ·
                        rfl

theorem cell23_351624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_351624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351624 prefixEnd_351624 := by exact prefixLift 351624
  have htrace : WordTrace (prefixWord ++ tailWord_351624) baseStart_351624 baseEnd_351624 := by
    simpa [prefixWord, tailWord_351624, baseEnd_351624] using wordTrace_append hprefix tailTrace_351624
  have hstable : (prefixWord ++ tailWord_351624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351624).length < 2 ^ (prefixWord ++ tailWord_351624).sum := by decide
  have hdescent : baseEnd_351624 < baseStart_351624 := by decide
  rcases family_descends (prefixWord ++ tailWord_351624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351637 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 4, 2, 2]
def baseStart_351637 : Nat := 118140960795 + 351637 * 2 ^ 59
def prefixEnd_351637 : Nat := 4983230072969 + 3 ^ 40 * 351637 * 2
def baseEnd_351637 : Nat := 180558796905145952320357

theorem tailTrace_351637 : CollatzResearch.WordTrace tailWord_351637 prefixEnd_351637 180558796905145952320357 := by
  unfold tailWord_351637
  simp only [CollatzResearch.WordTrace]
  refine ⟨12825255027086678663501165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8550170018057785775667443 12825255027086678663501165)
  ·
    refine ⟨4809470635157504498812937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12825255027086678663501165 4809470635157504498812937)
    ·
      refine ⟨3607102976368128374109703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4809470635157504498812937 3607102976368128374109703)
      ·
        refine ⟨5410654464552192561164555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607102976368128374109703 5410654464552192561164555)
        ·
          refine ⟨8115981696828288841746833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5410654464552192561164555 8115981696828288841746833)
          ·
            refine ⟨6086986272621216631310125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8115981696828288841746833 6086986272621216631310125)
            ·
              refine ⟨2282619852232956236741297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6086986272621216631310125 2282619852232956236741297)
              ·
                refine ⟨1711964889174717177555973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2282619852232956236741297 1711964889174717177555973)
                ·
                  refine ⟨320993416720259470791745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1711964889174717177555973 320993416720259470791745)
                  ·
                    refine ⟨240745062540194603093809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 320993416720259470791745 240745062540194603093809)
                    ·
                      refine ⟨180558796905145952320357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 240745062540194603093809 180558796905145952320357)
                      ·
                        rfl

theorem cell23_351637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_351637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351637 prefixEnd_351637 := by exact prefixLift 351637
  have htrace : WordTrace (prefixWord ++ tailWord_351637) baseStart_351637 baseEnd_351637 := by
    simpa [prefixWord, tailWord_351637, baseEnd_351637] using wordTrace_append hprefix tailTrace_351637
  have hstable : (prefixWord ++ tailWord_351637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351637).length < 2 ^ (prefixWord ++ tailWord_351637).sum := by decide
  have hdescent : baseEnd_351637 < baseStart_351637 := by decide
  rcases family_descends (prefixWord ++ tailWord_351637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351660 : List Nat := [2, 2, 1, 1, 1, 1, 4, 6, 5]
def baseStart_351660 : Nat := 118140960795 + 351660 * 2 ^ 59
def prefixEnd_351660 : Nat := 4983230072969 + 3 ^ 40 * 351660 * 2
def baseEnd_351660 : Nat := 20063400773355484703639

theorem tailTrace_351660 : CollatzResearch.WordTrace tailWord_351660 prefixEnd_351660 20063400773355484703639 := by
  unfold tailWord_351660
  simp only [CollatzResearch.WordTrace]
  refine ⟨6413046953001676795794217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8550729270668902394392289 6413046953001676795794217)
  ·
    refine ⟨4809785214751257596845663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6413046953001676795794217 4809785214751257596845663)
    ·
      refine ⟨7214677822126886395268495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4809785214751257596845663 7214677822126886395268495)
      ·
        refine ⟨10822016733190329592902743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7214677822126886395268495 10822016733190329592902743)
        ·
          refine ⟨16233025099785494389354115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10822016733190329592902743 16233025099785494389354115)
          ·
            refine ⟨24349537649678241584031173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16233025099785494389354115 24349537649678241584031173)
            ·
              refine ⟨4565538309314670297005845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24349537649678241584031173 4565538309314670297005845)
              ·
                refine ⟨214009608249125170172149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4565538309314670297005845 214009608249125170172149)
                ·
                  refine ⟨20063400773355484703639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 214009608249125170172149 20063400773355484703639)
                  ·
                    rfl

theorem cell23_351660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_351660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351660 prefixEnd_351660 := by exact prefixLift 351660
  have htrace : WordTrace (prefixWord ++ tailWord_351660) baseStart_351660 baseEnd_351660 := by
    simpa [prefixWord, tailWord_351660, baseEnd_351660] using wordTrace_append hprefix tailTrace_351660
  have hstable : (prefixWord ++ tailWord_351660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351660).length < 2 ^ (prefixWord ++ tailWord_351660).sum := by decide
  have hdescent : baseEnd_351660 < baseStart_351660 := by decide
  rcases family_descends (prefixWord ++ tailWord_351660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351690 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 2, 5]
def baseStart_351690 : Nat := 118140960795 + 351690 * 2 ^ 59
def prefixEnd_351690 : Nat := 4983230072969 + 3 ^ 40 * 351690 * 2
def baseEnd_351690 : Nat := 60195337126611414985871

theorem tailTrace_351690 : CollatzResearch.WordTrace tailWord_351690 prefixEnd_351690 60195337126611414985871 := by
  unfold tailWord_351690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3206797023973667178795131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8551458730596445810120349 3206797023973667178795131)
  ·
    refine ⟨4810195535960500768192697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3206797023973667178795131 4810195535960500768192697)
    ·
      refine ⟨3607646651970375576144523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4810195535960500768192697 3607646651970375576144523)
      ·
        refine ⟨5411469977955563364216785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607646651970375576144523 5411469977955563364216785)
        ·
          refine ⟨4058602483466672523162589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5411469977955563364216785 4058602483466672523162589)
          ·
            refine ⟨1521975931300002196185971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4058602483466672523162589 1521975931300002196185971)
            ·
              refine ⟨2282963896950003294278957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521975931300002196185971 2282963896950003294278957)
              ·
                refine ⟨856111461356251235354609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2282963896950003294278957 856111461356251235354609)
                ·
                  refine ⟨642083596017188426515957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 856111461356251235354609 642083596017188426515957)
                  ·
                    refine ⟨60195337126611414985871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 642083596017188426515957 60195337126611414985871)
                    ·
                      rfl

theorem cell23_351690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_351690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351690 prefixEnd_351690 := by exact prefixLift 351690
  have htrace : WordTrace (prefixWord ++ tailWord_351690) baseStart_351690 baseEnd_351690 := by
    simpa [prefixWord, tailWord_351690, baseEnd_351690] using wordTrace_append hprefix tailTrace_351690
  have hstable : (prefixWord ++ tailWord_351690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351690).length < 2 ^ (prefixWord ++ tailWord_351690).sum := by decide
  have hdescent : baseEnd_351690 < baseStart_351690 := by decide
  rcases family_descends (prefixWord ++ tailWord_351690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351723 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 6]
def baseStart_351723 : Nat := 118140960795 + 351723 * 2 ^ 59
def prefixEnd_351723 : Nat := 4983230072969 + 3 ^ 40 * 351723 * 2
def baseEnd_351723 : Nat := 180602956241432615844961

theorem tailTrace_351723 : CollatzResearch.WordTrace tailWord_351723 prefixEnd_351723 180602956241432615844961 := by
  unfold tailWord_351723
  simp only [CollatzResearch.WordTrace]
  refine ⟨12828391704775115351131823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8552261136516743567421215 12828391704775115351131823)
  ·
    refine ⟨19242587557162673026697735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12828391704775115351131823 19242587557162673026697735)
    ·
      refine ⟨28863881335744009540046603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19242587557162673026697735 28863881335744009540046603)
      ·
        refine ⟨43295822003616014310069905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28863881335744009540046603 43295822003616014310069905)
        ·
          refine ⟨32471866502712010732552429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43295822003616014310069905 32471866502712010732552429)
          ·
            refine ⟨12176949938517004024707161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32471866502712010732552429 12176949938517004024707161)
            ·
              refine ⟨9132712453887753018530371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12176949938517004024707161 9132712453887753018530371)
              ·
                refine ⟨13699068680831629527795557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9132712453887753018530371 13699068680831629527795557)
                ·
                  refine ⟨2568575377655930536461667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13699068680831629527795557 2568575377655930536461667)
                  ·
                    refine ⟨3852863066483895804692501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2568575377655930536461667 3852863066483895804692501)
                    ·
                      refine ⟨180602956241432615844961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3852863066483895804692501 180602956241432615844961)
                      ·
                        rfl

theorem cell23_351723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_351723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351723 prefixEnd_351723 := by exact prefixLift 351723
  have htrace : WordTrace (prefixWord ++ tailWord_351723) baseStart_351723 baseEnd_351723 := by
    simpa [prefixWord, tailWord_351723, baseEnd_351723] using wordTrace_append hprefix tailTrace_351723
  have hstable : (prefixWord ++ tailWord_351723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351723).length < 2 ^ (prefixWord ++ tailWord_351723).sum := by decide
  have hdescent : baseEnd_351723 < baseStart_351723 := by decide
  rcases family_descends (prefixWord ++ tailWord_351723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351754 : List Nat := [3, 1, 2, 2, 2, 2, 1, 5, 1, 4]
def baseStart_351754 : Nat := 118140960795 + 351754 * 2 ^ 59
def prefixEnd_351754 : Nat := 4983230072969 + 3 ^ 40 * 351754 * 2
def baseEnd_351754 : Nat := 60206291380573998185773

theorem tailTrace_351754 : CollatzResearch.WordTrace tailWord_351754 prefixEnd_351754 60206291380573998185773 := by
  unfold tailWord_351754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207380591915701911377579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8553014911775205097006877 3207380591915701911377579)
  ·
    refine ⟨4811070887873552867066369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3207380591915701911377579 4811070887873552867066369)
    ·
      refine ⟨3608303165905164650299777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4811070887873552867066369 3608303165905164650299777)
      ·
        refine ⟨2706227374428873487724833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3608303165905164650299777 2706227374428873487724833)
        ·
          refine ⟨2029670530821655115793625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2706227374428873487724833 2029670530821655115793625)
          ·
            refine ⟨1522252898116241336845219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2029670530821655115793625 1522252898116241336845219)
            ·
              refine ⟨2283379347174362005267829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522252898116241336845219 2283379347174362005267829)
              ·
                refine ⟨214066813797596437993859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2283379347174362005267829 214066813797596437993859)
                ·
                  refine ⟨321100220696394656990789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214066813797596437993859 321100220696394656990789)
                  ·
                    refine ⟨60206291380573998185773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 321100220696394656990789 60206291380573998185773)
                    ·
                      rfl

theorem cell23_351754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_351754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351754 prefixEnd_351754 := by exact prefixLift 351754
  have htrace : WordTrace (prefixWord ++ tailWord_351754) baseStart_351754 baseEnd_351754 := by
    simpa [prefixWord, tailWord_351754, baseEnd_351754] using wordTrace_append hprefix tailTrace_351754
  have hstable : (prefixWord ++ tailWord_351754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351754).length < 2 ^ (prefixWord ++ tailWord_351754).sum := by decide
  have hdescent : baseEnd_351754 < baseStart_351754 := by decide
  rcases family_descends (prefixWord ++ tailWord_351754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351797 : List Nat := [1, 3, 3, 1, 1, 3, 1, 4, 1, 5]
def baseStart_351797 : Nat := 118140960795 + 351797 * 2 ^ 59
def prefixEnd_351797 : Nat := 4983230072969 + 3 ^ 40 * 351797 * 2
def baseEnd_351797 : Nat := 60213651269955108773207

theorem tailTrace_351797 : CollatzResearch.WordTrace tailWord_351797 prefixEnd_351797 60213651269955108773207 := by
  unfold tailWord_351797
  simp only [CollatzResearch.WordTrace]
  refine ⟨12831090706507025989325645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8554060471004683992883763 12831090706507025989325645)
  ·
    refine ⟨4811659014940134745997117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12831090706507025989325645 4811659014940134745997117)
    ·
      refine ⟨1804372130602550529748919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4811659014940134745997117 1804372130602550529748919)
      ·
        refine ⟨2706558195903825794623379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1804372130602550529748919 2706558195903825794623379)
        ·
          refine ⟨4059837293855738691935069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706558195903825794623379 4059837293855738691935069)
          ·
            refine ⟨1522438985195902009475651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4059837293855738691935069 1522438985195902009475651)
            ·
              refine ⟨2283658477793853014213477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522438985195902009475651 2283658477793853014213477)
              ·
                refine ⟨428185964586347440165027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2283658477793853014213477 428185964586347440165027)
                ·
                  refine ⟨642278946879521160247541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428185964586347440165027 642278946879521160247541)
                  ·
                    refine ⟨60213651269955108773207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 642278946879521160247541 60213651269955108773207)
                    ·
                      rfl

theorem cell23_351797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_351797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351797 prefixEnd_351797 := by exact prefixLift 351797
  have htrace : WordTrace (prefixWord ++ tailWord_351797) baseStart_351797 baseEnd_351797 := by
    simpa [prefixWord, tailWord_351797, baseEnd_351797] using wordTrace_append hprefix tailTrace_351797
  have hstable : (prefixWord ++ tailWord_351797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351797).length < 2 ^ (prefixWord ++ tailWord_351797).sum := by decide
  have hdescent : baseEnd_351797 < baseStart_351797 := by decide
  rcases family_descends (prefixWord ++ tailWord_351797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351828 : List Nat := [2, 4, 1, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_351828 : Nat := 118140960795 + 351828 * 2 ^ 59
def prefixEnd_351828 : Nat := 4983230072969 + 3 ^ 40 * 351828 * 2
def baseEnd_351828 : Nat := 180656871710154705031979

theorem tailTrace_351828 : CollatzResearch.WordTrace tailWord_351828 prefixEnd_351828 180656871710154705031979 := by
  unfold tailWord_351828
  simp only [CollatzResearch.WordTrace]
  refine ⟨6416110684697359141852069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8554814246263145522469425 6416110684697359141852069)
  ·
    refine ⟨1203020753380754839097263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6416110684697359141852069 1203020753380754839097263)
    ·
      refine ⟨1804531130071132258645895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1203020753380754839097263 1804531130071132258645895)
      ·
        refine ⟨2706796695106698387968843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1804531130071132258645895 2706796695106698387968843)
        ·
          refine ⟨4060195042660047581953265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706796695106698387968843 4060195042660047581953265)
          ·
            refine ⟨3045146281995035686464949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4060195042660047581953265 3045146281995035686464949)
            ·
              refine ⟨285482463937034595606089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3045146281995035686464949 285482463937034595606089)
              ·
                refine ⟨214111847952775946704567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285482463937034595606089 214111847952775946704567)
                ·
                  refine ⟨321167771929163920056851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214111847952775946704567 321167771929163920056851)
                  ·
                    refine ⟨481751657893745880085277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 321167771929163920056851 481751657893745880085277)
                    ·
                      refine ⟨180656871710154705031979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 481751657893745880085277 180656871710154705031979)
                      ·
                        rfl

theorem cell23_351828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_351828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351828 prefixEnd_351828 := by exact prefixLift 351828
  have htrace : WordTrace (prefixWord ++ tailWord_351828) baseStart_351828 baseEnd_351828 := by
    simpa [prefixWord, tailWord_351828, baseEnd_351828] using wordTrace_append hprefix tailTrace_351828
  have hstable : (prefixWord ++ tailWord_351828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351828).length < 2 ^ (prefixWord ++ tailWord_351828).sum := by decide
  have hdescent : baseEnd_351828 < baseStart_351828 := by decide
  rcases family_descends (prefixWord ++ tailWord_351828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351844 : List Nat := [2, 3, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_351844 : Nat := 118140960795 + 351844 * 2 ^ 59
def prefixEnd_351844 : Nat := 4983230072969 + 3 ^ 40 * 351844 * 2
def baseEnd_351844 : Nat := 60221695800208880810635

theorem tailTrace_351844 : CollatzResearch.WordTrace tailWord_351844 prefixEnd_351844 60221695800208880810635 := by
  unfold tailWord_351844
  simp only [CollatzResearch.WordTrace]
  refine ⟨6416402468668376508143293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8555203291557835344191057 6416402468668376508143293)
  ·
    refine ⟨2406150925750641190553735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6416402468668376508143293 2406150925750641190553735)
    ·
      refine ⟨3609226388625961785830603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2406150925750641190553735 3609226388625961785830603)
      ·
        refine ⟨5413839582938942678745905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3609226388625961785830603 5413839582938942678745905)
        ·
          refine ⟨4060379687204207009059429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5413839582938942678745905 4060379687204207009059429)
          ·
            refine ⟨761321191350788814198643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4060379687204207009059429 761321191350788814198643)
            ·
              refine ⟨1141981787026183221297965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761321191350788814198643 1141981787026183221297965)
              ·
                refine ⟨428243170134818707986737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1141981787026183221297965 428243170134818707986737)
                ·
                  refine ⟨321182377601114030990053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428243170134818707986737 321182377601114030990053)
                  ·
                    refine ⟨60221695800208880810635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 321182377601114030990053 60221695800208880810635)
                    ·
                      rfl

theorem cell23_351844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_351844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351844 prefixEnd_351844 := by exact prefixLift 351844
  have htrace : WordTrace (prefixWord ++ tailWord_351844) baseStart_351844 baseEnd_351844 := by
    simpa [prefixWord, tailWord_351844, baseEnd_351844] using wordTrace_append hprefix tailTrace_351844
  have hstable : (prefixWord ++ tailWord_351844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351844).length < 2 ^ (prefixWord ++ tailWord_351844).sum := by decide
  have hdescent : baseEnd_351844 < baseStart_351844 := by decide
  rcases family_descends (prefixWord ++ tailWord_351844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351867 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 3]
def baseStart_351867 : Nat := 118140960795 + 351867 * 2 ^ 59
def prefixEnd_351867 : Nat := 4983230072969 + 3 ^ 40 * 351867 * 2
def baseEnd_351867 : Nat := 180676897455680052444299

theorem tailTrace_351867 : CollatzResearch.WordTrace tailWord_351867 prefixEnd_351867 180676897455680052444299 := by
  unfold tailWord_351867
  simp only [CollatzResearch.WordTrace]
  refine ⟨12833643816253427944373855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8555762544168951962915903 12833643816253427944373855)
  ·
    refine ⟨19250465724380141916560783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12833643816253427944373855 19250465724380141916560783)
    ·
      refine ⟨28875698586570212874841175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19250465724380141916560783 28875698586570212874841175)
      ·
        refine ⟨43313547879855319312261763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28875698586570212874841175 43313547879855319312261763)
        ·
          refine ⟨64970321819782978968392645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43313547879855319312261763 64970321819782978968392645)
          ·
            refine ⟨12181935341209308556573621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64970321819782978968392645 12181935341209308556573621)
            ·
              refine ⟨1142056438238372677178777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12181935341209308556573621 1142056438238372677178777)
              ·
                refine ⟨856542328678779507884083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142056438238372677178777 856542328678779507884083)
                ·
                  refine ⟨1284813493018169261826125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856542328678779507884083 1284813493018169261826125)
                  ·
                    refine ⟨481805059881813473184797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1284813493018169261826125 481805059881813473184797)
                    ·
                      refine ⟨180676897455680052444299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 481805059881813473184797 180676897455680052444299)
                      ·
                        rfl

theorem cell23_351867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 3].length) (baseStart_351867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351867 prefixEnd_351867 := by exact prefixLift 351867
  have htrace : WordTrace (prefixWord ++ tailWord_351867) baseStart_351867 baseEnd_351867 := by
    simpa [prefixWord, tailWord_351867, baseEnd_351867] using wordTrace_append hprefix tailTrace_351867
  have hstable : (prefixWord ++ tailWord_351867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351867).length < 2 ^ (prefixWord ++ tailWord_351867).sum := by decide
  have hdescent : baseEnd_351867 < baseStart_351867 := by decide
  rcases family_descends (prefixWord ++ tailWord_351867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351917 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_351917 : Nat := 118140960795 + 351917 * 2 ^ 59
def prefixEnd_351917 : Nat := 4983230072969 + 3 ^ 40 * 351917 * 2
def baseEnd_351917 : Nat := 60234190496134952273023

theorem tailTrace_351917 : CollatzResearch.WordTrace tailWord_351917 prefixEnd_351917 60234190496134952273023 := by
  unfold tailWord_351917
  simp only [CollatzResearch.WordTrace]
  refine ⟨12835467466072286483694005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8556978310714857655796003 12835467466072286483694005)
  ·
    refine ⟨1203325074944276857846313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12835467466072286483694005 1203325074944276857846313)
    ·
      refine ⟨902493806208207643384735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1203325074944276857846313 902493806208207643384735)
      ·
        refine ⟨1353740709312311465077103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902493806208207643384735 1353740709312311465077103)
        ·
          refine ⟨2030611063968467197615655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353740709312311465077103 2030611063968467197615655)
          ·
            refine ⟨3045916595952700796423483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030611063968467197615655 3045916595952700796423483)
            ·
              refine ⟨4568874893929051194635225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3045916595952700796423483 4568874893929051194635225)
              ·
                refine ⟨3426656170446788395976419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4568874893929051194635225 3426656170446788395976419)
                ·
                  refine ⟨5139984255670182593964629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426656170446788395976419 5139984255670182593964629)
                  ·
                    refine ⟨60234190496134952273023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5139984255670182593964629 60234190496134952273023)
                    ·
                      rfl

theorem cell23_351917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_351917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351917 prefixEnd_351917 := by exact prefixLift 351917
  have htrace : WordTrace (prefixWord ++ tailWord_351917) baseStart_351917 baseEnd_351917 := by
    simpa [prefixWord, tailWord_351917, baseEnd_351917] using wordTrace_append hprefix tailTrace_351917
  have hstable : (prefixWord ++ tailWord_351917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351917).length < 2 ^ (prefixWord ++ tailWord_351917).sum := by decide
  have hdescent : baseEnd_351917 < baseStart_351917 := by decide
  rcases family_descends (prefixWord ++ tailWord_351917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351954 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_351954 : Nat := 118140960795 + 351954 * 2 ^ 59
def prefixEnd_351954 : Nat := 4983230072969 + 3 ^ 40 * 351954 * 2
def baseEnd_351954 : Nat := 180721570272621212056399

theorem tailTrace_351954 : CollatzResearch.WordTrace tailWord_351954 prefixEnd_351954 180721570272621212056399 := by
  unfold tailWord_351954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3209204241734560450697729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8557877977958827868527277 3209204241734560450697729)
  ·
    refine ⟨2406903181300920338023297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3209204241734560450697729 2406903181300920338023297)
    ·
      refine ⟨1805177385975690253517473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2406903181300920338023297 1805177385975690253517473)
      ·
        refine ⟨1353883039481767690138105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1805177385975690253517473 1353883039481767690138105)
        ·
          refine ⟨1015412279611325767603579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1353883039481767690138105 1015412279611325767603579)
          ·
            refine ⟨1523118419416988651405369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015412279611325767603579 1523118419416988651405369)
            ·
              refine ⟨1142338814562741488554027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523118419416988651405369 1142338814562741488554027)
              ·
                refine ⟨1713508221844112232831041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142338814562741488554027 1713508221844112232831041)
                ·
                  refine ⟨1285131166383084174623281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1713508221844112232831041 1285131166383084174623281)
                  ·
                    refine ⟨963848374787313130967461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1285131166383084174623281 963848374787313130967461)
                    ·
                      refine ⟨180721570272621212056399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 963848374787313130967461 180721570272621212056399)
                      ·
                        rfl

theorem cell23_351954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_351954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351954 prefixEnd_351954 := by exact prefixLift 351954
  have htrace : WordTrace (prefixWord ++ tailWord_351954) baseStart_351954 baseEnd_351954 := by
    simpa [prefixWord, tailWord_351954, baseEnd_351954] using wordTrace_append hprefix tailTrace_351954
  have hstable : (prefixWord ++ tailWord_351954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351954).length < 2 ^ (prefixWord ++ tailWord_351954).sum := by decide
  have hdescent : baseEnd_351954 < baseStart_351954 := by decide
  rcases family_descends (prefixWord ++ tailWord_351954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351977 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 2, 5]
def baseStart_351977 : Nat := 118140960795 + 351977 * 2 ^ 59
def prefixEnd_351977 : Nat := 4983230072969 + 3 ^ 40 * 351977 * 2
def baseEnd_351977 : Nat := 60244460109224874022931

theorem tailTrace_351977 : CollatzResearch.WordTrace tailWord_351977 prefixEnd_351977 60244460109224874022931 := by
  unfold tailWord_351977
  simp only [CollatzResearch.WordTrace]
  refine ⟨12837655845854916730878185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8558437230569944487252123 12837655845854916730878185)
  ·
    refine ⟨9628241884391187548158639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12837655845854916730878185 9628241884391187548158639)
    ·
      refine ⟨14442362826586781322237959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9628241884391187548158639 14442362826586781322237959)
      ·
        refine ⟨21663544239880171983356939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14442362826586781322237959 21663544239880171983356939)
        ·
          refine ⟨32495316359820257975035409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21663544239880171983356939 32495316359820257975035409)
          ·
            refine ⟨24371487269865193481276557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32495316359820257975035409 24371487269865193481276557)
            ·
              refine ⟨9139307726199447555478709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24371487269865193481276557 9139307726199447555478709)
              ·
                refine ⟨856810099331198208326129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9139307726199447555478709 856810099331198208326129)
                ·
                  refine ⟨642607574498398656244597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 856810099331198208326129 642607574498398656244597)
                  ·
                    refine ⟨60244460109224874022931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 642607574498398656244597 60244460109224874022931)
                    ·
                      rfl

theorem cell23_351977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_351977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351977 prefixEnd_351977 := by exact prefixLift 351977
  have htrace : WordTrace (prefixWord ++ tailWord_351977) baseStart_351977 baseEnd_351977 := by
    simpa [prefixWord, tailWord_351977, baseEnd_351977] using wordTrace_append hprefix tailTrace_351977
  have hstable : (prefixWord ++ tailWord_351977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351977).length < 2 ^ (prefixWord ++ tailWord_351977).sum := by decide
  have hdescent : baseEnd_351977 < baseStart_351977 := by decide
  rcases family_descends (prefixWord ++ tailWord_351977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351981 : List Nat := [1, 5, 1, 2, 1, 2, 3, 3, 5]
def baseStart_351981 : Nat := 118140960795 + 351981 * 2 ^ 59
def prefixEnd_351981 : Nat := 4983230072969 + 3 ^ 40 * 351981 * 2
def baseEnd_351981 : Nat := 20081714916699178490975

theorem tailTrace_351981 : CollatzResearch.WordTrace tailWord_351981 prefixEnd_351981 20081714916699178490975 := by
  unfold tailWord_351981
  simp only [CollatzResearch.WordTrace]
  refine ⟨12837801737840425414023797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8558534491893616942682531 12837801737840425414023797)
  ·
    refine ⟨1203543912922539882564731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12837801737840425414023797 1203543912922539882564731)
    ·
      refine ⟨1805315869383809823847097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1203543912922539882564731 1805315869383809823847097)
      ·
        refine ⟨1353986902037857367885323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1805315869383809823847097 1353986902037857367885323)
        ·
          refine ⟨2030980353056786051827985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353986902037857367885323 2030980353056786051827985)
          ·
            refine ⟨1523235264792589538870989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2030980353056786051827985 1523235264792589538870989)
            ·
              refine ⟨571213224297221077076621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1523235264792589538870989 571213224297221077076621)
              ·
                refine ⟨214204959111457903903733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 571213224297221077076621 214204959111457903903733)
                ·
                  refine ⟨20081714916699178490975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 214204959111457903903733 20081714916699178490975)
                  ·
                    rfl

theorem cell23_351981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_351981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351981 prefixEnd_351981 := by exact prefixLift 351981
  have htrace : WordTrace (prefixWord ++ tailWord_351981) baseStart_351981 baseEnd_351981 := by
    simpa [prefixWord, tailWord_351981, baseEnd_351981] using wordTrace_append hprefix tailTrace_351981
  have hstable : (prefixWord ++ tailWord_351981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351981).length < 2 ^ (prefixWord ++ tailWord_351981).sum := by decide
  have hdescent : baseEnd_351981 < baseStart_351981 := by decide
  rcases family_descends (prefixWord ++ tailWord_351981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351997 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_351997 : Nat := 118140960795 + 351997 * 2 ^ 59
def prefixEnd_351997 : Nat := 4983230072969 + 3 ^ 40 * 351997 * 2
def baseEnd_351997 : Nat := 180743649940764543818701

theorem tailTrace_351997 : CollatzResearch.WordTrace tailWord_351997 prefixEnd_351997 180743649940764543818701 := by
  unfold tailWord_351997
  simp only [CollatzResearch.WordTrace]
  refine ⟨12838385305782460146606245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8558923537188306764404163 12838385305782460146606245)
  ·
    refine ⟨2407197244834211277488671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12838385305782460146606245 2407197244834211277488671)
    ·
      refine ⟨3610795867251316916233007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2407197244834211277488671 3610795867251316916233007)
      ·
        refine ⟨5416193800876975374349511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3610795867251316916233007 5416193800876975374349511)
        ·
          refine ⟨8124290701315463061524267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5416193800876975374349511 8124290701315463061524267)
          ·
            refine ⟨12186436051973194592286401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8124290701315463061524267 12186436051973194592286401)
            ·
              refine ⟨9139827038979895944214801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12186436051973194592286401 9139827038979895944214801)
              ·
                refine ⟨6854870279234921958161101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9139827038979895944214801 6854870279234921958161101)
                ·
                  refine ⟨2570576354713095734310413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6854870279234921958161101 2570576354713095734310413)
                  ·
                    refine ⟨963966133017410900366405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2570576354713095734310413 963966133017410900366405)
                    ·
                      refine ⟨180743649940764543818701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 963966133017410900366405 180743649940764543818701)
                      ·
                        rfl

theorem cell23_351997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_351997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351997 prefixEnd_351997 := by exact prefixLift 351997
  have htrace : WordTrace (prefixWord ++ tailWord_351997) baseStart_351997 baseEnd_351997 := by
    simpa [prefixWord, tailWord_351997, baseEnd_351997] using wordTrace_append hprefix tailTrace_351997
  have hstable : (prefixWord ++ tailWord_351997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351997).length < 2 ^ (prefixWord ++ tailWord_351997).sum := by decide
  have hdescent : baseEnd_351997 < baseStart_351997 := by decide
  rcases family_descends (prefixWord ++ tailWord_351997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351998 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 7]
def baseStart_351998 : Nat := 118140960795 + 351998 * 2 ^ 59
def prefixEnd_351998 : Nat := 4983230072969 + 3 ^ 40 * 351998 * 2
def baseEnd_351998 : Nat := 20082684824602115545133

theorem tailTrace_351998 : CollatzResearch.WordTrace tailWord_351998 prefixEnd_351998 20082684824602115545133 := by
  unfold tailWord_351998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604802722347354664674081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8558947852519224878261765 1604802722347354664674081)
  ·
    refine ⟨1203602041760515998505561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1604802722347354664674081 1203602041760515998505561)
    ·
      refine ⟨902701531320386998879171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1203602041760515998505561 902701531320386998879171)
      ·
        refine ⟨1354052296980580498318757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902701531320386998879171 1354052296980580498318757)
        ·
          refine ⟨253884805683858843434767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1354052296980580498318757 253884805683858843434767)
          ·
            refine ⟨380827208525788265152151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253884805683858843434767 380827208525788265152151)
            ·
              refine ⟨571240812788682397728227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380827208525788265152151 571240812788682397728227)
              ·
                refine ⟨856861219183023596592341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571240812788682397728227 856861219183023596592341)
                ·
                  refine ⟨20082684824602115545133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 856861219183023596592341 20082684824602115545133)
                  ·
                    rfl

theorem cell23_351998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_351998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_351998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_351998 prefixEnd_351998 := by exact prefixLift 351998
  have htrace : WordTrace (prefixWord ++ tailWord_351998) baseStart_351998 baseEnd_351998 := by
    simpa [prefixWord, tailWord_351998, baseEnd_351998] using wordTrace_append hprefix tailTrace_351998
  have hstable : (prefixWord ++ tailWord_351998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351998).length < 2 ^ (prefixWord ++ tailWord_351998).sum := by decide
  have hdescent : baseEnd_351998 < baseStart_351998 := by decide
  rcases family_descends (prefixWord ++ tailWord_351998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352004 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_352004 : Nat := 118140960795 + 352004 * 2 ^ 59
def prefixEnd_352004 : Nat := 4983230072969 + 3 ^ 40 * 352004 * 2
def baseEnd_352004 : Nat := 180747244305346016431169

theorem tailTrace_352004 : CollatzResearch.WordTrace tailWord_352004 prefixEnd_352004 180747244305346016431169 := by
  unfold tailWord_352004
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419320308378550171055533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8559093744504733561407377 6419320308378550171055533)
  ·
    refine ⟨2407245115641956314145825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6419320308378550171055533 2407245115641956314145825)
    ·
      refine ⟨1805433836731467235609369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2407245115641956314145825 1805433836731467235609369)
      ·
        refine ⟨1354075377548600426707027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1805433836731467235609369 1354075377548600426707027)
        ·
          refine ⟨2031113066322900640060541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354075377548600426707027 2031113066322900640060541)
          ·
            refine ⟨761667399871087740022703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2031113066322900640060541 761667399871087740022703)
            ·
              refine ⟨1142501099806631610034055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761667399871087740022703 1142501099806631610034055)
              ·
                refine ⟨1713751649709947415051083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142501099806631610034055 1713751649709947415051083)
                ·
                  refine ⟨2570627474564921122576625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713751649709947415051083 2570627474564921122576625)
                  ·
                    refine ⟨1927970605923690841932469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2570627474564921122576625 1927970605923690841932469)
                    ·
                      refine ⟨180747244305346016431169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1927970605923690841932469 180747244305346016431169)
                      ·
                        rfl

theorem cell23_352004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_352004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352004 prefixEnd_352004 := by exact prefixLift 352004
  have htrace : WordTrace (prefixWord ++ tailWord_352004) baseStart_352004 baseEnd_352004 := by
    simpa [prefixWord, tailWord_352004, baseEnd_352004] using wordTrace_append hprefix tailTrace_352004
  have hstable : (prefixWord ++ tailWord_352004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352004).length < 2 ^ (prefixWord ++ tailWord_352004).sum := by decide
  have hdescent : baseEnd_352004 < baseStart_352004 := by decide
  rcases family_descends (prefixWord ++ tailWord_352004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352024 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 3, 4]
def baseStart_352024 : Nat := 118140960795 + 352024 * 2 ^ 59
def prefixEnd_352024 : Nat := 4983230072969 + 3 ^ 40 * 352024 * 2
def baseEnd_352024 : Nat := 60252504639478646060359

theorem tailTrace_352024 : CollatzResearch.WordTrace tailWord_352024 prefixEnd_352024 60252504639478646060359 := by
  unfold tailWord_352024
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419685038342321878919563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8559580051123095838559417 6419685038342321878919563)
  ·
    refine ⟨9629527557513482818379345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6419685038342321878919563 9629527557513482818379345)
    ·
      refine ⟨7222145668135112113784509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9629527557513482818379345 7222145668135112113784509)
      ·
        refine ⟨2708304625550667042669191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7222145668135112113784509 2708304625550667042669191)
        ·
          refine ⟨4062456938326000564003787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2708304625550667042669191 4062456938326000564003787)
          ·
            refine ⟨6093685407489000846005681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4062456938326000564003787 6093685407489000846005681)
            ·
              refine ⟨4570264055616750634504261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6093685407489000846005681 4570264055616750634504261)
              ·
                refine ⟨856924510428140743969549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4570264055616750634504261 856924510428140743969549)
                ·
                  refine ⟨321346691410552778988581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856924510428140743969549 321346691410552778988581)
                  ·
                    refine ⟨60252504639478646060359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 321346691410552778988581 60252504639478646060359)
                    ·
                      rfl

theorem cell23_352024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_352024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352024 prefixEnd_352024 := by exact prefixLift 352024
  have htrace : WordTrace (prefixWord ++ tailWord_352024) baseStart_352024 baseEnd_352024 := by
    simpa [prefixWord, tailWord_352024, baseEnd_352024] using wordTrace_append hprefix tailTrace_352024
  have hstable : (prefixWord ++ tailWord_352024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352024).length < 2 ^ (prefixWord ++ tailWord_352024).sum := by decide
  have hdescent : baseEnd_352024 < baseStart_352024 := by decide
  rcases family_descends (prefixWord ++ tailWord_352024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352058 : List Nat := [3, 1, 1, 1, 5, 2, 1, 4, 1, 4]
def baseStart_352058 : Nat := 118140960795 + 352058 * 2 ^ 59
def prefixEnd_352058 : Nat := 4983230072969 + 3 ^ 40 * 352058 * 2
def baseEnd_352058 : Nat := 60258324086896268385307

theorem tailTrace_352058 : CollatzResearch.WordTrace tailWord_352058 prefixEnd_352058 60258324086896268385307 := by
  unfold tailWord_352058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210152539640366891144207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8560406772374311709717885 3210152539640366891144207)
  ·
    refine ⟨4815228809460550336716311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3210152539640366891144207 4815228809460550336716311)
    ·
      refine ⟨7222843214190825505074467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4815228809460550336716311 7222843214190825505074467)
      ·
        refine ⟨10834264821286238257611701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7222843214190825505074467 10834264821286238257611701)
        ·
          refine ⟨1015712326995584836651097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10834264821286238257611701 1015712326995584836651097)
          ·
            refine ⟨761784245246688627488323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1015712326995584836651097 761784245246688627488323)
            ·
              refine ⟨1142676367870032941232485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761784245246688627488323 1142676367870032941232485)
              ·
                refine ⟨214251818975631176481091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1142676367870032941232485 214251818975631176481091)
                ·
                  refine ⟨321377728463446764721637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214251818975631176481091 321377728463446764721637)
                  ·
                    refine ⟨60258324086896268385307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 321377728463446764721637 60258324086896268385307)
                    ·
                      rfl

theorem cell23_352058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_352058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352058 prefixEnd_352058 := by exact prefixLift 352058
  have htrace : WordTrace (prefixWord ++ tailWord_352058) baseStart_352058 baseEnd_352058 := by
    simpa [prefixWord, tailWord_352058, baseEnd_352058] using wordTrace_append hprefix tailTrace_352058
  have hstable : (prefixWord ++ tailWord_352058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352058).length < 2 ^ (prefixWord ++ tailWord_352058).sum := by decide
  have hdescent : baseEnd_352058 < baseStart_352058 := by decide
  rcases family_descends (prefixWord ++ tailWord_352058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352081 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 5, 1, 3]
def baseStart_352081 : Nat := 118140960795 + 352081 * 2 ^ 59
def prefixEnd_352081 : Nat := 4983230072969 + 3 ^ 40 * 352081 * 2
def baseEnd_352081 : Nat := 180786782315742215168315

theorem tailTrace_352081 : CollatzResearch.WordTrace tailWord_352081 prefixEnd_352081 180786782315742215168315 := by
  unfold tailWord_352081
  simp only [CollatzResearch.WordTrace]
  refine ⟨12841449037478142492664097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8560966024985428328442731 12841449037478142492664097)
  ·
    refine ⟨9631086778108606869498073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12841449037478142492664097 9631086778108606869498073)
    ·
      refine ⟨7223315083581455152123555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9631086778108606869498073 7223315083581455152123555)
      ·
        refine ⟨10834972625372182728185333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7223315083581455152123555 10834972625372182728185333)
        ·
          refine ⟨1015778683628642130767375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10834972625372182728185333 1015778683628642130767375)
          ·
            refine ⟨1523668025442963196151063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015778683628642130767375 1523668025442963196151063)
            ·
              refine ⟨2285502038164444794226595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523668025442963196151063 2285502038164444794226595)
              ·
                refine ⟨3428253057246667191339893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2285502038164444794226595 3428253057246667191339893)
                ·
                  refine ⟨321398724116875049188115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3428253057246667191339893 321398724116875049188115)
                  ·
                    refine ⟨482098086175312573782173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 321398724116875049188115 482098086175312573782173)
                    ·
                      refine ⟨180786782315742215168315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 482098086175312573782173 180786782315742215168315)
                      ·
                        rfl

theorem cell23_352081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_352081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352081 prefixEnd_352081 := by exact prefixLift 352081
  have htrace : WordTrace (prefixWord ++ tailWord_352081) baseStart_352081 baseEnd_352081 := by
    simpa [prefixWord, tailWord_352081, baseEnd_352081] using wordTrace_append hprefix tailTrace_352081
  have hstable : (prefixWord ++ tailWord_352081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352081).length < 2 ^ (prefixWord ++ tailWord_352081).sum := by decide
  have hdescent : baseEnd_352081 < baseStart_352081 := by decide
  rcases family_descends (prefixWord ++ tailWord_352081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352127 : List Nat := [1, 1, 2, 2, 1, 1, 3, 12]
def baseStart_352127 : Nat := 118140960795 + 352127 * 2 ^ 59
def prefixEnd_352127 : Nat := 4983230072969 + 3 ^ 40 * 352127 * 2
def baseEnd_352127 : Nat := 6696681571327742044189

theorem tailTrace_352127 : CollatzResearch.WordTrace tailWord_352127 prefixEnd_352127 6696681571327742044189 := by
  unfold tailWord_352127
  simp only [CollatzResearch.WordTrace]
  refine ⟨12843126795311492348838635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8562084530207661565892423 12843126795311492348838635)
  ·
    refine ⟨19264690192967238523257953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12843126795311492348838635 19264690192967238523257953)
    ·
      refine ⟨14448517644725428892443465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19264690192967238523257953 14448517644725428892443465)
      ·
        refine ⟨10836388233544071669332599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14448517644725428892443465 10836388233544071669332599)
        ·
          refine ⟨16254582350316107503998899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10836388233544071669332599 16254582350316107503998899)
          ·
            refine ⟨24381873525474161255998349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16254582350316107503998899 24381873525474161255998349)
            ·
              refine ⟨9143202572052810470999381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24381873525474161255998349 9143202572052810470999381)
              ·
                refine ⟨6696681571327742044189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 9143202572052810470999381 6696681571327742044189)
                ·
                  rfl

theorem cell23_352127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 12].length) (baseStart_352127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352127 prefixEnd_352127 := by exact prefixLift 352127
  have htrace : WordTrace (prefixWord ++ tailWord_352127) baseStart_352127 baseEnd_352127 := by
    simpa [prefixWord, tailWord_352127, baseEnd_352127] using wordTrace_append hprefix tailTrace_352127
  have hstable : (prefixWord ++ tailWord_352127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352127).length < 2 ^ (prefixWord ++ tailWord_352127).sum := by decide
  have hdescent : baseEnd_352127 < baseStart_352127 := by decide
  rcases family_descends (prefixWord ++ tailWord_352127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352131 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 1, 6]
def baseStart_352131 : Nat := 118140960795 + 352131 * 2 ^ 59
def prefixEnd_352131 : Nat := 4983230072969 + 3 ^ 40 * 352131 * 2
def baseEnd_352131 : Nat := 60270818782822339847695

theorem tailTrace_352131 : CollatzResearch.WordTrace tailWord_352131 prefixEnd_352131 60270818782822339847695 := by
  unfold tailWord_352131
  simp only [CollatzResearch.WordTrace]
  refine ⟨12843272687297001031984247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8562181791531334021322831 12843272687297001031984247)
  ·
    refine ⟨19264909030945501547976371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12843272687297001031984247 19264909030945501547976371)
    ·
      refine ⟨28897363546418252321964557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19264909030945501547976371 28897363546418252321964557)
      ·
        refine ⟨10836511329906844620736709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28897363546418252321964557 10836511329906844620736709)
        ·
          refine ⟨2031845874357533366388133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10836511329906844620736709 2031845874357533366388133)
          ·
            refine ⟨380971101442037506197775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2031845874357533366388133 380971101442037506197775)
            ·
              refine ⟨571456652163056259296663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380971101442037506197775 571456652163056259296663)
              ·
                refine ⟨857184978244584388944995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571456652163056259296663 857184978244584388944995)
                ·
                  refine ⟨1285777467366876583417493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857184978244584388944995 1285777467366876583417493)
                  ·
                    refine ⟨60270818782822339847695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1285777467366876583417493 60270818782822339847695)
                    ·
                      rfl

theorem cell23_352131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 6].length) (baseStart_352131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352131 prefixEnd_352131 := by exact prefixLift 352131
  have htrace : WordTrace (prefixWord ++ tailWord_352131) baseStart_352131 baseEnd_352131 := by
    simpa [prefixWord, tailWord_352131, baseEnd_352131] using wordTrace_append hprefix tailTrace_352131
  have hstable : (prefixWord ++ tailWord_352131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352131).length < 2 ^ (prefixWord ++ tailWord_352131).sum := by decide
  have hdescent : baseEnd_352131 < baseStart_352131 := by decide
  rcases family_descends (prefixWord ++ tailWord_352131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352161 : List Nat := [1, 2, 3, 4, 2, 2, 9]
def baseStart_352161 : Nat := 118140960795 + 352161 * 2 ^ 59
def prefixEnd_352161 : Nat := 4983230072969 + 3 ^ 40 * 352161 * 2
def baseEnd_352161 : Nat := 2232442725532122248987

theorem tailTrace_352161 : CollatzResearch.WordTrace tailWord_352161 prefixEnd_352161 2232442725532122248987 := by
  unfold tailWord_352161
  simp only [CollatzResearch.WordTrace]
  refine ⟨12844366877188316155576337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8562911251458877437050891 12844366877188316155576337)
  ·
    refine ⟨9633275157891237116682253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12844366877188316155576337 9633275157891237116682253)
    ·
      refine ⟨3612478184209213918755845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9633275157891237116682253 3612478184209213918755845)
      ·
        refine ⟨677339659539227609766721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3612478184209213918755845 677339659539227609766721)
        ·
          refine ⟨508004744654420707325041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677339659539227609766721 508004744654420707325041)
          ·
            refine ⟨381003558490815530493781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508004744654420707325041 381003558490815530493781)
            ·
              refine ⟨2232442725532122248987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 381003558490815530493781 2232442725532122248987)
              ·
                rfl

theorem cell23_352161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 9].length) (baseStart_352161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352161 prefixEnd_352161 := by exact prefixLift 352161
  have htrace : WordTrace (prefixWord ++ tailWord_352161) baseStart_352161 baseEnd_352161 := by
    simpa [prefixWord, tailWord_352161, baseEnd_352161] using wordTrace_append hprefix tailTrace_352161
  have hstable : (prefixWord ++ tailWord_352161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352161).length < 2 ^ (prefixWord ++ tailWord_352161).sum := by decide
  have hdescent : baseEnd_352161 < baseStart_352161 := by decide
  rcases family_descends (prefixWord ++ tailWord_352161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352215 : List Nat := [1, 1, 3, 2, 1, 1, 7, 1, 1, 3, 2]
def baseStart_352215 : Nat := 118140960795 + 352215 * 2 ^ 59
def prefixEnd_352215 : Nat := 4983230072969 + 3 ^ 40 * 352215 * 2
def baseEnd_352215 : Nat := 180855588723444690892699

theorem tailTrace_352215 : CollatzResearch.WordTrace tailWord_352215 prefixEnd_352215 180855588723444690892699 := by
  unfold tailWord_352215
  simp only [CollatzResearch.WordTrace]
  refine ⟨12846336418992683378042099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8564224279328455585361399 12846336418992683378042099)
  ·
    refine ⟨19269504628489025067063149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12846336418992683378042099 19269504628489025067063149)
    ·
      refine ⟨7226064235683384400148681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19269504628489025067063149 7226064235683384400148681)
      ·
        refine ⟨5419548176762538300111511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7226064235683384400148681 5419548176762538300111511)
        ·
          refine ⟨8129322265143807450167267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5419548176762538300111511 8129322265143807450167267)
          ·
            refine ⟨12193983397715711175250901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8129322265143807450167267 12193983397715711175250901)
            ·
              refine ⟨285796485883961980669943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12193983397715711175250901 285796485883961980669943)
              ·
                refine ⟨428694728825942971004915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285796485883961980669943 428694728825942971004915)
                ·
                  refine ⟨643042093238914456507373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428694728825942971004915 643042093238914456507373)
                  ·
                    refine ⟨241140784964592921190265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 643042093238914456507373 241140784964592921190265)
                    ·
                      refine ⟨180855588723444690892699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241140784964592921190265 180855588723444690892699)
                      ·
                        rfl

theorem cell23_352215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_352215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352215 prefixEnd_352215 := by exact prefixLift 352215
  have htrace : WordTrace (prefixWord ++ tailWord_352215) baseStart_352215 baseEnd_352215 := by
    simpa [prefixWord, tailWord_352215, baseEnd_352215] using wordTrace_append hprefix tailTrace_352215
  have hstable : (prefixWord ++ tailWord_352215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352215).length < 2 ^ (prefixWord ++ tailWord_352215).sum := by decide
  have hdescent : baseEnd_352215 < baseStart_352215 := by decide
  rcases family_descends (prefixWord ++ tailWord_352215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352224 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 4]
def baseStart_352224 : Nat := 118140960795 + 352224 * 2 ^ 59
def prefixEnd_352224 : Nat := 4983230072969 + 3 ^ 40 * 352224 * 2
def baseEnd_352224 : Nat := 180860210049335155680157

theorem tailTrace_352224 : CollatzResearch.WordTrace tailWord_352224 prefixEnd_352224 180860210049335155680157 := by
  unfold tailWord_352224
  simp only [CollatzResearch.WordTrace]
  refine ⟨6423332337980038957559863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8564443117306718610079817 6423332337980038957559863)
  ·
    refine ⟨9634998506970058436339795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6423332337980038957559863 9634998506970058436339795)
    ·
      refine ⟨14452497760455087654509693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9634998506970058436339795 14452497760455087654509693)
      ·
        refine ⟨5419686660170657870441135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14452497760455087654509693 5419686660170657870441135)
        ·
          refine ⟨8129529990255986805661703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5419686660170657870441135 8129529990255986805661703)
          ·
            refine ⟨12194294985383980208492555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8129529990255986805661703 12194294985383980208492555)
            ·
              refine ⟨18291442478075970312738833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12194294985383980208492555 18291442478075970312738833)
              ·
                refine ⟨13718581858556977734554125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18291442478075970312738833 13718581858556977734554125)
                ·
                  refine ⟨5144468196958866650457797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13718581858556977734554125 5144468196958866650457797)
                  ·
                    refine ⟨964587786929787496960837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5144468196958866650457797 964587786929787496960837)
                    ·
                      refine ⟨180860210049335155680157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 964587786929787496960837 180860210049335155680157)
                      ·
                        rfl

theorem cell23_352224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_352224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352224 prefixEnd_352224 := by exact prefixLift 352224
  have htrace : WordTrace (prefixWord ++ tailWord_352224) baseStart_352224 baseEnd_352224 := by
    simpa [prefixWord, tailWord_352224, baseEnd_352224] using wordTrace_append hprefix tailTrace_352224
  have hstable : (prefixWord ++ tailWord_352224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352224).length < 2 ^ (prefixWord ++ tailWord_352224).sum := by decide
  have hdescent : baseEnd_352224 < baseStart_352224 := by decide
  rcases family_descends (prefixWord ++ tailWord_352224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352268 : List Nat := [2, 2, 1, 2, 3, 1, 4, 3, 5]
def baseStart_352268 : Nat := 118140960795 + 352268 * 2 ^ 59
def prefixEnd_352268 : Nat := 4983230072969 + 3 ^ 40 * 352268 * 2
def baseEnd_352268 : Nat := 20098089244236998169995

theorem tailTrace_352268 : CollatzResearch.WordTrace tailWord_352268 prefixEnd_352268 20098089244236998169995 := by
  unfold tailWord_352268
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424134743900336714860729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8565512991867115619814305 6424134743900336714860729)
  ·
    refine ⟨4818101057925252536145547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6424134743900336714860729 4818101057925252536145547)
    ·
      refine ⟨7227151586887878804218321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4818101057925252536145547 7227151586887878804218321)
      ·
        refine ⟨5420363690165909103163741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7227151586887878804218321 5420363690165909103163741)
        ·
          refine ⟨2032636383812215913686403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5420363690165909103163741 2032636383812215913686403)
          ·
            refine ⟨3048954575718323870529605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032636383812215913686403 3048954575718323870529605)
            ·
              refine ⟨571678982947185725724301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3048954575718323870529605 571678982947185725724301)
              ·
                refine ⟨214379618605194647146613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 571678982947185725724301 214379618605194647146613)
                ·
                  refine ⟨20098089244236998169995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 214379618605194647146613 20098089244236998169995)
                  ·
                    rfl

theorem cell23_352268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_352268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352268 prefixEnd_352268 := by exact prefixLift 352268
  have htrace : WordTrace (prefixWord ++ tailWord_352268) baseStart_352268 baseEnd_352268 := by
    simpa [prefixWord, tailWord_352268, baseEnd_352268] using wordTrace_append hprefix tailTrace_352268
  have hstable : (prefixWord ++ tailWord_352268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352268).length < 2 ^ (prefixWord ++ tailWord_352268).sum := by decide
  have hdescent : baseEnd_352268 < baseStart_352268 := by decide
  rcases family_descends (prefixWord ++ tailWord_352268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352279 : List Nat := [1, 1, 3, 5, 2, 2, 1, 2, 2, 2, 2]
def baseStart_352279 : Nat := 118140960795 + 352279 * 2 ^ 59
def prefixEnd_352279 : Nat := 4983230072969 + 3 ^ 40 * 352279 * 2
def baseEnd_352279 : Nat := 180888451485332440492405

theorem tailTrace_352279 : CollatzResearch.WordTrace tailWord_352279 prefixEnd_352279 180888451485332440492405 := by
  unfold tailWord_352279
  simp only [CollatzResearch.WordTrace]
  refine ⟨12848670690760822308371891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8565780460507214872247927 12848670690760822308371891)
  ·
    refine ⟨19273006036141233462557837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12848670690760822308371891 19273006036141233462557837)
    ·
      refine ⟨7227377263552962548459189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19273006036141233462557837 7227377263552962548459189)
      ·
        refine ⟨677566618458090238918049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7227377263552962548459189 677566618458090238918049)
        ·
          refine ⟨508174963843567679188537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677566618458090238918049 508174963843567679188537)
          ·
            refine ⟨381131222882675759391403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508174963843567679188537 381131222882675759391403)
            ·
              refine ⟨571696834324013639087105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381131222882675759391403 571696834324013639087105)
              ·
                refine ⟨428772625743010229315329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 571696834324013639087105 428772625743010229315329)
                ·
                  refine ⟨321579469307257671986497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428772625743010229315329 321579469307257671986497)
                  ·
                    refine ⟨241184601980443253989873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 321579469307257671986497 241184601980443253989873)
                    ·
                      refine ⟨180888451485332440492405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241184601980443253989873 180888451485332440492405)
                      ·
                        rfl

theorem cell23_352279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_352279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352279 prefixEnd_352279 := by exact prefixLift 352279
  have htrace : WordTrace (prefixWord ++ tailWord_352279) baseStart_352279 baseEnd_352279 := by
    simpa [prefixWord, tailWord_352279, baseEnd_352279] using wordTrace_append hprefix tailTrace_352279
  have hstable : (prefixWord ++ tailWord_352279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352279).length < 2 ^ (prefixWord ++ tailWord_352279).sum := by decide
  have hdescent : baseEnd_352279 < baseStart_352279 := by decide
  rcases family_descends (prefixWord ++ tailWord_352279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352296 : List Nat := [2, 1, 5, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_352296 : Nat := 118140960795 + 352296 * 2 ^ 59
def prefixEnd_352296 : Nat := 4983230072969 + 3 ^ 40 * 352296 * 2
def baseEnd_352296 : Nat := 180897180656458873979827

theorem tailTrace_352296 : CollatzResearch.WordTrace tailWord_352296 prefixEnd_352296 180897180656458873979827 := by
  unfold tailWord_352296
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424645365849617105870371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8566193821132822807827161 6424645365849617105870371)
  ·
    refine ⟨9636968048774425658805557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6424645365849617105870371 9636968048774425658805557)
    ·
      refine ⟨903465754572602405513021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9636968048774425658805557 903465754572602405513021)
      ·
        refine ⟨338799657964725902067383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 903465754572602405513021 338799657964725902067383)
        ·
          refine ⟨508199486947088853101075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338799657964725902067383 508199486947088853101075)
          ·
            refine ⟨762299230420633279651613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508199486947088853101075 762299230420633279651613)
            ·
              refine ⟨285862211407737479869355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 762299230420633279651613 285862211407737479869355)
              ·
                refine ⟨428793317111606219804033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285862211407737479869355 428793317111606219804033)
                ·
                  refine ⟨321594987833704664853025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428793317111606219804033 321594987833704664853025)
                  ·
                    refine ⟨241196240875278498639769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 321594987833704664853025 241196240875278498639769)
                    ·
                      refine ⟨180897180656458873979827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241196240875278498639769 180897180656458873979827)
                      ·
                        rfl

theorem cell23_352296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_352296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352296 prefixEnd_352296 := by exact prefixLift 352296
  have htrace : WordTrace (prefixWord ++ tailWord_352296) baseStart_352296 baseEnd_352296 := by
    simpa [prefixWord, tailWord_352296, baseEnd_352296] using wordTrace_append hprefix tailTrace_352296
  have hstable : (prefixWord ++ tailWord_352296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352296).length < 2 ^ (prefixWord ++ tailWord_352296).sum := by decide
  have hdescent : baseEnd_352296 < baseStart_352296 := by decide
  rcases family_descends (prefixWord ++ tailWord_352296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352341 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 8]
def baseStart_352341 : Nat := 118140960795 + 352341 * 2 ^ 59
def prefixEnd_352341 : Nat := 4983230072969 + 3 ^ 40 * 352341 * 2
def baseEnd_352341 : Nat := 20102254142879021990791

theorem tailTrace_352341 : CollatzResearch.WordTrace tailWord_352341 prefixEnd_352341 20102254142879021990791 := by
  unfold tailWord_352341
  simp only [CollatzResearch.WordTrace]
  refine ⟨12850932016536206897128877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8567288011024137931419251 12850932016536206897128877)
  ·
    refine ⟨4819099506201077586423329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12850932016536206897128877 4819099506201077586423329)
    ·
      refine ⟨3614324629650808189817497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4819099506201077586423329 3614324629650808189817497)
      ·
        refine ⟨2710743472238106142363123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3614324629650808189817497 2710743472238106142363123)
        ·
          refine ⟨4066115208357159213544685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2710743472238106142363123 4066115208357159213544685)
          ·
            refine ⟨1524793203133934705079257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4066115208357159213544685 1524793203133934705079257)
            ·
              refine ⟨1143594902350451028809443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1524793203133934705079257 1143594902350451028809443)
              ·
                refine ⟨1715392353525676543214165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1143594902350451028809443 1715392353525676543214165)
                ·
                  refine ⟨20102254142879021990791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1715392353525676543214165 20102254142879021990791)
                  ·
                    rfl

theorem cell23_352341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_352341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352341 prefixEnd_352341 := by exact prefixLift 352341
  have htrace : WordTrace (prefixWord ++ tailWord_352341) baseStart_352341 baseEnd_352341 := by
    simpa [prefixWord, tailWord_352341, baseEnd_352341] using wordTrace_append hprefix tailTrace_352341
  have hstable : (prefixWord ++ tailWord_352341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352341).length < 2 ^ (prefixWord ++ tailWord_352341).sum := by decide
  have hdescent : baseEnd_352341 < baseStart_352341 := by decide
  rcases family_descends (prefixWord ++ tailWord_352341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352351 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 3]
def baseStart_352351 : Nat := 118140960795 + 352351 * 2 ^ 59
def prefixEnd_352351 : Nat := 4983230072969 + 3 ^ 40 * 352351 * 2
def baseEnd_352351 : Nat := 180925422092456158792073

theorem tailTrace_352351 : CollatzResearch.WordTrace tailWord_352351 prefixEnd_352351 180925422092456158792073 := by
  unfold tailWord_352351
  simp only [CollatzResearch.WordTrace]
  refine ⟨12851296746499978604992907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8567531164333319069995271 12851296746499978604992907)
  ·
    refine ⟨19276945119749967907489361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12851296746499978604992907 19276945119749967907489361)
    ·
      refine ⟨14457708839812475930617021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19276945119749967907489361 14457708839812475930617021)
      ·
        refine ⟨5421640814929678473981383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14457708839812475930617021 5421640814929678473981383)
        ·
          refine ⟨8132461222394517710972075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5421640814929678473981383 8132461222394517710972075)
          ·
            refine ⟨12198691833591776566458113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8132461222394517710972075 12198691833591776566458113)
            ·
              refine ⟨9149018875193832424843585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12198691833591776566458113 9149018875193832424843585)
              ·
                refine ⟨6861764156395374318632689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9149018875193832424843585 6861764156395374318632689)
                ·
                  refine ⟨5146323117296530738974517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6861764156395374318632689 5146323117296530738974517)
                  ·
                    refine ⟨482467792246549756778861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5146323117296530738974517 482467792246549756778861)
                    ·
                      refine ⟨180925422092456158792073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 482467792246549756778861 180925422092456158792073)
                      ·
                        rfl

theorem cell23_352351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_352351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352351 prefixEnd_352351 := by exact prefixLift 352351
  have htrace : WordTrace (prefixWord ++ tailWord_352351) baseStart_352351 baseEnd_352351 := by
    simpa [prefixWord, tailWord_352351, baseEnd_352351] using wordTrace_append hprefix tailTrace_352351
  have hstable : (prefixWord ++ tailWord_352351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352351).length < 2 ^ (prefixWord ++ tailWord_352351).sum := by decide
  have hdescent : baseEnd_352351 < baseStart_352351 := by decide
  rcases family_descends (prefixWord ++ tailWord_352351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352429 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_352429 : Nat := 118140960795 + 352429 * 2 ^ 59
def prefixEnd_352429 : Nat := 4983230072969 + 3 ^ 40 * 352429 * 2
def baseEnd_352429 : Nat := 180965473583506853616715

theorem tailTrace_352429 : CollatzResearch.WordTrace tailWord_352429 prefixEnd_352429 180965473583506853616715 := by
  unfold tailWord_352429
  simp only [CollatzResearch.WordTrace]
  refine ⟨12854141640217397926332341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8569427760144931950888227 12854141640217397926332341)
  ·
    refine ⟨1205075778770381055593657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12854141640217397926332341 1205075778770381055593657)
    ·
      refine ⟨903806834077785791695243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1205075778770381055593657 903806834077785791695243)
      ·
        refine ⟨1355710251116678687542865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903806834077785791695243 1355710251116678687542865)
        ·
          refine ⟨1016782688337509015657149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1355710251116678687542865 1016782688337509015657149)
          ·
            refine ⟨381293508126565880871431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1016782688337509015657149 381293508126565880871431)
            ·
              refine ⟨571940262189848821307147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381293508126565880871431 571940262189848821307147)
              ·
                refine ⟨857910393284773231960721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571940262189848821307147 857910393284773231960721)
                ·
                  refine ⟨643432794963579923970541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 857910393284773231960721 643432794963579923970541)
                  ·
                    refine ⟨241287298111342471488953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 643432794963579923970541 241287298111342471488953)
                    ·
                      refine ⟨180965473583506853616715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241287298111342471488953 180965473583506853616715)
                      ·
                        rfl

theorem cell23_352429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_352429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352429 prefixEnd_352429 := by exact prefixLift 352429
  have htrace : WordTrace (prefixWord ++ tailWord_352429) baseStart_352429 baseEnd_352429 := by
    simpa [prefixWord, tailWord_352429, baseEnd_352429] using wordTrace_append hprefix tailTrace_352429
  have hstable : (prefixWord ++ tailWord_352429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352429).length < 2 ^ (prefixWord ++ tailWord_352429).sum := by decide
  have hdescent : baseEnd_352429 < baseStart_352429 := by decide
  rcases family_descends (prefixWord ++ tailWord_352429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352452 : List Nat := [2, 3, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_352452 : Nat := 118140960795 + 352452 * 2 ^ 59
def prefixEnd_352452 : Nat := 4983230072969 + 3 ^ 40 * 352452 * 2
def baseEnd_352452 : Nat := 60325761212853421209703

theorem tailTrace_352452 : CollatzResearch.WordTrace tailWord_352452 prefixEnd_352452 60325761212853421209703 := by
  unfold tailWord_352452
  simp only [CollatzResearch.WordTrace]
  refine ⟨6427490259567036427209805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8569987012756048569613073 6427490259567036427209805)
  ·
    refine ⟨2410308847337638660203677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6427490259567036427209805 2410308847337638660203677)
    ·
      refine ⟨903865817751614497576379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2410308847337638660203677 903865817751614497576379)
      ·
        refine ⟨1355798726627421746364569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903865817751614497576379 1355798726627421746364569)
        ·
          refine ⟨1016849044970566309773427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1355798726627421746364569 1016849044970566309773427)
          ·
            refine ⟨1525273567455849464660141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016849044970566309773427 1525273567455849464660141)
            ·
              refine ⟨571977587795943549247553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1525273567455849464660141 571977587795943549247553)
              ·
                refine ⟨428983190846957661935665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 571977587795943549247553 428983190846957661935665)
                ·
                  refine ⟨321737393135218246451749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428983190846957661935665 321737393135218246451749)
                  ·
                    refine ⟨60325761212853421209703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 321737393135218246451749 60325761212853421209703)
                    ·
                      rfl

theorem cell23_352452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_352452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352452 prefixEnd_352452 := by exact prefixLift 352452
  have htrace : WordTrace (prefixWord ++ tailWord_352452) baseStart_352452 baseEnd_352452 := by
    simpa [prefixWord, tailWord_352452, baseEnd_352452] using wordTrace_append hprefix tailTrace_352452
  have hstable : (prefixWord ++ tailWord_352452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352452).length < 2 ^ (prefixWord ++ tailWord_352452).sum := by decide
  have hdescent : baseEnd_352452 < baseStart_352452 := by decide
  rcases family_descends (prefixWord ++ tailWord_352452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352469 : List Nat := [1, 3, 2, 4, 2, 1, 3, 1, 2, 4]
def baseStart_352469 : Nat := 118140960795 + 352469 * 2 ^ 59
def prefixEnd_352469 : Nat := 4983230072969 + 3 ^ 40 * 352469 * 2
def baseEnd_352469 : Nat := 60328670936562232372177

theorem tailTrace_352469 : CollatzResearch.WordTrace tailWord_352469 prefixEnd_352469 60328670936562232372177 := by
  unfold tailWord_352469
  simp only [CollatzResearch.WordTrace]
  refine ⟨12855600560072484757788461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8570400373381656505192307 12855600560072484757788461)
  ·
    refine ⟨4820850210027181784170673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12855600560072484757788461 4820850210027181784170673)
    ·
      refine ⟨3615637657520386338128005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4820850210027181784170673 3615637657520386338128005)
      ·
        refine ⟨677932060785072438399001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3615637657520386338128005 677932060785072438399001)
        ·
          refine ⟨508449045588804328799251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677932060785072438399001 508449045588804328799251)
          ·
            refine ⟨762673568383206493198877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508449045588804328799251 762673568383206493198877)
            ·
              refine ⟨286002588143702434949579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 762673568383206493198877 286002588143702434949579)
              ·
                refine ⟨429003882215553652424369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286002588143702434949579 429003882215553652424369)
                ·
                  refine ⟨321752911661665239318277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429003882215553652424369 321752911661665239318277)
                  ·
                    refine ⟨60328670936562232372177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 321752911661665239318277 60328670936562232372177)
                    ·
                      rfl

theorem cell23_352469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_352469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352469 prefixEnd_352469 := by exact prefixLift 352469
  have htrace : WordTrace (prefixWord ++ tailWord_352469) baseStart_352469 baseEnd_352469 := by
    simpa [prefixWord, tailWord_352469, baseEnd_352469] using wordTrace_append hprefix tailTrace_352469
  have hstable : (prefixWord ++ tailWord_352469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352469).length < 2 ^ (prefixWord ++ tailWord_352469).sum := by decide
  have hdescent : baseEnd_352469 < baseStart_352469 := by decide
  rcases family_descends (prefixWord ++ tailWord_352469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352488 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_352488 : Nat := 118140960795 + 352488 * 2 ^ 59
def prefixEnd_352488 : Nat := 4983230072969 + 3 ^ 40 * 352488 * 2
def baseEnd_352488 : Nat := 180995768942122122778943

theorem tailTrace_352488 : CollatzResearch.WordTrace tailWord_352488 prefixEnd_352488 180995768942122122778943 := by
  unfold tailWord_352488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6428146773501825501365059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8570862364669100668486745 6428146773501825501365059)
  ·
    refine ⟨9642220160252738252047589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6428146773501825501365059 9642220160252738252047589)
    ·
      refine ⟨1807916280047388422258923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9642220160252738252047589 1807916280047388422258923)
      ·
        refine ⟨2711874420071082633388385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1807916280047388422258923 2711874420071082633388385)
        ·
          refine ⟨2033905815053311975041289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2711874420071082633388385 2033905815053311975041289)
          ·
            refine ⟨1525429361289983981280967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2033905815053311975041289 1525429361289983981280967)
            ·
              refine ⟨2288144041934975971921451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525429361289983981280967 2288144041934975971921451)
              ·
                refine ⟨3432216062902463957882177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288144041934975971921451 3432216062902463957882177)
                ·
                  refine ⟨2574162047176847968411633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3432216062902463957882177 2574162047176847968411633)
                  ·
                    refine ⟨1930621535382635976308725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2574162047176847968411633 1930621535382635976308725)
                    ·
                      refine ⟨180995768942122122778943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1930621535382635976308725 180995768942122122778943)
                      ·
                        rfl

theorem cell23_352488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_352488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352488 prefixEnd_352488 := by exact prefixLift 352488
  have htrace : WordTrace (prefixWord ++ tailWord_352488) baseStart_352488 baseEnd_352488 := by
    simpa [prefixWord, tailWord_352488, baseEnd_352488] using wordTrace_append hprefix tailTrace_352488
  have hstable : (prefixWord ++ tailWord_352488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352488).length < 2 ^ (prefixWord ++ tailWord_352488).sum := by decide
  have hdescent : baseEnd_352488 < baseStart_352488 := by decide
  rcases family_descends (prefixWord ++ tailWord_352488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352493 : List Nat := [1, 5, 1, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_352493 : Nat := 118140960795 + 352493 * 2 ^ 59
def prefixEnd_352493 : Nat := 4983230072969 + 3 ^ 40 * 352493 * 2
def baseEnd_352493 : Nat := 180998336345394603216421

theorem tailTrace_352493 : CollatzResearch.WordTrace tailWord_352493 prefixEnd_352493 180998336345394603216421 := by
  unfold tailWord_352493
  simp only [CollatzResearch.WordTrace]
  refine ⟨12856475911985536856662133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8570983941323691237774755 12856475911985536856662133)
  ·
    refine ⟨1205294616748644080312075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12856475911985536856662133 1205294616748644080312075)
    ·
      refine ⟨1807941925122966120468113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1205294616748644080312075 1807941925122966120468113)
      ·
        refine ⟨1355956443842224590351085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1807941925122966120468113 1355956443842224590351085)
        ·
          refine ⟨508483666440834221381657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1355956443842224590351085 508483666440834221381657)
          ·
            refine ⟨381362749830625666036243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508483666440834221381657 381362749830625666036243)
            ·
              refine ⟨572044124745938499054365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381362749830625666036243 572044124745938499054365)
              ·
                refine ⟨214516546779726937145387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 572044124745938499054365 214516546779726937145387)
                ·
                  refine ⟨321774820169590405718081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214516546779726937145387 321774820169590405718081)
                  ·
                    refine ⟨241331115127192804288561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 321774820169590405718081 241331115127192804288561)
                    ·
                      refine ⟨180998336345394603216421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241331115127192804288561 180998336345394603216421)
                      ·
                        rfl

theorem cell23_352493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_352493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352493 prefixEnd_352493 := by exact prefixLift 352493
  have htrace : WordTrace (prefixWord ++ tailWord_352493) baseStart_352493 baseEnd_352493 := by
    simpa [prefixWord, tailWord_352493, baseEnd_352493] using wordTrace_append hprefix tailTrace_352493
  have hstable : (prefixWord ++ tailWord_352493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352493).length < 2 ^ (prefixWord ++ tailWord_352493).sum := by decide
  have hdescent : baseEnd_352493 < baseStart_352493 := by decide
  rcases family_descends (prefixWord ++ tailWord_352493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352565 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_352565 : Nat := 118140960795 + 352565 * 2 ^ 59
def prefixEnd_352565 : Nat := 4983230072969 + 3 ^ 40 * 352565 * 2
def baseEnd_352565 : Nat := 181035306952518321516089

theorem tailTrace_352565 : CollatzResearch.WordTrace tailWord_352565 prefixEnd_352565 181035306952518321516089 := by
  unfold tailWord_352565
  simp only [CollatzResearch.WordTrace]
  refine ⟨12859101967724693153283149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8572734645149795435522099 12859101967724693153283149)
  ·
    refine ⟨4822163237896759932481181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12859101967724693153283149 4822163237896759932481181)
    ·
      refine ⟨1808311214211284974680443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4822163237896759932481181 1808311214211284974680443)
      ·
        refine ⟨2712466821316927462020665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1808311214211284974680443 2712466821316927462020665)
        ·
          refine ⟨2034350115987695596515499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2712466821316927462020665 2034350115987695596515499)
          ·
            refine ⟨3051525173981543394773249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034350115987695596515499 3051525173981543394773249)
            ·
              refine ⟨2288643880486157546079937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3051525173981543394773249 2288643880486157546079937)
              ·
                refine ⟨1716482910364618159559953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2288643880486157546079937 1716482910364618159559953)
                ·
                  refine ⟨1287362182773463619669965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1716482910364618159559953 1287362182773463619669965)
                  ·
                    refine ⟨482760818540048857376237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1287362182773463619669965 482760818540048857376237)
                    ·
                      refine ⟨181035306952518321516089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 482760818540048857376237 181035306952518321516089)
                      ·
                        rfl

theorem cell23_352565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_352565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352565 prefixEnd_352565 := by exact prefixLift 352565
  have htrace : WordTrace (prefixWord ++ tailWord_352565) baseStart_352565 baseEnd_352565 := by
    simpa [prefixWord, tailWord_352565, baseEnd_352565] using wordTrace_append hprefix tailTrace_352565
  have hstable : (prefixWord ++ tailWord_352565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352565).length < 2 ^ (prefixWord ++ tailWord_352565).sum := by decide
  have hdescent : baseEnd_352565 < baseStart_352565 := by decide
  rcases family_descends (prefixWord ++ tailWord_352565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352575 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 1, 7, 2]
def baseStart_352575 : Nat := 118140960795 + 352575 * 2 ^ 59
def prefixEnd_352575 : Nat := 4983230072969 + 3 ^ 40 * 352575 * 2
def baseEnd_352575 : Nat := 181040441759063282391043

theorem tailTrace_352575 : CollatzResearch.WordTrace tailWord_352575 prefixEnd_352575 181040441759063282391043 := by
  unfold tailWord_352575
  simp only [CollatzResearch.WordTrace]
  refine ⟨12859466697688464861147179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8572977798458976574098119 12859466697688464861147179)
  ·
    refine ⟨19289200046532697291720769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12859466697688464861147179 19289200046532697291720769)
    ·
      refine ⟨14466900034899522968790577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19289200046532697291720769 14466900034899522968790577)
      ·
        refine ⟨10850175026174642226592933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14466900034899522968790577 10850175026174642226592933)
        ·
          refine ⟨2034407817407745417486175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10850175026174642226592933 2034407817407745417486175)
          ·
            refine ⟨3051611726111618126229263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034407817407745417486175 3051611726111618126229263)
            ·
              refine ⟨4577417589167427189343895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051611726111618126229263 4577417589167427189343895)
              ·
                refine ⟨6866126383751140784015843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4577417589167427189343895 6866126383751140784015843)
                ·
                  refine ⟨10299189575626711176023765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6866126383751140784015843 10299189575626711176023765)
                  ·
                    refine ⟨241387255678751043188057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10299189575626711176023765 241387255678751043188057)
                    ·
                      refine ⟨181040441759063282391043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241387255678751043188057 181040441759063282391043)
                      ·
                        rfl

theorem cell23_352575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 7, 2].length) (baseStart_352575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352575 prefixEnd_352575 := by exact prefixLift 352575
  have htrace : WordTrace (prefixWord ++ tailWord_352575) baseStart_352575 baseEnd_352575 := by
    simpa [prefixWord, tailWord_352575, baseEnd_352575] using wordTrace_append hprefix tailTrace_352575
  have hstable : (prefixWord ++ tailWord_352575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352575).length < 2 ^ (prefixWord ++ tailWord_352575).sum := by decide
  have hdescent : baseEnd_352575 < baseStart_352575 := by decide
  rcases family_descends (prefixWord ++ tailWord_352575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352625 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 4, 2, 3]
def baseStart_352625 : Nat := 118140960795 + 352625 * 2 ^ 59
def prefixEnd_352625 : Nat := 4983230072969 + 3 ^ 40 * 352625 * 2
def baseEnd_352625 : Nat := 181066115791788086765813

theorem tailTrace_352625 : CollatzResearch.WordTrace tailWord_352625 prefixEnd_352625 181066115791788086765813 := by
  unfold tailWord_352625
  simp only [CollatzResearch.WordTrace]
  refine ⟨12861290347507323400467329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8574193565004882266978219 12861290347507323400467329)
  ·
    refine ⟨9645967760630492550350497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12861290347507323400467329 9645967760630492550350497)
    ·
      refine ⟨7234475820472869412762873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9645967760630492550350497 7234475820472869412762873)
      ·
        refine ⟨5425856865354652059572155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7234475820472869412762873 5425856865354652059572155)
        ·
          refine ⟨8138785298031978089358233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5425856865354652059572155 8138785298031978089358233)
          ·
            refine ⟨6104088973523983567018675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8138785298031978089358233 6104088973523983567018675)
            ·
              refine ⟨9156133460285975350528013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6104088973523983567018675 9156133460285975350528013)
              ·
                refine ⟨3433550047607240756448005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9156133460285975350528013 3433550047607240756448005)
                ·
                  refine ⟨643790633926357641834001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3433550047607240756448005 643790633926357641834001)
                  ·
                    refine ⟨482842975444768231375501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 643790633926357641834001 482842975444768231375501)
                    ·
                      refine ⟨181066115791788086765813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 482842975444768231375501 181066115791788086765813)
                      ·
                        rfl

theorem cell23_352625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_352625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352625 prefixEnd_352625 := by exact prefixLift 352625
  have htrace : WordTrace (prefixWord ++ tailWord_352625) baseStart_352625 baseEnd_352625 := by
    simpa [prefixWord, tailWord_352625, baseEnd_352625] using wordTrace_append hprefix tailTrace_352625
  have hstable : (prefixWord ++ tailWord_352625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352625).length < 2 ^ (prefixWord ++ tailWord_352625).sum := by decide
  have hdescent : baseEnd_352625 < baseStart_352625 := by decide
  rcases family_descends (prefixWord ++ tailWord_352625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352666 : List Nat := [3, 1, 1, 4, 1, 4, 1, 3, 1, 4]
def baseStart_352666 : Nat := 118140960795 + 352666 * 2 ^ 59
def prefixEnd_352666 : Nat := 4983230072969 + 3 ^ 40 * 352666 * 2
def baseEnd_352666 : Nat := 60362389499540808784375

theorem tailTrace_352666 : CollatzResearch.WordTrace tailWord_352666 prefixEnd_352666 60362389499540808784375 := by
  unfold tailWord_352666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215696435089696850677463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8575190493572524935139901 3215696435089696850677463)
  ·
    refine ⟨4823544652634545276016195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3215696435089696850677463 4823544652634545276016195)
    ·
      refine ⟨7235316978951817914024293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4823544652634545276016195 7235316978951817914024293)
      ·
        refine ⟨1356621933553465858879555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7235316978951817914024293 1356621933553465858879555)
        ·
          refine ⟨2034932900330198788319333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356621933553465858879555 2034932900330198788319333)
          ·
            refine ⟨381549918811912272809875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2034932900330198788319333 381549918811912272809875)
            ·
              refine ⟨572324878217868409214813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381549918811912272809875 572324878217868409214813)
              ·
                refine ⟨214621829331700653455555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 572324878217868409214813 214621829331700653455555)
                ·
                  refine ⟨321932743997550980183333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214621829331700653455555 321932743997550980183333)
                  ·
                    refine ⟨60362389499540808784375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 321932743997550980183333 60362389499540808784375)
                    ·
                      rfl

theorem cell23_352666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_352666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352666 prefixEnd_352666 := by exact prefixLift 352666
  have htrace : WordTrace (prefixWord ++ tailWord_352666) baseStart_352666 baseEnd_352666 := by
    simpa [prefixWord, tailWord_352666, baseEnd_352666] using wordTrace_append hprefix tailTrace_352666
  have hstable : (prefixWord ++ tailWord_352666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352666).length < 2 ^ (prefixWord ++ tailWord_352666).sum := by decide
  have hdescent : baseEnd_352666 < baseStart_352666 := by decide
  rcases family_descends (prefixWord ++ tailWord_352666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352689 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 3, 1, 3]
def baseStart_352689 : Nat := 118140960795 + 352689 * 2 ^ 59
def prefixEnd_352689 : Nat := 4983230072969 + 3 ^ 40 * 352689 * 2
def baseEnd_352689 : Nat := 181098978553675836365519

theorem tailTrace_352689 : CollatzResearch.WordTrace tailWord_352689 prefixEnd_352689 181098978553675836365519 := by
  unfold tailWord_352689
  simp only [CollatzResearch.WordTrace]
  refine ⟨12863624619275462330797121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8575749746183641553864747 12863624619275462330797121)
  ·
    refine ⟨9647718464456596748097841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12863624619275462330797121 9647718464456596748097841)
    ·
      refine ⟨7235788848342447561073381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9647718464456596748097841 7235788848342447561073381)
      ·
        refine ⟨1356710409064208917701259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7235788848342447561073381 1356710409064208917701259)
        ·
          refine ⟨2035065613596313376551889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356710409064208917701259 2035065613596313376551889)
          ·
            refine ⟨1526299210197235032413917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2035065613596313376551889 1526299210197235032413917)
            ·
              refine ⟨572362203823963137155219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1526299210197235032413917 572362203823963137155219)
              ·
                refine ⟨858543305735944705732829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572362203823963137155219 858543305735944705732829)
                ·
                  refine ⟨321953739650979264649811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858543305735944705732829 321953739650979264649811)
                  ·
                    refine ⟨482930609476468896974717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 321953739650979264649811 482930609476468896974717)
                    ·
                      refine ⟨181098978553675836365519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 482930609476468896974717 181098978553675836365519)
                      ·
                        rfl

theorem cell23_352689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_352689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352689 prefixEnd_352689 := by exact prefixLift 352689
  have htrace : WordTrace (prefixWord ++ tailWord_352689) baseStart_352689 baseEnd_352689 := by
    simpa [prefixWord, tailWord_352689, baseEnd_352689] using wordTrace_append hprefix tailTrace_352689
  have hstable : (prefixWord ++ tailWord_352689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352689).length < 2 ^ (prefixWord ++ tailWord_352689).sum := by decide
  have hdescent : baseEnd_352689 < baseStart_352689 := by decide
  rcases family_descends (prefixWord ++ tailWord_352689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352712 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_352712 : Nat := 118140960795 + 352712 * 2 ^ 59
def prefixEnd_352712 : Nat := 4983230072969 + 3 ^ 40 * 352712 * 2
def baseEnd_352712 : Nat := 181110788608729246377913

theorem tailTrace_352712 : CollatzResearch.WordTrace tailWord_352712 prefixEnd_352712 181110788608729246377913 := by
  unfold tailWord_352712
  simp only [CollatzResearch.WordTrace]
  refine ⟨6432231749096068629442195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8576308998794758172589593 6432231749096068629442195)
  ·
    refine ⟨9648347623644102944163293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6432231749096068629442195 9648347623644102944163293)
    ·
      refine ⟨3618130358866538604061235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9648347623644102944163293 3618130358866538604061235)
      ·
        refine ⟨5427195538299807906091853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618130358866538604061235 5427195538299807906091853)
        ·
          refine ⟨2035198326862427964784445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5427195538299807906091853 2035198326862427964784445)
          ·
            refine ⟨763199372573410486794167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2035198326862427964784445 763199372573410486794167)
            ·
              refine ⟨1144799058860115730191251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763199372573410486794167 1144799058860115730191251)
              ·
                refine ⟨1717198588290173595286877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144799058860115730191251 1717198588290173595286877)
                ·
                  refine ⟨643949470608815098232579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1717198588290173595286877 643949470608815098232579)
                  ·
                    refine ⟨965924205913222647348869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 643949470608815098232579 965924205913222647348869)
                    ·
                      refine ⟨181110788608729246377913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 965924205913222647348869 181110788608729246377913)
                      ·
                        rfl

theorem cell23_352712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_352712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352712 prefixEnd_352712 := by exact prefixLift 352712
  have htrace : WordTrace (prefixWord ++ tailWord_352712) baseStart_352712 baseEnd_352712 := by
    simpa [prefixWord, tailWord_352712, baseEnd_352712] using wordTrace_append hprefix tailTrace_352712
  have hstable : (prefixWord ++ tailWord_352712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352712).length < 2 ^ (prefixWord ++ tailWord_352712).sum := by decide
  have hdescent : baseEnd_352712 < baseStart_352712 := by decide
  rcases family_descends (prefixWord ++ tailWord_352712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352716 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 2, 3, 2]
def baseStart_352716 : Nat := 118140960795 + 352716 * 2 ^ 59
def prefixEnd_352716 : Nat := 4983230072969 + 3 ^ 40 * 352716 * 2
def baseEnd_352716 : Nat := 181112842531347230727895

theorem tailTrace_352716 : CollatzResearch.WordTrace tailWord_352716 prefixEnd_352716 181112842531347230727895 := by
  unfold tailWord_352716
  simp only [CollatzResearch.WordTrace]
  refine ⟨6432304695088822971015001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8576406260118430628020001 6432304695088822971015001)
  ·
    refine ⟨4824228521316617228261251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6432304695088822971015001 4824228521316617228261251)
    ·
      refine ⟨7236342781974925842391877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4824228521316617228261251 7236342781974925842391877)
      ·
        refine ⟨1356814271620298595448477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7236342781974925842391877 1356814271620298595448477)
        ·
          refine ⟨508805351857611973293179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1356814271620298595448477 508805351857611973293179)
          ·
            refine ⟨763208027786417959939769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508805351857611973293179 763208027786417959939769)
            ·
              refine ⟨572406020839813469954827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763208027786417959939769 572406020839813469954827)
              ·
                refine ⟨858609031259720204932241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572406020839813469954827 858609031259720204932241)
                ·
                  refine ⟨643956773444790153699181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 858609031259720204932241 643956773444790153699181)
                  ·
                    refine ⟨241483790041796307637193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 643956773444790153699181 241483790041796307637193)
                    ·
                      refine ⟨181112842531347230727895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241483790041796307637193 181112842531347230727895)
                      ·
                        rfl

theorem cell23_352716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_352716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352716 prefixEnd_352716 := by exact prefixLift 352716
  have htrace : WordTrace (prefixWord ++ tailWord_352716) baseStart_352716 baseEnd_352716 := by
    simpa [prefixWord, tailWord_352716, baseEnd_352716] using wordTrace_append hprefix tailTrace_352716
  have hstable : (prefixWord ++ tailWord_352716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352716).length < 2 ^ (prefixWord ++ tailWord_352716).sum := by decide
  have hdescent : baseEnd_352716 < baseStart_352716 := by decide
  rcases family_descends (prefixWord ++ tailWord_352716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352726 : List Nat := [5, 2, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_352726 : Nat := 118140960795 + 352726 * 2 ^ 59
def prefixEnd_352726 : Nat := 4983230072969 + 3 ^ 40 * 352726 * 2
def baseEnd_352726 : Nat := 60372659112630730534283

theorem tailTrace_352726 : CollatzResearch.WordTrace tailWord_352726 prefixEnd_352726 60372659112630730534283 := by
  unfold tailWord_352726
  simp only [CollatzResearch.WordTrace]
  refine ⟨804060882508838603118377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8576649413427611766596021 804060882508838603118377)
  ·
    refine ⟨603045661881628952338783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 804060882508838603118377 603045661881628952338783)
    ·
      refine ⟨904568492822443428508175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603045661881628952338783 904568492822443428508175)
      ·
        refine ⟨1356852739233665142762263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904568492822443428508175 1356852739233665142762263)
        ·
          refine ⟨2035279108850497714143395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356852739233665142762263 2035279108850497714143395)
          ·
            refine ⟨3052918663275746571215093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035279108850497714143395 3052918663275746571215093)
            ·
              refine ⟨286211124682101241051415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3052918663275746571215093 286211124682101241051415)
              ·
                refine ⟨429316687023151861577123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286211124682101241051415 429316687023151861577123)
                ·
                  refine ⟨643975030534727792365685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429316687023151861577123 643975030534727792365685)
                  ·
                    refine ⟨60372659112630730534283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 643975030534727792365685 60372659112630730534283)
                    ·
                      rfl

theorem cell23_352726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_352726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352726 prefixEnd_352726 := by exact prefixLift 352726
  have htrace : WordTrace (prefixWord ++ tailWord_352726) baseStart_352726 baseEnd_352726 := by
    simpa [prefixWord, tailWord_352726, baseEnd_352726] using wordTrace_append hprefix tailTrace_352726
  have hstable : (prefixWord ++ tailWord_352726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352726).length < 2 ^ (prefixWord ++ tailWord_352726).sum := by decide
  have hdescent : baseEnd_352726 < baseStart_352726 := by decide
  rcases family_descends (prefixWord ++ tailWord_352726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352729 : List Nat := [1, 2, 1, 2, 4, 1, 5, 1, 1, 1, 4]
def baseStart_352729 : Nat := 118140960795 + 352729 * 2 ^ 59
def prefixEnd_352729 : Nat := 4983230072969 + 3 ^ 40 * 352729 * 2
def baseEnd_352729 : Nat := 181119517779855679865335

theorem tailTrace_352729 : CollatzResearch.WordTrace tailWord_352729 prefixEnd_352729 181119517779855679865335 := by
  unfold tailWord_352729
  simp only [CollatzResearch.WordTrace]
  refine ⟨12865083539130549162253241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8576722359420366108168827 12865083539130549162253241)
  ·
    refine ⟨9648812654347911871689931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12865083539130549162253241 9648812654347911871689931)
    ·
      refine ⟨14473218981521867807534897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9648812654347911871689931 14473218981521867807534897)
      ·
        refine ⟨10854914236141400855651173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14473218981521867807534897 10854914236141400855651173)
        ·
          refine ⟨2035296419276512660434595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10854914236141400855651173 2035296419276512660434595)
          ·
            refine ⟨3052944628914768990651893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035296419276512660434595 3052944628914768990651893)
            ·
              refine ⟨286213558960759592873615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3052944628914768990651893 286213558960759592873615)
              ·
                refine ⟨429320338441139389310423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286213558960759592873615 429320338441139389310423)
                ·
                  refine ⟨643980507661709083965635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429320338441139389310423 643980507661709083965635)
                  ·
                    refine ⟨965970761492563625948453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 643980507661709083965635 965970761492563625948453)
                    ·
                      refine ⟨181119517779855679865335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 965970761492563625948453 181119517779855679865335)
                      ·
                        rfl

theorem cell23_352729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 1, 1, 4].length) (baseStart_352729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352729 prefixEnd_352729 := by exact prefixLift 352729
  have htrace : WordTrace (prefixWord ++ tailWord_352729) baseStart_352729 baseEnd_352729 := by
    simpa [prefixWord, tailWord_352729, baseEnd_352729] using wordTrace_append hprefix tailTrace_352729
  have hstable : (prefixWord ++ tailWord_352729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352729).length < 2 ^ (prefixWord ++ tailWord_352729).sum := by decide
  have hdescent : baseEnd_352729 < baseStart_352729 := by decide
  rcases family_descends (prefixWord ++ tailWord_352729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352749 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_352749 : Nat := 118140960795 + 352749 * 2 ^ 59
def prefixEnd_352749 : Nat := 4983230072969 + 3 ^ 40 * 352749 * 2
def baseEnd_352749 : Nat := 181129787392945601615243

theorem tailTrace_352749 : CollatzResearch.WordTrace tailWord_352749 prefixEnd_352749 181129787392945601615243 := by
  unfold tailWord_352749
  simp only [CollatzResearch.WordTrace]
  refine ⟨12865812999058092577981301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8577208666038728385320867 12865812999058092577981301)
  ·
    refine ⟨1206169968661696179185747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12865812999058092577981301 1206169968661696179185747)
    ·
      refine ⟨1809254952992544268778621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1206169968661696179185747 1809254952992544268778621)
      ·
        refine ⟨678470607372204100791983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1809254952992544268778621 678470607372204100791983)
        ·
          refine ⟨1017705911058306151187975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678470607372204100791983 1017705911058306151187975)
          ·
            refine ⟨1526558866587459226781963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017705911058306151187975 1526558866587459226781963)
            ·
              refine ⟨2289838299881188840172945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526558866587459226781963 2289838299881188840172945)
              ·
                refine ⟨1717378724910891630129709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289838299881188840172945 1717378724910891630129709)
                ·
                  refine ⟨644017021841584361298641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1717378724910891630129709 644017021841584361298641)
                  ·
                    refine ⟨483012766381188270973981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 644017021841584361298641 483012766381188270973981)
                    ·
                      refine ⟨181129787392945601615243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 483012766381188270973981 181129787392945601615243)
                      ·
                        rfl

theorem cell23_352749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_352749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352749 prefixEnd_352749 := by exact prefixLift 352749
  have htrace : WordTrace (prefixWord ++ tailWord_352749) baseStart_352749 baseEnd_352749 := by
    simpa [prefixWord, tailWord_352749, baseEnd_352749] using wordTrace_append hprefix tailTrace_352749
  have hstable : (prefixWord ++ tailWord_352749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352749).length < 2 ^ (prefixWord ++ tailWord_352749).sum := by decide
  have hdescent : baseEnd_352749 < baseStart_352749 := by decide
  rcases family_descends (prefixWord ++ tailWord_352749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352765 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_352765 : Nat := 118140960795 + 352765 * 2 ^ 59
def prefixEnd_352765 : Nat := 4983230072969 + 3 ^ 40 * 352765 * 2
def baseEnd_352765 : Nat := 60379334361139179671723

theorem tailTrace_352765 : CollatzResearch.WordTrace tailWord_352765 prefixEnd_352765 60379334361139179671723 := by
  unfold tailWord_352765
  simp only [CollatzResearch.WordTrace]
  refine ⟨12866396567000127310563749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8577597711333418207042499 12866396567000127310563749)
  ·
    refine ⟨2412449356312523870730703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12866396567000127310563749 2412449356312523870730703)
    ·
      refine ⟨3618674034468785806096055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2412449356312523870730703 3618674034468785806096055)
      ·
        refine ⟨5428011051703178709144083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618674034468785806096055 5428011051703178709144083)
        ·
          refine ⟨8142016577554768063716125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5428011051703178709144083 8142016577554768063716125)
          ·
            refine ⟨3053256216583038023893547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8142016577554768063716125 3053256216583038023893547)
            ·
              refine ⟨4579884324874557035840321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3053256216583038023893547 4579884324874557035840321)
              ·
                refine ⟨3434913243655917776880241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4579884324874557035840321 3434913243655917776880241)
                ·
                  refine ⟨2576184932741938332660181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3434913243655917776880241 2576184932741938332660181)
                  ·
                    refine ⟨60379334361139179671723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2576184932741938332660181 60379334361139179671723)
                    ·
                      rfl

theorem cell23_352765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_352765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352765 prefixEnd_352765 := by exact prefixLift 352765
  have htrace : WordTrace (prefixWord ++ tailWord_352765) baseStart_352765 baseEnd_352765 := by
    simpa [prefixWord, tailWord_352765, baseEnd_352765] using wordTrace_append hprefix tailTrace_352765
  have hstable : (prefixWord ++ tailWord_352765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352765).length < 2 ^ (prefixWord ++ tailWord_352765).sum := by decide
  have hdescent : baseEnd_352765 < baseStart_352765 := by decide
  rcases family_descends (prefixWord ++ tailWord_352765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352785 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_352785 : Nat := 118140960795 + 352785 * 2 ^ 59
def prefixEnd_352785 : Nat := 4983230072969 + 3 ^ 40 * 352785 * 2
def baseEnd_352785 : Nat := 181148272696507460765077

theorem tailTrace_352785 : CollatzResearch.WordTrace tailWord_352785 prefixEnd_352785 181148272696507460765077 := by
  unfold tailWord_352785
  simp only [CollatzResearch.WordTrace]
  refine ⟨12867126026927670726291809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8578084017951780484194539 12867126026927670726291809)
  ·
    refine ⟨9650344520195753044718857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12867126026927670726291809 9650344520195753044718857)
    ·
      refine ⟨7237758390146814783539143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9650344520195753044718857 7237758390146814783539143)
      ·
        refine ⟨10856637585220222175308715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7237758390146814783539143 10856637585220222175308715)
        ·
          refine ⟨16284956377830333262963073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10856637585220222175308715 16284956377830333262963073)
          ·
            refine ⟨12213717283372749947222305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16284956377830333262963073 12213717283372749947222305)
            ·
              refine ⟨9160287962529562460416729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12213717283372749947222305 9160287962529562460416729)
              ·
                refine ⟨6870215971897171845312547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9160287962529562460416729 6870215971897171845312547)
                ·
                  refine ⟨10305323957845757767968821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6870215971897171845312547 10305323957845757767968821)
                  ·
                    refine ⟨966124121048039790747077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10305323957845757767968821 966124121048039790747077)
                    ·
                      refine ⟨181148272696507460765077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 966124121048039790747077 181148272696507460765077)
                      ·
                        rfl

theorem cell23_352785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_352785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352785 prefixEnd_352785 := by exact prefixLift 352785
  have htrace : WordTrace (prefixWord ++ tailWord_352785) baseStart_352785 baseEnd_352785 := by
    simpa [prefixWord, tailWord_352785, baseEnd_352785] using wordTrace_append hprefix tailTrace_352785
  have hstable : (prefixWord ++ tailWord_352785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352785).length < 2 ^ (prefixWord ++ tailWord_352785).sum := by decide
  have hdescent : baseEnd_352785 < baseStart_352785 := by decide
  rcases family_descends (prefixWord ++ tailWord_352785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352796 : List Nat := [2, 2, 3, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_352796 : Nat := 118140960795 + 352796 * 2 ^ 59
def prefixEnd_352796 : Nat := 4983230072969 + 3 ^ 40 * 352796 * 2
def baseEnd_352796 : Nat := 181153920983706917727527

theorem tailTrace_352796 : CollatzResearch.WordTrace tailWord_352796 prefixEnd_352796 181153920983706917727527 := by
  unfold tailWord_352796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6433763614943909802471121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8578351486591879736628161 6433763614943909802471121)
  ·
    refine ⟨4825322711207932351853341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6433763614943909802471121 4825322711207932351853341)
    ·
      refine ⟨1809496016702974631945003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4825322711207932351853341 1809496016702974631945003)
      ·
        refine ⟨2714244025054461947917505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1809496016702974631945003 2714244025054461947917505)
        ·
          refine ⟨2035683018790846460938129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2714244025054461947917505 2035683018790846460938129)
          ·
            refine ⟨1526762264093134845703597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2035683018790846460938129 1526762264093134845703597)
            ·
              refine ⟨572535849034925567138849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1526762264093134845703597 572535849034925567138849)
              ·
                refine ⟨429401886776194175354137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572535849034925567138849 429401886776194175354137)
                ·
                  refine ⟨322051415082145631515603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429401886776194175354137 322051415082145631515603)
                  ·
                    refine ⟨483077122623218447273405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 322051415082145631515603 483077122623218447273405)
                    ·
                      refine ⟨181153920983706917727527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 483077122623218447273405 181153920983706917727527)
                      ·
                        rfl

theorem cell23_352796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_352796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352796 prefixEnd_352796 := by exact prefixLift 352796
  have htrace : WordTrace (prefixWord ++ tailWord_352796) baseStart_352796 baseEnd_352796 := by
    simpa [prefixWord, tailWord_352796, baseEnd_352796] using wordTrace_append hprefix tailTrace_352796
  have hstable : (prefixWord ++ tailWord_352796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352796).length < 2 ^ (prefixWord ++ tailWord_352796).sum := by decide
  have hdescent : baseEnd_352796 < baseStart_352796 := by decide
  rcases family_descends (prefixWord ++ tailWord_352796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352889 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 2, 5]
def baseStart_352889 : Nat := 118140960795 + 352889 * 2 ^ 59
def prefixEnd_352889 : Nat := 4983230072969 + 3 ^ 40 * 352889 * 2
def baseEnd_352889 : Nat := 60400558228191684621533

theorem tailTrace_352889 : CollatzResearch.WordTrace tailWord_352889 prefixEnd_352889 60400558228191684621533 := by
  unfold tailWord_352889
  simp only [CollatzResearch.WordTrace]
  refine ⟨12870919218550896488077721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8580612812367264325385147 12870919218550896488077721)
  ·
    refine ⟨9653189413913172366058291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12870919218550896488077721 9653189413913172366058291)
    ·
      refine ⟨14479784120869758549087437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9653189413913172366058291 14479784120869758549087437)
      ·
        refine ⟨5429919045326159455907789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14479784120869758549087437 5429919045326159455907789)
        ·
          refine ⟨2036219641997309795965421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5429919045326159455907789 2036219641997309795965421)
          ·
            refine ⟨763582365748991173487033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2036219641997309795965421 763582365748991173487033)
            ·
              refine ⟨572686774311743380115275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763582365748991173487033 572686774311743380115275)
              ·
                refine ⟨859030161467615070172913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572686774311743380115275 859030161467615070172913)
                ·
                  refine ⟨644272621100711302629685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 859030161467615070172913 644272621100711302629685)
                  ·
                    refine ⟨60400558228191684621533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 644272621100711302629685 60400558228191684621533)
                    ·
                      rfl

theorem cell23_352889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 5].length) (baseStart_352889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352889 prefixEnd_352889 := by exact prefixLift 352889
  have htrace : WordTrace (prefixWord ++ tailWord_352889) baseStart_352889 baseEnd_352889 := by
    simpa [prefixWord, tailWord_352889, baseEnd_352889] using wordTrace_append hprefix tailTrace_352889
  have hstable : (prefixWord ++ tailWord_352889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352889).length < 2 ^ (prefixWord ++ tailWord_352889).sum := by decide
  have hdescent : baseEnd_352889 < baseStart_352889 := by decide
  rcases family_descends (prefixWord ++ tailWord_352889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352892 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_352892 : Nat := 118140960795 + 352892 * 2 ^ 59
def prefixEnd_352892 : Nat := 4983230072969 + 3 ^ 40 * 352892 * 2
def baseEnd_352892 : Nat := 181203215126538542127085

theorem tailTrace_352892 : CollatzResearch.WordTrace tailWord_352892 prefixEnd_352892 181203215126538542127085 := by
  unfold tailWord_352892
  simp only [CollatzResearch.WordTrace]
  refine ⟨6435514318770014000218465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8580685758360018666957953 6435514318770014000218465)
  ·
    refine ⟨4826635739077510500163849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6435514318770014000218465 4826635739077510500163849)
    ·
      refine ⟨3619976804308132875122887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4826635739077510500163849 3619976804308132875122887)
      ·
        refine ⟨5429965206462199312684331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3619976804308132875122887 5429965206462199312684331)
        ·
          refine ⟨8144947809693298969026497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5429965206462199312684331 8144947809693298969026497)
          ·
            refine ⟨6108710857269974226769873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8144947809693298969026497 6108710857269974226769873)
            ·
              refine ⟨4581533142952480670077405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6108710857269974226769873 4581533142952480670077405)
              ·
                refine ⟨1718074928607180251279027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4581533142952480670077405 1718074928607180251279027)
                ·
                  refine ⟨2577112392910770376918541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718074928607180251279027 2577112392910770376918541)
                  ·
                    refine ⟨966417147341538891344453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2577112392910770376918541 966417147341538891344453)
                    ·
                      refine ⟨181203215126538542127085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 966417147341538891344453 181203215126538542127085)
                      ·
                        rfl

theorem cell23_352892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_352892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352892 prefixEnd_352892 := by exact prefixLift 352892
  have htrace : WordTrace (prefixWord ++ tailWord_352892) baseStart_352892 baseEnd_352892 := by
    simpa [prefixWord, tailWord_352892, baseEnd_352892] using wordTrace_append hprefix tailTrace_352892
  have hstable : (prefixWord ++ tailWord_352892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352892).length < 2 ^ (prefixWord ++ tailWord_352892).sum := by decide
  have hdescent : baseEnd_352892 < baseStart_352892 := by decide
  rcases family_descends (prefixWord ++ tailWord_352892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352912 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 3]
def baseStart_352912 : Nat := 118140960795 + 352912 * 2 ^ 59
def prefixEnd_352912 : Nat := 4983230072969 + 3 ^ 40 * 352912 * 2
def baseEnd_352912 : Nat := 181213484739628463876993

theorem tailTrace_352912 : CollatzResearch.WordTrace tailWord_352912 prefixEnd_352912 181213484739628463876993 := by
  unfold tailWord_352912
  simp only [CollatzResearch.WordTrace]
  refine ⟨6435879048733785708082495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8581172064978380944109993 6435879048733785708082495)
  ·
    refine ⟨9653818573100678562123743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6435879048733785708082495 9653818573100678562123743)
    ·
      refine ⟨14480727859651017843185615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9653818573100678562123743 14480727859651017843185615)
      ·
        refine ⟨21721091789476526764778423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14480727859651017843185615 21721091789476526764778423)
        ·
          refine ⟨32581637684214790147167635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21721091789476526764778423 32581637684214790147167635)
          ·
            refine ⟨48872456526322185220751453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32581637684214790147167635 48872456526322185220751453)
            ·
              refine ⟨18327171197370819457781795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48872456526322185220751453 18327171197370819457781795)
              ·
                refine ⟨27490756796056229186672693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18327171197370819457781795 27490756796056229186672693)
                ·
                  refine ⟨2577258449630271486250565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27490756796056229186672693 2577258449630271486250565)
                  ·
                    refine ⟨483235959305675903671981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2577258449630271486250565 483235959305675903671981)
                    ·
                      refine ⟨181213484739628463876993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 483235959305675903671981 181213484739628463876993)
                      ·
                        rfl

theorem cell23_352912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 3].length) (baseStart_352912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352912 prefixEnd_352912 := by exact prefixLift 352912
  have htrace : WordTrace (prefixWord ++ tailWord_352912) baseStart_352912 baseEnd_352912 := by
    simpa [prefixWord, tailWord_352912, baseEnd_352912] using wordTrace_append hprefix tailTrace_352912
  have hstable : (prefixWord ++ tailWord_352912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352912).length < 2 ^ (prefixWord ++ tailWord_352912).sum := by decide
  have hdescent : baseEnd_352912 < baseStart_352912 := by decide
  rcases family_descends (prefixWord ++ tailWord_352912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352919 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 3, 4]
def baseStart_352919 : Nat := 118140960795 + 352919 * 2 ^ 59
def prefixEnd_352919 : Nat := 4983230072969 + 3 ^ 40 * 352919 * 2
def baseEnd_352919 : Nat := 60405693034736645496487

theorem tailTrace_352919 : CollatzResearch.WordTrace tailWord_352919 prefixEnd_352919 60405693034736645496487 := by
  unfold tailWord_352919
  simp only [CollatzResearch.WordTrace]
  refine ⟨12872013408442211611669811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8581342272294807741113207 12872013408442211611669811)
  ·
    refine ⟨19308020112663317417504717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12872013408442211611669811 19308020112663317417504717)
    ·
      refine ⟨7240507542248744031564269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19308020112663317417504717 7240507542248744031564269)
      ·
        refine ⟨2715190328343279011836601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7240507542248744031564269 2715190328343279011836601)
        ·
          refine ⟨2036392746257459258877451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2715190328343279011836601 2036392746257459258877451)
          ·
            refine ⟨3054589119386188888316177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036392746257459258877451 3054589119386188888316177)
            ·
              refine ⟨2290941839539641666237133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3054589119386188888316177 2290941839539641666237133)
              ·
                refine ⟨859103189827365624838925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2290941839539641666237133 859103189827365624838925)
                ·
                  refine ⟨322163696185262109314597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859103189827365624838925 322163696185262109314597)
                  ·
                    refine ⟨60405693034736645496487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 322163696185262109314597 60405693034736645496487)
                    ·
                      rfl

theorem cell23_352919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_352919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352919 prefixEnd_352919 := by exact prefixLift 352919
  have htrace : WordTrace (prefixWord ++ tailWord_352919) baseStart_352919 baseEnd_352919 := by
    simpa [prefixWord, tailWord_352919, baseEnd_352919] using wordTrace_append hprefix tailTrace_352919
  have hstable : (prefixWord ++ tailWord_352919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352919).length < 2 ^ (prefixWord ++ tailWord_352919).sum := by decide
  have hdescent : baseEnd_352919 < baseStart_352919 := by decide
  rcases family_descends (prefixWord ++ tailWord_352919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352996 : List Nat := [2, 3, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_352996 : Nat := 118140960795 + 352996 * 2 ^ 59
def prefixEnd_352996 : Nat := 4983230072969 + 3 ^ 40 * 352996 * 2
def baseEnd_352996 : Nat := 60418872371535378408869

theorem tailTrace_352996 : CollatzResearch.WordTrace tailWord_352996 prefixEnd_352996 60418872371535378408869 := by
  unfold tailWord_352996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6437410914581626881111421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8583214552775502508148561 6437410914581626881111421)
  ·
    refine ⟨2414029092968110080416783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6437410914581626881111421 2414029092968110080416783)
    ·
      refine ⟨3621043639452165120625175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414029092968110080416783 3621043639452165120625175)
      ·
        refine ⟨5431565459178247680937763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3621043639452165120625175 5431565459178247680937763)
        ·
          refine ⟨8147348188767371521406645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5431565459178247680937763 8147348188767371521406645)
          ·
            refine ⟨763813892696941080131873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8147348188767371521406645 763813892696941080131873)
            ·
              refine ⟨572860419522705810098905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763813892696941080131873 572860419522705810098905)
              ·
                refine ⟨429645314642029357574179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572860419522705810098905 429645314642029357574179)
                ·
                  refine ⟨644467971963044036361269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429645314642029357574179 644467971963044036361269)
                  ·
                    refine ⟨60418872371535378408869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 644467971963044036361269 60418872371535378408869)
                    ·
                      rfl

theorem cell23_352996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_352996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_352996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_352996 prefixEnd_352996 := by exact prefixLift 352996
  have htrace : WordTrace (prefixWord ++ tailWord_352996) baseStart_352996 baseEnd_352996 := by
    simpa [prefixWord, tailWord_352996, baseEnd_352996] using wordTrace_append hprefix tailTrace_352996
  have hstable : (prefixWord ++ tailWord_352996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352996).length < 2 ^ (prefixWord ++ tailWord_352996).sum := by decide
  have hdescent : baseEnd_352996 < baseStart_352996 := by decide
  rcases family_descends (prefixWord ++ tailWord_352996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353009 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 6, 4]
def baseStart_353009 : Nat := 118140960795 + 353009 * 2 ^ 59
def prefixEnd_353009 : Nat := 4983230072969 + 3 ^ 40 * 353009 * 2
def baseEnd_353009 : Nat := 60421097454371528121349

theorem tailTrace_353009 : CollatzResearch.WordTrace tailWord_353009 prefixEnd_353009 60421097454371528121349 := by
  unfold tailWord_353009
  simp only [CollatzResearch.WordTrace]
  refine ⟨12875295978116156982446081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8583530652077437988297387 12875295978116156982446081)
  ·
    refine ⟨9656471983587117736834561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12875295978116156982446081 9656471983587117736834561)
    ·
      refine ⟨7242353987690338302625921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9656471983587117736834561 7242353987690338302625921)
      ·
        refine ⟨5431765490767753726969441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7242353987690338302625921 5431765490767753726969441)
        ·
          refine ⟨4073824118075815295227081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5431765490767753726969441 4073824118075815295227081)
          ·
            refine ⟨3055368088556861471420311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4073824118075815295227081 3055368088556861471420311)
            ·
              refine ⟨4583052132835292207130467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3055368088556861471420311 4583052132835292207130467)
              ·
                refine ⟨6874578199252938310695701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4583052132835292207130467 6874578199252938310695701)
                ·
                  refine ⟨322245853089981483313861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6874578199252938310695701 322245853089981483313861)
                  ·
                    refine ⟨60421097454371528121349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 322245853089981483313861 60421097454371528121349)
                    ·
                      rfl

theorem cell23_353009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_353009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353009 prefixEnd_353009 := by exact prefixLift 353009
  have htrace : WordTrace (prefixWord ++ tailWord_353009) baseStart_353009 baseEnd_353009 := by
    simpa [prefixWord, tailWord_353009, baseEnd_353009] using wordTrace_append hprefix tailTrace_353009
  have hstable : (prefixWord ++ tailWord_353009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353009).length < 2 ^ (prefixWord ++ tailWord_353009).sum := by decide
  have hdescent : baseEnd_353009 < baseStart_353009 := by decide
  rcases family_descends (prefixWord ++ tailWord_353009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353010 : List Nat := [3, 2, 1, 3, 1, 2, 3, 3, 1, 1, 3]
def baseStart_353010 : Nat := 118140960795 + 353010 * 2 ^ 59
def prefixEnd_353010 : Nat := 4983230072969 + 3 ^ 40 * 353010 * 2
def baseEnd_353010 : Nat := 181263805843769080451543

theorem tailTrace_353010 : CollatzResearch.WordTrace tailWord_353010 prefixEnd_353010 181263805843769080451543 := by
  unfold tailWord_353010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3218833112778133538308121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8583554967408356102154989 3218833112778133538308121)
  ·
    refine ⟨2414124834583600153731091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3218833112778133538308121 2414124834583600153731091)
    ·
      refine ⟨3621187251875400230596637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414124834583600153731091 3621187251875400230596637)
      ·
        refine ⟨1357945219453275086473739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3621187251875400230596637 1357945219453275086473739)
        ·
          refine ⟨2036917829179912629710609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357945219453275086473739 2036917829179912629710609)
          ·
            refine ⟨1527688371884934472282957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2036917829179912629710609 1527688371884934472282957)
            ·
              refine ⟨572883139456850427106109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1527688371884934472282957 572883139456850427106109)
              ·
                refine ⟨214831177296318910164791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 572883139456850427106109 214831177296318910164791)
                ·
                  refine ⟨322246765944478365247187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214831177296318910164791 322246765944478365247187)
                  ·
                    refine ⟨483370148916717547870781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 322246765944478365247187 483370148916717547870781)
                    ·
                      refine ⟨181263805843769080451543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 483370148916717547870781 181263805843769080451543)
                      ·
                        rfl

theorem cell23_353010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_353010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353010 prefixEnd_353010 := by exact prefixLift 353010
  have htrace : WordTrace (prefixWord ++ tailWord_353010) baseStart_353010 baseEnd_353010 := by
    simpa [prefixWord, tailWord_353010, baseEnd_353010] using wordTrace_append hprefix tailTrace_353010
  have hstable : (prefixWord ++ tailWord_353010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353010).length < 2 ^ (prefixWord ++ tailWord_353010).sum := by decide
  have hdescent : baseEnd_353010 < baseStart_353010 := by decide
  rcases family_descends (prefixWord ++ tailWord_353010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353033 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 3, 2, 2]
def baseStart_353033 : Nat := 118140960795 + 353033 * 2 ^ 59
def prefixEnd_353033 : Nat := 4983230072969 + 3 ^ 40 * 353033 * 2
def baseEnd_353033 : Nat := 181275615898822490463937

theorem tailTrace_353033 : CollatzResearch.WordTrace tailWord_353033 prefixEnd_353033 181275615898822490463937 := by
  unfold tailWord_353033
  simp only [CollatzResearch.WordTrace]
  refine ⟨12876171330029209081319753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8584114220019472720879835 12876171330029209081319753)
  ·
    refine ⟨9657128497521906810989815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12876171330029209081319753 9657128497521906810989815)
    ·
      refine ⟨14485692746282860216484723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9657128497521906810989815 14485692746282860216484723)
      ·
        refine ⟨21728539119424290324727085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14485692746282860216484723 21728539119424290324727085)
        ·
          refine ⟨8148202169784108871772657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21728539119424290324727085 8148202169784108871772657)
          ·
            refine ⟨6111151627338081653829493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8148202169784108871772657 6111151627338081653829493)
            ·
              refine ⟨572920465062945155046515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6111151627338081653829493 572920465062945155046515)
              ·
                refine ⟨859380697594417732569773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572920465062945155046515 859380697594417732569773)
                ·
                  refine ⟨322267761597906649713665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859380697594417732569773 322267761597906649713665)
                  ·
                    refine ⟨241700821198429987285249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 322267761597906649713665 241700821198429987285249)
                    ·
                      refine ⟨181275615898822490463937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241700821198429987285249 181275615898822490463937)
                      ·
                        rfl

theorem cell23_353033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 2, 2].length) (baseStart_353033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353033 prefixEnd_353033 := by exact prefixLift 353033
  have htrace : WordTrace (prefixWord ++ tailWord_353033) baseStart_353033 baseEnd_353033 := by
    simpa [prefixWord, tailWord_353033, baseEnd_353033] using wordTrace_append hprefix tailTrace_353033
  have hstable : (prefixWord ++ tailWord_353033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353033).length < 2 ^ (prefixWord ++ tailWord_353033).sum := by decide
  have hdescent : baseEnd_353033 < baseStart_353033 := by decide
  rcases family_descends (prefixWord ++ tailWord_353033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353119 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 4]
def baseStart_353119 : Nat := 118140960795 + 353119 * 2 ^ 59
def prefixEnd_353119 : Nat := 4983230072969 + 3 ^ 40 * 353119 * 2
def baseEnd_353119 : Nat := 181319775235109153988541

theorem tailTrace_353119 : CollatzResearch.WordTrace tailWord_353119 prefixEnd_353119 181319775235109153988541 := by
  unfold tailWord_353119
  simp only [CollatzResearch.WordTrace]
  refine ⟨12879308007717645768950411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8586205338478430512633607 12879308007717645768950411)
  ·
    refine ⟨19318962011576468653425617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12879308007717645768950411 19318962011576468653425617)
    ·
      refine ⟨14489221508682351490069213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19318962011576468653425617 14489221508682351490069213)
      ·
        refine ⟨5433458065755881808775955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14489221508682351490069213 5433458065755881808775955)
        ·
          refine ⟨8150187098633822713163933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5433458065755881808775955 8150187098633822713163933)
          ·
            refine ⟨3056320161987683517436475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8150187098633822713163933 3056320161987683517436475)
            ·
              refine ⟨4584480242981525276154713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3056320161987683517436475 4584480242981525276154713)
              ·
                refine ⟨3438360182236143957116035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4584480242981525276154713 3438360182236143957116035)
                ·
                  refine ⟨5157540273354215935674053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3438360182236143957116035 5157540273354215935674053)
                  ·
                    refine ⟨967038801253915487938885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5157540273354215935674053 967038801253915487938885)
                    ·
                      refine ⟨181319775235109153988541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 967038801253915487938885 181319775235109153988541)
                      ·
                        rfl

theorem cell23_353119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_353119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353119 prefixEnd_353119 := by exact prefixLift 353119
  have htrace : WordTrace (prefixWord ++ tailWord_353119) baseStart_353119 baseEnd_353119 := by
    simpa [prefixWord, tailWord_353119, baseEnd_353119] using wordTrace_append hprefix tailTrace_353119
  have hstable : (prefixWord ++ tailWord_353119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353119).length < 2 ^ (prefixWord ++ tailWord_353119).sum := by decide
  have hdescent : baseEnd_353119 < baseStart_353119 := by decide
  rcases family_descends (prefixWord ++ tailWord_353119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353123 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 1, 4, 2]
def baseStart_353123 : Nat := 118140960795 + 353123 * 2 ^ 59
def prefixEnd_353123 : Nat := 4983230072969 + 3 ^ 40 * 353123 * 2
def baseEnd_353123 : Nat := 181321829157727138338523

theorem tailTrace_353123 : CollatzResearch.WordTrace tailWord_353123 prefixEnd_353123 181321829157727138338523 := by
  unfold tailWord_353123
  simp only [CollatzResearch.WordTrace]
  refine ⟨12879453899703154452096023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8586302599802102968064015 12879453899703154452096023)
  ·
    refine ⟨19319180849554731678144035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12879453899703154452096023 19319180849554731678144035)
    ·
      refine ⟨28978771274332097517216053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19319180849554731678144035 28978771274332097517216053)
      ·
        refine ⟨2716759806968634142239005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28978771274332097517216053 2716759806968634142239005)
        ·
          refine ⟨1018784927613237803339627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2716759806968634142239005 1018784927613237803339627)
          ·
            refine ⟨1528177391419856705009441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018784927613237803339627 1528177391419856705009441)
            ·
              refine ⟨1146133043564892528757081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528177391419856705009441 1146133043564892528757081)
              ·
                refine ⟨859599782673669396567811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146133043564892528757081 859599782673669396567811)
                ·
                  refine ⟨1289399674010504094851717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859599782673669396567811 1289399674010504094851717)
                  ·
                    refine ⟨241762438876969517784697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1289399674010504094851717 241762438876969517784697)
                    ·
                      refine ⟨181321829157727138338523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241762438876969517784697 181321829157727138338523)
                      ·
                        rfl

theorem cell23_353123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_353123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353123 prefixEnd_353123 := by exact prefixLift 353123
  have htrace : WordTrace (prefixWord ++ tailWord_353123) baseStart_353123 baseEnd_353123 := by
    simpa [prefixWord, tailWord_353123, baseEnd_353123] using wordTrace_append hprefix tailTrace_353123
  have hstable : (prefixWord ++ tailWord_353123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353123).length < 2 ^ (prefixWord ++ tailWord_353123).sum := by decide
  have hdescent : baseEnd_353123 < baseStart_353123 := by decide
  rcases family_descends (prefixWord ++ tailWord_353123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353127 : List Nat := [1, 1, 5, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_353127 : Nat := 118140960795 + 353127 * 2 ^ 59
def prefixEnd_353127 : Nat := 4983230072969 + 3 ^ 40 * 353127 * 2
def baseEnd_353127 : Nat := 181323883080345122688505

theorem tailTrace_353127 : CollatzResearch.WordTrace tailWord_353127 prefixEnd_353127 181323883080345122688505 := by
  unfold tailWord_353127
  simp only [CollatzResearch.WordTrace]
  refine ⟨12879599791688663135241635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8586399861125775423494423 12879599791688663135241635)
  ·
    refine ⟨19319399687532994702862453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12879599791688663135241635 19319399687532994702862453)
    ·
      refine ⟨1811193720706218253393355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19319399687532994702862453 1811193720706218253393355)
      ·
        refine ⟨2716790581059327380090033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1811193720706218253393355 2716790581059327380090033)
        ·
          refine ⟨2037592935794495535067525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2716790581059327380090033 2037592935794495535067525)
          ·
            refine ⟨382048675461467912825161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2037592935794495535067525 382048675461467912825161)
            ·
              refine ⟨286536506596100934618871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382048675461467912825161 286536506596100934618871)
              ·
                refine ⟨429804759894151401928307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286536506596100934618871 429804759894151401928307)
                ·
                  refine ⟨644707139841227102892461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429804759894151401928307 644707139841227102892461)
                  ·
                    refine ⟨241765177440460163584673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 644707139841227102892461 241765177440460163584673)
                    ·
                      refine ⟨181323883080345122688505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241765177440460163584673 181323883080345122688505)
                      ·
                        rfl

theorem cell23_353127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_353127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353127 prefixEnd_353127 := by exact prefixLift 353127
  have htrace : WordTrace (prefixWord ++ tailWord_353127) baseStart_353127 baseEnd_353127 := by
    simpa [prefixWord, tailWord_353127, baseEnd_353127] using wordTrace_append hprefix tailTrace_353127
  have hstable : (prefixWord ++ tailWord_353127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353127).length < 2 ^ (prefixWord ++ tailWord_353127).sum := by decide
  have hdescent : baseEnd_353127 < baseStart_353127 := by decide
  rcases family_descends (prefixWord ++ tailWord_353127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353134 : List Nat := [4, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_353134 : Nat := 118140960795 + 353134 * 2 ^ 59
def prefixEnd_353134 : Nat := 4983230072969 + 3 ^ 40 * 353134 * 2
def baseEnd_353134 : Nat := 181327477444926595300973

theorem tailTrace_353134 : CollatzResearch.WordTrace tailWord_353134 prefixEnd_353134 181327477444926595300973 := by
  unfold tailWord_353134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1609981887832912916343307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8586570068442202220497637 1609981887832912916343307)
  ·
    refine ⟨2414972831749369374514961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1609981887832912916343307 2414972831749369374514961)
    ·
      refine ⟨1811229623812027030886221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2414972831749369374514961 1811229623812027030886221)
      ·
        refine ⟨679211108929510136582333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1811229623812027030886221 679211108929510136582333)
        ·
          refine ⟨254704165848566301218375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 679211108929510136582333 254704165848566301218375)
          ·
            refine ⟨382056248772849451827563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254704165848566301218375 382056248772849451827563)
            ·
              refine ⟨573084373159274177741345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382056248772849451827563 573084373159274177741345)
              ·
                refine ⟨429813279869455633306009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573084373159274177741345 429813279869455633306009)
                ·
                  refine ⟨322359959902091724979507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429813279869455633306009 322359959902091724979507)
                  ·
                    refine ⟨483539939853137587469261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 322359959902091724979507 483539939853137587469261)
                    ·
                      refine ⟨181327477444926595300973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 483539939853137587469261 181327477444926595300973)
                      ·
                        rfl

theorem cell23_353134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_353134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353134 prefixEnd_353134 := by exact prefixLift 353134
  have htrace : WordTrace (prefixWord ++ tailWord_353134) baseStart_353134 baseEnd_353134 := by
    simpa [prefixWord, tailWord_353134, baseEnd_353134] using wordTrace_append hprefix tailTrace_353134
  have hstable : (prefixWord ++ tailWord_353134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353134).length < 2 ^ (prefixWord ++ tailWord_353134).sum := by decide
  have hdescent : baseEnd_353134 < baseStart_353134 := by decide
  rcases family_descends (prefixWord ++ tailWord_353134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353157 : List Nat := [1, 3, 1, 1, 3, 4, 3, 1, 2, 2, 2]
def baseStart_353157 : Nat := 118140960795 + 353157 * 2 ^ 59
def prefixEnd_353157 : Nat := 4983230072969 + 3 ^ 40 * 353157 * 2
def baseEnd_353157 : Nat := 181339287499980005313367

theorem tailTrace_353157 : CollatzResearch.WordTrace tailWord_353157 prefixEnd_353157 181339287499980005313367 := by
  unfold tailWord_353157
  simp only [CollatzResearch.WordTrace]
  refine ⟨12880693981579978258833725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8587129321053318839222483 12880693981579978258833725)
  ·
    refine ⟨4830260243092491847062647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12880693981579978258833725 4830260243092491847062647)
    ·
      refine ⟨7245390364638737770593971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4830260243092491847062647 7245390364638737770593971)
      ·
        refine ⟨10868085546958106655890957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7245390364638737770593971 10868085546958106655890957)
        ·
          refine ⟨4075532080109289995959109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10868085546958106655890957 4075532080109289995959109)
          ·
            refine ⟨764162265020491874242333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4075532080109289995959109 764162265020491874242333)
            ·
              refine ⟨286560849382684452840875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 764162265020491874242333 286560849382684452840875)
              ·
                refine ⟨429841274074026679261313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286560849382684452840875 429841274074026679261313)
                ·
                  refine ⟨322380955555520009445985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429841274074026679261313 322380955555520009445985)
                  ·
                    refine ⟨241785716666640007084489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 322380955555520009445985 241785716666640007084489)
                    ·
                      refine ⟨181339287499980005313367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241785716666640007084489 181339287499980005313367)
                      ·
                        rfl

theorem cell23_353157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 2, 2, 2].length) (baseStart_353157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353157 prefixEnd_353157 := by exact prefixLift 353157
  have htrace : WordTrace (prefixWord ++ tailWord_353157) baseStart_353157 baseEnd_353157 := by
    simpa [prefixWord, tailWord_353157, baseEnd_353157] using wordTrace_append hprefix tailTrace_353157
  have hstable : (prefixWord ++ tailWord_353157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353157).length < 2 ^ (prefixWord ++ tailWord_353157).sum := by decide
  have hdescent : baseEnd_353157 < baseStart_353157 := by decide
  rcases family_descends (prefixWord ++ tailWord_353157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353169 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_353169 : Nat := 118140960795 + 353169 * 2 ^ 59
def prefixEnd_353169 : Nat := 4983230072969 + 3 ^ 40 * 353169 * 2
def baseEnd_353169 : Nat := 181345449267833958363311

theorem tailTrace_353169 : CollatzResearch.WordTrace tailWord_353169 prefixEnd_353169 181345449267833958363311 := by
  unfold tailWord_353169
  simp only [CollatzResearch.WordTrace]
  refine ⟨12881131657536504308270561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8587421105024336205513707 12881131657536504308270561)
  ·
    refine ⟨9660848743152378231202921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12881131657536504308270561 9660848743152378231202921)
    ·
      refine ⟨7245636557364283673402191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9660848743152378231202921 7245636557364283673402191)
      ·
        refine ⟨10868454836046425510103287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7245636557364283673402191 10868454836046425510103287)
        ·
          refine ⟨16302682254069638265154931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10868454836046425510103287 16302682254069638265154931)
          ·
            refine ⟨24454023381104457397732397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16302682254069638265154931 24454023381104457397732397)
            ·
              refine ⟨9170258767914171524149649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24454023381104457397732397 9170258767914171524149649)
              ·
                refine ⟨6877694075935628643112237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9170258767914171524149649 6877694075935628643112237)
                ·
                  refine ⟨2579135278475860741167089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6877694075935628643112237 2579135278475860741167089)
                  ·
                    refine ⟨1934351458856895555875317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2579135278475860741167089 1934351458856895555875317)
                    ·
                      refine ⟨181345449267833958363311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1934351458856895555875317 181345449267833958363311)
                      ·
                        rfl

theorem cell23_353169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_353169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353169 prefixEnd_353169 := by exact prefixLift 353169
  have htrace : WordTrace (prefixWord ++ tailWord_353169) baseStart_353169 baseEnd_353169 := by
    simpa [prefixWord, tailWord_353169, baseEnd_353169] using wordTrace_append hprefix tailTrace_353169
  have hstable : (prefixWord ++ tailWord_353169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353169).length < 2 ^ (prefixWord ++ tailWord_353169).sum := by decide
  have hdescent : baseEnd_353169 < baseStart_353169 := by decide
  rcases family_descends (prefixWord ++ tailWord_353169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353174 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_353174 : Nat := 118140960795 + 353174 * 2 ^ 59
def prefixEnd_353174 : Nat := 4983230072969 + 3 ^ 40 * 353174 * 2
def baseEnd_353174 : Nat := 181348016671106438800789

theorem tailTrace_353174 : CollatzResearch.WordTrace tailWord_353174 prefixEnd_353174 181348016671106438800789 := by
  unfold tailWord_353174
  simp only [CollatzResearch.WordTrace]
  refine ⟨805082126407399385137661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8587542681678926774801717 805082126407399385137661)
  ·
    refine ⟨301905797402774769426623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 805082126407399385137661 301905797402774769426623)
    ·
      refine ⟨452858696104162154139935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301905797402774769426623 452858696104162154139935)
      ·
        refine ⟨679288044156243231209903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452858696104162154139935 679288044156243231209903)
        ·
          refine ⟨1018932066234364846814855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679288044156243231209903 1018932066234364846814855)
          ·
            refine ⟨1528398099351547270222283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018932066234364846814855 1528398099351547270222283)
            ·
              refine ⟨2292597149027320905333425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528398099351547270222283 2292597149027320905333425)
              ·
                refine ⟨1719447861770490679000069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2292597149027320905333425 1719447861770490679000069)
                ·
                  refine ⟨322396474081967002312513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719447861770490679000069 322396474081967002312513)
                  ·
                    refine ⟨241797355561475251734385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 322396474081967002312513 241797355561475251734385)
                    ·
                      refine ⟨181348016671106438800789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241797355561475251734385 181348016671106438800789)
                      ·
                        rfl

theorem cell23_353174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_353174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353174 prefixEnd_353174 := by exact prefixLift 353174
  have htrace : WordTrace (prefixWord ++ tailWord_353174) baseStart_353174 baseEnd_353174 := by
    simpa [prefixWord, tailWord_353174, baseEnd_353174] using wordTrace_append hprefix tailTrace_353174
  have hstable : (prefixWord ++ tailWord_353174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353174).length < 2 ^ (prefixWord ++ tailWord_353174).sum := by decide
  have hdescent : baseEnd_353174 < baseStart_353174 := by decide
  rcases family_descends (prefixWord ++ tailWord_353174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353196 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_353196 : Nat := 118140960795 + 353196 * 2 ^ 59
def prefixEnd_353196 : Nat := 4983230072969 + 3 ^ 40 * 353196 * 2
def baseEnd_353196 : Nat := 181359313245505352725687

theorem tailTrace_353196 : CollatzResearch.WordTrace tailWord_353196 prefixEnd_353196 181359313245505352725687 := by
  unfold tailWord_353196
  simp only [CollatzResearch.WordTrace]
  refine ⟨6441058214219343959751721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8588077618959125279668961 6441058214219343959751721)
  ·
    refine ⟨4830793660664507969813791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6441058214219343959751721 4830793660664507969813791)
    ·
      refine ⟨7246190490996761954720687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4830793660664507969813791 7246190490996761954720687)
      ·
        refine ⟨10869285736495142932081031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7246190490996761954720687 10869285736495142932081031)
        ·
          refine ⟨16303928604742714398121547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10869285736495142932081031 16303928604742714398121547)
          ·
            refine ⟨24455892907114071597182321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16303928604742714398121547 24455892907114071597182321)
            ·
              refine ⟨18341919680335553697886741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24455892907114071597182321 18341919680335553697886741)
              ·
                refine ⟨859777485015729079588441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18341919680335553697886741 859777485015729079588441)
                ·
                  refine ⟨644833113761796809691331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 859777485015729079588441 644833113761796809691331)
                  ·
                    refine ⟨967249670642695214536997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 644833113761796809691331 967249670642695214536997)
                    ·
                      refine ⟨181359313245505352725687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 967249670642695214536997 181359313245505352725687)
                      ·
                        rfl

theorem cell23_353196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_353196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353196 prefixEnd_353196 := by exact prefixLift 353196
  have htrace : WordTrace (prefixWord ++ tailWord_353196) baseStart_353196 baseEnd_353196 := by
    simpa [prefixWord, tailWord_353196, baseEnd_353196] using wordTrace_append hprefix tailTrace_353196
  have hstable : (prefixWord ++ tailWord_353196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353196).length < 2 ^ (prefixWord ++ tailWord_353196).sum := by decide
  have hdescent : baseEnd_353196 < baseStart_353196 := by decide
  rcases family_descends (prefixWord ++ tailWord_353196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353197 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 7]
def baseStart_353197 : Nat := 118140960795 + 353197 * 2 ^ 59
def prefixEnd_353197 : Nat := 4983230072969 + 3 ^ 40 * 353197 * 2
def baseEnd_353197 : Nat := 20151091858462205423687

theorem tailTrace_353197 : CollatzResearch.WordTrace tailWord_353197 prefixEnd_353197 20151091858462205423687 := by
  unfold tailWord_353197
  simp only [CollatzResearch.WordTrace]
  refine ⟨12882152901435065090289845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8588101934290043393526563 12882152901435065090289845)
  ·
    refine ⟨1207701834509537352214673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12882152901435065090289845 1207701834509537352214673)
    ·
      refine ⟨905776375882153014161005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1207701834509537352214673 905776375882153014161005)
      ·
        refine ⟨339666140955807380310377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 905776375882153014161005 339666140955807380310377)
        ·
          refine ⟨254749605716855535232783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339666140955807380310377 254749605716855535232783)
          ·
            refine ⟨382124408575283302849175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254749605716855535232783 382124408575283302849175)
            ·
              refine ⟨573186612862924954273763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382124408575283302849175 573186612862924954273763)
              ·
                refine ⟨859779919294387431410645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573186612862924954273763 859779919294387431410645)
                ·
                  refine ⟨20151091858462205423687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 859779919294387431410645 20151091858462205423687)
                  ·
                    rfl

theorem cell23_353197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_353197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353197 prefixEnd_353197 := by exact prefixLift 353197
  have htrace : WordTrace (prefixWord ++ tailWord_353197) baseStart_353197 baseEnd_353197 := by
    simpa [prefixWord, tailWord_353197, baseEnd_353197] using wordTrace_append hprefix tailTrace_353197
  have hstable : (prefixWord ++ tailWord_353197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353197).length < 2 ^ (prefixWord ++ tailWord_353197).sum := by decide
  have hdescent : baseEnd_353197 < baseStart_353197 := by decide
  rcases family_descends (prefixWord ++ tailWord_353197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353199 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 5]
def baseStart_353199 : Nat := 118140960795 + 353199 * 2 ^ 59
def prefixEnd_353199 : Nat := 4983230072969 + 3 ^ 40 * 353199 * 2
def baseEnd_353199 : Nat := 181360853687468840988173

theorem tailTrace_353199 : CollatzResearch.WordTrace tailWord_353199 prefixEnd_353199 181360853687468840988173 := by
  unfold tailWord_353199
  simp only [CollatzResearch.WordTrace]
  refine ⟨12882225847427819431862651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8588150564951879621241767 12882225847427819431862651)
  ·
    refine ⟨19323338771141729147793977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12882225847427819431862651 19323338771141729147793977)
    ·
      refine ⟨14492504078356296860845483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19323338771141729147793977 14492504078356296860845483)
      ·
        refine ⟨21738756117534445291268225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14492504078356296860845483 21738756117534445291268225)
        ·
          refine ⟨16304067088150833968451169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21738756117534445291268225 16304067088150833968451169)
          ·
            refine ⟨12228050316113125476338377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16304067088150833968451169 12228050316113125476338377)
            ·
              refine ⟨9171037737084844107253783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12228050316113125476338377 9171037737084844107253783)
              ·
                refine ⟨13756556605627266160880675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9171037737084844107253783 13756556605627266160880675)
                ·
                  refine ⟨20634834908440899241321013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13756556605627266160880675 20634834908440899241321013)
                  ·
                    refine ⟨1934515772666334303873845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20634834908440899241321013 1934515772666334303873845)
                    ·
                      refine ⟨181360853687468840988173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1934515772666334303873845 181360853687468840988173)
                      ·
                        rfl

theorem cell23_353199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_353199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353199 prefixEnd_353199 := by exact prefixLift 353199
  have htrace : WordTrace (prefixWord ++ tailWord_353199) baseStart_353199 baseEnd_353199 := by
    simpa [prefixWord, tailWord_353199, baseEnd_353199] using wordTrace_append hprefix tailTrace_353199
  have hstable : (prefixWord ++ tailWord_353199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353199).length < 2 ^ (prefixWord ++ tailWord_353199).sum := by decide
  have hdescent : baseEnd_353199 < baseStart_353199 := by decide
  rcases family_descends (prefixWord ++ tailWord_353199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353233 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 2, 2, 3]
def baseStart_353233 : Nat := 118140960795 + 353233 * 2 ^ 59
def prefixEnd_353233 : Nat := 4983230072969 + 3 ^ 40 * 353233 * 2
def baseEnd_353233 : Nat := 181378312029721707963017

theorem tailTrace_353233 : CollatzResearch.WordTrace tailWord_353233 prefixEnd_353233 181378312029721707963017 := by
  unfold tailWord_353233
  simp only [CollatzResearch.WordTrace]
  refine ⟨12883465929304643238600353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8588977286203095492400235 12883465929304643238600353)
  ·
    refine ⟨9662599446978482428950265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12883465929304643238600353 9662599446978482428950265)
    ·
      refine ⟨7246949585233861821712699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9662599446978482428950265 7246949585233861821712699)
      ·
        refine ⟨10870424377850792732569049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7246949585233861821712699 10870424377850792732569049)
        ·
          refine ⟨8152818283388094549426787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10870424377850792732569049 8152818283388094549426787)
          ·
            refine ⟨12229227425082141824140181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8152818283388094549426787 12229227425082141824140181)
            ·
              refine ⟨573245035550725398006571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12229227425082141824140181 573245035550725398006571)
              ·
                refine ⟨859867553326088097009857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573245035550725398006571 859867553326088097009857)
                ·
                  refine ⟨644900664994566072757393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 859867553326088097009857 644900664994566072757393)
                  ·
                    refine ⟨483675498745924554568045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 644900664994566072757393 483675498745924554568045)
                    ·
                      refine ⟨181378312029721707963017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 483675498745924554568045 181378312029721707963017)
                      ·
                        rfl

theorem cell23_353233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_353233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353233 prefixEnd_353233 := by exact prefixLift 353233
  have htrace : WordTrace (prefixWord ++ tailWord_353233) baseStart_353233 baseEnd_353233 := by
    simpa [prefixWord, tailWord_353233, baseEnd_353233] using wordTrace_append hprefix tailTrace_353233
  have hstable : (prefixWord ++ tailWord_353233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353233).length < 2 ^ (prefixWord ++ tailWord_353233).sum := by decide
  have hdescent : baseEnd_353233 < baseStart_353233 := by decide
  rcases family_descends (prefixWord ++ tailWord_353233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353273 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 1, 5, 2]
def baseStart_353273 : Nat := 118140960795 + 353273 * 2 ^ 59
def prefixEnd_353273 : Nat := 4983230072969 + 3 ^ 40 * 353273 * 2
def baseEnd_353273 : Nat := 181398851255901551462833

theorem tailTrace_353273 : CollatzResearch.WordTrace tailWord_353273 prefixEnd_353273 181398851255901551462833 := by
  unfold tailWord_353273
  simp only [CollatzResearch.WordTrace]
  refine ⟨12884924849159730070056473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8589949899439820046704315 12884924849159730070056473)
  ·
    refine ⟨9663693636869797552542355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12884924849159730070056473 9663693636869797552542355)
    ·
      refine ⟨14495540455304696328813533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9663693636869797552542355 14495540455304696328813533)
      ·
        refine ⟨5435827670739261123305075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14495540455304696328813533 5435827670739261123305075)
        ·
          refine ⟨8153741506108891684957613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5435827670739261123305075 8153741506108891684957613)
          ·
            refine ⟨3057653064790834381859105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8153741506108891684957613 3057653064790834381859105)
            ·
              refine ⟨2293239798593125786394329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3057653064790834381859105 2293239798593125786394329)
              ·
                refine ⟨1719929848944844339795747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2293239798593125786394329 1719929848944844339795747)
                ·
                  refine ⟨2579894773417266509693621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719929848944844339795747 2579894773417266509693621)
                  ·
                    refine ⟨241865135007868735283777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2579894773417266509693621 241865135007868735283777)
                    ·
                      refine ⟨181398851255901551462833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241865135007868735283777 181398851255901551462833)
                      ·
                        rfl

theorem cell23_353273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_353273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353273 prefixEnd_353273 := by exact prefixLift 353273
  have htrace : WordTrace (prefixWord ++ tailWord_353273) baseStart_353273 baseEnd_353273 := by
    simpa [prefixWord, tailWord_353273, baseEnd_353273] using wordTrace_append hprefix tailTrace_353273
  have hstable : (prefixWord ++ tailWord_353273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353273).length < 2 ^ (prefixWord ++ tailWord_353273).sum := by decide
  have hdescent : baseEnd_353273 < baseStart_353273 := by decide
  rcases family_descends (prefixWord ++ tailWord_353273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353290 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 1, 5, 2]
def baseStart_353290 : Nat := 118140960795 + 353290 * 2 ^ 59
def prefixEnd_353290 : Nat := 4983230072969 + 3 ^ 40 * 353290 * 2
def baseEnd_353290 : Nat := 181407580427027984950255

theorem tailTrace_353290 : CollatzResearch.WordTrace tailWord_353290 prefixEnd_353290 181407580427027984950255 := by
  unfold tailWord_353290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221386222524535493356331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8590363260065427982283549 3221386222524535493356331)
  ·
    refine ⟨4832079333786803240034497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3221386222524535493356331 4832079333786803240034497)
    ·
      refine ⟨3624059500340102430025873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4832079333786803240034497 3624059500340102430025873)
      ·
        refine ⟨2718044625255076822519405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3624059500340102430025873 2718044625255076822519405)
        ·
          refine ⟨1019266734470653808444777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2718044625255076822519405 1019266734470653808444777)
          ·
            refine ⟨764450050852990356333583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1019266734470653808444777 764450050852990356333583)
            ·
              refine ⟨1146675076279485534500375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764450050852990356333583 1146675076279485534500375)
              ·
                refine ⟨1720012614419228301750563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1146675076279485534500375 1720012614419228301750563)
                ·
                  refine ⟨2580018921628842452625845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720012614419228301750563 2580018921628842452625845)
                  ·
                    refine ⟨241876773902703979933673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2580018921628842452625845 241876773902703979933673)
                    ·
                      refine ⟨181407580427027984950255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241876773902703979933673 181407580427027984950255)
                      ·
                        rfl

theorem cell23_353290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_353290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353290 prefixEnd_353290 := by exact prefixLift 353290
  have htrace : WordTrace (prefixWord ++ tailWord_353290) baseStart_353290 baseEnd_353290 := by
    simpa [prefixWord, tailWord_353290, baseEnd_353290] using wordTrace_append hprefix tailTrace_353290
  have hstable : (prefixWord ++ tailWord_353290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353290).length < 2 ^ (prefixWord ++ tailWord_353290).sum := by decide
  have hdescent : baseEnd_353290 < baseStart_353290 := by decide
  rcases family_descends (prefixWord ++ tailWord_353290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353337 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 3, 2, 2]
def baseStart_353337 : Nat := 118140960795 + 353337 * 2 ^ 59
def prefixEnd_353337 : Nat := 4983230072969 + 3 ^ 40 * 353337 * 2
def baseEnd_353337 : Nat := 181431714017789301062539

theorem tailTrace_353337 : CollatzResearch.WordTrace tailWord_353337 prefixEnd_353337 181431714017789301062539 := by
  unfold tailWord_353337
  simp only [CollatzResearch.WordTrace]
  refine ⟨12887259120927869000386265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8591506080618579333590843 12887259120927869000386265)
  ·
    refine ⟨9665444340695901750289699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12887259120927869000386265 9665444340695901750289699)
    ·
      refine ⟨14498166511043852625434549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9665444340695901750289699 14498166511043852625434549)
      ·
        refine ⟨1359203110410361183634489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14498166511043852625434549 1359203110410361183634489)
        ·
          refine ⟨1019402332807770887725867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1359203110410361183634489 1019402332807770887725867)
          ·
            refine ⟨1529103499211656331588801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019402332807770887725867 1529103499211656331588801)
            ·
              refine ⟨1146827624408742248691601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529103499211656331588801 1146827624408742248691601)
              ·
                refine ⟨860120718306556686518701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146827624408742248691601 860120718306556686518701)
                ·
                  refine ⟨322545269364958757444513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860120718306556686518701 322545269364958757444513)
                  ·
                    refine ⟨241908952023719068083385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 322545269364958757444513 241908952023719068083385)
                    ·
                      refine ⟨181431714017789301062539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241908952023719068083385 181431714017789301062539)
                      ·
                        rfl

theorem cell23_353337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_353337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353337 prefixEnd_353337 := by exact prefixLift 353337
  have htrace : WordTrace (prefixWord ++ tailWord_353337) baseStart_353337 baseEnd_353337 := by
    simpa [prefixWord, tailWord_353337, baseEnd_353337] using wordTrace_append hprefix tailTrace_353337
  have hstable : (prefixWord ++ tailWord_353337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353337).length < 2 ^ (prefixWord ++ tailWord_353337).sum := by decide
  have hdescent : baseEnd_353337 < baseStart_353337 := by decide
  rcases family_descends (prefixWord ++ tailWord_353337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353340 : List Nat := [2, 2, 2, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_353340 : Nat := 118140960795 + 353340 * 2 ^ 59
def prefixEnd_353340 : Nat := 4983230072969 + 3 ^ 40 * 353340 * 2
def baseEnd_353340 : Nat := 181433254459752789325025

theorem tailTrace_353340 : CollatzResearch.WordTrace tailWord_353340 prefixEnd_353340 181433254459752789325025 := by
  unfold tailWord_353340
  simp only [CollatzResearch.WordTrace]
  refine ⟨6443684269958500256372737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8591579026611333675163649 6443684269958500256372737)
  ·
    refine ⟨4832763202468875192279553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6443684269958500256372737 4832763202468875192279553)
    ·
      refine ⟨3624572401851656394209665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4832763202468875192279553 3624572401851656394209665)
      ·
        refine ⟨2718429301388742295657249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3624572401851656394209665 2718429301388742295657249)
        ·
          refine ⟨2038821976041556721742937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2718429301388742295657249 2038821976041556721742937)
          ·
            refine ⟨1529116482031167541307203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2038821976041556721742937 1529116482031167541307203)
            ·
              refine ⟨2293674723046751311960805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529116482031167541307203 2293674723046751311960805)
              ·
                refine ⟨430064010571265870992651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2293674723046751311960805 430064010571265870992651)
                ·
                  refine ⟨645096015856898806488977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430064010571265870992651 645096015856898806488977)
                  ·
                    refine ⟨483822011892674104866733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 645096015856898806488977 483822011892674104866733)
                    ·
                      refine ⟨181433254459752789325025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 483822011892674104866733 181433254459752789325025)
                      ·
                        rfl

theorem cell23_353340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_353340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353340 prefixEnd_353340 := by exact prefixLift 353340
  have htrace : WordTrace (prefixWord ++ tailWord_353340) baseStart_353340 baseEnd_353340 := by
    simpa [prefixWord, tailWord_353340, baseEnd_353340] using wordTrace_append hprefix tailTrace_353340
  have hstable : (prefixWord ++ tailWord_353340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353340).length < 2 ^ (prefixWord ++ tailWord_353340).sum := by decide
  have hdescent : baseEnd_353340 < baseStart_353340 := by decide
  rcases family_descends (prefixWord ++ tailWord_353340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353354 : List Nat := [3, 1, 2, 1, 1, 2, 5, 3, 1, 2, 2]
def baseStart_353354 : Nat := 118140960795 + 353354 * 2 ^ 59
def prefixEnd_353354 : Nat := 4983230072969 + 3 ^ 40 * 353354 * 2
def baseEnd_353354 : Nat := 181440443188915734549961

theorem tailTrace_353354 : CollatzResearch.WordTrace tailWord_353354 prefixEnd_353354 181440443188915734549961 := by
  unfold tailWord_353354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221969790466570225938779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8591919441244187269170077 3221969790466570225938779)
  ·
    refine ⟨4832954685699855338908169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3221969790466570225938779 4832954685699855338908169)
    ·
      refine ⟨3624716014274891504181127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4832954685699855338908169 3624716014274891504181127)
      ·
        refine ⟨5437074021412337256271691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3624716014274891504181127 5437074021412337256271691)
        ·
          refine ⟨8155611032118505884407537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5437074021412337256271691 8155611032118505884407537)
          ·
            refine ⟨6116708274088879413305653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8155611032118505884407537 6116708274088879413305653)
            ·
              refine ⟨573441400695832444997405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6116708274088879413305653 573441400695832444997405)
              ·
                refine ⟨215040525260937166874027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 573441400695832444997405 215040525260937166874027)
                ·
                  refine ⟨322560787891405750311041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215040525260937166874027 322560787891405750311041)
                  ·
                    refine ⟨241920590918554312733281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 322560787891405750311041 241920590918554312733281)
                    ·
                      refine ⟨181440443188915734549961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241920590918554312733281 181440443188915734549961)
                      ·
                        rfl

theorem cell23_353354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_353354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353354 prefixEnd_353354 := by exact prefixLift 353354
  have htrace : WordTrace (prefixWord ++ tailWord_353354) baseStart_353354 baseEnd_353354 := by
    simpa [prefixWord, tailWord_353354, baseEnd_353354] using wordTrace_append hprefix tailTrace_353354
  have hstable : (prefixWord ++ tailWord_353354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353354).length < 2 ^ (prefixWord ++ tailWord_353354).sum := by decide
  have hdescent : baseEnd_353354 < baseStart_353354 := by decide
  rcases family_descends (prefixWord ++ tailWord_353354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353356 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 1, 9]
def baseStart_353356 : Nat := 118140960795 + 353356 * 2 ^ 59
def prefixEnd_353356 : Nat := 4983230072969 + 3 ^ 40 * 353356 * 2
def baseEnd_353356 : Nat := 60480490050074908908317

theorem tailTrace_353356 : CollatzResearch.WordTrace tailWord_353356 prefixEnd_353356 60480490050074908908317 := by
  unfold tailWord_353356
  simp only [CollatzResearch.WordTrace]
  refine ⟨6443976053929517622663961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8591968071906023496885281 6443976053929517622663961)
  ·
    refine ⟨4832982040447138216997971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6443976053929517622663961 4832982040447138216997971)
    ·
      refine ⟨7249473060670707325496957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4832982040447138216997971 7249473060670707325496957)
      ·
        refine ⟨2718552397751515247061359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7249473060670707325496957 2718552397751515247061359)
        ·
          refine ⟨4077828596627272870592039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718552397751515247061359 4077828596627272870592039)
          ·
            refine ⟨6116742894940909305888059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4077828596627272870592039 6116742894940909305888059)
            ·
              refine ⟨9175114342411363958832089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6116742894940909305888059 9175114342411363958832089)
              ·
                refine ⟨6881335756808522969124067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9175114342411363958832089 6881335756808522969124067)
                ·
                  refine ⟨10322003635212784453686101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6881335756808522969124067 10322003635212784453686101)
                  ·
                    refine ⟨60480490050074908908317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 10322003635212784453686101 60480490050074908908317)
                    ·
                      rfl

theorem cell23_353356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_353356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353356 prefixEnd_353356 := by exact prefixLift 353356
  have htrace : WordTrace (prefixWord ++ tailWord_353356) baseStart_353356 baseEnd_353356 := by
    simpa [prefixWord, tailWord_353356, baseEnd_353356] using wordTrace_append hprefix tailTrace_353356
  have hstable : (prefixWord ++ tailWord_353356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353356).length < 2 ^ (prefixWord ++ tailWord_353356).sum := by decide
  have hdescent : baseEnd_353356 < baseStart_353356 := by decide
  rcases family_descends (prefixWord ++ tailWord_353356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353357 : List Nat := [1, 6, 1, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_353357 : Nat := 118140960795 + 353357 * 2 ^ 59
def prefixEnd_353357 : Nat := 4983230072969 + 3 ^ 40 * 353357 * 2
def baseEnd_353357 : Nat := 181441983630879222812447

theorem tailTrace_353357 : CollatzResearch.WordTrace tailWord_353357 prefixEnd_353357 181441983630879222812447 := by
  unfold tailWord_353357
  simp only [CollatzResearch.WordTrace]
  refine ⟨12887988580855412416114325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8591992387236941610742883 12887988580855412416114325)
  ·
    refine ⟨604124464727597457005359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12887988580855412416114325 604124464727597457005359)
    ·
      refine ⟨906186697091396185508039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 604124464727597457005359 906186697091396185508039)
      ·
        refine ⟨1359280045637094278262059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906186697091396185508039 1359280045637094278262059)
        ·
          refine ⟨2038920068455641417393089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359280045637094278262059 2038920068455641417393089)
          ·
            refine ⟨1529190051341731063044817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2038920068455641417393089 1529190051341731063044817)
            ·
              refine ⟨1146892538506298297283613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529190051341731063044817 1146892538506298297283613)
              ·
                refine ⟨430084701939861861481355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1146892538506298297283613 430084701939861861481355)
                ·
                  refine ⟨645127052909792792222033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430084701939861861481355 645127052909792792222033)
                  ·
                    refine ⟨483845289682344594166525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 645127052909792792222033 483845289682344594166525)
                    ·
                      refine ⟨181441983630879222812447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 483845289682344594166525 181441983630879222812447)
                      ·
                        rfl

theorem cell23_353357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_353357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353357 prefixEnd_353357 := by exact prefixLift 353357
  have htrace : WordTrace (prefixWord ++ tailWord_353357) baseStart_353357 baseEnd_353357 := by
    simpa [prefixWord, tailWord_353357, baseEnd_353357] using wordTrace_append hprefix tailTrace_353357
  have hstable : (prefixWord ++ tailWord_353357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353357).length < 2 ^ (prefixWord ++ tailWord_353357).sum := by decide
  have hdescent : baseEnd_353357 < baseStart_353357 := by decide
  rcases family_descends (prefixWord ++ tailWord_353357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353380 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 3, 3, 2]
def baseStart_353380 : Nat := 118140960795 + 353380 * 2 ^ 59
def prefixEnd_353380 : Nat := 4983230072969 + 3 ^ 40 * 353380 * 2
def baseEnd_353380 : Nat := 181453793685932632824841

theorem tailTrace_353380 : CollatzResearch.WordTrace tailWord_353380 prefixEnd_353380 181453793685932632824841 := by
  unfold tailWord_353380
  simp only [CollatzResearch.WordTrace]
  refine ⟨6444413729886043672100797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8592551639848058229467729 6444413729886043672100797)
  ·
    refine ⟨2416655148707266377037799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6444413729886043672100797 2416655148707266377037799)
    ·
      refine ⟨3624982723060899565556699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2416655148707266377037799 3624982723060899565556699)
      ·
        refine ⟨5437474084591349348335049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3624982723060899565556699 5437474084591349348335049)
        ·
          refine ⟨4078105563443512011251287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5437474084591349348335049 4078105563443512011251287)
          ·
            refine ⟨6117158345165268016876931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078105563443512011251287 6117158345165268016876931)
            ·
              refine ⟨9175737517747902025315397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6117158345165268016876931 9175737517747902025315397)
              ·
                refine ⟨1720450784577731629746637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9175737517747902025315397 1720450784577731629746637)
                ·
                  refine ⟨645169044216649361154989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1720450784577731629746637 645169044216649361154989)
                  ·
                    refine ⟨241938391581243510433121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 645169044216649361154989 241938391581243510433121)
                    ·
                      refine ⟨181453793685932632824841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241938391581243510433121 181453793685932632824841)
                      ·
                        rfl

theorem cell23_353380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_353380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353380 prefixEnd_353380 := by exact prefixLift 353380
  have htrace : WordTrace (prefixWord ++ tailWord_353380) baseStart_353380 baseEnd_353380 := by
    simpa [prefixWord, tailWord_353380, baseEnd_353380] using wordTrace_append hprefix tailTrace_353380
  have hstable : (prefixWord ++ tailWord_353380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353380).length < 2 ^ (prefixWord ++ tailWord_353380).sum := by decide
  have hdescent : baseEnd_353380 < baseStart_353380 := by decide
  rcases family_descends (prefixWord ++ tailWord_353380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353427 : List Nat := [1, 1, 1, 2, 1, 2, 5, 4, 2, 2, 2]
def baseStart_353427 : Nat := 118140960795 + 353427 * 2 ^ 59
def prefixEnd_353427 : Nat := 4983230072969 + 3 ^ 40 * 353427 * 2
def baseEnd_353427 : Nat := 181477927276693948937125

theorem tailTrace_353427 : CollatzResearch.WordTrace tailWord_353427 prefixEnd_353427 181477927276693948937125 := by
  unfold tailWord_353427
  simp only [CollatzResearch.WordTrace]
  refine ⟨12890541690601814371162535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8593694460401209580775023 12890541690601814371162535)
  ·
    refine ⟨19335812535902721556743803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12890541690601814371162535 19335812535902721556743803)
    ·
      refine ⟨29003718803854082335115705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19335812535902721556743803 29003718803854082335115705)
      ·
        refine ⟨21752789102890561751336779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29003718803854082335115705 21752789102890561751336779)
        ·
          refine ⟨32629183654335842627005169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21752789102890561751336779 32629183654335842627005169)
          ·
            refine ⟨24471887740751881970253877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32629183654335842627005169 24471887740751881970253877)
            ·
              refine ⟨2294239475695488934711301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24471887740751881970253877 2294239475695488934711301)
              ·
                refine ⟨430169901692904175258369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2294239475695488934711301 430169901692904175258369)
                ·
                  refine ⟨322627426269678131443777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430169901692904175258369 322627426269678131443777)
                  ·
                    refine ⟨241970569702258598582833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 322627426269678131443777 241970569702258598582833)
                    ·
                      refine ⟨181477927276693948937125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241970569702258598582833 181477927276693948937125)
                      ·
                        rfl

theorem cell23_353427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 2, 2].length) (baseStart_353427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353427 prefixEnd_353427 := by exact prefixLift 353427
  have htrace : WordTrace (prefixWord ++ tailWord_353427) baseStart_353427 baseEnd_353427 := by
    simpa [prefixWord, tailWord_353427, baseEnd_353427] using wordTrace_append hprefix tailTrace_353427
  have hstable : (prefixWord ++ tailWord_353427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353427).length < 2 ^ (prefixWord ++ tailWord_353427).sum := by decide
  have hdescent : baseEnd_353427 < baseStart_353427 := by decide
  rcases family_descends (prefixWord ++ tailWord_353427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353444 : List Nat := [2, 3, 1, 2, 3, 1, 2, 3, 2, 2, 2]
def baseStart_353444 : Nat := 118140960795 + 353444 * 2 ^ 59
def prefixEnd_353444 : Nat := 4983230072969 + 3 ^ 40 * 353444 * 2
def baseEnd_353444 : Nat := 181486656447820382424547

theorem tailTrace_353444 : CollatzResearch.WordTrace tailWord_353444 prefixEnd_353444 181486656447820382424547 := by
  unfold tailWord_353444
  simp only [CollatzResearch.WordTrace]
  refine ⟨6445580865770113137265693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8594107821026817516354257 6445580865770113137265693)
  ·
    refine ⟨2417092824663792426474635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6445580865770113137265693 2417092824663792426474635)
    ·
      refine ⟨3625639236995688639711953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2417092824663792426474635 3625639236995688639711953)
      ·
        refine ⟨2719229427746766479783965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3625639236995688639711953 2719229427746766479783965)
        ·
          refine ⟨1019711035405037429918987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2719229427746766479783965 1019711035405037429918987)
          ·
            refine ⟨1529566553107556144878481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019711035405037429918987 1529566553107556144878481)
            ·
              refine ⟨1147174914830667108658861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529566553107556144878481 1147174914830667108658861)
              ·
                refine ⟨430190593061500165747073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1147174914830667108658861 430190593061500165747073)
                ·
                  refine ⟨322642944796125124310305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430190593061500165747073 322642944796125124310305)
                  ·
                    refine ⟨241982208597093843232729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 322642944796125124310305 241982208597093843232729)
                    ·
                      refine ⟨181486656447820382424547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 241982208597093843232729 181486656447820382424547)
                      ·
                        rfl

theorem cell23_353444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_353444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353444 prefixEnd_353444 := by exact prefixLift 353444
  have htrace : WordTrace (prefixWord ++ tailWord_353444) baseStart_353444 baseEnd_353444 := by
    simpa [prefixWord, tailWord_353444, baseEnd_353444] using wordTrace_append hprefix tailTrace_353444
  have hstable : (prefixWord ++ tailWord_353444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353444).length < 2 ^ (prefixWord ++ tailWord_353444).sum := by decide
  have hdescent : baseEnd_353444 < baseStart_353444 := by decide
  rcases family_descends (prefixWord ++ tailWord_353444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353450 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 9]
def baseStart_353450 : Nat := 118140960795 + 353450 * 2 ^ 59
def prefixEnd_353450 : Nat := 4983230072969 + 3 ^ 40 * 353450 * 2
def baseEnd_353450 : Nat := 20165526370194150994391

theorem tailTrace_353450 : CollatzResearch.WordTrace tailWord_353450 prefixEnd_353450 20165526370194150994391 := by
  unfold tailWord_353450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3222845142379622324812451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8594253713012326199499869 3222845142379622324812451)
  ·
    refine ⟨4834267713569433487218677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3222845142379622324812451 4834267713569433487218677)
    ·
      refine ⟨453212598147134389426751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4834267713569433487218677 453212598147134389426751)
      ·
        refine ⟨679818897220701584140127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453212598147134389426751 679818897220701584140127)
        ·
          refine ⟨1019728345831052376210191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679818897220701584140127 1019728345831052376210191)
          ·
            refine ⟨1529592518746578564315287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019728345831052376210191 1529592518746578564315287)
            ·
              refine ⟨2294388778119867846472931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529592518746578564315287 2294388778119867846472931)
              ·
                refine ⟨3441583167179801769709397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294388778119867846472931 3441583167179801769709397)
                ·
                  refine ⟨20165526370194150994391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3441583167179801769709397 20165526370194150994391)
                  ·
                    rfl

theorem cell23_353450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_353450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353450 prefixEnd_353450 := by exact prefixLift 353450
  have htrace : WordTrace (prefixWord ++ tailWord_353450) baseStart_353450 baseEnd_353450 := by
    simpa [prefixWord, tailWord_353450, baseEnd_353450] using wordTrace_append hprefix tailTrace_353450
  have hstable : (prefixWord ++ tailWord_353450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353450).length < 2 ^ (prefixWord ++ tailWord_353450).sum := by decide
  have hdescent : baseEnd_353450 < baseStart_353450 := by decide
  rcases family_descends (prefixWord ++ tailWord_353450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353463 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 1, 7]
def baseStart_353463 : Nat := 118140960795 + 353463 * 2 ^ 59
def prefixEnd_353463 : Nat := 4983230072969 + 3 ^ 40 * 353463 * 2
def baseEnd_353463 : Nat := 60498804193418602695653

theorem tailTrace_353463 : CollatzResearch.WordTrace tailWord_353463 prefixEnd_353463 60498804193418602695653 := by
  unfold tailWord_353463
  simp only [CollatzResearch.WordTrace]
  refine ⟨12891854718471392519473043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8594569812314261679648695 12891854718471392519473043)
  ·
    refine ⟨19337782077707088779209565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12891854718471392519473043 19337782077707088779209565)
    ·
      refine ⟨7251668279140158292203587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19337782077707088779209565 7251668279140158292203587)
      ·
        refine ⟨10877502418710237438305381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7251668279140158292203587 10877502418710237438305381)
        ·
          refine ⟨2039531703508169519682259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10877502418710237438305381 2039531703508169519682259)
          ·
            refine ⟨3059297555262254279523389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039531703508169519682259 3059297555262254279523389)
            ·
              refine ⟨1147236583223345354821271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3059297555262254279523389 1147236583223345354821271)
              ·
                refine ⟨1720854874835018032231907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1147236583223345354821271 1720854874835018032231907)
                ·
                  refine ⟨2581282312252527048347861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720854874835018032231907 2581282312252527048347861)
                  ·
                    refine ⟨60498804193418602695653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2581282312252527048347861 60498804193418602695653)
                    ·
                      rfl

theorem cell23_353463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_353463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353463 prefixEnd_353463 := by exact prefixLift 353463
  have htrace : WordTrace (prefixWord ++ tailWord_353463) baseStart_353463 baseEnd_353463 := by
    simpa [prefixWord, tailWord_353463, baseEnd_353463] using wordTrace_append hprefix tailTrace_353463
  have hstable : (prefixWord ++ tailWord_353463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353463).length < 2 ^ (prefixWord ++ tailWord_353463).sum := by decide
  have hdescent : baseEnd_353463 < baseStart_353463 := by decide
  rcases family_descends (prefixWord ++ tailWord_353463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353523 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 8]
def baseStart_353523 : Nat := 118140960795 + 353523 * 2 ^ 59
def prefixEnd_353523 : Nat := 4983230072969 + 3 ^ 40 * 353523 * 2
def baseEnd_353523 : Nat := 20169691268836174815187

theorem tailTrace_353523 : CollatzResearch.WordTrace tailWord_353523 prefixEnd_353523 20169691268836174815187 := by
  unfold tailWord_353523
  simp only [CollatzResearch.WordTrace]
  refine ⟨12894043098254022766657223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8596028732169348511104815 12894043098254022766657223)
  ·
    refine ⟨19341064647381034149985835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12894043098254022766657223 19341064647381034149985835)
    ·
      refine ⟨29011596971071551224978753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19341064647381034149985835 29011596971071551224978753)
      ·
        refine ⟨21758697728303663418734065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29011596971071551224978753 21758697728303663418734065)
        ·
          refine ⟨16319023296227747564050549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21758697728303663418734065 16319023296227747564050549)
          ·
            refine ⟨1529908434021351334129739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16319023296227747564050549 1529908434021351334129739)
            ·
              refine ⟨2294862651032027001194609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529908434021351334129739 2294862651032027001194609)
              ·
                refine ⟨1721146988274020250895957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2294862651032027001194609 1721146988274020250895957)
                ·
                  refine ⟨20169691268836174815187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1721146988274020250895957 20169691268836174815187)
                  ·
                    rfl

theorem cell23_353523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 8].length) (baseStart_353523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353523 prefixEnd_353523 := by exact prefixLift 353523
  have htrace : WordTrace (prefixWord ++ tailWord_353523) baseStart_353523 baseEnd_353523 := by
    simpa [prefixWord, tailWord_353523, baseEnd_353523] using wordTrace_append hprefix tailTrace_353523
  have hstable : (prefixWord ++ tailWord_353523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353523).length < 2 ^ (prefixWord ++ tailWord_353523).sum := by decide
  have hdescent : baseEnd_353523 < baseStart_353523 := by decide
  rcases family_descends (prefixWord ++ tailWord_353523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353537 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_353537 : Nat := 118140960795 + 353537 * 2 ^ 59
def prefixEnd_353537 : Nat := 4983230072969 + 3 ^ 40 * 353537 * 2
def baseEnd_353537 : Nat := 181534410148688518561619

theorem tailTrace_353537 : CollatzResearch.WordTrace tailWord_353537 prefixEnd_353537 181534410148688518561619 := by
  unfold tailWord_353537
  simp only [CollatzResearch.WordTrace]
  refine ⟨12894553720203303157666865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8596369146802202105111243 12894553720203303157666865)
  ·
    refine ⟨9670915290152477368250149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12894553720203303157666865 9670915290152477368250149)
    ·
      refine ⟨1813296616903589506546903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9670915290152477368250149 1813296616903589506546903)
      ·
        refine ⟨2719944925355384259820355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1813296616903589506546903 2719944925355384259820355)
        ·
          refine ⟨4079917388033076389730533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2719944925355384259820355 4079917388033076389730533)
          ·
            refine ⟨764984510256201823074475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4079917388033076389730533 764984510256201823074475)
            ·
              refine ⟨1147476765384302734611713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764984510256201823074475 1147476765384302734611713)
              ·
                refine ⟨860607574038227050958785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147476765384302734611713 860607574038227050958785)
                ·
                  refine ⟨645455680528670288219089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 860607574038227050958785 645455680528670288219089)
                  ·
                    refine ⟨484091760396502716164317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 645455680528670288219089 484091760396502716164317)
                    ·
                      refine ⟨181534410148688518561619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 484091760396502716164317 181534410148688518561619)
                      ·
                        rfl

theorem cell23_353537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_353537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353537 prefixEnd_353537 := by exact prefixLift 353537
  have htrace : WordTrace (prefixWord ++ tailWord_353537) baseStart_353537 baseEnd_353537 := by
    simpa [prefixWord, tailWord_353537, baseEnd_353537] using wordTrace_append hprefix tailTrace_353537
  have hstable : (prefixWord ++ tailWord_353537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353537).length < 2 ^ (prefixWord ++ tailWord_353537).sum := by decide
  have hdescent : baseEnd_353537 < baseStart_353537 := by decide
  rcases family_descends (prefixWord ++ tailWord_353537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353540 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 8]
def baseStart_353540 : Nat := 118140960795 + 353540 * 2 ^ 59
def prefixEnd_353540 : Nat := 4983230072969 + 3 ^ 40 * 353540 * 2
def baseEnd_353540 : Nat := 20170661176739111869345

theorem tailTrace_353540 : CollatzResearch.WordTrace tailWord_353540 prefixEnd_353540 20170661176739111869345 := by
  unfold tailWord_353540
  simp only [CollatzResearch.WordTrace]
  refine ⟨6447331569596217335013037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8596442092794956446684049 6447331569596217335013037)
  ·
    refine ⟨2417749338598581500629889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6447331569596217335013037 2417749338598581500629889)
    ·
      refine ⟨1813312003948936125472417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2417749338598581500629889 1813312003948936125472417)
      ·
        refine ⟨1359984002961702094104313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1813312003948936125472417 1359984002961702094104313)
        ·
          refine ⟨1019988002221276570578235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1359984002961702094104313 1019988002221276570578235)
          ·
            refine ⟨1529982003331914855867353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019988002221276570578235 1529982003331914855867353)
            ·
              refine ⟨1147486502498936141900515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529982003331914855867353 1147486502498936141900515)
              ·
                refine ⟨1721229753748404212850773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1147486502498936141900515 1721229753748404212850773)
                ·
                  refine ⟨20170661176739111869345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1721229753748404212850773 20170661176739111869345)
                  ·
                    rfl

theorem cell23_353540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_353540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353540 prefixEnd_353540 := by exact prefixLift 353540
  have htrace : WordTrace (prefixWord ++ tailWord_353540) baseStart_353540 baseEnd_353540 := by
    simpa [prefixWord, tailWord_353540, baseEnd_353540] using wordTrace_append hprefix tailTrace_353540
  have hstable : (prefixWord ++ tailWord_353540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353540).length < 2 ^ (prefixWord ++ tailWord_353540).sum := by decide
  have hdescent : baseEnd_353540 < baseStart_353540 := by decide
  rcases family_descends (prefixWord ++ tailWord_353540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353544 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 3, 4]
def baseStart_353544 : Nat := 118140960795 + 353544 * 2 ^ 59
def prefixEnd_353544 : Nat := 4983230072969 + 3 ^ 40 * 353544 * 2
def baseEnd_353544 : Nat := 60512668171089997058029

theorem tailTrace_353544 : CollatzResearch.WordTrace tailWord_353544 prefixEnd_353544 60512668171089997058029 := by
  unfold tailWord_353544
  simp only [CollatzResearch.WordTrace]
  refine ⟨6447404515588971676585843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8596539354118628902114457 6447404515588971676585843)
  ·
    refine ⟨9671106773383457514878765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6447404515588971676585843 9671106773383457514878765)
    ·
      refine ⟨3626665040018796568079537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9671106773383457514878765 3626665040018796568079537)
      ·
        refine ⟨2719998780014097426059653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3626665040018796568079537 2719998780014097426059653)
        ·
          refine ⟨509999771252643267386185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2719998780014097426059653 509999771252643267386185)
          ·
            refine ⟨382499828439482450539639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509999771252643267386185 382499828439482450539639)
            ·
              refine ⟨573749742659223675809459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382499828439482450539639 573749742659223675809459)
              ·
                refine ⟨860624613988835513714189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573749742659223675809459 860624613988835513714189)
                ·
                  refine ⟨322734230245813317642821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860624613988835513714189 322734230245813317642821)
                  ·
                    refine ⟨60512668171089997058029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 322734230245813317642821 60512668171089997058029)
                    ·
                      rfl

theorem cell23_353544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_353544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353544 prefixEnd_353544 := by exact prefixLift 353544
  have htrace : WordTrace (prefixWord ++ tailWord_353544) baseStart_353544 baseEnd_353544 := by
    simpa [prefixWord, tailWord_353544, baseEnd_353544] using wordTrace_append hprefix tailTrace_353544
  have hstable : (prefixWord ++ tailWord_353544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353544).length < 2 ^ (prefixWord ++ tailWord_353544).sum := by decide
  have hdescent : baseEnd_353544 < baseStart_353544 := by decide
  rcases family_descends (prefixWord ++ tailWord_353544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353584 : List Nat := [2, 1, 1, 1, 2, 2, 4, 5, 1, 1, 3]
def baseStart_353584 : Nat := 118140960795 + 353584 * 2 ^ 59
def prefixEnd_353584 : Nat := 4983230072969 + 3 ^ 40 * 353584 * 2
def baseEnd_353584 : Nat := 181558543739449834673903

theorem tailTrace_353584 : CollatzResearch.WordTrace tailWord_353584 prefixEnd_353584 181558543739449834673903 := by
  unfold tailWord_353584
  simp only [CollatzResearch.WordTrace]
  refine ⟨6448133975516515092313903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8597511967355353456418537 6448133975516515092313903)
  ·
    refine ⟨9672200963274772638470855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6448133975516515092313903 9672200963274772638470855)
    ·
      refine ⟨14508301444912158957706283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9672200963274772638470855 14508301444912158957706283)
      ·
        refine ⟨21762452167368238436559425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14508301444912158957706283 21762452167368238436559425)
        ·
          refine ⟨16321839125526178827419569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21762452167368238436559425 16321839125526178827419569)
          ·
            refine ⟨12241379344144634120564677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16321839125526178827419569 12241379344144634120564677)
            ·
              refine ⟨2295258627027118897605877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12241379344144634120564677 2295258627027118897605877)
              ·
                refine ⟨215180496283792396650551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2295258627027118897605877 215180496283792396650551)
                ·
                  refine ⟨322770744425688594975827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215180496283792396650551 322770744425688594975827)
                  ·
                    refine ⟨484156116638532892463741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 322770744425688594975827 484156116638532892463741)
                    ·
                      refine ⟨181558543739449834673903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 484156116638532892463741 181558543739449834673903)
                      ·
                        rfl

theorem cell23_353584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 1, 1, 3].length) (baseStart_353584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353584 prefixEnd_353584 := by exact prefixLift 353584
  have htrace : WordTrace (prefixWord ++ tailWord_353584) baseStart_353584 baseEnd_353584 := by
    simpa [prefixWord, tailWord_353584, baseEnd_353584] using wordTrace_append hprefix tailTrace_353584
  have hstable : (prefixWord ++ tailWord_353584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353584).length < 2 ^ (prefixWord ++ tailWord_353584).sum := by decide
  have hdescent : baseEnd_353584 < baseStart_353584 := by decide
  rcases family_descends (prefixWord ++ tailWord_353584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353610 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_353610 : Nat := 118140960795 + 353610 * 2 ^ 59
def prefixEnd_353610 : Nat := 4983230072969 + 3 ^ 40 * 353610 * 2
def baseEnd_353610 : Nat := 181571894236466732948783

theorem tailTrace_353610 : CollatzResearch.WordTrace tailWord_353610 prefixEnd_353610 181571894236466732948783 := by
  unfold tailWord_353610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3224304062234709156268571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8598144165959224416716189 3224304062234709156268571)
  ·
    refine ⟨4836456093352063734402857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3224304062234709156268571 4836456093352063734402857)
    ·
      refine ⟨3627342070014047800802143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4836456093352063734402857 3627342070014047800802143)
      ·
        refine ⟨5441013105021071701203215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3627342070014047800802143 5441013105021071701203215)
        ·
          refine ⟨8161519657531607551804823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5441013105021071701203215 8161519657531607551804823)
          ·
            refine ⟨12242279486297411327707235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8161519657531607551804823 12242279486297411327707235)
            ·
              refine ⟨18363419229446116991560853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12242279486297411327707235 18363419229446116991560853)
              ·
                refine ⟨860785276380286733979415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18363419229446116991560853 860785276380286733979415)
                ·
                  refine ⟨1291177914570430100969123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860785276380286733979415 1291177914570430100969123)
                  ·
                    refine ⟨1936766871855645151453685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1291177914570430100969123 1936766871855645151453685)
                    ·
                      refine ⟨181571894236466732948783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1936766871855645151453685 181571894236466732948783)
                      ·
                        rfl

theorem cell23_353610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_353610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353610 prefixEnd_353610 := by exact prefixLift 353610
  have htrace : WordTrace (prefixWord ++ tailWord_353610) baseStart_353610 baseEnd_353610 := by
    simpa [prefixWord, tailWord_353610, baseEnd_353610] using wordTrace_append hprefix tailTrace_353610
  have hstable : (prefixWord ++ tailWord_353610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353610).length < 2 ^ (prefixWord ++ tailWord_353610).sum := by decide
  have hdescent : baseEnd_353610 < baseStart_353610 := by decide
  rcases family_descends (prefixWord ++ tailWord_353610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353617 : List Nat := [1, 2, 2, 1, 4, 1, 1, 5, 2, 4]
def baseStart_353617 : Nat := 118140960795 + 353617 * 2 ^ 59
def prefixEnd_353617 : Nat := 4983230072969 + 3 ^ 40 * 353617 * 2
def baseEnd_353617 : Nat := 60525162867016068520417

theorem tailTrace_353617 : CollatzResearch.WordTrace tailWord_353617 prefixEnd_353617 60525162867016068520417 := by
  unfold tailWord_353617
  simp only [CollatzResearch.WordTrace]
  refine ⟨12897471559913476820579105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8598314373275651213719403 12897471559913476820579105)
  ·
    refine ⟨9673103669935107615434329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12897471559913476820579105 9673103669935107615434329)
    ·
      refine ⟨7254827752451330711575747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9673103669935107615434329 7254827752451330711575747)
      ·
        refine ⟨10882241628676996067363621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7254827752451330711575747 10882241628676996067363621)
        ·
          refine ⟨2040420305376936762630679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10882241628676996067363621 2040420305376936762630679)
          ·
            refine ⟨3060630458065405143946019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040420305376936762630679 3060630458065405143946019)
            ·
              refine ⟨4590945687098107715919029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060630458065405143946019 4590945687098107715919029)
              ·
                refine ⟨430401158165447598367409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4590945687098107715919029 430401158165447598367409)
                ·
                  refine ⟨322800868624085698775557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430401158165447598367409 322800868624085698775557)
                  ·
                    refine ⟨60525162867016068520417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 322800868624085698775557 60525162867016068520417)
                    ·
                      rfl

theorem cell23_353617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_353617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353617 prefixEnd_353617 := by exact prefixLift 353617
  have htrace : WordTrace (prefixWord ++ tailWord_353617) baseStart_353617 baseEnd_353617 := by
    simpa [prefixWord, tailWord_353617, baseEnd_353617] using wordTrace_append hprefix tailTrace_353617
  have hstable : (prefixWord ++ tailWord_353617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353617).length < 2 ^ (prefixWord ++ tailWord_353617).sum := by decide
  have hdescent : baseEnd_353617 < baseStart_353617 := by decide
  rcases family_descends (prefixWord ++ tailWord_353617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353622 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_353622 : Nat := 118140960795 + 353622 * 2 ^ 59
def prefixEnd_353622 : Nat := 4983230072969 + 3 ^ 40 * 353622 * 2
def baseEnd_353622 : Nat := 181578056004320685998729

theorem tailTrace_353622 : CollatzResearch.WordTrace tailWord_353622 prefixEnd_353622 181578056004320685998729 := by
  unfold tailWord_353622
  simp only [CollatzResearch.WordTrace]
  refine ⟨806103370305960167156945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8598435949930241783007413 806103370305960167156945)
  ·
    refine ⟨604577527729470125367709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 806103370305960167156945 604577527729470125367709)
    ·
      refine ⟨226716572898551297012891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 604577527729470125367709 226716572898551297012891)
      ·
        refine ⟨340074859347826945519337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226716572898551297012891 340074859347826945519337)
        ·
          refine ⟨255056144510870209139503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340074859347826945519337 255056144510870209139503)
          ·
            refine ⟨382584216766305313709255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255056144510870209139503 382584216766305313709255)
            ·
              refine ⟨573876325149457970563883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382584216766305313709255 573876325149457970563883)
              ·
                refine ⟨860814487724186955845825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573876325149457970563883 860814487724186955845825)
                ·
                  refine ⟨645610865793140216884369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 860814487724186955845825 645610865793140216884369)
                  ·
                    refine ⟨484208149344855162663277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 645610865793140216884369 484208149344855162663277)
                    ·
                      refine ⟨181578056004320685998729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 484208149344855162663277 181578056004320685998729)
                      ·
                        rfl

theorem cell23_353622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_353622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353622 prefixEnd_353622 := by exact prefixLift 353622
  have htrace : WordTrace (prefixWord ++ tailWord_353622) baseStart_353622 baseEnd_353622 := by
    simpa [prefixWord, tailWord_353622, baseEnd_353622] using wordTrace_append hprefix tailTrace_353622
  have hstable : (prefixWord ++ tailWord_353622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353622).length < 2 ^ (prefixWord ++ tailWord_353622).sum := by decide
  have hdescent : baseEnd_353622 < baseStart_353622 := by decide
  rcases family_descends (prefixWord ++ tailWord_353622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353624 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 3, 2, 2]
def baseStart_353624 : Nat := 118140960795 + 353624 * 2 ^ 59
def prefixEnd_353624 : Nat := 4983230072969 + 3 ^ 40 * 353624 * 2
def baseEnd_353624 : Nat := 181579082965629678173719

theorem tailTrace_353624 : CollatzResearch.WordTrace tailWord_353624 prefixEnd_353624 181579082965629678173719 := by
  unfold tailWord_353624
  simp only [CollatzResearch.WordTrace]
  refine ⟨6448863435444058508041963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8598484580592078010722617 6448863435444058508041963)
  ·
    refine ⟨9673295153166087762062945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6448863435444058508041963 9673295153166087762062945)
    ·
      refine ⟨7254971364874565821547209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9673295153166087762062945 7254971364874565821547209)
      ·
        refine ⟨5441228523655924366160407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7254971364874565821547209 5441228523655924366160407)
        ·
          refine ⟨8161842785483886549240611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5441228523655924366160407 8161842785483886549240611)
          ·
            refine ⟨12242764178225829823860917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8161842785483886549240611 12242764178225829823860917)
            ·
              refine ⟨1147759141708671545986961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12242764178225829823860917 1147759141708671545986961)
              ·
                refine ⟨860819356281503659490221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147759141708671545986961 860819356281503659490221)
                ·
                  refine ⟨322807258605563872308833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860819356281503659490221 322807258605563872308833)
                  ·
                    refine ⟨242105443954172904231625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 322807258605563872308833 242105443954172904231625)
                    ·
                      refine ⟨181579082965629678173719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 242105443954172904231625 181579082965629678173719)
                      ·
                        rfl

theorem cell23_353624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_353624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353624 prefixEnd_353624 := by exact prefixLift 353624
  have htrace : WordTrace (prefixWord ++ tailWord_353624) baseStart_353624 baseEnd_353624 := by
    simpa [prefixWord, tailWord_353624, baseEnd_353624] using wordTrace_append hprefix tailTrace_353624
  have hstable : (prefixWord ++ tailWord_353624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353624).length < 2 ^ (prefixWord ++ tailWord_353624).sum := by decide
  have hdescent : baseEnd_353624 < baseStart_353624 := by decide
  rcases family_descends (prefixWord ++ tailWord_353624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353644 : List Nat := [2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 3]
def baseStart_353644 : Nat := 118140960795 + 353644 * 2 ^ 59
def prefixEnd_353644 : Nat := 4983230072969 + 3 ^ 40 * 353644 * 2
def baseEnd_353644 : Nat := 181589352578719599923627

theorem tailTrace_353644 : CollatzResearch.WordTrace tailWord_353644 prefixEnd_353644 181589352578719599923627 := by
  unfold tailWord_353644
  simp only [CollatzResearch.WordTrace]
  refine ⟨6449228165407830215905993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8598970887210440287874657 6449228165407830215905993)
  ·
    refine ⟨4836921124055872661929495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6449228165407830215905993 4836921124055872661929495)
    ·
      refine ⟨7255381686083808992894243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4836921124055872661929495 7255381686083808992894243)
      ·
        refine ⟨10883072529125713489341365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7255381686083808992894243 10883072529125713489341365)
        ·
          refine ⟨1020288049605535639625753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10883072529125713489341365 1020288049605535639625753)
          ·
            refine ⟨765216037204151729719315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1020288049605535639625753 765216037204151729719315)
            ·
              refine ⟨1147824055806227594578973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765216037204151729719315 1147824055806227594578973)
              ·
                refine ⟨430434020927335347967115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1147824055806227594578973 430434020927335347967115)
                ·
                  refine ⟨645651031391003021950673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430434020927335347967115 645651031391003021950673)
                  ·
                    refine ⟨484238273543252266463005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 645651031391003021950673 484238273543252266463005)
                    ·
                      refine ⟨181589352578719599923627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 484238273543252266463005 181589352578719599923627)
                      ·
                        rfl

theorem cell23_353644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_353644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353644 prefixEnd_353644 := by exact prefixLift 353644
  have htrace : WordTrace (prefixWord ++ tailWord_353644) baseStart_353644 baseEnd_353644 := by
    simpa [prefixWord, tailWord_353644, baseEnd_353644] using wordTrace_append hprefix tailTrace_353644
  have hstable : (prefixWord ++ tailWord_353644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353644).length < 2 ^ (prefixWord ++ tailWord_353644).sum := by decide
  have hdescent : baseEnd_353644 < baseStart_353644 := by decide
  rcases family_descends (prefixWord ++ tailWord_353644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353692 : List Nat := [2, 2, 3, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_353692 : Nat := 118140960795 + 353692 * 2 ^ 59
def prefixEnd_353692 : Nat := 4983230072969 + 3 ^ 40 * 353692 * 2
def baseEnd_353692 : Nat := 181613999650135412123407

theorem tailTrace_353692 : CollatzResearch.WordTrace tailWord_353692 prefixEnd_353692 181613999650135412123407 := by
  unfold tailWord_353692
  simp only [CollatzResearch.WordTrace]
  refine ⟨6450103517320882314779665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8600138023094509753039553 6450103517320882314779665)
  ·
    refine ⟨4837577637990661736084749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6450103517320882314779665 4837577637990661736084749)
    ·
      refine ⟨1814091614246498151031781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4837577637990661736084749 1814091614246498151031781)
      ·
        refine ⟨340142177671218403318459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1814091614246498151031781 340142177671218403318459)
        ·
          refine ⟨510213266506827604977689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340142177671218403318459 510213266506827604977689)
          ·
            refine ⟨382659949880120703733267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510213266506827604977689 382659949880120703733267)
            ·
              refine ⟨573989924820181055599901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382659949880120703733267 573989924820181055599901)
              ·
                refine ⟨215246221807567895849963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 573989924820181055599901 215246221807567895849963)
                ·
                  refine ⟨322869332711351843774945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215246221807567895849963 322869332711351843774945)
                  ·
                    refine ⟨242151999533513882831209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 322869332711351843774945 242151999533513882831209)
                    ·
                      refine ⟨181613999650135412123407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 242151999533513882831209 181613999650135412123407)
                      ·
                        rfl

theorem cell23_353692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_353692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353692 prefixEnd_353692 := by exact prefixLift 353692
  have htrace : WordTrace (prefixWord ++ tailWord_353692) baseStart_353692 baseEnd_353692 := by
    simpa [prefixWord, tailWord_353692, baseEnd_353692] using wordTrace_append hprefix tailTrace_353692
  have hstable : (prefixWord ++ tailWord_353692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353692).length < 2 ^ (prefixWord ++ tailWord_353692).sum := by decide
  have hdescent : baseEnd_353692 < baseStart_353692 := by decide
  rcases family_descends (prefixWord ++ tailWord_353692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353774 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_353774 : Nat := 118140960795 + 353774 * 2 ^ 59
def prefixEnd_353774 : Nat := 4983230072969 + 3 ^ 40 * 353774 * 2
def baseEnd_353774 : Nat := 181656105063804091298029

theorem tailTrace_353774 : CollatzResearch.WordTrace tailWord_353774 prefixEnd_353774 181656105063804091298029 := by
  unfold tailWord_353774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1612899727543086579255547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8602131880229795089362917 1612899727543086579255547)
  ·
    refine ⟨2419349591314629868883321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1612899727543086579255547 2419349591314629868883321)
    ·
      refine ⟨1814512193485972401662491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2419349591314629868883321 1814512193485972401662491)
      ·
        refine ⟨2721768290228958602493737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814512193485972401662491 2721768290228958602493737)
        ·
          refine ⟨2041326217671718951870303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2721768290228958602493737 2041326217671718951870303)
          ·
            refine ⟨3061989326507578427805455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041326217671718951870303 3061989326507578427805455)
            ·
              refine ⟨4592983989761367641708183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061989326507578427805455 4592983989761367641708183)
              ·
                refine ⟨6889475984642051462562275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592983989761367641708183 6889475984642051462562275)
                ·
                  refine ⟨10334213976963077193843413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6889475984642051462562275 10334213976963077193843413)
                  ·
                    refine ⟨242208140085072121730705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10334213976963077193843413 242208140085072121730705)
                    ·
                      refine ⟨181656105063804091298029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 242208140085072121730705 181656105063804091298029)
                      ·
                        rfl

theorem cell23_353774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_353774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353774 prefixEnd_353774 := by exact prefixLift 353774
  have htrace : WordTrace (prefixWord ++ tailWord_353774) baseStart_353774 baseEnd_353774 := by
    simpa [prefixWord, tailWord_353774, baseEnd_353774] using wordTrace_append hprefix tailTrace_353774
  have hstable : (prefixWord ++ tailWord_353774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353774).length < 2 ^ (prefixWord ++ tailWord_353774).sum := by decide
  have hdescent : baseEnd_353774 < baseStart_353774 := by decide
  rcases family_descends (prefixWord ++ tailWord_353774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353777 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_353777 : Nat := 118140960795 + 353777 * 2 ^ 59
def prefixEnd_353777 : Nat := 4983230072969 + 3 ^ 40 * 353777 * 2
def baseEnd_353777 : Nat := 181657645505767579560515

theorem tailTrace_353777 : CollatzResearch.WordTrace tailWord_353777 prefixEnd_353777 181657645505767579560515 := by
  unfold tailWord_353777
  simp only [CollatzResearch.WordTrace]
  refine ⟨12903307239333824146403585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8602204826222549430935723 12903307239333824146403585)
  ·
    refine ⟨9677480429500368109802689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12903307239333824146403585 9677480429500368109802689)
    ·
      refine ⟨7258110322125276082352017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9677480429500368109802689 7258110322125276082352017)
      ·
        refine ⟨5443582741593957061764013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7258110322125276082352017 5443582741593957061764013)
        ·
          refine ⟨2041343528097733898161505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5443582741593957061764013 2041343528097733898161505)
          ·
            refine ⟨1531007646073300423621129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2041343528097733898161505 1531007646073300423621129)
            ·
              refine ⟨1148255734554975317715847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1531007646073300423621129 1148255734554975317715847)
              ·
                refine ⟨1722383601832462976573771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148255734554975317715847 1722383601832462976573771)
                ·
                  refine ⟨2583575402748694464860657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1722383601832462976573771 2583575402748694464860657)
                  ·
                    refine ⟨1937681552061520848645493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2583575402748694464860657 1937681552061520848645493)
                    ·
                      refine ⟨181657645505767579560515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1937681552061520848645493 181657645505767579560515)
                      ·
                        rfl

theorem cell23_353777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_353777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353777 prefixEnd_353777 := by exact prefixLift 353777
  have htrace : WordTrace (prefixWord ++ tailWord_353777) baseStart_353777 baseEnd_353777 := by
    simpa [prefixWord, tailWord_353777, baseEnd_353777] using wordTrace_append hprefix tailTrace_353777
  have hstable : (prefixWord ++ tailWord_353777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353777).length < 2 ^ (prefixWord ++ tailWord_353777).sum := by decide
  have hdescent : baseEnd_353777 < baseStart_353777 := by decide
  rcases family_descends (prefixWord ++ tailWord_353777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353781 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_353781 : Nat := 118140960795 + 353781 * 2 ^ 59
def prefixEnd_353781 : Nat := 4983230072969 + 3 ^ 40 * 353781 * 2
def baseEnd_353781 : Nat := 181659699428385563910497

theorem tailTrace_353781 : CollatzResearch.WordTrace tailWord_353781 prefixEnd_353781 181659699428385563910497 := by
  unfold tailWord_353781
  simp only [CollatzResearch.WordTrace]
  refine ⟨12903453131319332829549197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8602302087546221886366131 12903453131319332829549197)
  ·
    refine ⟨4838794924244749811080949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12903453131319332829549197 4838794924244749811080949)
    ·
      refine ⟨453637024147945294788839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4838794924244749811080949 453637024147945294788839)
      ·
        refine ⟨680455536221917942183259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453637024147945294788839 680455536221917942183259)
        ·
          refine ⟨1020683304332876913274889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680455536221917942183259 1020683304332876913274889)
          ·
            refine ⟨765512478249657684956167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1020683304332876913274889 765512478249657684956167)
            ·
              refine ⟨1148268717374486527434251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765512478249657684956167 1148268717374486527434251)
              ·
                refine ⟨1722403076061729791151377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148268717374486527434251 1722403076061729791151377)
                ·
                  refine ⟨1291802307046297343363533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1722403076061729791151377 1291802307046297343363533)
                  ·
                    refine ⟨484425865142361503761325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1291802307046297343363533 484425865142361503761325)
                    ·
                      refine ⟨181659699428385563910497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 484425865142361503761325 181659699428385563910497)
                      ·
                        rfl

theorem cell23_353781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_353781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353781 prefixEnd_353781 := by exact prefixLift 353781
  have htrace : WordTrace (prefixWord ++ tailWord_353781) baseStart_353781 baseEnd_353781 := by
    simpa [prefixWord, tailWord_353781, baseEnd_353781] using wordTrace_append hprefix tailTrace_353781
  have hstable : (prefixWord ++ tailWord_353781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353781).length < 2 ^ (prefixWord ++ tailWord_353781).sum := by decide
  have hdescent : baseEnd_353781 < baseStart_353781 := by decide
  rcases family_descends (prefixWord ++ tailWord_353781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353804 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 1, 3, 4]
def baseStart_353804 : Nat := 118140960795 + 353804 * 2 ^ 59
def prefixEnd_353804 : Nat := 4983230072969 + 3 ^ 40 * 353804 * 2
def baseEnd_353804 : Nat := 181671509483438973922891

theorem tailTrace_353804 : CollatzResearch.WordTrace tailWord_353804 prefixEnd_353804 181671509483438973922891 := by
  unfold tailWord_353804
  simp only [CollatzResearch.WordTrace]
  refine ⟨6452146005118003878818233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8602861340157338505090977 6452146005118003878818233)
  ·
    refine ⟨4839109503838502909113675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6452146005118003878818233 4839109503838502909113675)
    ·
      refine ⟨7258664255757754363670513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4839109503838502909113675 7258664255757754363670513)
      ·
        refine ⟨5443998191818315772752885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7258664255757754363670513 5443998191818315772752885)
        ·
          refine ⟨510374830482967103695583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5443998191818315772752885 510374830482967103695583)
          ·
            refine ⟨765562245724450655543375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510374830482967103695583 765562245724450655543375)
            ·
              refine ⟨1148343368586675983315063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765562245724450655543375 1148343368586675983315063)
              ·
                refine ⟨1722515052880013974972595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148343368586675983315063 1722515052880013974972595)
                ·
                  refine ⟨2583772579320020962458893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1722515052880013974972595 2583772579320020962458893)
                  ·
                    refine ⟨968914717245007860922085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2583772579320020962458893 968914717245007860922085)
                    ·
                      refine ⟨181671509483438973922891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 968914717245007860922085 181671509483438973922891)
                      ·
                        rfl

theorem cell23_353804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_353804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353804 prefixEnd_353804 := by exact prefixLift 353804
  have htrace : WordTrace (prefixWord ++ tailWord_353804) baseStart_353804 baseEnd_353804 := by
    simpa [prefixWord, tailWord_353804, baseEnd_353804] using wordTrace_append hprefix tailTrace_353804
  have hstable : (prefixWord ++ tailWord_353804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353804).length < 2 ^ (prefixWord ++ tailWord_353804).sum := by decide
  have hdescent : baseEnd_353804 < baseStart_353804 := by decide
  rcases family_descends (prefixWord ++ tailWord_353804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353805 : List Nat := [1, 7, 1, 1, 2, 1, 2, 3, 5]
def baseStart_353805 : Nat := 118140960795 + 353805 * 2 ^ 59
def prefixEnd_353805 : Nat := 4983230072969 + 3 ^ 40 * 353805 * 2
def baseEnd_353805 : Nat := 20185780329343718890043

theorem tailTrace_353805 : CollatzResearch.WordTrace tailWord_353805 prefixEnd_353805 20185780329343718890043 := by
  unfold tailWord_353805
  simp only [CollatzResearch.WordTrace]
  refine ⟨12904328483232384928422869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8602885655488256618948579 12904328483232384928422869)
  ·
    refine ⟨302445198825759021759911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12904328483232384928422869 302445198825759021759911)
    ·
      refine ⟨453667798238638532639867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302445198825759021759911 453667798238638532639867)
      ·
        refine ⟨680501697357957798959801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453667798238638532639867 680501697357957798959801)
        ·
          refine ⟨510376273018468349219851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680501697357957798959801 510376273018468349219851)
          ·
            refine ⟨765564409527702523829777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510376273018468349219851 765564409527702523829777)
            ·
              refine ⟨574173307145776892872333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 765564409527702523829777 574173307145776892872333)
              ·
                refine ⟨215314990179666334827125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 574173307145776892872333 215314990179666334827125)
                ·
                  refine ⟨20185780329343718890043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 215314990179666334827125 20185780329343718890043)
                  ·
                    rfl

theorem cell23_353805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_353805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353805 prefixEnd_353805 := by exact prefixLift 353805
  have htrace : WordTrace (prefixWord ++ tailWord_353805) baseStart_353805 baseEnd_353805 := by
    simpa [prefixWord, tailWord_353805, baseEnd_353805] using wordTrace_append hprefix tailTrace_353805
  have hstable : (prefixWord ++ tailWord_353805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353805).length < 2 ^ (prefixWord ++ tailWord_353805).sum := by decide
  have hdescent : baseEnd_353805 < baseStart_353805 := by decide
  rcases family_descends (prefixWord ++ tailWord_353805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353911 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 5, 2, 2]
def baseStart_353911 : Nat := 118140960795 + 353911 * 2 ^ 59
def prefixEnd_353911 : Nat := 4983230072969 + 3 ^ 40 * 353911 * 2
def baseEnd_353911 : Nat := 181726451913470055284899

theorem tailTrace_353911 : CollatzResearch.WordTrace tailWord_353911 prefixEnd_353911 181726451913470055284899 := by
  unfold tailWord_353911
  simp only [CollatzResearch.WordTrace]
  refine ⟨12908194620848365031781587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8605463080565576687854391 12908194620848365031781587)
  ·
    refine ⟨19362291931272547547672381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12908194620848365031781587 19362291931272547547672381)
    ·
      refine ⟨7260859474227205330377143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19362291931272547547672381 7260859474227205330377143)
      ·
        refine ⟨10891289211340807995565715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7260859474227205330377143 10891289211340807995565715)
        ·
          refine ⟨16336933817011211993348573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10891289211340807995565715 16336933817011211993348573)
          ·
            refine ⟨6126350181379204497505715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16336933817011211993348573 6126350181379204497505715)
            ·
              refine ⟨9189525272068806746258573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6126350181379204497505715 9189525272068806746258573)
              ·
                refine ⟨3446071977025802529846965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9189525272068806746258573 3446071977025802529846965)
                ·
                  refine ⟨323069247846168987173153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3446071977025802529846965 323069247846168987173153)
                  ·
                    refine ⟨242301935884626740379865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 323069247846168987173153 242301935884626740379865)
                    ·
                      refine ⟨181726451913470055284899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 242301935884626740379865 181726451913470055284899)
                      ·
                        rfl

theorem cell23_353911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 2, 2].length) (baseStart_353911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353911 prefixEnd_353911 := by exact prefixLift 353911
  have htrace : WordTrace (prefixWord ++ tailWord_353911) baseStart_353911 baseEnd_353911 := by
    simpa [prefixWord, tailWord_353911, baseEnd_353911] using wordTrace_append hprefix tailTrace_353911
  have hstable : (prefixWord ++ tailWord_353911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353911).length < 2 ^ (prefixWord ++ tailWord_353911).sum := by decide
  have hdescent : baseEnd_353911 < baseStart_353911 := by decide
  rcases family_descends (prefixWord ++ tailWord_353911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353937 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_353937 : Nat := 118140960795 + 353937 * 2 ^ 59
def prefixEnd_353937 : Nat := 4983230072969 + 3 ^ 40 * 353937 * 2
def baseEnd_353937 : Nat := 181739802410486953559779

theorem tailTrace_353937 : CollatzResearch.WordTrace tailWord_353937 prefixEnd_353937 181739802410486953559779 := by
  unfold tailWord_353937
  simp only [CollatzResearch.WordTrace]
  refine ⟨12909142918754171472228065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8606095279169447648152043 12909142918754171472228065)
  ·
    refine ⟨9681857189065628604171049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12909142918754171472228065 9681857189065628604171049)
    ·
      refine ⟨7261392891799221453128287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9681857189065628604171049 7261392891799221453128287)
      ·
        refine ⟨10892089337698832179692431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7261392891799221453128287 10892089337698832179692431)
        ·
          refine ⟨16338134006548248269538647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10892089337698832179692431 16338134006548248269538647)
          ·
            refine ⟨24507201009822372404307971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16338134006548248269538647 24507201009822372404307971)
            ·
              refine ⟨36760801514733558606461957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24507201009822372404307971 36760801514733558606461957)
              ·
                refine ⟨6892650284012542238711617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36760801514733558606461957 6892650284012542238711617)
                ·
                  refine ⟨5169487713009406679033713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6892650284012542238711617 5169487713009406679033713)
                  ·
                    refine ⟨3877115784757055009275285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5169487713009406679033713 3877115784757055009275285)
                    ·
                      refine ⟨181739802410486953559779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3877115784757055009275285 181739802410486953559779)
                      ·
                        rfl

theorem cell23_353937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_353937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353937 prefixEnd_353937 := by exact prefixLift 353937
  have htrace : WordTrace (prefixWord ++ tailWord_353937) baseStart_353937 baseEnd_353937 := by
    simpa [prefixWord, tailWord_353937, baseEnd_353937] using wordTrace_append hprefix tailTrace_353937
  have hstable : (prefixWord ++ tailWord_353937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353937).length < 2 ^ (prefixWord ++ tailWord_353937).sum := by decide
  have hdescent : baseEnd_353937 < baseStart_353937 := by decide
  rcases family_descends (prefixWord ++ tailWord_353937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353971 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 3, 3, 2]
def baseStart_353971 : Nat := 118140960795 + 353971 * 2 ^ 59
def prefixEnd_353971 : Nat := 4983230072969 + 3 ^ 40 * 353971 * 2
def baseEnd_353971 : Nat := 181757260752739820534623

theorem tailTrace_353971 : CollatzResearch.WordTrace tailWord_353971 prefixEnd_353971 181757260752739820534623 := by
  unfold tailWord_353971
  simp only [CollatzResearch.WordTrace]
  refine ⟨12910383000630995278965767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8606922000420663519310511 12910383000630995278965767)
  ·
    refine ⟨19365574500946492918448651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12910383000630995278965767 19365574500946492918448651)
    ·
      refine ⟨29048361751419739377672977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19365574500946492918448651 29048361751419739377672977)
      ·
        refine ⟨21786271313564804533254733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29048361751419739377672977 21786271313564804533254733)
        ·
          refine ⟨8169851742586801699970525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21786271313564804533254733 8169851742586801699970525)
          ·
            refine ⟨3063694403470050637488947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8169851742586801699970525 3063694403470050637488947)
            ·
              refine ⟨4595541605205075956233421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3063694403470050637488947 4595541605205075956233421)
              ·
                refine ⟨1723328101951903483587533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4595541605205075956233421 1723328101951903483587533)
                ·
                  refine ⟨646248038231963806345325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1723328101951903483587533 646248038231963806345325)
                  ·
                    refine ⟨242343014336986427379497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 646248038231963806345325 242343014336986427379497)
                    ·
                      refine ⟨181757260752739820534623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 242343014336986427379497 181757260752739820534623)
                      ·
                        rfl

theorem cell23_353971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 3, 2].length) (baseStart_353971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_353971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_353971 prefixEnd_353971 := by exact prefixLift 353971
  have htrace : WordTrace (prefixWord ++ tailWord_353971) baseStart_353971 baseEnd_353971 := by
    simpa [prefixWord, tailWord_353971, baseEnd_353971] using wordTrace_append hprefix tailTrace_353971
  have hstable : (prefixWord ++ tailWord_353971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353971).length < 2 ^ (prefixWord ++ tailWord_353971).sum := by decide
  have hdescent : baseEnd_353971 < baseStart_353971 := by decide
  rcases family_descends (prefixWord ++ tailWord_353971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354012 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_354012 : Nat := 118140960795 + 354012 * 2 ^ 59
def prefixEnd_354012 : Nat := 4983230072969 + 3 ^ 40 * 354012 * 2
def baseEnd_354012 : Nat := 181778313459574160121935

theorem tailTrace_354012 : CollatzResearch.WordTrace tailWord_354012 prefixEnd_354012 181778313459574160121935 := by
  unfold tailWord_354012
  simp only [CollatzResearch.WordTrace]
  refine ⟨6455939196741229640604145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8607918928988306187472193 6455939196741229640604145)
  ·
    refine ⟨4841954397555922230453109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6455939196741229640604145 4841954397555922230453109)
    ·
      refine ⟨453933224770867709104979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4841954397555922230453109 453933224770867709104979)
      ·
        refine ⟨680899837156301563657469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453933224770867709104979 680899837156301563657469)
        ·
          refine ⟨255337438933613086371551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 680899837156301563657469 255337438933613086371551)
          ·
            refine ⟨383006158400419629557327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255337438933613086371551 383006158400419629557327)
            ·
              refine ⟨574509237600629444335991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383006158400419629557327 574509237600629444335991)
              ·
                refine ⟨861763856400944166503987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574509237600629444335991 861763856400944166503987)
                ·
                  refine ⟨1292645784601416249755981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861763856400944166503987 1292645784601416249755981)
                  ·
                    refine ⟨484742169225531093658493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1292645784601416249755981 484742169225531093658493)
                    ·
                      refine ⟨181778313459574160121935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 484742169225531093658493 181778313459574160121935)
                      ·
                        rfl

theorem cell23_354012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_354012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354012 prefixEnd_354012 := by exact prefixLift 354012
  have htrace : WordTrace (prefixWord ++ tailWord_354012) baseStart_354012 baseEnd_354012 := by
    simpa [prefixWord, tailWord_354012, baseEnd_354012] using wordTrace_append hprefix tailTrace_354012
  have hstable : (prefixWord ++ tailWord_354012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354012).length < 2 ^ (prefixWord ++ tailWord_354012).sum := by decide
  have hdescent : baseEnd_354012 < baseStart_354012 := by decide
  rcases family_descends (prefixWord ++ tailWord_354012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354088 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 2, 5]
def baseStart_354088 : Nat := 118140960795 + 354088 * 2 ^ 59
def prefixEnd_354088 : Nat := 4983230072969 + 3 ^ 40 * 354088 * 2
def baseEnd_354088 : Nat := 60605779329771954257195

theorem tailTrace_354088 : CollatzResearch.WordTrace tailWord_354088 prefixEnd_354088 60605779329771954257195 := by
  unfold tailWord_354088
  simp only [CollatzResearch.WordTrace]
  refine ⟨6457325170603562130487459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8609766894138082840649945 6457325170603562130487459)
  ·
    refine ⟨9685987755905343195731189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6457325170603562130487459 9685987755905343195731189)
    ·
      refine ⟨908061352116125924599799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9685987755905343195731189 908061352116125924599799)
      ·
        refine ⟨1362092028174188886899699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908061352116125924599799 1362092028174188886899699)
        ·
          refine ⟨2043138042261283330349549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362092028174188886899699 2043138042261283330349549)
          ·
            refine ⟨766176765847981248881081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2043138042261283330349549 766176765847981248881081)
            ·
              refine ⟨574632574385985936660811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766176765847981248881081 574632574385985936660811)
              ·
                refine ⟨861948861578978904991217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574632574385985936660811 861948861578978904991217)
                ·
                  refine ⟨646461646184234178743413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 861948861578978904991217 646461646184234178743413)
                  ·
                    refine ⟨60605779329771954257195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 646461646184234178743413 60605779329771954257195)
                    ·
                      rfl

theorem cell23_354088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_354088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354088 prefixEnd_354088 := by exact prefixLift 354088
  have htrace : WordTrace (prefixWord ++ tailWord_354088) baseStart_354088 baseEnd_354088 := by
    simpa [prefixWord, tailWord_354088, baseEnd_354088] using wordTrace_append hprefix tailTrace_354088
  have hstable : (prefixWord ++ tailWord_354088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354088).length < 2 ^ (prefixWord ++ tailWord_354088).sum := by decide
  have hdescent : baseEnd_354088 < baseStart_354088 := by decide
  rcases family_descends (prefixWord ++ tailWord_354088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354125 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_354125 : Nat := 118140960795 + 354125 * 2 ^ 59
def prefixEnd_354125 : Nat := 4983230072969 + 3 ^ 40 * 354125 * 2
def baseEnd_354125 : Nat := 181836336773532218008915

theorem tailTrace_354125 : CollatzResearch.WordTrace tailWord_354125 prefixEnd_354125 181836336773532218008915 := by
  unfold tailWord_354125
  simp only [CollatzResearch.WordTrace]
  refine ⟨12915999842073079580071829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8610666561382053053381219 12915999842073079580071829)
  ·
    refine ⟨605437492597175605315867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12915999842073079580071829 605437492597175605315867)
    ·
      refine ⟨908156238895763407973801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605437492597175605315867 908156238895763407973801)
      ·
        refine ⟨681117179171822555980351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 908156238895763407973801 681117179171822555980351)
        ·
          refine ⟨1021675768757733833970527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681117179171822555980351 1021675768757733833970527)
          ·
            refine ⟨1532513653136600750955791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021675768757733833970527 1532513653136600750955791)
            ·
              refine ⟨2298770479704901126433687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532513653136600750955791 2298770479704901126433687)
              ·
                refine ⟨3448155719557351689650531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298770479704901126433687 3448155719557351689650531)
                ·
                  refine ⟨5172233579336027534475797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448155719557351689650531 5172233579336027534475797)
                  ·
                    refine ⟨242448449031376290678553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5172233579336027534475797 242448449031376290678553)
                    ·
                      refine ⟨181836336773532218008915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 242448449031376290678553 181836336773532218008915)
                      ·
                        rfl

theorem cell23_354125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_354125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354125 prefixEnd_354125 := by exact prefixLift 354125
  have htrace : WordTrace (prefixWord ++ tailWord_354125) baseStart_354125 baseEnd_354125 := by
    simpa [prefixWord, tailWord_354125, baseEnd_354125] using wordTrace_append hprefix tailTrace_354125
  have hstable : (prefixWord ++ tailWord_354125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354125).length < 2 ^ (prefixWord ++ tailWord_354125).sum := by decide
  have hdescent : baseEnd_354125 < baseStart_354125 := by decide
  rcases family_descends (prefixWord ++ tailWord_354125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354211 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 4]
def baseStart_354211 : Nat := 118140960795 + 354211 * 2 ^ 59
def prefixEnd_354211 : Nat := 4983230072969 + 3 ^ 40 * 354211 * 2
def baseEnd_354211 : Nat := 181880496109818881533519

theorem tailTrace_354211 : CollatzResearch.WordTrace tailWord_354211 prefixEnd_354211 181880496109818881533519 := by
  unfold tailWord_354211
  simp only [CollatzResearch.WordTrace]
  refine ⟨12919136519761516267702487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8612757679841010845134991 12919136519761516267702487)
  ·
    refine ⟨19378704779642274401553731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12919136519761516267702487 19378704779642274401553731)
    ·
      refine ⟨29068057169463411602330597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19378704779642274401553731 29068057169463411602330597)
      ·
        refine ⟨5450260719274389675436987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29068057169463411602330597 5450260719274389675436987)
        ·
          refine ⟨8175391078911584513155481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5450260719274389675436987 8175391078911584513155481)
          ·
            refine ⟨6131543309183688384866611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8175391078911584513155481 6131543309183688384866611)
            ·
              refine ⟨9197314963775532577299917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131543309183688384866611 9197314963775532577299917)
              ·
                refine ⟨3448993111415824716487469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9197314963775532577299917 3448993111415824716487469)
                ·
                  refine ⟨1293372416780934268682801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3448993111415824716487469 1293372416780934268682801)
                  ·
                    refine ⟨970029312585700701512101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1293372416780934268682801 970029312585700701512101)
                    ·
                      refine ⟨181880496109818881533519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 970029312585700701512101 181880496109818881533519)
                      ·
                        rfl

theorem cell23_354211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_354211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354211 prefixEnd_354211 := by exact prefixLift 354211
  have htrace : WordTrace (prefixWord ++ tailWord_354211) baseStart_354211 baseEnd_354211 := by
    simpa [prefixWord, tailWord_354211, baseEnd_354211] using wordTrace_append hprefix tailTrace_354211
  have hstable : (prefixWord ++ tailWord_354211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354211).length < 2 ^ (prefixWord ++ tailWord_354211).sum := by decide
  have hdescent : baseEnd_354211 < baseStart_354211 := by decide
  rcases family_descends (prefixWord ++ tailWord_354211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354215 : List Nat := [1, 1, 6, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_354215 : Nat := 118140960795 + 354215 * 2 ^ 59
def prefixEnd_354215 : Nat := 4983230072969 + 3 ^ 40 * 354215 * 2
def baseEnd_354215 : Nat := 181882550032436865883501

theorem tailTrace_354215 : CollatzResearch.WordTrace tailWord_354215 prefixEnd_354215 181882550032436865883501 := by
  unfold tailWord_354215
  simp only [CollatzResearch.WordTrace]
  refine ⟨12919282411747024950848099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8612854941164683300565399 12919282411747024950848099)
  ·
    refine ⟨19378923617620537426272149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12919282411747024950848099 19378923617620537426272149)
    ·
      refine ⟨908387044575962691856507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19378923617620537426272149 908387044575962691856507)
      ·
        refine ⟨1362580566863944037784761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908387044575962691856507 1362580566863944037784761)
        ·
          refine ⟨1021935425147958028338571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1362580566863944037784761 1021935425147958028338571)
          ·
            refine ⟨1532903137721937042507857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021935425147958028338571 1532903137721937042507857)
            ·
              refine ⟨1149677353291452781880893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532903137721937042507857 1149677353291452781880893)
              ·
                refine ⟨431129007484294793205335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1149677353291452781880893 431129007484294793205335)
                ·
                  refine ⟨646693511226442189808003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431129007484294793205335 646693511226442189808003)
                  ·
                    refine ⟨970040266839663284712005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 646693511226442189808003 970040266839663284712005)
                    ·
                      refine ⟨181882550032436865883501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 970040266839663284712005 181882550032436865883501)
                      ·
                        rfl

theorem cell23_354215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_354215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354215 prefixEnd_354215 := by exact prefixLift 354215
  have htrace : WordTrace (prefixWord ++ tailWord_354215) baseStart_354215 baseEnd_354215 := by
    simpa [prefixWord, tailWord_354215, baseEnd_354215] using wordTrace_append hprefix tailTrace_354215
  have hstable : (prefixWord ++ tailWord_354215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354215).length < 2 ^ (prefixWord ++ tailWord_354215).sum := by decide
  have hdescent : baseEnd_354215 < baseStart_354215 := by decide
  rcases family_descends (prefixWord ++ tailWord_354215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354238 : List Nat := [4, 2, 1, 1, 1, 4, 2, 8]
def baseStart_354238 : Nat := 118140960795 + 354238 * 2 ^ 59
def prefixEnd_354238 : Nat := 4983230072969 + 3 ^ 40 * 354238 * 2
def baseEnd_354238 : Nat := 6736828151388528736885

theorem tailTrace_354238 : CollatzResearch.WordTrace tailWord_354238 prefixEnd_354238 6736828151388528736885 := by
  unfold tailWord_354238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1615015161332962484866921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8613414193775799919290245 1615015161332962484866921)
  ·
    refine ⟨1211261370999721863650191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1615015161332962484866921 1211261370999721863650191)
    ·
      refine ⟨1816892056499582795475287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1211261370999721863650191 1816892056499582795475287)
      ·
        refine ⟨2725338084749374193212931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1816892056499582795475287 2725338084749374193212931)
        ·
          refine ⟨4088007127124061289819397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2725338084749374193212931 4088007127124061289819397)
          ·
            refine ⟨766501336335761491841137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4088007127124061289819397 766501336335761491841137)
            ·
              refine ⟨574876002251821118880853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766501336335761491841137 574876002251821118880853)
              ·
                refine ⟨6736828151388528736885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 574876002251821118880853 6736828151388528736885)
                ·
                  rfl

theorem cell23_354238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_354238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354238 prefixEnd_354238 := by exact prefixLift 354238
  have htrace : WordTrace (prefixWord ++ tailWord_354238) baseStart_354238 baseEnd_354238 := by
    simpa [prefixWord, tailWord_354238, baseEnd_354238] using wordTrace_append hprefix tailTrace_354238
  have hstable : (prefixWord ++ tailWord_354238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354238).length < 2 ^ (prefixWord ++ tailWord_354238).sum := by decide
  have hdescent : baseEnd_354238 < baseStart_354238 := by decide
  rcases family_descends (prefixWord ++ tailWord_354238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354252 : List Nat := [2, 2, 1, 4, 1, 4, 1, 2, 1, 2, 3]
def baseStart_354252 : Nat := 118140960795 + 354252 * 2 ^ 59
def prefixEnd_354252 : Nat := 4983230072969 + 3 ^ 40 * 354252 * 2
def baseEnd_354252 : Nat := 181901548816653221120831

theorem tailTrace_354252 : CollatzResearch.WordTrace tailWord_354252 prefixEnd_354252 181901548816653221120831 := by
  unfold tailWord_354252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6460315956306490134972505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8613754608408653513296673 6460315956306490134972505)
  ·
    refine ⟨4845236967229867601229379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6460315956306490134972505 4845236967229867601229379)
    ·
      refine ⟨7267855450844801401844069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4845236967229867601229379 7267855450844801401844069)
      ·
        refine ⟨1362722897033400262845763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7267855450844801401844069 1362722897033400262845763)
        ·
          refine ⟨2044084345550100394268645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362722897033400262845763 2044084345550100394268645)
          ·
            refine ⟨383265814790643823925371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2044084345550100394268645 383265814790643823925371)
            ·
              refine ⟨574898722185965735888057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383265814790643823925371 574898722185965735888057)
              ·
                refine ⟨431174041639474301916043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574898722185965735888057 431174041639474301916043)
                ·
                  refine ⟨646761062459211452874065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431174041639474301916043 646761062459211452874065)
                  ·
                    refine ⟨485070796844408589655549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 646761062459211452874065 485070796844408589655549)
                    ·
                      refine ⟨181901548816653221120831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 485070796844408589655549 181901548816653221120831)
                      ·
                        rfl

theorem cell23_354252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_354252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354252 prefixEnd_354252 := by exact prefixLift 354252
  have htrace : WordTrace (prefixWord ++ tailWord_354252) baseStart_354252 baseEnd_354252 := by
    simpa [prefixWord, tailWord_354252, baseEnd_354252] using wordTrace_append hprefix tailTrace_354252
  have hstable : (prefixWord ++ tailWord_354252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354252).length < 2 ^ (prefixWord ++ tailWord_354252).sum := by decide
  have hdescent : baseEnd_354252 < baseStart_354252 := by decide
  rcases family_descends (prefixWord ++ tailWord_354252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354262 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_354262 : Nat := 118140960795 + 354262 * 2 ^ 59
def prefixEnd_354262 : Nat := 4983230072969 + 3 ^ 40 * 354262 * 2
def baseEnd_354262 : Nat := 181906683623198181995785

theorem tailTrace_354262 : CollatzResearch.WordTrace tailWord_354262 prefixEnd_354262 181906683623198181995785 := by
  unfold tailWord_354262
  simp only [CollatzResearch.WordTrace]
  refine ⟨807562290161046998613065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8613997761717834651872693 807562290161046998613065)
  ·
    refine ⟨605671717620785248959799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 807562290161046998613065 605671717620785248959799)
    ·
      refine ⟨908507576431177873439699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605671717620785248959799 908507576431177873439699)
      ·
        refine ⟨1362761364646766810159549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908507576431177873439699 1362761364646766810159549)
        ·
          refine ⟨511035511742537553809831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1362761364646766810159549 511035511742537553809831)
          ·
            refine ⟨766553267613806330714747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511035511742537553809831 766553267613806330714747)
            ·
              refine ⟨1149829901420709496072121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766553267613806330714747 1149829901420709496072121)
              ·
                refine ⟨862372426065532122054091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149829901420709496072121 862372426065532122054091)
                ·
                  refine ⟨1293558639098298183081137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862372426065532122054091 1293558639098298183081137)
                  ·
                    refine ⟨970168979323723637310853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1293558639098298183081137 970168979323723637310853)
                    ·
                      refine ⟨181906683623198181995785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 970168979323723637310853 181906683623198181995785)
                      ·
                        rfl

theorem cell23_354262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_354262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354262 prefixEnd_354262 := by exact prefixLift 354262
  have htrace : WordTrace (prefixWord ++ tailWord_354262) baseStart_354262 baseEnd_354262 := by
    simpa [prefixWord, tailWord_354262, baseEnd_354262] using wordTrace_append hprefix tailTrace_354262
  have hstable : (prefixWord ++ tailWord_354262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354262).length < 2 ^ (prefixWord ++ tailWord_354262).sum := by decide
  have hdescent : baseEnd_354262 < baseStart_354262 := by decide
  rcases family_descends (prefixWord ++ tailWord_354262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354265 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 1, 3, 3]
def baseStart_354265 : Nat := 118140960795 + 354265 * 2 ^ 59
def prefixEnd_354265 : Nat := 4983230072969 + 3 ^ 40 * 354265 * 2
def baseEnd_354265 : Nat := 181908224065161670258271

theorem tailTrace_354265 : CollatzResearch.WordTrace tailWord_354265 prefixEnd_354265 181908224065161670258271 := by
  unfold tailWord_354265
  simp only [CollatzResearch.WordTrace]
  refine ⟨12921106061565883490168249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8614070707710588993445499 12921106061565883490168249)
  ·
    refine ⟨9690829546174412617626187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12921106061565883490168249 9690829546174412617626187)
    ·
      refine ⟨14536244319261618926439281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9690829546174412617626187 14536244319261618926439281)
      ·
        refine ⟨10902183239446214194829461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14536244319261618926439281 10902183239446214194829461)
        ·
          refine ⟨511039839349041290382631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10902183239446214194829461 511039839349041290382631)
          ·
            refine ⟨766559759023561935573947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511039839349041290382631 766559759023561935573947)
            ·
              refine ⟨1149839638535342903360921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766559759023561935573947 1149839638535342903360921)
              ·
                refine ⟨862379728901507177520691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149839638535342903360921 862379728901507177520691)
                ·
                  refine ⟨1293569593352260766281037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862379728901507177520691 1293569593352260766281037)
                  ·
                    refine ⟨485088597507097787355389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1293569593352260766281037 485088597507097787355389)
                    ·
                      refine ⟨181908224065161670258271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 485088597507097787355389 181908224065161670258271)
                      ·
                        rfl

theorem cell23_354265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_354265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354265 prefixEnd_354265 := by exact prefixLift 354265
  have htrace : WordTrace (prefixWord ++ tailWord_354265) baseStart_354265 baseEnd_354265 := by
    simpa [prefixWord, tailWord_354265, baseEnd_354265] using wordTrace_append hprefix tailTrace_354265
  have hstable : (prefixWord ++ tailWord_354265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354265).length < 2 ^ (prefixWord ++ tailWord_354265).sum := by decide
  have hdescent : baseEnd_354265 < baseStart_354265 := by decide
  rcases family_descends (prefixWord ++ tailWord_354265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354269 : List Nat := [1, 4, 3, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_354269 : Nat := 118140960795 + 354269 * 2 ^ 59
def prefixEnd_354269 : Nat := 4983230072969 + 3 ^ 40 * 354269 * 2
def baseEnd_354269 : Nat := 181910277987779654608253

theorem tailTrace_354269 : CollatzResearch.WordTrace tailWord_354269 prefixEnd_354269 181910277987779654608253 := by
  unfold tailWord_354269
  simp only [CollatzResearch.WordTrace]
  refine ⟨12921251953551392173313861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8614167969034261448875907 12921251953551392173313861)
  ·
    refine ⟨2422734741290886032496349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12921251953551392173313861 2422734741290886032496349)
    ·
      refine ⟨908525527984082262186131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2422734741290886032496349 908525527984082262186131)
      ·
        refine ⟨1362788291976123393279197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908525527984082262186131 1362788291976123393279197)
        ·
          refine ⟨511045609491046272479699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1362788291976123393279197 511045609491046272479699)
          ·
            refine ⟨766568414236569408719549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511045609491046272479699 766568414236569408719549)
            ·
              refine ⟨287463155338713528269831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 766568414236569408719549 287463155338713528269831)
              ·
                refine ⟨431194733008070292404747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287463155338713528269831 431194733008070292404747)
                ·
                  refine ⟨646792099512105438607121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431194733008070292404747 646792099512105438607121)
                  ·
                    refine ⟨485094074634079078955341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 646792099512105438607121 485094074634079078955341)
                    ·
                      refine ⟨181910277987779654608253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 485094074634079078955341 181910277987779654608253)
                      ·
                        rfl

theorem cell23_354269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_354269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354269 prefixEnd_354269 := by exact prefixLift 354269
  have htrace : WordTrace (prefixWord ++ tailWord_354269) baseStart_354269 baseEnd_354269 := by
    simpa [prefixWord, tailWord_354269, baseEnd_354269] using wordTrace_append hprefix tailTrace_354269
  have hstable : (prefixWord ++ tailWord_354269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354269).length < 2 ^ (prefixWord ++ tailWord_354269).sum := by decide
  have hdescent : baseEnd_354269 < baseStart_354269 := by decide
  rcases family_descends (prefixWord ++ tailWord_354269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354282 : List Nat := [3, 1, 3, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_354282 : Nat := 118140960795 + 354282 * 2 ^ 59
def prefixEnd_354282 : Nat := 4983230072969 + 3 ^ 40 * 354282 * 2
def baseEnd_354282 : Nat := 181916953236288103745693

theorem tailTrace_354282 : CollatzResearch.WordTrace tailWord_354282 prefixEnd_354282 181916953236288103745693 := by
  unfold tailWord_354282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3230431525626073848384275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8614484068336196929024733 3230431525626073848384275)
  ·
    refine ⟨4845647288439110772576413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3230431525626073848384275 4845647288439110772576413)
    ·
      refine ⟨1817117733164666539716155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4845647288439110772576413 1817117733164666539716155)
      ·
        refine ⟨2725676599746999809574233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817117733164666539716155 2725676599746999809574233)
        ·
          refine ⟨2044257449810249857180675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2725676599746999809574233 2044257449810249857180675)
          ·
            refine ⟨3066386174715374785771013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044257449810249857180675 3066386174715374785771013)
            ·
              refine ⟨574947407759132772332065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3066386174715374785771013 574947407759132772332065)
              ·
                refine ⟨431210555819349579249049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574947407759132772332065 431210555819349579249049)
                ·
                  refine ⟨323407916864512184436787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431210555819349579249049 323407916864512184436787)
                  ·
                    refine ⟨485111875296768276655181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 323407916864512184436787 485111875296768276655181)
                    ·
                      refine ⟨181916953236288103745693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 485111875296768276655181 181916953236288103745693)
                      ·
                        rfl

theorem cell23_354282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_354282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354282 prefixEnd_354282 := by exact prefixLift 354282
  have htrace : WordTrace (prefixWord ++ tailWord_354282) baseStart_354282 baseEnd_354282 := by
    simpa [prefixWord, tailWord_354282, baseEnd_354282] using wordTrace_append hprefix tailTrace_354282
  have hstable : (prefixWord ++ tailWord_354282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354282).length < 2 ^ (prefixWord ++ tailWord_354282).sum := by decide
  have hdescent : baseEnd_354282 < baseStart_354282 := by decide
  rcases family_descends (prefixWord ++ tailWord_354282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354291 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 5]
def baseStart_354291 : Nat := 118140960795 + 354291 * 2 ^ 59
def prefixEnd_354291 : Nat := 4983230072969 + 3 ^ 40 * 354291 * 2
def baseEnd_354291 : Nat := 181921574562178568533151

theorem tailTrace_354291 : CollatzResearch.WordTrace tailWord_354291 prefixEnd_354291 181921574562178568533151 := by
  unfold tailWord_354291
  simp only [CollatzResearch.WordTrace]
  refine ⟨12922054359471689930614727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8614702906314459953743151 12922054359471689930614727)
  ·
    refine ⟨19383081539207534895922091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12922054359471689930614727 19383081539207534895922091)
    ·
      refine ⟨29074622308811302343883137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19383081539207534895922091 29074622308811302343883137)
      ·
        refine ⟨21805966731608476757912353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29074622308811302343883137 21805966731608476757912353)
        ·
          refine ⟨16354475048706357568434265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21805966731608476757912353 16354475048706357568434265)
          ·
            refine ⟨12265856286529768176325699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16354475048706357568434265 12265856286529768176325699)
            ·
              refine ⟨18398784429794652264488549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12265856286529768176325699 18398784429794652264488549)
              ·
                refine ⟨3449772080586497299591603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18398784429794652264488549 3449772080586497299591603)
                ·
                  refine ⟨5174658120879745949387405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449772080586497299591603 5174658120879745949387405)
                  ·
                    refine ⟨1940496795329904731020277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5174658120879745949387405 1940496795329904731020277)
                    ·
                      refine ⟨181921574562178568533151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1940496795329904731020277 181921574562178568533151)
                      ·
                        rfl

theorem cell23_354291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_354291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354291 prefixEnd_354291 := by exact prefixLift 354291
  have htrace : WordTrace (prefixWord ++ tailWord_354291) baseStart_354291 baseEnd_354291 := by
    simpa [prefixWord, tailWord_354291, baseEnd_354291] using wordTrace_append hprefix tailTrace_354291
  have hstable : (prefixWord ++ tailWord_354291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354291).length < 2 ^ (prefixWord ++ tailWord_354291).sum := by decide
  have hdescent : baseEnd_354291 < baseStart_354291 := by decide
  rcases family_descends (prefixWord ++ tailWord_354291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354318 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_354318 : Nat := 118140960795 + 354318 * 2 ^ 59
def prefixEnd_354318 : Nat := 4983230072969 + 3 ^ 40 * 354318 * 2
def baseEnd_354318 : Nat := 181935438539849962895527

theorem tailTrace_354318 : CollatzResearch.WordTrace tailWord_354318 prefixEnd_354318 181935438539849962895527 := by
  unfold tailWord_354318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1615379891296734192730951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8615359420249249027898405 1615379891296734192730951)
  ·
    refine ⟨2423069836945101289096427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1615379891296734192730951 2423069836945101289096427)
    ·
      refine ⟨3634604755417651933644641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2423069836945101289096427 3634604755417651933644641)
      ·
        refine ⟨2725953566563238950233481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3634604755417651933644641 2725953566563238950233481)
        ·
          refine ⟨2044465174922429212675111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2725953566563238950233481 2044465174922429212675111)
          ·
            refine ⟨3066697762383643819012667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044465174922429212675111 3066697762383643819012667)
            ·
              refine ⟨4600046643575465728519001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3066697762383643819012667 4600046643575465728519001)
              ·
                refine ⟨3450034982681599296389251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4600046643575465728519001 3450034982681599296389251)
                ·
                  refine ⟨5175052474022398944583877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3450034982681599296389251 5175052474022398944583877)
                  ·
                    refine ⟨970322338879199802109477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5175052474022398944583877 970322338879199802109477)
                    ·
                      refine ⟨181935438539849962895527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 970322338879199802109477 181935438539849962895527)
                      ·
                        rfl

theorem cell23_354318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_354318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354318 prefixEnd_354318 := by exact prefixLift 354318
  have htrace : WordTrace (prefixWord ++ tailWord_354318) baseStart_354318 baseEnd_354318 := by
    simpa [prefixWord, tailWord_354318, baseEnd_354318] using wordTrace_append hprefix tailTrace_354318
  have hstable : (prefixWord ++ tailWord_354318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354318).length < 2 ^ (prefixWord ++ tailWord_354318).sum := by decide
  have hdescent : baseEnd_354318 < baseStart_354318 := by decide
  rcases family_descends (prefixWord ++ tailWord_354318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354321 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_354321 : Nat := 118140960795 + 354321 * 2 ^ 59
def prefixEnd_354321 : Nat := 4983230072969 + 3 ^ 40 * 354321 * 2
def baseEnd_354321 : Nat := 181936978981813451158013

theorem tailTrace_354321 : CollatzResearch.WordTrace tailWord_354321 prefixEnd_354321 181936978981813451158013 := by
  unfold tailWord_354321
  simp only [CollatzResearch.WordTrace]
  refine ⟨12923148549363005054206817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8615432366242003369471211 12923148549363005054206817)
  ·
    refine ⟨9692361412022253790655113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12923148549363005054206817 9692361412022253790655113)
    ·
      refine ⟨7269271059016690342991335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9692361412022253790655113 7269271059016690342991335)
      ·
        refine ⟨10903906588525035514487003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7269271059016690342991335 10903906588525035514487003)
        ·
          refine ⟨16355859882787553271730505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10903906588525035514487003 16355859882787553271730505)
          ·
            refine ⟨12266894912090664953797879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16355859882787553271730505 12266894912090664953797879)
            ·
              refine ⟨18400342368135997430696819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12266894912090664953797879 18400342368135997430696819)
              ·
                refine ⟨27600513552203996146045229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18400342368135997430696819 27600513552203996146045229)
                ·
                  refine ⟨10350192582076498554766961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27600513552203996146045229 10350192582076498554766961)
                  ·
                    refine ⟨7762644436557373916075221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10350192582076498554766961 7762644436557373916075221)
                    ·
                      refine ⟨181936978981813451158013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7762644436557373916075221 181936978981813451158013)
                      ·
                        rfl

theorem cell23_354321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_354321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354321 prefixEnd_354321 := by exact prefixLift 354321
  have htrace : WordTrace (prefixWord ++ tailWord_354321) baseStart_354321 baseEnd_354321 := by
    simpa [prefixWord, tailWord_354321, baseEnd_354321] using wordTrace_append hprefix tailTrace_354321
  have hstable : (prefixWord ++ tailWord_354321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354321).length < 2 ^ (prefixWord ++ tailWord_354321).sum := by decide
  have hdescent : baseEnd_354321 < baseStart_354321 := by decide
  rcases family_descends (prefixWord ++ tailWord_354321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354356 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_354356 : Nat := 118140960795 + 354356 * 2 ^ 59
def prefixEnd_354356 : Nat := 4983230072969 + 3 ^ 40 * 354356 * 2
def baseEnd_354356 : Nat := 181954950804720814220353

theorem tailTrace_354356 : CollatzResearch.WordTrace tailWord_354356 prefixEnd_354356 181954950804720814220353 := by
  unfold tailWord_354356
  simp only [CollatzResearch.WordTrace]
  refine ⟨6462212552118103015865461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8616283402824137354487281 6462212552118103015865461)
  ·
    refine ⟨605832426761072157737387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6462212552118103015865461 605832426761072157737387)
    ·
      refine ⟨908748640141608236606081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605832426761072157737387 908748640141608236606081)
      ·
        refine ⟨681561480106206177454561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 908748640141608236606081 681561480106206177454561)
        ·
          refine ⟨511171110079654633090921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681561480106206177454561 511171110079654633090921)
          ·
            refine ⟨383378332559740974818191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511171110079654633090921 383378332559740974818191)
            ·
              refine ⟨575067498839611462227287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383378332559740974818191 575067498839611462227287)
              ·
                refine ⟨862601248259417193340931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575067498839611462227287 862601248259417193340931)
                ·
                  refine ⟨1293901872389125790011397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862601248259417193340931 1293901872389125790011397)
                  ·
                    refine ⟨242606601072961085627137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1293901872389125790011397 242606601072961085627137)
                    ·
                      refine ⟨181954950804720814220353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 242606601072961085627137 181954950804720814220353)
                      ·
                        rfl

theorem cell23_354356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_354356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354356 prefixEnd_354356 := by exact prefixLift 354356
  have htrace : WordTrace (prefixWord ++ tailWord_354356) baseStart_354356 baseEnd_354356 := by
    simpa [prefixWord, tailWord_354356, baseEnd_354356] using wordTrace_append hprefix tailTrace_354356
  have hstable : (prefixWord ++ tailWord_354356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354356).length < 2 ^ (prefixWord ++ tailWord_354356).sum := by decide
  have hdescent : baseEnd_354356 < baseStart_354356 := by decide
  rcases family_descends (prefixWord ++ tailWord_354356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354402 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_354402 : Nat := 118140960795 + 354402 * 2 ^ 59
def prefixEnd_354402 : Nat := 4983230072969 + 3 ^ 40 * 354402 * 2
def baseEnd_354402 : Nat := 181978570914827634245141

theorem tailTrace_354402 : CollatzResearch.WordTrace tailWord_354402 prefixEnd_354402 181978570914827634245141 := by
  unfold tailWord_354402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3231525715517388971976365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8617401908046370591936973 3231525715517388971976365)
  ·
    refine ⟨1211822143319020864491137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3231525715517388971976365 1211822143319020864491137)
    ·
      refine ⟨908866607489265648368353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1211822143319020864491137 908866607489265648368353)
      ·
        refine ⟨681649955616949236276265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 908866607489265648368353 681649955616949236276265)
        ·
          refine ⟨511237466712711927207199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681649955616949236276265 511237466712711927207199)
          ·
            refine ⟨766856200069067890810799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511237466712711927207199 766856200069067890810799)
            ·
              refine ⟨1150284300103601836216199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766856200069067890810799 1150284300103601836216199)
              ·
                refine ⟨1725426450155402754324299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150284300103601836216199 1725426450155402754324299)
                ·
                  refine ⟨2588139675233104131486449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725426450155402754324299 2588139675233104131486449)
                  ·
                    refine ⟨1941104756424828098614837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2588139675233104131486449 1941104756424828098614837)
                    ·
                      refine ⟨181978570914827634245141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1941104756424828098614837 181978570914827634245141)
                      ·
                        rfl

theorem cell23_354402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_354402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354402 prefixEnd_354402 := by exact prefixLift 354402
  have htrace : WordTrace (prefixWord ++ tailWord_354402) baseStart_354402 baseEnd_354402 := by
    simpa [prefixWord, tailWord_354402, baseEnd_354402] using wordTrace_append hprefix tailTrace_354402
  have hstable : (prefixWord ++ tailWord_354402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354402).length < 2 ^ (prefixWord ++ tailWord_354402).sum := by decide
  have hdescent : baseEnd_354402 < baseStart_354402 := by decide
  rcases family_descends (prefixWord ++ tailWord_354402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354465 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 3, 5]
def baseStart_354465 : Nat := 118140960795 + 354465 * 2 ^ 59
def prefixEnd_354465 : Nat := 4983230072969 + 3 ^ 40 * 354465 * 2
def baseEnd_354465 : Nat := 60670306732020295919117

theorem tailTrace_354465 : CollatzResearch.WordTrace tailWord_354465 prefixEnd_354465 60670306732020295919117 := by
  unfold tailWord_354465
  simp only [CollatzResearch.WordTrace]
  refine ⟨12928400660841317647448849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8618933773894211764965899 12928400660841317647448849)
  ·
    refine ⟨9696300495630988235586637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12928400660841317647448849 9696300495630988235586637)
    ·
      refine ⟨3636112685861620588344989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9696300495630988235586637 3636112685861620588344989)
      ·
        refine ⟨1363542257198107720629371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3636112685861620588344989 1363542257198107720629371)
        ·
          refine ⟨2045313385797161580944057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363542257198107720629371 2045313385797161580944057)
          ·
            refine ⟨1533985039347871185708043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2045313385797161580944057 1533985039347871185708043)
            ·
              refine ⟨2300977559021806778562065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533985039347871185708043 2300977559021806778562065)
              ·
                refine ⟨1725733169266355083921549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2300977559021806778562065 1725733169266355083921549)
                ·
                  refine ⟨647149938474883156470581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1725733169266355083921549 647149938474883156470581)
                  ·
                    refine ⟨60670306732020295919117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 647149938474883156470581 60670306732020295919117)
                    ·
                      rfl

theorem cell23_354465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_354465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354465 prefixEnd_354465 := by exact prefixLift 354465
  have htrace : WordTrace (prefixWord ++ tailWord_354465) baseStart_354465 baseEnd_354465 := by
    simpa [prefixWord, tailWord_354465, baseEnd_354465] using wordTrace_append hprefix tailTrace_354465
  have hstable : (prefixWord ++ tailWord_354465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354465).length < 2 ^ (prefixWord ++ tailWord_354465).sum := by decide
  have hdescent : baseEnd_354465 < baseStart_354465 := by decide
  rcases family_descends (prefixWord ++ tailWord_354465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354495 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 4, 4]
def baseStart_354495 : Nat := 118140960795 + 354495 * 2 ^ 59
def prefixEnd_354495 : Nat := 4983230072969 + 3 ^ 40 * 354495 * 2
def baseEnd_354495 : Nat := 60675441538565256794071

theorem tailTrace_354495 : CollatzResearch.WordTrace tailWord_354495 prefixEnd_354495 60675441538565256794071 := by
  unfold tailWord_354495
  simp only [CollatzResearch.WordTrace]
  refine ⟨12929494850732632771040939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8619663233821755180693959 12929494850732632771040939)
  ·
    refine ⟨19394242276098949156561409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12929494850732632771040939 19394242276098949156561409)
    ·
      refine ⟨14545681707074211867421057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19394242276098949156561409 14545681707074211867421057)
      ·
        refine ⟨10909261280305658900565793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14545681707074211867421057 10909261280305658900565793)
        ·
          refine ⟨8181945960229244175424345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10909261280305658900565793 8181945960229244175424345)
          ·
            refine ⟨6136459470171933131568259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8181945960229244175424345 6136459470171933131568259)
            ·
              refine ⟨9204689205257899697352389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6136459470171933131568259 9204689205257899697352389)
              ·
                refine ⟨1725879225985856193253573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9204689205257899697352389 1725879225985856193253573)
                ·
                  refine ⟨323602354872348036235045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1725879225985856193253573 323602354872348036235045)
                  ·
                    refine ⟨60675441538565256794071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 323602354872348036235045 60675441538565256794071)
                    ·
                      rfl

theorem cell23_354495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 4].length) (baseStart_354495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354495 prefixEnd_354495 := by exact prefixLift 354495
  have htrace : WordTrace (prefixWord ++ tailWord_354495) baseStart_354495 baseEnd_354495 := by
    simpa [prefixWord, tailWord_354495, baseEnd_354495] using wordTrace_append hprefix tailTrace_354495
  have hstable : (prefixWord ++ tailWord_354495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354495).length < 2 ^ (prefixWord ++ tailWord_354495).sum := by decide
  have hdescent : baseEnd_354495 < baseStart_354495 := by decide
  rcases family_descends (prefixWord ++ tailWord_354495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354496 : List Nat := [2, 1, 1, 2, 5, 2, 2, 3, 1, 1, 3]
def baseStart_354496 : Nat := 118140960795 + 354496 * 2 ^ 59
def prefixEnd_354496 : Nat := 4983230072969 + 3 ^ 40 * 354496 * 2
def baseEnd_354496 : Nat := 182026838096350266469709

theorem tailTrace_354496 : CollatzResearch.WordTrace tailWord_354496 prefixEnd_354496 182026838096350266469709 := by
  unfold tailWord_354496
  simp only [CollatzResearch.WordTrace]
  refine ⟨6464765661864504970913671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8619687549152673294551561 6464765661864504970913671)
  ·
    refine ⟨9697148492796757456370507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6464765661864504970913671 9697148492796757456370507)
    ·
      refine ⟨14545722739195136184555761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9697148492796757456370507 14545722739195136184555761)
      ·
        refine ⟨10909292054396352138416821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14545722739195136184555761 10909292054396352138416821)
        ·
          refine ⟨1022746130099658012976577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10909292054396352138416821 1022746130099658012976577)
          ·
            refine ⟨767059597574743509732433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1022746130099658012976577 767059597574743509732433)
            ·
              refine ⟨575294698181057632299325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767059597574743509732433 575294698181057632299325)
              ·
                refine ⟨215735511817896612112247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 575294698181057632299325 215735511817896612112247)
                ·
                  refine ⟨323603267726844918168371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215735511817896612112247 323603267726844918168371)
                  ·
                    refine ⟨485404901590267377252557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 323603267726844918168371 485404901590267377252557)
                    ·
                      refine ⟨182026838096350266469709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 485404901590267377252557 182026838096350266469709)
                      ·
                        rfl

theorem cell23_354496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 1, 1, 3].length) (baseStart_354496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354496 prefixEnd_354496 := by exact prefixLift 354496
  have htrace : WordTrace (prefixWord ++ tailWord_354496) baseStart_354496 baseEnd_354496 := by
    simpa [prefixWord, tailWord_354496, baseEnd_354496] using wordTrace_append hprefix tailTrace_354496
  have hstable : (prefixWord ++ tailWord_354496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354496).length < 2 ^ (prefixWord ++ tailWord_354496).sum := by decide
  have hdescent : baseEnd_354496 < baseStart_354496 := by decide
  rcases family_descends (prefixWord ++ tailWord_354496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354505 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 5, 2, 3]
def baseStart_354505 : Nat := 118140960795 + 354505 * 2 ^ 59
def prefixEnd_354505 : Nat := 4983230072969 + 3 ^ 40 * 354505 * 2
def baseEnd_354505 : Nat := 182031459422240731257167

theorem tailTrace_354505 : CollatzResearch.WordTrace tailWord_354505 prefixEnd_354505 182031459422240731257167 := by
  unfold tailWord_354505
  simp only [CollatzResearch.WordTrace]
  refine ⟨12929859580696404478904969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8619906387130936319269979 12929859580696404478904969)
  ·
    refine ⟨9697394685522303359178727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12929859580696404478904969 9697394685522303359178727)
    ·
      refine ⟨14546092028283455038768091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9697394685522303359178727 14546092028283455038768091)
      ·
        refine ⟨21819138042425182558152137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14546092028283455038768091 21819138042425182558152137)
        ·
          refine ⟨16364353531818886918614103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21819138042425182558152137 16364353531818886918614103)
          ·
            refine ⟨24546530297728330377921155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16364353531818886918614103 24546530297728330377921155)
            ·
              refine ⟨36819795446592495566881733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24546530297728330377921155 36819795446592495566881733)
              ·
                refine ⟨6903711646236092918790325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36819795446592495566881733 6903711646236092918790325)
                ·
                  refine ⟨647222966834633711136593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6903711646236092918790325 647222966834633711136593)
                  ·
                    refine ⟨485417225125975283352445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 647222966834633711136593 485417225125975283352445)
                    ·
                      refine ⟨182031459422240731257167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 485417225125975283352445 182031459422240731257167)
                      ·
                        rfl

theorem cell23_354505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 2, 3].length) (baseStart_354505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354505 prefixEnd_354505 := by exact prefixLift 354505
  have htrace : WordTrace (prefixWord ++ tailWord_354505) baseStart_354505 baseEnd_354505 := by
    simpa [prefixWord, tailWord_354505, baseEnd_354505] using wordTrace_append hprefix tailTrace_354505
  have hstable : (prefixWord ++ tailWord_354505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354505).length < 2 ^ (prefixWord ++ tailWord_354505).sum := by decide
  have hdescent : baseEnd_354505 < baseStart_354505 := by decide
  rcases family_descends (prefixWord ++ tailWord_354505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354529 : List Nat := [1, 2, 3, 1, 3, 1, 5, 1, 2, 4]
def baseStart_354529 : Nat := 118140960795 + 354529 * 2 ^ 59
def prefixEnd_354529 : Nat := 4983230072969 + 3 ^ 40 * 354529 * 2
def baseEnd_354529 : Nat := 60681260985982879119019

theorem tailTrace_354529 : CollatzResearch.WordTrace tailWord_354529 prefixEnd_354529 60681260985982879119019 := by
  unfold tailWord_354529
  simp only [CollatzResearch.WordTrace]
  refine ⟨12930734932609456577778641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8620489955072971051852427 12930734932609456577778641)
  ·
    refine ⟨9698051199457092433333981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12930734932609456577778641 9698051199457092433333981)
    ·
      refine ⟨3636769199796409662500243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9698051199457092433333981 3636769199796409662500243)
      ·
        refine ⟨5455153799694614493750365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3636769199796409662500243 5455153799694614493750365)
        ·
          refine ⟨2045682674885480435156387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5455153799694614493750365 2045682674885480435156387)
          ·
            refine ⟨3068524012328220652734581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045682674885480435156387 3068524012328220652734581)
            ·
              refine ⟨287674126155770686193867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3068524012328220652734581 287674126155770686193867)
              ·
                refine ⟨431511189233656029290801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287674126155770686193867 431511189233656029290801)
                ·
                  refine ⟨323633391925242021968101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431511189233656029290801 323633391925242021968101)
                  ·
                    refine ⟨60681260985982879119019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 323633391925242021968101 60681260985982879119019)
                    ·
                      rfl

theorem cell23_354529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_354529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354529 prefixEnd_354529 := by exact prefixLift 354529
  have htrace : WordTrace (prefixWord ++ tailWord_354529) baseStart_354529 baseEnd_354529 := by
    simpa [prefixWord, tailWord_354529, baseEnd_354529] using wordTrace_append hprefix tailTrace_354529
  have hstable : (prefixWord ++ tailWord_354529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354529).length < 2 ^ (prefixWord ++ tailWord_354529).sum := by decide
  have hdescent : baseEnd_354529 < baseStart_354529 := by decide
  rcases family_descends (prefixWord ++ tailWord_354529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354586 : List Nat := [3, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3]
def baseStart_354586 : Nat := 118140960795 + 354586 * 2 ^ 59
def prefixEnd_354586 : Nat := 4983230072969 + 3 ^ 40 * 354586 * 2
def baseEnd_354586 : Nat := 182073051355254914344295

theorem tailTrace_354586 : CollatzResearch.WordTrace tailWord_354586 prefixEnd_354586 182073051355254914344295 := by
  unfold tailWord_354586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3233203473350738828150903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8621875928935303541735741 3233203473350738828150903)
  ·
    refine ⟨4849805210026108242226355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3233203473350738828150903 4849805210026108242226355)
    ·
      refine ⟨7274707815039162363339533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4849805210026108242226355 7274707815039162363339533)
      ·
        refine ⟨2728015430639685886252325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7274707815039162363339533 2728015430639685886252325)
        ·
          refine ⟨511502893244941103672311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2728015430639685886252325 511502893244941103672311)
          ·
            refine ⟨767254339867411655508467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511502893244941103672311 767254339867411655508467)
            ·
              refine ⟨1150881509801117483262701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767254339867411655508467 1150881509801117483262701)
              ·
                refine ⟨431580566175419056223513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1150881509801117483262701 431580566175419056223513)
                ·
                  refine ⟨323685424631564292167635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431580566175419056223513 323685424631564292167635)
                  ·
                    refine ⟨485528136947346438251453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 323685424631564292167635 485528136947346438251453)
                    ·
                      refine ⟨182073051355254914344295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 485528136947346438251453 182073051355254914344295)
                      ·
                        rfl

theorem cell23_354586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_354586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354586 prefixEnd_354586 := by exact prefixLift 354586
  have htrace : WordTrace (prefixWord ++ tailWord_354586) baseStart_354586 baseEnd_354586 := by
    simpa [prefixWord, tailWord_354586, baseEnd_354586] using wordTrace_append hprefix tailTrace_354586
  have hstable : (prefixWord ++ tailWord_354586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354586).length < 2 ^ (prefixWord ++ tailWord_354586).sum := by decide
  have hdescent : baseEnd_354586 < baseStart_354586 := by decide
  rcases family_descends (prefixWord ++ tailWord_354586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354595 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 5]
def baseStart_354595 : Nat := 118140960795 + 354595 * 2 ^ 59
def prefixEnd_354595 : Nat := 4983230072969 + 3 ^ 40 * 354595 * 2
def baseEnd_354595 : Nat := 182077672681145379131753

theorem tailTrace_354595 : CollatzResearch.WordTrace tailWord_354595 prefixEnd_354595 182077672681145379131753 := by
  unfold tailWord_354595
  simp only [CollatzResearch.WordTrace]
  refine ⟨12933142150370349849681239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8622094766913566566454159 12933142150370349849681239)
  ·
    refine ⟨19399713225555524774521859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12933142150370349849681239 19399713225555524774521859)
    ·
      refine ⟨29099569838333287161782789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19399713225555524774521859 29099569838333287161782789)
      ·
        refine ⟨5456169344687491342834273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29099569838333287161782789 5456169344687491342834273)
        ·
          refine ⟨4092127008515618507125705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5456169344687491342834273 4092127008515618507125705)
          ·
            refine ⟨3069095256386713880344279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4092127008515618507125705 3069095256386713880344279)
            ·
              refine ⟨4603642884580070820516419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069095256386713880344279 4603642884580070820516419)
              ·
                refine ⟨6905464326870106230774629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4603642884580070820516419 6905464326870106230774629)
                ·
                  refine ⟨1294774561288144918270243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6905464326870106230774629 1294774561288144918270243)
                  ·
                    refine ⟨1942161841932217377405365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1294774561288144918270243 1942161841932217377405365)
                    ·
                      refine ⟨182077672681145379131753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1942161841932217377405365 182077672681145379131753)
                      ·
                        rfl

theorem cell23_354595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_354595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354595 prefixEnd_354595 := by exact prefixLift 354595
  have htrace : WordTrace (prefixWord ++ tailWord_354595) baseStart_354595 baseEnd_354595 := by
    simpa [prefixWord, tailWord_354595, baseEnd_354595] using wordTrace_append hprefix tailTrace_354595
  have hstable : (prefixWord ++ tailWord_354595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354595).length < 2 ^ (prefixWord ++ tailWord_354595).sum := by decide
  have hdescent : baseEnd_354595 < baseStart_354595 := by decide
  rcases family_descends (prefixWord ++ tailWord_354595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354596 : List Nat := [2, 3, 1, 3, 1, 2, 3, 2, 1, 3, 2]
def baseStart_354596 : Nat := 118140960795 + 354596 * 2 ^ 59
def prefixEnd_354596 : Nat := 4983230072969 + 3 ^ 40 * 354596 * 2
def baseEnd_354596 : Nat := 182078186161799875219249

theorem tailTrace_354596 : CollatzResearch.WordTrace tailWord_354596 prefixEnd_354596 182078186161799875219249 := by
  unfold tailWord_354596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6466589311683363510233821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8622119082244484680311761 6466589311683363510233821)
  ·
    refine ⟨2424970991881261316337683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6466589311683363510233821 2424970991881261316337683)
    ·
      refine ⟨3637456487821891974506525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2424970991881261316337683 3637456487821891974506525)
      ·
        refine ⟨1364046182933209490439947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3637456487821891974506525 1364046182933209490439947)
        ·
          refine ⟨2046069274399814235659921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364046182933209490439947 2046069274399814235659921)
          ·
            refine ⟨1534551955799860676744941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2046069274399814235659921 1534551955799860676744941)
            ·
              refine ⟨575456983424947753779353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1534551955799860676744941 575456983424947753779353)
              ·
                refine ⟨431592737568710815334515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575456983424947753779353 431592737568710815334515)
                ·
                  refine ⟨647389106353066223001773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431592737568710815334515 647389106353066223001773)
                  ·
                    refine ⟨242770914882399833625665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 647389106353066223001773 242770914882399833625665)
                    ·
                      refine ⟨182078186161799875219249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 242770914882399833625665 182078186161799875219249)
                      ·
                        rfl

theorem cell23_354596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_354596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354596 prefixEnd_354596 := by exact prefixLift 354596
  have htrace : WordTrace (prefixWord ++ tailWord_354596) baseStart_354596 baseEnd_354596 := by
    simpa [prefixWord, tailWord_354596, baseEnd_354596] using wordTrace_append hprefix tailTrace_354596
  have hstable : (prefixWord ++ tailWord_354596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354596).length < 2 ^ (prefixWord ++ tailWord_354596).sum := by decide
  have hdescent : baseEnd_354596 < baseStart_354596 := by decide
  rcases family_descends (prefixWord ++ tailWord_354596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354642 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_354642 : Nat := 118140960795 + 354642 * 2 ^ 59
def prefixEnd_354642 : Nat := 4983230072969 + 3 ^ 40 * 354642 * 2
def baseEnd_354642 : Nat := 182101806271906695244037

theorem tailTrace_354642 : CollatzResearch.WordTrace tailWord_354642 prefixEnd_354642 182101806271906695244037 := by
  unfold tailWord_354642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3233714095300019219160545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8623237587466717917761453 3233714095300019219160545)
  ·
    refine ⟨2425285571475014414370409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3233714095300019219160545 2425285571475014414370409)
    ·
      refine ⟨1818964178606260810777807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2425285571475014414370409 1818964178606260810777807)
      ·
        refine ⟨2728446267909391216166711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1818964178606260810777807 2728446267909391216166711)
        ·
          refine ⟨4092669401864086824250067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2728446267909391216166711 4092669401864086824250067)
          ·
            refine ⟨6139004102796130236375101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4092669401864086824250067 6139004102796130236375101)
            ·
              refine ⟨2302126538548548838640663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6139004102796130236375101 2302126538548548838640663)
              ·
                refine ⟨3453189807822823257960995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2302126538548548838640663 3453189807822823257960995)
                ·
                  refine ⟨5179784711734234886941493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453189807822823257960995 5179784711734234886941493)
                  ·
                    refine ⟨485604816725084520650765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5179784711734234886941493 485604816725084520650765)
                    ·
                      refine ⟨182101806271906695244037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 485604816725084520650765 182101806271906695244037)
                      ·
                        rfl

theorem cell23_354642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_354642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354642 prefixEnd_354642 := by exact prefixLift 354642
  have htrace : WordTrace (prefixWord ++ tailWord_354642) baseStart_354642 baseEnd_354642 := by
    simpa [prefixWord, tailWord_354642, baseEnd_354642] using wordTrace_append hprefix tailTrace_354642
  have hstable : (prefixWord ++ tailWord_354642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354642).length < 2 ^ (prefixWord ++ tailWord_354642).sum := by decide
  have hdescent : baseEnd_354642 < baseStart_354642 := by decide
  rcases family_descends (prefixWord ++ tailWord_354642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354655 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 7]
def baseStart_354655 : Nat := 118140960795 + 354655 * 2 ^ 59
def prefixEnd_354655 : Nat := 4983230072969 + 3 ^ 40 * 354655 * 2
def baseEnd_354655 : Nat := 182108481520415144381477

theorem tailTrace_354655 : CollatzResearch.WordTrace tailWord_354655 prefixEnd_354655 182108481520415144381477 := by
  unfold tailWord_354655
  simp only [CollatzResearch.WordTrace]
  refine ⟨12935330530152980096865419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8623553686768653397910279 12935330530152980096865419)
  ·
    refine ⟨19402995795229470145298129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12935330530152980096865419 19402995795229470145298129)
    ·
      refine ⟨14552246846422102608973597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19402995795229470145298129 14552246846422102608973597)
      ·
        refine ⟨5457092567408288478365099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14552246846422102608973597 5457092567408288478365099)
        ·
          refine ⟨8185638851112432717547649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5457092567408288478365099 8185638851112432717547649)
          ·
            refine ⟨6139229138334324538160737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8185638851112432717547649 6139229138334324538160737)
            ·
              refine ⟨4604421853750743403620553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6139229138334324538160737 4604421853750743403620553)
              ·
                refine ⟨3453316390313057552715415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4604421853750743403620553 3453316390313057552715415)
                ·
                  refine ⟨5179974585469586329073123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453316390313057552715415 5179974585469586329073123)
                  ·
                    refine ⟨7769961878204379493609685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5179974585469586329073123 7769961878204379493609685)
                    ·
                      refine ⟨182108481520415144381477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7769961878204379493609685 182108481520415144381477)
                      ·
                        rfl

theorem cell23_354655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_354655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354655 prefixEnd_354655 := by exact prefixLift 354655
  have htrace : WordTrace (prefixWord ++ tailWord_354655) baseStart_354655 baseEnd_354655 := by
    simpa [prefixWord, tailWord_354655, baseEnd_354655] using wordTrace_append hprefix tailTrace_354655
  have hstable : (prefixWord ++ tailWord_354655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354655).length < 2 ^ (prefixWord ++ tailWord_354655).sum := by decide
  have hdescent : baseEnd_354655 < baseStart_354655 := by decide
  rcases family_descends (prefixWord ++ tailWord_354655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354666 : List Nat := [3, 1, 3, 3, 1, 2, 2, 3, 5]
def baseStart_354666 : Nat := 118140960795 + 354666 * 2 ^ 59
def prefixEnd_354666 : Nat := 4983230072969 + 3 ^ 40 * 354666 * 2
def baseEnd_354666 : Nat := 20234903311957177927103

theorem tailTrace_354666 : CollatzResearch.WordTrace tailWord_354666 prefixEnd_354666 20234903311957177927103 := by
  unfold tailWord_354666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3233932933278282243878963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8623821155408752650343901 3233932933278282243878963)
  ·
    refine ⟨4850899399917423365818445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3233932933278282243878963 4850899399917423365818445)
    ·
      refine ⟨1819087274969033762181917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4850899399917423365818445 1819087274969033762181917)
      ·
        refine ⟨682157728113387660818219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1819087274969033762181917 682157728113387660818219)
        ·
          refine ⟨1023236592170081491227329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682157728113387660818219 1023236592170081491227329)
          ·
            refine ⟨767427444127561118420497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1023236592170081491227329 767427444127561118420497)
            ·
              refine ⟨575570583095670838815373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767427444127561118420497 575570583095670838815373)
              ·
                refine ⟨215838968660876564555765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 575570583095670838815373 215838968660876564555765)
                ·
                  refine ⟨20234903311957177927103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 215838968660876564555765 20234903311957177927103)
                  ·
                    rfl

theorem cell23_354666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_354666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354666 prefixEnd_354666 := by exact prefixLift 354666
  have htrace : WordTrace (prefixWord ++ tailWord_354666) baseStart_354666 baseEnd_354666 := by
    simpa [prefixWord, tailWord_354666, baseEnd_354666] using wordTrace_append hprefix tailTrace_354666
  have hstable : (prefixWord ++ tailWord_354666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354666).length < 2 ^ (prefixWord ++ tailWord_354666).sum := by decide
  have hdescent : baseEnd_354666 < baseStart_354666 := by decide
  rcases family_descends (prefixWord ++ tailWord_354666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354699 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 2, 4, 2]
def baseStart_354699 : Nat := 118140960795 + 354699 * 2 ^ 59
def prefixEnd_354699 : Nat := 4983230072969 + 3 ^ 40 * 354699 * 2
def baseEnd_354699 : Nat := 182131074669212972231275

theorem tailTrace_354699 : CollatzResearch.WordTrace tailWord_354699 prefixEnd_354699 182131074669212972231275 := by
  unfold tailWord_354699
  simp only [CollatzResearch.WordTrace]
  refine ⟨12936935341993575611467151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8624623561329050407644767 12936935341993575611467151)
  ·
    refine ⟨19405403012990363417200727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12936935341993575611467151 19405403012990363417200727)
    ·
      refine ⟨29108104519485545125801091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19405403012990363417200727 29108104519485545125801091)
      ·
        refine ⟨43662156779228317688701637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29108104519485545125801091 43662156779228317688701637)
        ·
          refine ⟨8186654396105309566631557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43662156779228317688701637 8186654396105309566631557)
          ·
            refine ⟨1534997699269745543743417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8186654396105309566631557 1534997699269745543743417)
            ·
              refine ⟨1151248274452309157807563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1534997699269745543743417 1151248274452309157807563)
              ·
                refine ⟨1726872411678463736711345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151248274452309157807563 1726872411678463736711345)
                ·
                  refine ⟨1295154308758847802533509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1726872411678463736711345 1295154308758847802533509)
                  ·
                    refine ⟨242841432892283962975033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1295154308758847802533509 242841432892283962975033)
                    ·
                      refine ⟨182131074669212972231275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 242841432892283962975033 182131074669212972231275)
                      ·
                        rfl

theorem cell23_354699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 4, 2].length) (baseStart_354699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354699 prefixEnd_354699 := by exact prefixLift 354699
  have htrace : WordTrace (prefixWord ++ tailWord_354699) baseStart_354699 baseEnd_354699 := by
    simpa [prefixWord, tailWord_354699, baseEnd_354699] using wordTrace_append hprefix tailTrace_354699
  have hstable : (prefixWord ++ tailWord_354699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354699).length < 2 ^ (prefixWord ++ tailWord_354699).sum := by decide
  have hdescent : baseEnd_354699 < baseStart_354699 := by decide
  rcases family_descends (prefixWord ++ tailWord_354699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354705 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 12]
def baseStart_354705 : Nat := 118140960795 + 354705 * 2 ^ 59
def prefixEnd_354705 : Nat := 4983230072969 + 3 ^ 40 * 354705 * 2
def baseEnd_354705 : Nat := 20237128394793327639583

theorem tailTrace_354705 : CollatzResearch.WordTrace tailWord_354705 prefixEnd_354705 20237128394793327639583 := by
  unfold tailWord_354705
  simp only [CollatzResearch.WordTrace]
  refine ⟨12937154179971838636185569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8624769453314559090790379 12937154179971838636185569)
  ·
    refine ⟨9702865634978878977139177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12937154179971838636185569 9702865634978878977139177)
    ·
      refine ⟨7277149226234159232854383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9702865634978878977139177 7277149226234159232854383)
      ·
        refine ⟨10915723839351238849281575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7277149226234159232854383 10915723839351238849281575)
        ·
          refine ⟨16373585759026858273922363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10915723839351238849281575 16373585759026858273922363)
          ·
            refine ⟨24560378638540287410883545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16373585759026858273922363 24560378638540287410883545)
            ·
              refine ⟨18420283978905215558162659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24560378638540287410883545 18420283978905215558162659)
              ·
                refine ⟨27630425968357823337243989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18420283978905215558162659 27630425968357823337243989)
                ·
                  refine ⟨20237128394793327639583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 27630425968357823337243989 20237128394793327639583)
                  ·
                    rfl

theorem cell23_354705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 12].length) (baseStart_354705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354705 prefixEnd_354705 := by exact prefixLift 354705
  have htrace : WordTrace (prefixWord ++ tailWord_354705) baseStart_354705 baseEnd_354705 := by
    simpa [prefixWord, tailWord_354705, baseEnd_354705] using wordTrace_append hprefix tailTrace_354705
  have hstable : (prefixWord ++ tailWord_354705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354705).length < 2 ^ (prefixWord ++ tailWord_354705).sum := by decide
  have hdescent : baseEnd_354705 < baseStart_354705 := by decide
  rcases family_descends (prefixWord ++ tailWord_354705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354719 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 3]
def baseStart_354719 : Nat := 118140960795 + 354719 * 2 ^ 59
def prefixEnd_354719 : Nat := 4983230072969 + 3 ^ 40 * 354719 * 2
def baseEnd_354719 : Nat := 182141344282302893981183

theorem tailTrace_354719 : CollatzResearch.WordTrace tailWord_354719 prefixEnd_354719 182141344282302893981183 := by
  unfold tailWord_354719
  simp only [CollatzResearch.WordTrace]
  refine ⟨12937664801921119027195211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8625109867947412684796807 12937664801921119027195211)
  ·
    refine ⟨19406497202881678540792817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12937664801921119027195211 19406497202881678540792817)
    ·
      refine ⟨14554872902161258905594613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19406497202881678540792817 14554872902161258905594613)
      ·
        refine ⟨1364519334577618022399495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14554872902161258905594613 1364519334577618022399495)
        ·
          refine ⟨2046779001866427033599243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364519334577618022399495 2046779001866427033599243)
          ·
            refine ⟨3070168502799640550398865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2046779001866427033599243 3070168502799640550398865)
            ·
              refine ⟨2302626377099730412799149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3070168502799640550398865 2302626377099730412799149)
              ·
                refine ⟨863484891412398904799681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2302626377099730412799149 863484891412398904799681)
                ·
                  refine ⟨647613668559299178599761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 863484891412398904799681 647613668559299178599761)
                  ·
                    refine ⟨485710251419474383949821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 647613668559299178599761 485710251419474383949821)
                    ·
                      refine ⟨182141344282302893981183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 485710251419474383949821 182141344282302893981183)
                      ·
                        rfl

theorem cell23_354719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_354719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354719 prefixEnd_354719 := by exact prefixLift 354719
  have htrace : WordTrace (prefixWord ++ tailWord_354719) baseStart_354719 baseEnd_354719 := by
    simpa [prefixWord, tailWord_354719, baseEnd_354719] using wordTrace_append hprefix tailTrace_354719
  have hstable : (prefixWord ++ tailWord_354719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354719).length < 2 ^ (prefixWord ++ tailWord_354719).sum := by decide
  have hdescent : baseEnd_354719 < baseStart_354719 := by decide
  rcases family_descends (prefixWord ++ tailWord_354719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354722 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 10]
def baseStart_354722 : Nat := 118140960795 + 354722 * 2 ^ 59
def prefixEnd_354722 : Nat := 4983230072969 + 3 ^ 40 * 354722 * 2
def baseEnd_354722 : Nat := 20238098302696264693741

theorem tailTrace_354722 : CollatzResearch.WordTrace tailWord_354722 prefixEnd_354722 20238098302696264693741 := by
  unfold tailWord_354722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234443555227562634888605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8625182813940167026369613 3234443555227562634888605)
  ·
    refine ⟨1212916333210335988083227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3234443555227562634888605 1212916333210335988083227)
    ·
      refine ⟨1819374499815503982124841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1212916333210335988083227 1819374499815503982124841)
      ·
        refine ⟨1364530874861627986593631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1819374499815503982124841 1364530874861627986593631)
        ·
          refine ⟨2046796312292441979890447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364530874861627986593631 2046796312292441979890447)
          ·
            refine ⟨3070194468438662969835671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2046796312292441979890447 3070194468438662969835671)
            ·
              refine ⟨4605291702657994454753507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070194468438662969835671 4605291702657994454753507)
              ·
                refine ⟨6907937553986991682130261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605291702657994454753507 6907937553986991682130261)
                ·
                  refine ⟨20238098302696264693741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 6907937553986991682130261 20238098302696264693741)
                  ·
                    rfl

theorem cell23_354722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_354722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354722 prefixEnd_354722 := by exact prefixLift 354722
  have htrace : WordTrace (prefixWord ++ tailWord_354722) baseStart_354722 baseEnd_354722 := by
    simpa [prefixWord, tailWord_354722, baseEnd_354722] using wordTrace_append hprefix tailTrace_354722
  have hstable : (prefixWord ++ tailWord_354722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354722).length < 2 ^ (prefixWord ++ tailWord_354722).sum := by decide
  have hdescent : baseEnd_354722 < baseStart_354722 := by decide
  rcases family_descends (prefixWord ++ tailWord_354722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354743 : List Nat := [1, 1, 3, 1, 3, 4, 3, 2, 1, 4]
def baseStart_354743 : Nat := 118140960795 + 354743 * 2 ^ 59
def prefixEnd_354743 : Nat := 4983230072969 + 3 ^ 40 * 354743 * 2
def baseEnd_354743 : Nat := 60717889272670266693691

theorem tailTrace_354743 : CollatzResearch.WordTrace tailWord_354743 prefixEnd_354743 60717889272670266693691 := by
  unfold tailWord_354743
  simp only [CollatzResearch.WordTrace]
  refine ⟨12938540153834171126068883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8625693435889447417379255 12938540153834171126068883)
  ·
    refine ⟨19407810230751256689103325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12938540153834171126068883 19407810230751256689103325)
    ·
      refine ⟨7277928836531721258413747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19407810230751256689103325 7277928836531721258413747)
      ·
        refine ⟨10916893254797581887620621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7277928836531721258413747 10916893254797581887620621)
        ·
          refine ⟨4093834970549093207857733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10916893254797581887620621 4093834970549093207857733)
          ·
            refine ⟨767594056977954976473325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4093834970549093207857733 767594056977954976473325)
            ·
              refine ⟨287847771366733116177497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 767594056977954976473325 287847771366733116177497)
              ·
                refine ⟨215885828525049837133123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287847771366733116177497 215885828525049837133123)
                ·
                  refine ⟨323828742787574755699685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215885828525049837133123 323828742787574755699685)
                  ·
                    refine ⟨60717889272670266693691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 323828742787574755699685 60717889272670266693691)
                    ·
                      rfl

theorem cell23_354743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_354743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354743 prefixEnd_354743 := by exact prefixLift 354743
  have htrace : WordTrace (prefixWord ++ tailWord_354743) baseStart_354743 baseEnd_354743 := by
    simpa [prefixWord, tailWord_354743, baseEnd_354743] using wordTrace_append hprefix tailTrace_354743
  have hstable : (prefixWord ++ tailWord_354743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354743).length < 2 ^ (prefixWord ++ tailWord_354743).sum := by decide
  have hdescent : baseEnd_354743 < baseStart_354743 := by decide
  rcases family_descends (prefixWord ++ tailWord_354743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354752 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 3, 5]
def baseStart_354752 : Nat := 118140960795 + 354752 * 2 ^ 59
def prefixEnd_354752 : Nat := 4983230072969 + 3 ^ 40 * 354752 * 2
def baseEnd_354752 : Nat := 60719429714633754956177

theorem tailTrace_354752 : CollatzResearch.WordTrace tailWord_354752 prefixEnd_354752 60719429714633754956177 := by
  unfold tailWord_354752
  simp only [CollatzResearch.WordTrace]
  refine ⟨6469434205400782831573255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8625912273867710442097673 6469434205400782831573255)
  ·
    refine ⟨9704151308101174247359883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6469434205400782831573255 9704151308101174247359883)
    ·
      refine ⟨14556226962151761371039825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9704151308101174247359883 14556226962151761371039825)
      ·
        refine ⟨10917170221613821028279869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14556226962151761371039825 10917170221613821028279869)
        ·
          refine ⟨4093938833105182885604951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10917170221613821028279869 4093938833105182885604951)
          ·
            refine ⟨6140908249657774328407427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4093938833105182885604951 6140908249657774328407427)
            ·
              refine ⟨9211362374486661492611141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6140908249657774328407427 9211362374486661492611141)
              ·
                refine ⟨1727130445216249029864589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9211362374486661492611141 1727130445216249029864589)
                ·
                  refine ⟨647673916956093386199221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1727130445216249029864589 647673916956093386199221)
                  ·
                    refine ⟨60719429714633754956177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 647673916956093386199221 60719429714633754956177)
                    ·
                      rfl

theorem cell23_354752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_354752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354752 prefixEnd_354752 := by exact prefixLift 354752
  have htrace : WordTrace (prefixWord ++ tailWord_354752) baseStart_354752 baseEnd_354752 := by
    simpa [prefixWord, tailWord_354752, baseEnd_354752] using wordTrace_append hprefix tailTrace_354752
  have hstable : (prefixWord ++ tailWord_354752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354752).length < 2 ^ (prefixWord ++ tailWord_354752).sum := by decide
  have hdescent : baseEnd_354752 < baseStart_354752 := by decide
  rcases family_descends (prefixWord ++ tailWord_354752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354756 : List Nat := [2, 3, 3, 2, 2, 1, 1, 3, 6]
def baseStart_354756 : Nat := 118140960795 + 354756 * 2 ^ 59
def prefixEnd_354756 : Nat := 4983230072969 + 3 ^ 40 * 354756 * 2
def baseEnd_354756 : Nat := 20240038118502138802057

theorem tailTrace_354756 : CollatzResearch.WordTrace tailWord_354756 prefixEnd_354756 20240038118502138802057 := by
  unfold tailWord_354756
  simp only [CollatzResearch.WordTrace]
  refine ⟨6469507151393537173146061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8626009535191382897528081 6469507151393537173146061)
  ·
    refine ⟨2426065181772576439929773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6469507151393537173146061 2426065181772576439929773)
    ·
      refine ⟨909774443164716164973665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2426065181772576439929773 909774443164716164973665)
      ·
        refine ⟨682330832373537123730249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 909774443164716164973665 682330832373537123730249)
        ·
          refine ⟨511748124280152842797687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 682330832373537123730249 511748124280152842797687)
          ·
            refine ⟨767622186420229264196531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511748124280152842797687 767622186420229264196531)
            ·
              refine ⟨1151433279630343896294797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767622186420229264196531 1151433279630343896294797)
              ·
                refine ⟨431787479861378961110549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1151433279630343896294797 431787479861378961110549)
                ·
                  refine ⟨20240038118502138802057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 431787479861378961110549 20240038118502138802057)
                  ·
                    rfl

theorem cell23_354756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_354756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354756 prefixEnd_354756 := by exact prefixLift 354756
  have htrace : WordTrace (prefixWord ++ tailWord_354756) baseStart_354756 baseEnd_354756 := by
    simpa [prefixWord, tailWord_354756, baseEnd_354756] using wordTrace_append hprefix tailTrace_354756
  have hstable : (prefixWord ++ tailWord_354756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354756).length < 2 ^ (prefixWord ++ tailWord_354756).sum := by decide
  have hdescent : baseEnd_354756 < baseStart_354756 := by decide
  rcases family_descends (prefixWord ++ tailWord_354756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354809 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 3, 2, 3]
def baseStart_354809 : Nat := 118140960795 + 354809 * 2 ^ 59
def prefixEnd_354809 : Nat := 4983230072969 + 3 ^ 40 * 354809 * 2
def baseEnd_354809 : Nat := 182187557541207541855769

theorem tailTrace_354809 : CollatzResearch.WordTrace tailWord_354809 prefixEnd_354809 182187557541207541855769 := by
  unfold tailWord_354809
  simp only [CollatzResearch.WordTrace]
  refine ⟨12940947371595064397971481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8627298247730042931980987 12940947371595064397971481)
  ·
    refine ⟨9705710528696298298478611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12940947371595064397971481 9705710528696298298478611)
    ·
      refine ⟨14558565793044447447717917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9705710528696298298478611 14558565793044447447717917)
      ·
        refine ⟨5459462172391667792894219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14558565793044447447717917 5459462172391667792894219)
        ·
          refine ⟨8189193258587501689341329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5459462172391667792894219 8189193258587501689341329)
          ·
            refine ⟨6141894943940626267005997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8189193258587501689341329 6141894943940626267005997)
            ·
              refine ⟨2303210603977734850127249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6141894943940626267005997 2303210603977734850127249)
              ·
                refine ⟨1727407952983301137595437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2303210603977734850127249 1727407952983301137595437)
                ·
                  refine ⟨647777982368737926598289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1727407952983301137595437 647777982368737926598289)
                  ·
                    refine ⟨485833486776553444948717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 647777982368737926598289 485833486776553444948717)
                    ·
                      refine ⟨182187557541207541855769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 485833486776553444948717 182187557541207541855769)
                      ·
                        rfl

theorem cell23_354809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_354809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354809 prefixEnd_354809 := by exact prefixLift 354809
  have htrace : WordTrace (prefixWord ++ tailWord_354809) baseStart_354809 baseEnd_354809 := by
    simpa [prefixWord, tailWord_354809, baseEnd_354809] using wordTrace_append hprefix tailTrace_354809
  have hstable : (prefixWord ++ tailWord_354809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354809).length < 2 ^ (prefixWord ++ tailWord_354809).sum := by decide
  have hdescent : baseEnd_354809 < baseStart_354809 := by decide
  rcases family_descends (prefixWord ++ tailWord_354809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354819 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 4]
def baseStart_354819 : Nat := 118140960795 + 354819 * 2 ^ 59
def prefixEnd_354819 : Nat := 4983230072969 + 3 ^ 40 * 354819 * 2
def baseEnd_354819 : Nat := 182192692347752502730723

theorem tailTrace_354819 : CollatzResearch.WordTrace tailWord_354819 prefixEnd_354819 182192692347752502730723 := by
  unfold tailWord_354819
  simp only [CollatzResearch.WordTrace]
  refine ⟨12941312101558836105835511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8627541401039224070557007 12941312101558836105835511)
  ·
    refine ⟨19411968152338254158753267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12941312101558836105835511 19411968152338254158753267)
    ·
      refine ⟨29117952228507381238129901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19411968152338254158753267 29117952228507381238129901)
      ·
        refine ⟨10919232085690267964298713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29117952228507381238129901 10919232085690267964298713)
        ·
          refine ⟨8189424064267700973224035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10919232085690267964298713 8189424064267700973224035)
          ·
            refine ⟨12284136096401551459836053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8189424064267700973224035 12284136096401551459836053)
            ·
              refine ⟨575818879518822724679815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12284136096401551459836053 575818879518822724679815)
              ·
                refine ⟨863728319278234087019723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575818879518822724679815 863728319278234087019723)
                ·
                  refine ⟨1295592478917351130529585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863728319278234087019723 1295592478917351130529585)
                  ·
                    refine ⟨971694359188013347897189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1295592478917351130529585 971694359188013347897189)
                    ·
                      refine ⟨182192692347752502730723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 971694359188013347897189 182192692347752502730723)
                      ·
                        rfl

theorem cell23_354819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_354819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354819 prefixEnd_354819 := by exact prefixLift 354819
  have htrace : WordTrace (prefixWord ++ tailWord_354819) baseStart_354819 baseEnd_354819 := by
    simpa [prefixWord, tailWord_354819, baseEnd_354819] using wordTrace_append hprefix tailTrace_354819
  have hstable : (prefixWord ++ tailWord_354819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354819).length < 2 ^ (prefixWord ++ tailWord_354819).sum := by decide
  have hdescent : baseEnd_354819 < baseStart_354819 := by decide
  rcases family_descends (prefixWord ++ tailWord_354819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354826 : List Nat := [3, 1, 2, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_354826 : Nat := 118140960795 + 354826 * 2 ^ 59
def prefixEnd_354826 : Nat := 4983230072969 + 3 ^ 40 * 354826 * 2
def baseEnd_354826 : Nat := 182196286712333975343191

theorem tailTrace_354826 : CollatzResearch.WordTrace tailWord_354826 prefixEnd_354826 182196286712333975343191 := by
  unfold tailWord_354826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3235391853133369075335083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8627711608355650867560221 3235391853133369075335083)
  ·
    refine ⟨4853087779700053613002625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3235391853133369075335083 4853087779700053613002625)
    ·
      refine ⟨3639815834775040209751969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4853087779700053613002625 3639815834775040209751969)
      ·
        refine ⟨2729861876081280157313977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3639815834775040209751969 2729861876081280157313977)
        ·
          refine ⟨2047396407060960117985483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2729861876081280157313977 2047396407060960117985483)
          ·
            refine ⟨3071094610591440176978225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047396407060960117985483 3071094610591440176978225)
            ·
              refine ⟨2303320957943580132733669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3071094610591440176978225 2303320957943580132733669)
              ·
                refine ⟨431872679614421274887563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2303320957943580132733669 431872679614421274887563)
                ·
                  refine ⟨647809019421631912331345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431872679614421274887563 647809019421631912331345)
                  ·
                    refine ⟨485856764566223934248509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 647809019421631912331345 485856764566223934248509)
                    ·
                      refine ⟨182196286712333975343191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 485856764566223934248509 182196286712333975343191)
                      ·
                        rfl

theorem cell23_354826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_354826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354826 prefixEnd_354826 := by exact prefixLift 354826
  have htrace : WordTrace (prefixWord ++ tailWord_354826) baseStart_354826 baseEnd_354826 := by
    simpa [prefixWord, tailWord_354826, baseEnd_354826] using wordTrace_append hprefix tailTrace_354826
  have hstable : (prefixWord ++ tailWord_354826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354826).length < 2 ^ (prefixWord ++ tailWord_354826).sum := by decide
  have hdescent : baseEnd_354826 < baseStart_354826 := by decide
  rcases family_descends (prefixWord ++ tailWord_354826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354840 : List Nat := [2, 1, 2, 3, 3, 1, 1, 5, 1, 2, 2]
def baseStart_354840 : Nat := 118140960795 + 354840 * 2 ^ 59
def prefixEnd_354840 : Nat := 4983230072969 + 3 ^ 40 * 354840 * 2
def baseEnd_354840 : Nat := 182203475441496920568127

theorem tailTrace_354840 : CollatzResearch.WordTrace tailWord_354840 prefixEnd_354840 182203475441496920568127 := by
  unfold tailWord_354840
  simp only [CollatzResearch.WordTrace]
  refine ⟨6471039017241378346174987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8628052022988504461566649 6471039017241378346174987)
  ·
    refine ⟨9706558525862067519262481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6471039017241378346174987 9706558525862067519262481)
    ·
      refine ⟨7279918894396550639446861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9706558525862067519262481 7279918894396550639446861)
      ·
        refine ⟨2729969585398706489792573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7279918894396550639446861 2729969585398706489792573)
        ·
          refine ⟨1023738594524514933672215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2729969585398706489792573 1023738594524514933672215)
          ·
            refine ⟨1535607891786772400508323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023738594524514933672215 1535607891786772400508323)
            ·
              refine ⟨2303411837680158600762485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535607891786772400508323 2303411837680158600762485)
              ·
                refine ⟨215944859782514868821483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2303411837680158600762485 215944859782514868821483)
                ·
                  refine ⟨323917289673772303232225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215944859782514868821483 323917289673772303232225)
                  ·
                    refine ⟨242937967255329227424169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 323917289673772303232225 242937967255329227424169)
                    ·
                      refine ⟨182203475441496920568127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 242937967255329227424169 182203475441496920568127)
                      ·
                        rfl

theorem cell23_354840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_354840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354840 prefixEnd_354840 := by exact prefixLift 354840
  have htrace : WordTrace (prefixWord ++ tailWord_354840) baseStart_354840 baseEnd_354840 := by
    simpa [prefixWord, tailWord_354840, baseEnd_354840] using wordTrace_append hprefix tailTrace_354840
  have hstable : (prefixWord ++ tailWord_354840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354840).length < 2 ^ (prefixWord ++ tailWord_354840).sum := by decide
  have hdescent : baseEnd_354840 < baseStart_354840 := by decide
  rcases family_descends (prefixWord ++ tailWord_354840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354866 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2]
def baseStart_354866 : Nat := 118140960795 + 354866 * 2 ^ 59
def prefixEnd_354866 : Nat := 4983230072969 + 3 ^ 40 * 354866 * 2
def baseEnd_354866 : Nat := 182216825938513818843007

theorem tailTrace_354866 : CollatzResearch.WordTrace tailWord_354866 prefixEnd_354866 182216825938513818843007 := by
  unfold tailWord_354866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3235756583097140783199113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8628684221592375421864301 3235756583097140783199113)
  ·
    refine ⟨2426817437322855587399335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3235756583097140783199113 2426817437322855587399335)
    ·
      refine ⟨3640226155984283381099003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2426817437322855587399335 3640226155984283381099003)
      ·
        refine ⟨5460339233976425071648505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3640226155984283381099003 5460339233976425071648505)
        ·
          refine ⟨4095254425482318803736379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5460339233976425071648505 4095254425482318803736379)
          ·
            refine ⟨6142881638223478205604569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4095254425482318803736379 6142881638223478205604569)
            ·
              refine ⟨4607161228667608654203427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6142881638223478205604569 4607161228667608654203427)
              ·
                refine ⟨6910741843001412981305141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4607161228667608654203427 6910741843001412981305141)
                ·
                  refine ⟨647882047781382466997357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6910741843001412981305141 647882047781382466997357)
                  ·
                    refine ⟨242955767918018425124009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 647882047781382466997357 242955767918018425124009)
                    ·
                      refine ⟨182216825938513818843007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 242955767918018425124009 182216825938513818843007)
                      ·
                        rfl

theorem cell23_354866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_354866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354866 prefixEnd_354866 := by exact prefixLift 354866
  have htrace : WordTrace (prefixWord ++ tailWord_354866) baseStart_354866 baseEnd_354866 := by
    simpa [prefixWord, tailWord_354866, baseEnd_354866] using wordTrace_append hprefix tailTrace_354866
  have hstable : (prefixWord ++ tailWord_354866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354866).length < 2 ^ (prefixWord ++ tailWord_354866).sum := by decide
  have hdescent : baseEnd_354866 < baseStart_354866 := by decide
  rcases family_descends (prefixWord ++ tailWord_354866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
