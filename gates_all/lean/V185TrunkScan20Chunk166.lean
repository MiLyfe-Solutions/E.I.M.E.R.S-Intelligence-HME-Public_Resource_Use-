import V185TrunkScan20Chunk165

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_1010848 : List Nat := [2, 1, 1, 4, 2, 1, 3, 6]
def baseStart_1010848 : Nat := 118140960795 + 1010848 * 2 ^ 59
def prefixEnd_1010848 : Nat := 4983230072969 + 3 ^ 40 * 1010848 * 2
def baseEnd_1010848 : Nat := 153792857077382603333689

theorem tailTrace_1010848 : CollatzResearch.WordTrace tailWord_1010848 prefixEnd_1010848 153792857077382603333689 := by
  unfold tailWord_1010848
  simp only [CollatzResearch.WordTrace]
  refine ⟨18434327720938904969504599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24579103627918539959339465 18434327720938904969504599)
  ·
    refine ⟨27651491581408357454256899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18434327720938904969504599 27651491581408357454256899)
    ·
      refine ⟨41477237372112536181385349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27651491581408357454256899 41477237372112536181385349)
      ·
        refine ⟨7776982007271100534009753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41477237372112536181385349 7776982007271100534009753)
        ·
          refine ⟨5832736505453325400507315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7776982007271100534009753 5832736505453325400507315)
          ·
            refine ⟨8749104758179988100760973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5832736505453325400507315 8749104758179988100760973)
            ·
              refine ⟨3280914284317495537785365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8749104758179988100760973 3280914284317495537785365)
              ·
                refine ⟨153792857077382603333689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3280914284317495537785365 153792857077382603333689)
                ·
                  rfl

theorem cell20_1010848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_1010848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010848 prefixEnd_1010848 := by exact prefixLift 1010848
  have htrace : WordTrace (prefixWord ++ tailWord_1010848) baseStart_1010848 baseEnd_1010848 := by
    simpa [prefixWord, tailWord_1010848, baseEnd_1010848] using wordTrace_append hprefix tailTrace_1010848
  have hstable : (prefixWord ++ tailWord_1010848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010848).length < 2 ^ (prefixWord ++ tailWord_1010848).sum := by decide
  have hdescent : baseEnd_1010848 < baseStart_1010848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010865 : List Nat := [1, 2, 2, 5, 1, 3, 6]
def baseStart_1010865 : Nat := 118140960795 + 1010865 * 2 ^ 59
def prefixEnd_1010865 : Nat := 4983230072969 + 3 ^ 40 * 1010865 * 2
def baseEnd_1010865 : Nat := 51265147832819034048259

theorem tailTrace_1010865 : CollatzResearch.WordTrace tailWord_1010865 prefixEnd_1010865 51265147832819034048259 := by
  unfold tailWord_1010865
  simp only [CollatzResearch.WordTrace]
  refine ⟨36869275482816221842378049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24579516988544147894918699 36869275482816221842378049)
  ·
    refine ⟨27651956612112166381783537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36869275482816221842378049 27651956612112166381783537)
    ·
      refine ⟨20738967459084124786337653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27651956612112166381783537 20738967459084124786337653)
      ·
        refine ⟨1944278199289136698719155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20738967459084124786337653 1944278199289136698719155)
        ·
          refine ⟨2916417298933705048078733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944278199289136698719155 2916417298933705048078733)
          ·
            refine ⟨1093656487100139393029525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2916417298933705048078733 1093656487100139393029525)
            ·
              refine ⟨51265147832819034048259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1093656487100139393029525 51265147832819034048259)
              ·
                rfl

theorem cell20_1010865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 6].length) (baseStart_1010865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010865 prefixEnd_1010865 := by exact prefixLift 1010865
  have htrace : WordTrace (prefixWord ++ tailWord_1010865) baseStart_1010865 baseEnd_1010865 := by
    simpa [prefixWord, tailWord_1010865, baseEnd_1010865] using wordTrace_append hprefix tailTrace_1010865
  have hstable : (prefixWord ++ tailWord_1010865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010865).length < 2 ^ (prefixWord ++ tailWord_1010865).sum := by decide
  have hdescent : baseEnd_1010865 < baseStart_1010865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010879 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 4]
def baseStart_1010879 : Nat := 118140960795 + 1010879 * 2 ^ 59
def prefixEnd_1010879 : Nat := 4983230072969 + 3 ^ 40 * 1010879 * 2
def baseEnd_1010879 : Nat := 461392720476849479967607

theorem tailTrace_1010879 : CollatzResearch.WordTrace tailWord_1010879 prefixEnd_1010879 461392720476849479967607 := by
  unfold tailWord_1010879
  simp only [CollatzResearch.WordTrace]
  refine ⟨36869786104765502233387691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24579857403177001488925127 36869786104765502233387691)
  ·
    refine ⟨55304679157148253350081537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36869786104765502233387691 55304679157148253350081537)
    ·
      refine ⟨41478509367861190012561153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55304679157148253350081537 41478509367861190012561153)
      ·
        refine ⟨31108882025895892509420865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41478509367861190012561153 31108882025895892509420865)
        ·
          refine ⟨23331661519421919382065649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31108882025895892509420865 23331661519421919382065649)
          ·
            refine ⟨17498746139566439536549237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23331661519421919382065649 17498746139566439536549237)
            ·
              refine ⟨1640507450584353706551491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17498746139566439536549237 1640507450584353706551491)
              ·
                refine ⟨2460761175876530559827237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640507450584353706551491 2460761175876530559827237)
                ·
                  refine ⟨461392720476849479967607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2460761175876530559827237 461392720476849479967607)
                  ·
                    rfl

theorem cell20_1010879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_1010879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010879 prefixEnd_1010879 := by exact prefixLift 1010879
  have htrace : WordTrace (prefixWord ++ tailWord_1010879) baseStart_1010879 baseEnd_1010879 := by
    simpa [prefixWord, tailWord_1010879, baseEnd_1010879] using wordTrace_append hprefix tailTrace_1010879
  have hstable : (prefixWord ++ tailWord_1010879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010879).length < 2 ^ (prefixWord ++ tailWord_1010879).sum := by decide
  have hdescent : baseEnd_1010879 < baseStart_1010879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010927 : List Nat := [1, 1, 2, 1, 7, 1, 2, 2, 3]
def baseStart_1010927 : Nat := 118140960795 + 1010927 * 2 ^ 59
def prefixEnd_1010927 : Nat := 4983230072969 + 3 ^ 40 * 1010927 * 2
def baseEnd_1010927 : Nat := 461414628984774646367411

theorem tailTrace_1010927 : CollatzResearch.WordTrace tailWord_1010927 prefixEnd_1010927 461414628984774646367411 := by
  unfold tailWord_1010927
  simp only [CollatzResearch.WordTrace]
  refine ⟨36871536808591606431135035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24581024539061070954090023 36871536808591606431135035)
  ·
    refine ⟨55307305212887409646702553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36871536808591606431135035 55307305212887409646702553)
    ·
      refine ⟨41480478909665557235026915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55307305212887409646702553 41480478909665557235026915)
      ·
        refine ⟨62220718364498335852540373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41480478909665557235026915 62220718364498335852540373)
        ·
          refine ⟨1458298086667929746543915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 62220718364498335852540373 1458298086667929746543915)
          ·
            refine ⟨2187447130001894619815873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458298086667929746543915 2187447130001894619815873)
            ·
              refine ⟨1640585347501420964861905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187447130001894619815873 1640585347501420964861905)
              ·
                refine ⟨1230439010626065723646429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1640585347501420964861905 1230439010626065723646429)
                ·
                  refine ⟨461414628984774646367411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1230439010626065723646429 461414628984774646367411)
                  ·
                    rfl

theorem cell20_1010927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 3].length) (baseStart_1010927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010927 prefixEnd_1010927 := by exact prefixLift 1010927
  have htrace : WordTrace (prefixWord ++ tailWord_1010927) baseStart_1010927 baseEnd_1010927 := by
    simpa [prefixWord, tailWord_1010927, baseEnd_1010927] using wordTrace_append hprefix tailTrace_1010927
  have hstable : (prefixWord ++ tailWord_1010927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010927).length < 2 ^ (prefixWord ++ tailWord_1010927).sum := by decide
  have hdescent : baseEnd_1010927 < baseStart_1010927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010955 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 4]
def baseStart_1010955 : Nat := 118140960795 + 1010955 * 2 ^ 59
def prefixEnd_1010955 : Nat := 4983230072969 + 3 ^ 40 * 1010955 * 2
def baseEnd_1010955 : Nat := 461427408947730993433963

theorem tailTrace_1010955 : CollatzResearch.WordTrace tailWord_1010955 prefixEnd_1010955 461427408947730993433963 := by
  unfold tailWord_1010955
  simp only [CollatzResearch.WordTrace]
  refine ⟨36872558052490167213154319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24581705368326778142102879 36872558052490167213154319)
  ·
    refine ⟨55308837078735250819731479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36872558052490167213154319 55308837078735250819731479)
    ·
      refine ⟨82963255618102876229597219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55308837078735250819731479 82963255618102876229597219)
      ·
        refine ⟨124444883427154314344395829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82963255618102876229597219 124444883427154314344395829)
        ·
          refine ⟨11666707821295716969787109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124444883427154314344395829 11666707821295716969787109)
          ·
            refine ⟨2187507716492946931835083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11666707821295716969787109 2187507716492946931835083)
            ·
              refine ⟨3281261574739420397752625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2187507716492946931835083 3281261574739420397752625)
              ·
                refine ⟨2460946181054565298314469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3281261574739420397752625 2460946181054565298314469)
                ·
                  refine ⟨461427408947730993433963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2460946181054565298314469 461427408947730993433963)
                  ·
                    rfl

theorem cell20_1010955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_1010955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010955 prefixEnd_1010955 := by exact prefixLift 1010955
  have htrace : WordTrace (prefixWord ++ tailWord_1010955) baseStart_1010955 baseEnd_1010955 := by
    simpa [prefixWord, tailWord_1010955, baseEnd_1010955] using wordTrace_append hprefix tailTrace_1010955
  have hstable : (prefixWord ++ tailWord_1010955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010955).length < 2 ^ (prefixWord ++ tailWord_1010955).sum := by decide
  have hdescent : baseEnd_1010955 < baseStart_1010955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010972 : List Nat := [2, 2, 3, 1, 1, 1, 3, 5, 2]
def baseStart_1010972 : Nat := 118140960795 + 1010972 * 2 ^ 59
def prefixEnd_1010972 : Nat := 4983230072969 + 3 ^ 40 * 1010972 * 2
def baseEnd_1010972 : Nat := 461435168210954489867227

theorem tailTrace_1010972 : CollatzResearch.WordTrace tailWord_1010972 prefixEnd_1010972 461435168210954489867227 := by
  unfold tailWord_1010972
  simp only [CollatzResearch.WordTrace]
  refine ⟨18436589046714289558261585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24582118728952386077682113 18436589046714289558261585)
  ·
    refine ⟨13827441785035717168696189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18436589046714289558261585 13827441785035717168696189)
    ·
      refine ⟨5185290669388393938261071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13827441785035717168696189 5185290669388393938261071)
      ·
        refine ⟨7777936004082590907391607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5185290669388393938261071 7777936004082590907391607)
        ·
          refine ⟨11666904006123886361087411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7777936004082590907391607 11666904006123886361087411)
          ·
            refine ⟨17500356009185829541631117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11666904006123886361087411 17500356009185829541631117)
            ·
              refine ⟨6562633503444686078111669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17500356009185829541631117 6562633503444686078111669)
              ·
                refine ⟨615246890947939319822969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6562633503444686078111669 615246890947939319822969)
                ·
                  refine ⟨461435168210954489867227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615246890947939319822969 461435168210954489867227)
                  ·
                    rfl

theorem cell20_1010972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_1010972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010972 prefixEnd_1010972 := by exact prefixLift 1010972
  have htrace : WordTrace (prefixWord ++ tailWord_1010972) baseStart_1010972 baseEnd_1010972 := by
    simpa [prefixWord, tailWord_1010972, baseEnd_1010972] using wordTrace_append hprefix tailTrace_1010972
  have hstable : (prefixWord ++ tailWord_1010972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010972).length < 2 ^ (prefixWord ++ tailWord_1010972).sum := by decide
  have hdescent : baseEnd_1010972 < baseStart_1010972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010989 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1010989 : Nat := 118140960795 + 1010989 * 2 ^ 59
def prefixEnd_1010989 : Nat := 4983230072969 + 3 ^ 40 * 1010989 * 2
def baseEnd_1010989 : Nat := 461442927474177986300491

theorem tailTrace_1010989 : CollatzResearch.WordTrace tailWord_1010989 prefixEnd_1010989 461442927474177986300491 := by
  unfold tailWord_1010989
  simp only [CollatzResearch.WordTrace]
  refine ⟨36873798134366991019892021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24582532089577994013261347 36873798134366991019892021)
  ·
    refine ⟨3456918575096905408114877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36873798134366991019892021 3456918575096905408114877)
    ·
      refine ⟨1296344465661339528043079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3456918575096905408114877 1296344465661339528043079)
      ·
        refine ⟨1944516698492009292064619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296344465661339528043079 1944516698492009292064619)
        ·
          refine ⟨2916775047738013938096929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944516698492009292064619 2916775047738013938096929)
          ·
            refine ⟨2187581285803510453572697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2916775047738013938096929 2187581285803510453572697)
            ·
              refine ⟨1640685964352632840179523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187581285803510453572697 1640685964352632840179523)
              ·
                refine ⟨2461028946528949260269285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640685964352632840179523 2461028946528949260269285)
                ·
                  refine ⟨461442927474177986300491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2461028946528949260269285 461442927474177986300491)
                  ·
                    rfl

theorem cell20_1010989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1010989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010989 prefixEnd_1010989 := by exact prefixLift 1010989
  have htrace : WordTrace (prefixWord ++ tailWord_1010989) baseStart_1010989 baseEnd_1010989 := by
    simpa [prefixWord, tailWord_1010989, baseEnd_1010989] using wordTrace_append hprefix tailTrace_1010989
  have hstable : (prefixWord ++ tailWord_1010989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010989).length < 2 ^ (prefixWord ++ tailWord_1010989).sum := by decide
  have hdescent : baseEnd_1010989 < baseStart_1010989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010993 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 4]
def baseStart_1010993 : Nat := 118140960795 + 1010993 * 2 ^ 59
def prefixEnd_1010993 : Nat := 4983230072969 + 3 ^ 40 * 1010993 * 2
def baseEnd_1010993 : Nat := 461444753183171750167141

theorem tailTrace_1010993 : CollatzResearch.WordTrace tailWord_1010993 prefixEnd_1010993 461444753183171750167141 := by
  unfold tailWord_1010993
  simp only [CollatzResearch.WordTrace]
  refine ⟨36873944026352499703037633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24582629350901666468691755 36873944026352499703037633)
  ·
    refine ⟨27655458019764374777278225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36873944026352499703037633 27655458019764374777278225)
    ·
      refine ⟨20741593514823281082958669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27655458019764374777278225 20741593514823281082958669)
      ·
        refine ⟨7778097568058730406109501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20741593514823281082958669 7778097568058730406109501)
        ·
          refine ⟨2916786588022023902291063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7778097568058730406109501 2916786588022023902291063)
          ·
            refine ⟨4375179882033035853436595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916786588022023902291063 4375179882033035853436595)
            ·
              refine ⟨6562769823049553780154893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4375179882033035853436595 6562769823049553780154893)
              ·
                refine ⟨2461038683643582667558085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6562769823049553780154893 2461038683643582667558085)
                ·
                  refine ⟨461444753183171750167141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2461038683643582667558085 461444753183171750167141)
                  ·
                    rfl

theorem cell20_1010993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_1010993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010993 prefixEnd_1010993 := by exact prefixLift 1010993
  have htrace : WordTrace (prefixWord ++ tailWord_1010993) baseStart_1010993 baseEnd_1010993 := by
    simpa [prefixWord, tailWord_1010993, baseEnd_1010993] using wordTrace_append hprefix tailTrace_1010993
  have hstable : (prefixWord ++ tailWord_1010993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010993).length < 2 ^ (prefixWord ++ tailWord_1010993).sum := by decide
  have hdescent : baseEnd_1010993 < baseStart_1010993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011030 : List Nat := [5, 2, 3, 1, 1, 2, 6]
def baseStart_1011030 : Nat := 118140960795 + 1011030 * 2 ^ 59
def prefixEnd_1011030 : Nat := 4983230072969 + 3 ^ 40 * 1011030 * 2
def baseEnd_1011030 : Nat := 51273515665707118437073

theorem tailTrace_1011030 : CollatzResearch.WordTrace tailWord_1011030 prefixEnd_1011030 51273515665707118437073 := by
  unfold tailWord_1011030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2304705845451153438883409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24583529018145636681423029 2304705845451153438883409)
  ·
    refine ⟨1728529384088365079162557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2304705845451153438883409 1728529384088365079162557)
    ·
      refine ⟨648198519033136904685959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1728529384088365079162557 648198519033136904685959)
      ·
        refine ⟨972297778549705357028939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648198519033136904685959 972297778549705357028939)
        ·
          refine ⟨1458446667824558035543409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972297778549705357028939 1458446667824558035543409)
          ·
            refine ⟨1093835000868418526657557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1458446667824558035543409 1093835000868418526657557)
            ·
              refine ⟨51273515665707118437073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1093835000868418526657557 51273515665707118437073)
              ·
                rfl

theorem cell20_1011030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 6].length) (baseStart_1011030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011030 prefixEnd_1011030 := by exact prefixLift 1011030
  have htrace : WordTrace (prefixWord ++ tailWord_1011030) baseStart_1011030 baseEnd_1011030 := by
    simpa [prefixWord, tailWord_1011030, baseEnd_1011030] using wordTrace_append hprefix tailTrace_1011030
  have hstable : (prefixWord ++ tailWord_1011030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011030).length < 2 ^ (prefixWord ++ tailWord_1011030).sum := by decide
  have hdescent : baseEnd_1011030 < baseStart_1011030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011045 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 5]
def baseStart_1011045 : Nat := 118140960795 + 1011045 * 2 ^ 59
def prefixEnd_1011045 : Nat := 4983230072969 + 3 ^ 40 * 1011045 * 2
def baseEnd_1011045 : Nat := 461468487400090680433595

theorem tailTrace_1011045 : CollatzResearch.WordTrace tailWord_1011045 prefixEnd_1011045 461468487400090680433595 := by
  unfold tailWord_1011045
  simp only [CollatzResearch.WordTrace]
  refine ⟨36875840622164112583930589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24583893748109408389287059 36875840622164112583930589)
  ·
    refine ⟨13828440233311542218973971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36875840622164112583930589 13828440233311542218973971)
    ·
      refine ⟨20742660349967313328460957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13828440233311542218973971 20742660349967313328460957)
      ·
        refine ⟨7778497631237742498172859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20742660349967313328460957 7778497631237742498172859)
        ·
          refine ⟨11667746446856613747259289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7778497631237742498172859 11667746446856613747259289)
          ·
            refine ⟨8750809835142460310444467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11667746446856613747259289 8750809835142460310444467)
            ·
              refine ⟨13126214752713690465666701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8750809835142460310444467 13126214752713690465666701)
              ·
                refine ⟨4922330532267633924625013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13126214752713690465666701 4922330532267633924625013)
                ·
                  refine ⟨461468487400090680433595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4922330532267633924625013 461468487400090680433595)
                  ·
                    rfl

theorem cell20_1011045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_1011045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011045 prefixEnd_1011045 := by exact prefixLift 1011045
  have htrace : WordTrace (prefixWord ++ tailWord_1011045) baseStart_1011045 baseEnd_1011045 := by
    simpa [prefixWord, tailWord_1011045, baseEnd_1011045] using wordTrace_append hprefix tailTrace_1011045
  have hstable : (prefixWord ++ tailWord_1011045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011045).length < 2 ^ (prefixWord ++ tailWord_1011045).sum := by decide
  have hdescent : baseEnd_1011045 < baseStart_1011045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011054 : List Nat := [4, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_1011054 : Nat := 118140960795 + 1011054 * 2 ^ 59
def prefixEnd_1011054 : Nat := 4983230072969 + 3 ^ 40 * 1011054 * 2
def baseEnd_1011054 : Nat := 461472595245326649133559

theorem tailTrace_1011054 : CollatzResearch.WordTrace tailWord_1011054 prefixEnd_1011054 461472595245326649133559 := by
  unfold tailWord_1011054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4609521109891438390126027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24584112586087671414005477 4609521109891438390126027)
  ·
    refine ⟨6914281664837157585189041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4609521109891438390126027 6914281664837157585189041)
    ·
      refine ⟨5185711248627868188891781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6914281664837157585189041 5185711248627868188891781)
      ·
        refine ⟨972320859117725285417209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5185711248627868188891781 972320859117725285417209)
        ·
          refine ⟨729240644338293964062907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 972320859117725285417209 729240644338293964062907)
          ·
            refine ⟨1093860966507440946094361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729240644338293964062907 1093860966507440946094361)
            ·
              refine ⟨820395724880580709570771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093860966507440946094361 820395724880580709570771)
              ·
                refine ⟨1230593587320871064356157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820395724880580709570771 1230593587320871064356157)
                ·
                  refine ⟨461472595245326649133559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1230593587320871064356157 461472595245326649133559)
                  ·
                    rfl

theorem cell20_1011054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_1011054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011054 prefixEnd_1011054 := by exact prefixLift 1011054
  have htrace : WordTrace (prefixWord ++ tailWord_1011054) baseStart_1011054 baseEnd_1011054 := by
    simpa [prefixWord, tailWord_1011054, baseEnd_1011054] using wordTrace_append hprefix tailTrace_1011054
  have hstable : (prefixWord ++ tailWord_1011054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011054).length < 2 ^ (prefixWord ++ tailWord_1011054).sum := by decide
  have hdescent : baseEnd_1011054 < baseStart_1011054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011076 : List Nat := [2, 3, 2, 1, 1, 3, 2, 6]
def baseStart_1011076 : Nat := 118140960795 + 1011076 * 2 ^ 59
def prefixEnd_1011076 : Nat := 4983230072969 + 3 ^ 40 * 1011076 * 2
def baseEnd_1011076 : Nat := 153827545548264116800045

theorem tailTrace_1011076 : CollatzResearch.WordTrace tailWord_1011076 prefixEnd_1011076 153827545548264116800045 := by
  unfold tailWord_1011076
  simp only [CollatzResearch.WordTrace]
  refine ⟨18438485642525902439154541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24584647523367869918872721 18438485642525902439154541)
  ·
    refine ⟨6914432115947213414682953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18438485642525902439154541 6914432115947213414682953)
    ·
      refine ⟨5185824086960410061012215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6914432115947213414682953 5185824086960410061012215)
      ·
        refine ⟨7778736130440615091518323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5185824086960410061012215 7778736130440615091518323)
        ·
          refine ⟨11668104195660922637277485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7778736130440615091518323 11668104195660922637277485)
          ·
            refine ⟨4375539073372845988979057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11668104195660922637277485 4375539073372845988979057)
            ·
              refine ⟨3281654305029634491734293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4375539073372845988979057 3281654305029634491734293)
              ·
                refine ⟨153827545548264116800045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3281654305029634491734293 153827545548264116800045)
                ·
                  rfl

theorem cell20_1011076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_1011076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011076 prefixEnd_1011076 := by exact prefixLift 1011076
  have htrace : WordTrace (prefixWord ++ tailWord_1011076) baseStart_1011076 baseEnd_1011076 := by
    simpa [prefixWord, tailWord_1011076, baseEnd_1011076] using wordTrace_append hprefix tailTrace_1011076
  have hstable : (prefixWord ++ tailWord_1011076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011076).length < 2 ^ (prefixWord ++ tailWord_1011076).sum := by decide
  have hdescent : baseEnd_1011076 < baseStart_1011076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011097 : List Nat := [1, 2, 1, 2, 1, 13]
def baseStart_1011097 : Nat := 118140960795 + 1011097 * 2 ^ 59
def prefixEnd_1011097 : Nat := 4983230072969 + 3 ^ 40 * 1011097 * 2
def baseEnd_1011097 : Nat := 17092304504333689285187

theorem tailTrace_1011097 : CollatzResearch.WordTrace tailWord_1011097 prefixEnd_1011097 17092304504333689285187 := by
  unfold tailWord_1011097
  simp only [CollatzResearch.WordTrace]
  refine ⟨36877737217975725464823545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24585158145317150309882363 36877737217975725464823545)
  ·
    refine ⟨27658302913481794098617659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36877737217975725464823545 27658302913481794098617659)
    ·
      refine ⟨41487454370222691147926489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27658302913481794098617659 41487454370222691147926489)
      ·
        refine ⟨31115590777667018360944867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41487454370222691147926489 31115590777667018360944867)
        ·
          refine ⟨46673386166500527541417301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31115590777667018360944867 46673386166500527541417301)
          ·
            refine ⟨17092304504333689285187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 46673386166500527541417301 17092304504333689285187)
            ·
              rfl

theorem cell20_1011097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 13].length) (baseStart_1011097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011097 prefixEnd_1011097 := by exact prefixLift 1011097
  have htrace : WordTrace (prefixWord ++ tailWord_1011097) baseStart_1011097 baseEnd_1011097 := by
    simpa [prefixWord, tailWord_1011097, baseEnd_1011097] using wordTrace_append hprefix tailTrace_1011097
  have hstable : (prefixWord ++ tailWord_1011097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011097).length < 2 ^ (prefixWord ++ tailWord_1011097).sum := by decide
  have hdescent : baseEnd_1011097 < baseStart_1011097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011103 : List Nat := [1, 1, 2, 5, 1, 2, 4, 2, 2]
def baseStart_1011103 : Nat := 118140960795 + 1011103 * 2 ^ 59
def prefixEnd_1011103 : Nat := 4983230072969 + 3 ^ 40 * 1011103 * 2
def baseEnd_1011103 : Nat := 461494960180500256500025

theorem tailTrace_1011103 : CollatzResearch.WordTrace tailWord_1011103 prefixEnd_1011103 461494960180500256500025 := by
  unfold tailWord_1011103
  simp only [CollatzResearch.WordTrace]
  refine ⟨36877956055953988489541963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24585304037302658993027975 36877956055953988489541963)
  ·
    refine ⟨55316934083930982734312945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36877956055953988489541963 55316934083930982734312945)
    ·
      refine ⟨41487700562948237050734709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55316934083930982734312945 41487700562948237050734709)
      ·
        refine ⟨3889471927776397223506379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41487700562948237050734709 3889471927776397223506379)
        ·
          refine ⟨5834207891664595835259569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3889471927776397223506379 5834207891664595835259569)
          ·
            refine ⟨4375655918748446876444677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5834207891664595835259569 4375655918748446876444677)
            ·
              refine ⟨820435484765333789333377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4375655918748446876444677 820435484765333789333377)
              ·
                refine ⟨615326613574000342000033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820435484765333789333377 615326613574000342000033)
                ·
                  refine ⟨461494960180500256500025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615326613574000342000033 461494960180500256500025)
                  ·
                    rfl

theorem cell20_1011103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 2].length) (baseStart_1011103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011103 prefixEnd_1011103 := by exact prefixLift 1011103
  have htrace : WordTrace (prefixWord ++ tailWord_1011103) baseStart_1011103 baseEnd_1011103 := by
    simpa [prefixWord, tailWord_1011103, baseEnd_1011103] using wordTrace_append hprefix tailTrace_1011103
  have hstable : (prefixWord ++ tailWord_1011103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011103).length < 2 ^ (prefixWord ++ tailWord_1011103).sum := by decide
  have hdescent : baseEnd_1011103 < baseStart_1011103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011117 : List Nat := [1, 5, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1011117 : Nat := 118140960795 + 1011117 * 2 ^ 59
def prefixEnd_1011117 : Nat := 4983230072969 + 3 ^ 40 * 1011117 * 2
def baseEnd_1011117 : Nat := 461501350161978430033301

theorem tailTrace_1011117 : CollatzResearch.WordTrace tailWord_1011117 prefixEnd_1011117 461501350161978430033301 := by
  unfold tailWord_1011117
  simp only [CollatzResearch.WordTrace]
  refine ⟨36878466677903268880551605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24585644451935512587034403 36878466677903268880551605)
  ·
    refine ⟨3457356251053431457551713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36878466677903268880551605 3457356251053431457551713)
    ·
      refine ⟨2593017188290073593163785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3457356251053431457551713 2593017188290073593163785)
      ·
        refine ⟨1944762891217555194872839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2593017188290073593163785 1944762891217555194872839)
        ·
          refine ⟨2917144336826332792309259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944762891217555194872839 2917144336826332792309259)
          ·
            refine ⟨4375716505239499188463889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2917144336826332792309259 4375716505239499188463889)
            ·
              refine ⟨3281787378929624391347917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4375716505239499188463889 3281787378929624391347917)
              ·
                refine ⟨1230670267098609146755469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3281787378929624391347917 1230670267098609146755469)
                ·
                  refine ⟨461501350161978430033301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1230670267098609146755469 461501350161978430033301)
                  ·
                    rfl

theorem cell20_1011117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1011117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011117 prefixEnd_1011117 := by exact prefixLift 1011117
  have htrace : WordTrace (prefixWord ++ tailWord_1011117) baseStart_1011117 baseEnd_1011117 := by
    simpa [prefixWord, tailWord_1011117, baseEnd_1011117] using wordTrace_append hprefix tailTrace_1011117
  have hstable : (prefixWord ++ tailWord_1011117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011117).length < 2 ^ (prefixWord ++ tailWord_1011117).sum := by decide
  have hdescent : baseEnd_1011117 < baseStart_1011117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011128 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_1011128 : Nat := 118140960795 + 1011128 * 2 ^ 59
def prefixEnd_1011128 : Nat := 4983230072969 + 3 ^ 40 * 1011128 * 2
def baseEnd_1011128 : Nat := 461506370861711280666589

theorem tailTrace_1011128 : CollatzResearch.WordTrace tailWord_1011128 prefixEnd_1011128 461506370861711280666589 := by
  unfold tailWord_1011128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18439433940431708879601019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24585911920575611839468025 18439433940431708879601019)
  ·
    refine ⟨27659150910647563319401529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18439433940431708879601019 27659150910647563319401529)
    ·
      refine ⟨20744363182985672489551147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27659150910647563319401529 20744363182985672489551147)
      ·
        refine ⟨31116544774478508734326721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20744363182985672489551147 31116544774478508734326721)
        ·
          refine ⟨23337408580858881550745041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31116544774478508734326721 23337408580858881550745041)
          ·
            refine ⟨17503056435644161163058781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23337408580858881550745041 17503056435644161163058781)
            ·
              refine ⟨6563646163366560436147043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17503056435644161163058781 6563646163366560436147043)
              ·
                refine ⟨9845469245049840654220565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6563646163366560436147043 9845469245049840654220565)
                ·
                  refine ⟨461506370861711280666589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9845469245049840654220565 461506370861711280666589)
                  ·
                    rfl

theorem cell20_1011128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_1011128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011128 prefixEnd_1011128 := by exact prefixLift 1011128
  have htrace : WordTrace (prefixWord ++ tailWord_1011128) baseStart_1011128 baseEnd_1011128 := by
    simpa [prefixWord, tailWord_1011128, baseEnd_1011128] using wordTrace_append hprefix tailTrace_1011128
  have hstable : (prefixWord ++ tailWord_1011128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011128).length < 2 ^ (prefixWord ++ tailWord_1011128).sum := by decide
  have hdescent : baseEnd_1011128 < baseStart_1011128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011135 : List Nat := [1, 1, 2, 2, 2, 1, 1, 10]
def baseStart_1011135 : Nat := 118140960795 + 1011135 * 2 ^ 59
def prefixEnd_1011135 : Nat := 4983230072969 + 3 ^ 40 * 1011135 * 2
def baseEnd_1011135 : Nat := 153836521950816789144409

theorem tailTrace_1011135 : CollatzResearch.WordTrace tailWord_1011135 prefixEnd_1011135 153836521950816789144409 := by
  unfold tailWord_1011135
  simp only [CollatzResearch.WordTrace]
  refine ⟨36879123191838057954706859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24586082127892038636471239 36879123191838057954706859)
  ·
    refine ⟨55318684787757086932060289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36879123191838057954706859 55318684787757086932060289)
    ·
      refine ⟨41489013590817815199045217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55318684787757086932060289 41489013590817815199045217)
      ·
        refine ⟨31116760193113361399283913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41489013590817815199045217 31116760193113361399283913)
        ·
          refine ⟨23337570144835021049462935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31116760193113361399283913 23337570144835021049462935)
          ·
            refine ⟨35006355217252531574194403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23337570144835021049462935 35006355217252531574194403)
            ·
              refine ⟨52509532825878797361291605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35006355217252531574194403 52509532825878797361291605)
              ·
                refine ⟨153836521950816789144409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52509532825878797361291605 153836521950816789144409)
                ·
                  rfl

theorem cell20_1011135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_1011135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011135 prefixEnd_1011135 := by exact prefixLift 1011135
  have htrace : WordTrace (prefixWord ++ tailWord_1011135) baseStart_1011135 baseEnd_1011135 := by
    simpa [prefixWord, tailWord_1011135, baseEnd_1011135] using wordTrace_append hprefix tailTrace_1011135
  have hstable : (prefixWord ++ tailWord_1011135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011135).length < 2 ^ (prefixWord ++ tailWord_1011135).sum := by decide
  have hdescent : baseEnd_1011135 < baseStart_1011135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011162 : List Nat := [3, 1, 1, 2, 3, 2, 2, 4, 2]
def baseStart_1011162 : Nat := 118140960795 + 1011162 * 2 ^ 59
def prefixEnd_1011162 : Nat := 4983230072969 + 3 ^ 40 * 1011162 * 2
def baseEnd_1011162 : Nat := 461521889388158273533117

theorem tailTrace_1011162 : CollatzResearch.WordTrace tailWord_1011162 prefixEnd_1011162 461521889388158273533117 := by
  unfold tailWord_1011162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9220026990685060391484935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24586738641826827710626493 9220026990685060391484935)
  ·
    refine ⟨13830040486027590587227403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9220026990685060391484935 13830040486027590587227403)
    ·
      refine ⟨20745060729041385880841105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13830040486027590587227403 20745060729041385880841105)
      ·
        refine ⟨15558795546781039410630829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20745060729041385880841105 15558795546781039410630829)
        ·
          refine ⟨5834548330042889778986561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15558795546781039410630829 5834548330042889778986561)
          ·
            refine ⟨4375911247532167334239921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5834548330042889778986561 4375911247532167334239921)
            ·
              refine ⟨3281933435649125500679941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4375911247532167334239921 3281933435649125500679941)
              ·
                refine ⟨615362519184211031377489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3281933435649125500679941 615362519184211031377489)
                ·
                  refine ⟨461521889388158273533117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615362519184211031377489 461521889388158273533117)
                  ·
                    rfl

theorem cell20_1011162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_1011162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011162 prefixEnd_1011162 := by exact prefixLift 1011162
  have htrace : WordTrace (prefixWord ++ tailWord_1011162) baseStart_1011162 baseEnd_1011162 := by
    simpa [prefixWord, tailWord_1011162, baseEnd_1011162] using wordTrace_append hprefix tailTrace_1011162
  have hstable : (prefixWord ++ tailWord_1011162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011162).length < 2 ^ (prefixWord ++ tailWord_1011162).sum := by decide
  have hdescent : baseEnd_1011162 < baseStart_1011162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011186 : List Nat := [3, 2, 1, 4, 1, 3, 2, 4]
def baseStart_1011186 : Nat := 118140960795 + 1011186 * 2 ^ 59
def prefixEnd_1011186 : Nat := 4983230072969 + 3 ^ 40 * 1011186 * 2
def baseEnd_1011186 : Nat := 153844281214040285577673

theorem tailTrace_1011186 : CollatzResearch.WordTrace tailWord_1011186 prefixEnd_1011186 153844281214040285577673 := by
  unfold tailWord_1011186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9220245828663323416203353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24587322209768862443208941 9220245828663323416203353)
  ·
    refine ⟨6915184371497492562152515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9220245828663323416203353 6915184371497492562152515)
    ·
      refine ⟨10372776557246238843228773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6915184371497492562152515 10372776557246238843228773)
      ·
        refine ⟨1944895604483669783105395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10372776557246238843228773 1944895604483669783105395)
        ·
          refine ⟨2917343406725504674658093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944895604483669783105395 2917343406725504674658093)
          ·
            refine ⟨1094003777522064252996785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2917343406725504674658093 1094003777522064252996785)
            ·
              refine ⟨820502833141548189747589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094003777522064252996785 820502833141548189747589)
              ·
                refine ⟨153844281214040285577673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 820502833141548189747589 153844281214040285577673)
                ·
                  rfl

theorem cell20_1011186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_1011186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011186 prefixEnd_1011186 := by exact prefixLift 1011186
  have htrace : WordTrace (prefixWord ++ tailWord_1011186) baseStart_1011186 baseEnd_1011186 := by
    simpa [prefixWord, tailWord_1011186, baseEnd_1011186] using wordTrace_append hprefix tailTrace_1011186
  have hstable : (prefixWord ++ tailWord_1011186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011186).length < 2 ^ (prefixWord ++ tailWord_1011186).sum := by decide
  have hdescent : baseEnd_1011186 < baseStart_1011186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011197 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1011197 : Nat := 118140960795 + 1011197 * 2 ^ 59
def prefixEnd_1011197 : Nat := 4983230072969 + 3 ^ 40 * 1011197 * 2
def baseEnd_1011197 : Nat := 461537864341853707366307

theorem tailTrace_1011197 : CollatzResearch.WordTrace tailWord_1011197 prefixEnd_1011197 461537864341853707366307 := by
  unfold tailWord_1011197
  simp only [CollatzResearch.WordTrace]
  refine ⟨36881384517613442543463845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24587589678408961695642563 36881384517613442543463845)
  ·
    refine ⟨6915259597052520476899471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36881384517613442543463845 6915259597052520476899471)
    ·
      refine ⟨10372889395578780715349207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6915259597052520476899471 10372889395578780715349207)
      ·
        refine ⟨15559334093368171073023811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10372889395578780715349207 15559334093368171073023811)
        ·
          refine ⟨23339001140052256609535717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15559334093368171073023811 23339001140052256609535717)
          ·
            refine ⟨4376062713759798114287947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23339001140052256609535717 4376062713759798114287947)
            ·
              refine ⟨6564094070639697171431921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4376062713759798114287947 6564094070639697171431921)
              ·
                refine ⟨4923070552979772878573941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6564094070639697171431921 4923070552979772878573941)
                ·
                  refine ⟨461537864341853707366307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4923070552979772878573941 461537864341853707366307)
                  ·
                    rfl

theorem cell20_1011197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1011197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011197 prefixEnd_1011197 := by exact prefixLift 1011197
  have htrace : WordTrace (prefixWord ++ tailWord_1011197) baseStart_1011197 baseEnd_1011197 := by
    simpa [prefixWord, tailWord_1011197, baseEnd_1011197] using wordTrace_append hprefix tailTrace_1011197
  have hstable : (prefixWord ++ tailWord_1011197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011197).length < 2 ^ (prefixWord ++ tailWord_1011197).sum := by decide
  have hdescent : baseEnd_1011197 < baseStart_1011197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011213 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1011213 : Nat := 118140960795 + 1011213 * 2 ^ 59
def prefixEnd_1011213 : Nat := 4983230072969 + 3 ^ 40 * 1011213 * 2
def baseEnd_1011213 : Nat := 461545167177828762832909

theorem tailTrace_1011213 : CollatzResearch.WordTrace tailWord_1011213 prefixEnd_1011213 461545167177828762832909 := by
  unfold tailWord_1011213
  simp only [CollatzResearch.WordTrace]
  refine ⟨36881968085555477276046293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24587978723703651517364195 36881968085555477276046293)
  ·
    refine ⟨864421127005206498657335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 36881968085555477276046293 864421127005206498657335)
    ·
      refine ⟨1296631690507809747986003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 864421127005206498657335 1296631690507809747986003)
      ·
        refine ⟨1944947535761714621979005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296631690507809747986003 1944947535761714621979005)
        ·
          refine ⟨729355325910642983242127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1944947535761714621979005 729355325910642983242127)
          ·
            refine ⟨1094032988865964474863191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729355325910642983242127 1094032988865964474863191)
            ·
              refine ⟨1641049483298946712294787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094032988865964474863191 1641049483298946712294787)
              ·
                refine ⟨2461574224948420068442181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641049483298946712294787 2461574224948420068442181)
                ·
                  refine ⟨461545167177828762832909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2461574224948420068442181 461545167177828762832909)
                  ·
                    rfl

theorem cell20_1011213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1011213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011213 prefixEnd_1011213 := by exact prefixLift 1011213
  have htrace : WordTrace (prefixWord ++ tailWord_1011213) baseStart_1011213 baseEnd_1011213 := by
    simpa [prefixWord, tailWord_1011213, baseEnd_1011213] using wordTrace_append hprefix tailTrace_1011213
  have hstable : (prefixWord ++ tailWord_1011213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011213).length < 2 ^ (prefixWord ++ tailWord_1011213).sum := by decide
  have hdescent : baseEnd_1011213 < baseStart_1011213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011221 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1011221 : Nat := 118140960795 + 1011221 * 2 ^ 59
def prefixEnd_1011221 : Nat := 4983230072969 + 3 ^ 40 * 1011221 * 2
def baseEnd_1011221 : Nat := 461548818595816290566209

theorem tailTrace_1011221 : CollatzResearch.WordTrace tailWord_1011221 prefixEnd_1011221 461548818595816290566209 := by
  unfold tailWord_1011221
  simp only [CollatzResearch.WordTrace]
  refine ⟨36882259869526494642337517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24588173246350996428225011 36882259869526494642337517)
  ·
    refine ⟨13830847451072435490876569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36882259869526494642337517 13830847451072435490876569)
    ·
      refine ⟨10373135588304326618157427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13830847451072435490876569 10373135588304326618157427)
      ·
        refine ⟨15559703382456489927236141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10373135588304326618157427 15559703382456489927236141)
        ·
          refine ⟨5834888768421183722713553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15559703382456489927236141 5834888768421183722713553)
          ·
            refine ⟨4376166576315887792035165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5834888768421183722713553 4376166576315887792035165)
            ·
              refine ⟨1641062466118457922013187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4376166576315887792035165 1641062466118457922013187)
              ·
                refine ⟨2461593699177686883019781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641062466118457922013187 2461593699177686883019781)
                ·
                  refine ⟨461548818595816290566209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2461593699177686883019781 461548818595816290566209)
                  ·
                    rfl

theorem cell20_1011221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1011221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011221 prefixEnd_1011221 := by exact prefixLift 1011221
  have htrace : WordTrace (prefixWord ++ tailWord_1011221) baseStart_1011221 baseEnd_1011221 := by
    simpa [prefixWord, tailWord_1011221, baseEnd_1011221] using wordTrace_append hprefix tailTrace_1011221
  have hstable : (prefixWord ++ tailWord_1011221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011221).length < 2 ^ (prefixWord ++ tailWord_1011221).sum := by decide
  have hdescent : baseEnd_1011221 < baseStart_1011221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011228 : List Nat := [2, 2, 3, 1, 2, 1, 4, 5]
def baseStart_1011228 : Nat := 118140960795 + 1011228 * 2 ^ 59
def prefixEnd_1011228 : Nat := 4983230072969 + 3 ^ 40 * 1011228 * 2
def baseEnd_1011228 : Nat := 153850671195518459110949

theorem tailTrace_1011228 : CollatzResearch.WordTrace tailWord_1011228 prefixEnd_1011228 153850671195518459110949 := by
  unfold tailWord_1011228
  simp only [CollatzResearch.WordTrace]
  refine ⟨18441257590250567418921169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24588343453667423225228225 18441257590250567418921169)
  ·
    refine ⟨13830943192687925564190877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18441257590250567418921169 13830943192687925564190877)
    ·
      refine ⟨5186603697257972086571579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13830943192687925564190877 5186603697257972086571579)
      ·
        refine ⟨7779905545886958129857369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5186603697257972086571579 7779905545886958129857369)
        ·
          refine ⟨5834929159415218597393027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7779905545886958129857369 5834929159415218597393027)
          ·
            refine ⟨8752393739122827896089541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834929159415218597393027 8752393739122827896089541)
            ·
              refine ⟨1641073826085530230516789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8752393739122827896089541 1641073826085530230516789)
              ·
                refine ⟨153850671195518459110949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1641073826085530230516789 153850671195518459110949)
                ·
                  rfl

theorem cell20_1011228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_1011228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011228 prefixEnd_1011228 := by exact prefixLift 1011228
  have htrace : WordTrace (prefixWord ++ tailWord_1011228) baseStart_1011228 baseEnd_1011228 := by
    simpa [prefixWord, tailWord_1011228, baseEnd_1011228] using wordTrace_append hprefix tailTrace_1011228
  have hstable : (prefixWord ++ tailWord_1011228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011228).length < 2 ^ (prefixWord ++ tailWord_1011228).sum := by decide
  have hdescent : baseEnd_1011228 < baseStart_1011228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011276 : List Nat := [2, 2, 1, 3, 1, 4, 1, 4, 2]
def baseStart_1011276 : Nat := 118140960795 + 1011276 * 2 ^ 59
def prefixEnd_1011276 : Nat := 4983230072969 + 3 ^ 40 * 1011276 * 2
def baseEnd_1011276 : Nat := 461573922094480543732651

theorem tailTrace_1011276 : CollatzResearch.WordTrace tailWord_1011276 prefixEnd_1011276 461573922094480543732651 := by
  unfold tailWord_1011276
  simp only [CollatzResearch.WordTrace]
  refine ⟨18442132942163619517794841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24589510589551492690393121 18442132942163619517794841)
  ·
    refine ⟨13831599706622714638346131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18442132942163619517794841 13831599706622714638346131)
    ·
      refine ⟨20747399559934071957519197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13831599706622714638346131 20747399559934071957519197)
      ·
        refine ⟨7780274834975276984069699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20747399559934071957519197 7780274834975276984069699)
        ·
          refine ⟨11670412252462915476104549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7780274834975276984069699 11670412252462915476104549)
          ·
            refine ⟨2188202297336796651769603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11670412252462915476104549 2188202297336796651769603)
            ·
              refine ⟨3282303446005194977654405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188202297336796651769603 3282303446005194977654405)
              ·
                refine ⟨615431896125974058310201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3282303446005194977654405 615431896125974058310201)
                ·
                  refine ⟨461573922094480543732651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615431896125974058310201 461573922094480543732651)
                  ·
                    rfl

theorem cell20_1011276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_1011276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011276 prefixEnd_1011276 := by exact prefixLift 1011276
  have htrace : WordTrace (prefixWord ++ tailWord_1011276) baseStart_1011276 baseEnd_1011276 := by
    simpa [prefixWord, tailWord_1011276, baseEnd_1011276] using wordTrace_append hprefix tailTrace_1011276
  have hstable : (prefixWord ++ tailWord_1011276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011276).length < 2 ^ (prefixWord ++ tailWord_1011276).sum := by decide
  have hdescent : baseEnd_1011276 < baseStart_1011276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011280 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_1011280 : Nat := 118140960795 + 1011280 * 2 ^ 59
def prefixEnd_1011280 : Nat := 4983230072969 + 3 ^ 40 * 1011280 * 2
def baseEnd_1011280 : Nat := 461575747803474307599301

theorem tailTrace_1011280 : CollatzResearch.WordTrace tailWord_1011280 prefixEnd_1011280 461575747803474307599301 := by
  unfold tailWord_1011280
  simp only [CollatzResearch.WordTrace]
  refine ⟨18442205888156373859367647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24589607850875165145823529 18442205888156373859367647)
  ·
    refine ⟨27663308832234560789051471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18442205888156373859367647 27663308832234560789051471)
    ·
      refine ⟨41494963248351841183577207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27663308832234560789051471 41494963248351841183577207)
      ·
        refine ⟨62242444872527761775365811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41494963248351841183577207 62242444872527761775365811)
        ·
          refine ⟨93363667308791642663048717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62242444872527761775365811 93363667308791642663048717)
          ·
            refine ⟨35011375240796865998643269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93363667308791642663048717 35011375240796865998643269)
            ·
              refine ⟨6564632857649412374745613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35011375240796865998643269 6564632857649412374745613)
              ·
                refine ⟨2461737321618529640529605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6564632857649412374745613 2461737321618529640529605)
                ·
                  refine ⟨461575747803474307599301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2461737321618529640529605 461575747803474307599301)
                  ·
                    rfl

theorem cell20_1011280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_1011280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011280 prefixEnd_1011280 := by exact prefixLift 1011280
  have htrace : WordTrace (prefixWord ++ tailWord_1011280) baseStart_1011280 baseEnd_1011280 := by
    simpa [prefixWord, tailWord_1011280, baseEnd_1011280] using wordTrace_append hprefix tailTrace_1011280
  have hstable : (prefixWord ++ tailWord_1011280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011280).length < 2 ^ (prefixWord ++ tailWord_1011280).sum := by decide
  have hdescent : baseEnd_1011280 < baseStart_1011280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011293 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 4]
def baseStart_1011293 : Nat := 118140960795 + 1011293 * 2 ^ 59
def prefixEnd_1011293 : Nat := 4983230072969 + 3 ^ 40 * 1011293 * 2
def baseEnd_1011293 : Nat := 461581681357704040165915

theorem tailTrace_1011293 : CollatzResearch.WordTrace tailWord_1011293 prefixEnd_1011293 461581681357704040165915 := by
  unfold tailWord_1011293
  simp only [CollatzResearch.WordTrace]
  refine ⟨36884885925265650938958533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24589923950177100625972355 36884885925265650938958533)
  ·
    refine ⟨6915916110987309551054725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36884885925265650938958533 6915916110987309551054725)
    ·
      refine ⟨1296734270810120540822761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6915916110987309551054725 1296734270810120540822761)
      ·
        refine ⟨972550703107590405617071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1296734270810120540822761 972550703107590405617071)
        ·
          refine ⟨1458826054661385608425607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972550703107590405617071 1458826054661385608425607)
          ·
            refine ⟨2188239081992078412638411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458826054661385608425607 2188239081992078412638411)
            ·
              refine ⟨3282358622988117618957617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188239081992078412638411 3282358622988117618957617)
              ·
                refine ⟨2461768967241088214218213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3282358622988117618957617 2461768967241088214218213)
                ·
                  refine ⟨461581681357704040165915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2461768967241088214218213 461581681357704040165915)
                  ·
                    rfl

theorem cell20_1011293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_1011293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011293 prefixEnd_1011293 := by exact prefixLift 1011293
  have htrace : WordTrace (prefixWord ++ tailWord_1011293) baseStart_1011293 baseEnd_1011293 := by
    simpa [prefixWord, tailWord_1011293, baseEnd_1011293] using wordTrace_append hprefix tailTrace_1011293
  have hstable : (prefixWord ++ tailWord_1011293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011293).length < 2 ^ (prefixWord ++ tailWord_1011293).sum := by decide
  have hdescent : baseEnd_1011293 < baseStart_1011293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011314 : List Nat := [3, 2, 1, 2, 3, 1, 1, 5, 2]
def baseStart_1011314 : Nat := 118140960795 + 1011314 * 2 ^ 59
def prefixEnd_1011314 : Nat := 4983230072969 + 3 ^ 40 * 1011314 * 2
def baseEnd_1011314 : Nat := 461591266329921300465829

theorem tailTrace_1011314 : CollatzResearch.WordTrace tailWord_1011314 prefixEnd_1011314 461591266329921300465829 := by
  unfold tailWord_1011314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9221412964547392881368249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24590434572126381016981997 9221412964547392881368249)
  ·
    refine ⟨6916059723410544661026187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9221412964547392881368249 6916059723410544661026187)
    ·
      refine ⟨10374089585115816991539281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6916059723410544661026187 10374089585115816991539281)
      ·
        refine ⟨7780567188836862743654461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10374089585115816991539281 7780567188836862743654461)
        ·
          refine ⟨2917712695813823528870423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7780567188836862743654461 2917712695813823528870423)
          ·
            refine ⟨4376569043720735293305635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2917712695813823528870423 4376569043720735293305635)
            ·
              refine ⟨6564853565581102939958453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4376569043720735293305635 6564853565581102939958453)
              ·
                refine ⟨615455021773228400621105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6564853565581102939958453 615455021773228400621105)
                ·
                  refine ⟨461591266329921300465829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615455021773228400621105 461591266329921300465829)
                  ·
                    rfl

theorem cell20_1011314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_1011314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011314 prefixEnd_1011314 := by exact prefixLift 1011314
  have htrace : WordTrace (prefixWord ++ tailWord_1011314) baseStart_1011314 baseEnd_1011314 := by
    simpa [prefixWord, tailWord_1011314, baseEnd_1011314] using wordTrace_append hprefix tailTrace_1011314
  have hstable : (prefixWord ++ tailWord_1011314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011314).length < 2 ^ (prefixWord ++ tailWord_1011314).sum := by decide
  have hdescent : baseEnd_1011314 < baseStart_1011314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011335 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 4]
def baseStart_1011335 : Nat := 118140960795 + 1011335 * 2 ^ 59
def prefixEnd_1011335 : Nat := 4983230072969 + 3 ^ 40 * 1011335 * 2
def baseEnd_1011335 : Nat := 461600851302138560765743

theorem tailTrace_1011335 : CollatzResearch.WordTrace tailWord_1011335 prefixEnd_1011335 461600851302138560765743 := by
  unfold tailWord_1011335
  simp only [CollatzResearch.WordTrace]
  refine ⟨36886417791113492111987459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24590945194075661407991639 36886417791113492111987459)
  ·
    refine ⟨55329626686670238167981189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36886417791113492111987459 55329626686670238167981189)
    ·
      refine ⟨10374305003750669656496473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55329626686670238167981189 10374305003750669656496473)
      ·
        refine ⟨7780728752813002242372355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10374305003750669656496473 7780728752813002242372355)
        ·
          refine ⟨11671093129219503363558533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7780728752813002242372355 11671093129219503363558533)
          ·
            refine ⟨2188329961728656880667225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11671093129219503363558533 2188329961728656880667225)
            ·
              refine ⟨1641247471296492660500419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2188329961728656880667225 1641247471296492660500419)
              ·
                refine ⟨2461871206944738990750629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641247471296492660500419 2461871206944738990750629)
                ·
                  refine ⟨461600851302138560765743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2461871206944738990750629 461600851302138560765743)
                  ·
                    rfl

theorem cell20_1011335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_1011335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011335 prefixEnd_1011335 := by exact prefixLift 1011335
  have htrace : WordTrace (prefixWord ++ tailWord_1011335) baseStart_1011335 baseEnd_1011335 := by
    simpa [prefixWord, tailWord_1011335, baseEnd_1011335] using wordTrace_append hprefix tailTrace_1011335
  have hstable : (prefixWord ++ tailWord_1011335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011335).length < 2 ^ (prefixWord ++ tailWord_1011335).sum := by decide
  have hdescent : baseEnd_1011335 < baseStart_1011335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011349 : List Nat := [1, 3, 2, 1, 1, 1, 1, 7, 3]
def baseStart_1011349 : Nat := 118140960795 + 1011349 * 2 ^ 59
def prefixEnd_1011349 : Nat := 4983230072969 + 3 ^ 40 * 1011349 * 2
def baseEnd_1011349 : Nat := 461607241283616734299019

theorem tailTrace_1011349 : CollatzResearch.WordTrace tailWord_1011349 prefixEnd_1011349 461607241283616734299019 := by
  unfold tailWord_1011349
  simp only [CollatzResearch.WordTrace]
  refine ⟨36886928413062772502997101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24591285608708515001998067 36886928413062772502997101)
  ·
    refine ⟨13832598154898539688623913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36886928413062772502997101 13832598154898539688623913)
    ·
      refine ⟨10374448616173904766467935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13832598154898539688623913 10374448616173904766467935)
      ·
        refine ⟨15561672924260857149701903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10374448616173904766467935 15561672924260857149701903)
        ·
          refine ⟨23342509386391285724552855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15561672924260857149701903 23342509386391285724552855)
          ·
            refine ⟨35013764079586928586829283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23342509386391285724552855 35013764079586928586829283)
            ·
              refine ⟨52520646119380392880243925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35013764079586928586829283 52520646119380392880243925)
              ·
                refine ⟨1230952643422977958130717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52520646119380392880243925 1230952643422977958130717)
                ·
                  refine ⟨461607241283616734299019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1230952643422977958130717 461607241283616734299019)
                  ·
                    rfl

theorem cell20_1011349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_1011349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011349 prefixEnd_1011349 := by exact prefixLift 1011349
  have htrace : WordTrace (prefixWord ++ tailWord_1011349) baseStart_1011349 baseEnd_1011349 := by
    simpa [prefixWord, tailWord_1011349, baseEnd_1011349] using wordTrace_append hprefix tailTrace_1011349
  have hstable : (prefixWord ++ tailWord_1011349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011349).length < 2 ^ (prefixWord ++ tailWord_1011349).sum := by decide
  have hdescent : baseEnd_1011349 < baseStart_1011349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011359 : List Nat := [1, 1, 2, 7, 1, 1, 1, 6]
def baseStart_1011359 : Nat := 118140960795 + 1011359 * 2 ^ 59
def prefixEnd_1011359 : Nat := 4983230072969 + 3 ^ 40 * 1011359 * 2
def baseEnd_1011359 : Nat := 153870601852033714655215

theorem tailTrace_1011359 : CollatzResearch.WordTrace tailWord_1011359 prefixEnd_1011359 153870601852033714655215 := by
  unfold tailWord_1011359
  simp only [CollatzResearch.WordTrace]
  refine ⟨36887293143026544210861131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24591528762017696140574087 36887293143026544210861131)
  ·
    refine ⟨55330939714539816316291697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36887293143026544210861131 55330939714539816316291697)
    ·
      refine ⟨41498204785904862237218773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55330939714539816316291697 41498204785904862237218773)
      ·
        refine ⟨972614174669645208684815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 41498204785904862237218773 972614174669645208684815)
        ·
          refine ⟨1458921262004467813027223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972614174669645208684815 1458921262004467813027223)
          ·
            refine ⟨2188381893006701719540835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458921262004467813027223 2188381893006701719540835)
            ·
              refine ⟨3282572839510052579311253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188381893006701719540835 3282572839510052579311253)
              ·
                refine ⟨153870601852033714655215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3282572839510052579311253 153870601852033714655215)
                ·
                  rfl

theorem cell20_1011359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 6].length) (baseStart_1011359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011359 prefixEnd_1011359 := by exact prefixLift 1011359
  have htrace : WordTrace (prefixWord ++ tailWord_1011359) baseStart_1011359 baseEnd_1011359 := by
    simpa [prefixWord, tailWord_1011359, baseEnd_1011359] using wordTrace_append hprefix tailTrace_1011359
  have hstable : (prefixWord ++ tailWord_1011359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011359).length < 2 ^ (prefixWord ++ tailWord_1011359).sum := by decide
  have hdescent : baseEnd_1011359 < baseStart_1011359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011363 : List Nat := [1, 1, 1, 4, 1, 1, 5, 6]
def baseStart_1011363 : Nat := 118140960795 + 1011363 * 2 ^ 59
def prefixEnd_1011363 : Nat := 4983230072969 + 3 ^ 40 * 1011363 * 2
def baseEnd_1011363 : Nat := 153871210421698302610765

theorem tailTrace_1011363 : CollatzResearch.WordTrace tailWord_1011363 prefixEnd_1011363 153871210421698302610765 := by
  unfold tailWord_1011363
  simp only [CollatzResearch.WordTrace]
  refine ⟨36887439035012052894006743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24591626023341368596004495 36887439035012052894006743)
  ·
    refine ⟨55331158552518079341010115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36887439035012052894006743 55331158552518079341010115)
    ·
      refine ⟨82996737828777119011515173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55331158552518079341010115 82996737828777119011515173)
      ·
        refine ⟨15561888342895709814659095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82996737828777119011515173 15561888342895709814659095)
        ·
          refine ⟨23342832514343564721988643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15561888342895709814659095 23342832514343564721988643)
          ·
            refine ⟨35014248771515347082982965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23342832514343564721988643 35014248771515347082982965)
            ·
              refine ⟨3282585822329563789029653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35014248771515347082982965 3282585822329563789029653)
              ·
                refine ⟨153871210421698302610765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3282585822329563789029653 153871210421698302610765)
                ·
                  rfl

theorem cell20_1011363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_1011363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011363 prefixEnd_1011363 := by exact prefixLift 1011363
  have htrace : WordTrace (prefixWord ++ tailWord_1011363) baseStart_1011363 baseEnd_1011363 := by
    simpa [prefixWord, tailWord_1011363, baseEnd_1011363] using wordTrace_append hprefix tailTrace_1011363
  have hstable : (prefixWord ++ tailWord_1011363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011363).length < 2 ^ (prefixWord ++ tailWord_1011363).sum := by decide
  have hdescent : baseEnd_1011363 < baseStart_1011363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011390 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_1011390 : Nat := 118140960795 + 1011390 * 2 ^ 59
def prefixEnd_1011390 : Nat := 4983230072969 + 3 ^ 40 * 1011390 * 2
def baseEnd_1011390 : Nat := 461625954800802813932185

theorem tailTrace_1011390 : CollatzResearch.WordTrace tailWord_1011390 prefixEnd_1011390 461625954800802813932185 := by
  unfold tailWord_1011390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4611052975739279563154953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24592282537276157670159749 4611052975739279563154953)
  ·
    refine ⟨3458289731804459672366215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4611052975739279563154953 3458289731804459672366215)
    ·
      refine ⟨5187434597706689508549323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3458289731804459672366215 5187434597706689508549323)
      ·
        refine ⟨7781151896560034262823985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5187434597706689508549323 7781151896560034262823985)
        ·
          refine ⟨5835863922420025697117989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7781151896560034262823985 5835863922420025697117989)
          ·
            refine ⟨1094224485453754818209623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5835863922420025697117989 1094224485453754818209623)
            ·
              refine ⟨1641336728180632227314435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094224485453754818209623 1641336728180632227314435)
              ·
                refine ⟨2462005092270948340971653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641336728180632227314435 2462005092270948340971653)
                ·
                  refine ⟨461625954800802813932185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2462005092270948340971653 461625954800802813932185)
                  ·
                    rfl

theorem cell20_1011390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_1011390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011390 prefixEnd_1011390 := by exact prefixLift 1011390
  have htrace : WordTrace (prefixWord ++ tailWord_1011390) baseStart_1011390 baseEnd_1011390 := by
    simpa [prefixWord, tailWord_1011390, baseEnd_1011390] using wordTrace_append hprefix tailTrace_1011390
  have hstable : (prefixWord ++ tailWord_1011390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011390).length < 2 ^ (prefixWord ++ tailWord_1011390).sum := by decide
  have hdescent : baseEnd_1011390 < baseStart_1011390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011408 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_1011408 : Nat := 118140960795 + 1011408 * 2 ^ 59
def prefixEnd_1011408 : Nat := 4983230072969 + 3 ^ 40 * 1011408 * 2
def baseEnd_1011408 : Nat := 461634170491274751332111

theorem tailTrace_1011408 : CollatzResearch.WordTrace tailWord_1011408 prefixEnd_1011408 461634170491274751332111 := by
  unfold tailWord_1011408
  simp only [CollatzResearch.WordTrace]
  refine ⟨18444540159924512789697439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24592720213232683719596585 18444540159924512789697439)
  ·
    refine ⟨27666810239886769184546159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18444540159924512789697439 27666810239886769184546159)
    ·
      refine ⟨41500215359830153776819239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27666810239886769184546159 41500215359830153776819239)
      ·
        refine ⟨62250323039745230665228859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41500215359830153776819239 62250323039745230665228859)
        ·
          refine ⟨93375484559617845997843289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62250323039745230665228859 93375484559617845997843289)
          ·
            refine ⟨70031613419713384498382467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93375484559617845997843289 70031613419713384498382467)
            ·
              refine ⟨105047420129570076747573701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70031613419713384498382467 105047420129570076747573701)
              ·
                refine ⟨19696391274294389390170069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105047420129570076747573701 19696391274294389390170069)
                ·
                  refine ⟨461634170491274751332111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19696391274294389390170069 461634170491274751332111)
                  ·
                    rfl

theorem cell20_1011408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_1011408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011408 prefixEnd_1011408 := by exact prefixLift 1011408
  have htrace : WordTrace (prefixWord ++ tailWord_1011408) baseStart_1011408 baseEnd_1011408 := by
    simpa [prefixWord, tailWord_1011408, baseEnd_1011408] using wordTrace_append hprefix tailTrace_1011408
  have hstable : (prefixWord ++ tailWord_1011408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011408).length < 2 ^ (prefixWord ++ tailWord_1011408).sum := by decide
  have hdescent : baseEnd_1011408 < baseStart_1011408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011442 : List Nat := [3, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_1011442 : Nat := 118140960795 + 1011442 * 2 ^ 59
def prefixEnd_1011442 : Nat := 4983230072969 + 3 ^ 40 * 1011442 * 2
def baseEnd_1011442 : Nat := 461649689017721744198639

theorem tailTrace_1011442 : CollatzResearch.WordTrace tailWord_1011442 prefixEnd_1011442 461649689017721744198639 := by
  unfold tailWord_1011442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9222580100431462346533145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24593546934483899590755053 9222580100431462346533145)
  ·
    refine ⟨6916935075323596759899859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9222580100431462346533145 6916935075323596759899859)
    ·
      refine ⟨10375402612985395139849789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6916935075323596759899859 10375402612985395139849789)
      ·
        refine ⟨3890775979869523177443671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10375402612985395139849789 3890775979869523177443671)
        ·
          refine ⟨5836163969804284766165507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3890775979869523177443671 5836163969804284766165507)
          ·
            refine ⟨8754245954706427149248261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836163969804284766165507 8754245954706427149248261)
            ·
              refine ⟨1641421116507455090484049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8754245954706427149248261 1641421116507455090484049)
              ·
                refine ⟨1231065837380591317863037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1641421116507455090484049 1231065837380591317863037)
                ·
                  refine ⟨461649689017721744198639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231065837380591317863037 461649689017721744198639)
                  ·
                    rfl

theorem cell20_1011442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_1011442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011442 prefixEnd_1011442 := by exact prefixLift 1011442
  have htrace : WordTrace (prefixWord ++ tailWord_1011442) baseStart_1011442 baseEnd_1011442 := by
    simpa [prefixWord, tailWord_1011442, baseEnd_1011442] using wordTrace_append hprefix tailTrace_1011442
  have hstable : (prefixWord ++ tailWord_1011442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011442).length < 2 ^ (prefixWord ++ tailWord_1011442).sum := by decide
  have hdescent : baseEnd_1011442 < baseStart_1011442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011470 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1011470 : Nat := 118140960795 + 1011470 * 2 ^ 59
def prefixEnd_1011470 : Nat := 4983230072969 + 3 ^ 40 * 1011470 * 2
def baseEnd_1011470 : Nat := 461662468980678091265191

theorem tailTrace_1011470 : CollatzResearch.WordTrace tailWord_1011470 prefixEnd_1011470 461662468980678091265191 := by
  unfold tailWord_1011470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4611417705703051271018983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24594227763749606778767909 4611417705703051271018983)
  ·
    refine ⟨6917126558554576906528475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4611417705703051271018983 6917126558554576906528475)
    ·
      refine ⟨10375689837831865359792713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6917126558554576906528475 10375689837831865359792713)
      ·
        refine ⟨7781767378373899019844535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10375689837831865359792713 7781767378373899019844535)
        ·
          refine ⟨11672651067560848529766803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781767378373899019844535 11672651067560848529766803)
          ·
            refine ⟨17508976601341272794650205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11672651067560848529766803 17508976601341272794650205)
            ·
              refine ⟨6565866225502977297993827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17508976601341272794650205 6565866225502977297993827)
              ·
                refine ⟨9848799338254465946990741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6565866225502977297993827 9848799338254465946990741)
                ·
                  refine ⟨461662468980678091265191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9848799338254465946990741 461662468980678091265191)
                  ·
                    rfl

theorem cell20_1011470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1011470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011470 prefixEnd_1011470 := by exact prefixLift 1011470
  have htrace : WordTrace (prefixWord ++ tailWord_1011470) baseStart_1011470 baseEnd_1011470 := by
    simpa [prefixWord, tailWord_1011470, baseEnd_1011470] using wordTrace_append hprefix tailTrace_1011470
  have hstable : (prefixWord ++ tailWord_1011470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011470).length < 2 ^ (prefixWord ++ tailWord_1011470).sum := by decide
  have hdescent : baseEnd_1011470 < baseStart_1011470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011532 : List Nat := [2, 2, 1, 3, 4, 1, 1, 6]
def baseStart_1011532 : Nat := 118140960795 + 1011532 * 2 ^ 59
def prefixEnd_1011532 : Nat := 4983230072969 + 3 ^ 40 * 1011532 * 2
def baseEnd_1011532 : Nat := 153896922490027143732757

theorem tailTrace_1011532 : CollatzResearch.WordTrace tailWord_1011532 prefixEnd_1011532 153896922490027143732757 := by
  unfold tailWord_1011532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18446801485699897378454425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24595735314266529837939233 18446801485699897378454425)
  ·
    refine ⟨13835101114274923033840819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18446801485699897378454425 13835101114274923033840819)
    ·
      refine ⟨20752651671412384550761229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13835101114274923033840819 20752651671412384550761229)
      ·
        refine ⟨7782244376779644206535461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20752651671412384550761229 7782244376779644206535461)
        ·
          refine ⟨1459170820646183288725399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7782244376779644206535461 1459170820646183288725399)
          ·
            refine ⟨2188756230969274933088099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459170820646183288725399 2188756230969274933088099)
            ·
              refine ⟨3283134346453912399632149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188756230969274933088099 3283134346453912399632149)
              ·
                refine ⟨153896922490027143732757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3283134346453912399632149 153896922490027143732757)
                ·
                  rfl

theorem cell20_1011532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_1011532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011532 prefixEnd_1011532 := by exact prefixLift 1011532
  have htrace : WordTrace (prefixWord ++ tailWord_1011532) baseStart_1011532 baseEnd_1011532 := by
    simpa [prefixWord, tailWord_1011532, baseEnd_1011532] using wordTrace_append hprefix tailTrace_1011532
  have hstable : (prefixWord ++ tailWord_1011532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011532).length < 2 ^ (prefixWord ++ tailWord_1011532).sum := by decide
  have hdescent : baseEnd_1011532 < baseStart_1011532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011577 : List Nat := [1, 2, 1, 3, 2, 2, 3, 3, 3]
def baseStart_1011577 : Nat := 118140960795 + 1011577 * 2 ^ 59
def prefixEnd_1011577 : Nat := 4983230072969 + 3 ^ 40 * 1011577 * 2
def baseEnd_1011577 : Nat := 461711306696261274698087

theorem tailTrace_1011577 : CollatzResearch.WordTrace tailWord_1011577 prefixEnd_1011577 461711306696261274698087 := by
  unfold tailWord_1011577
  simp only [CollatzResearch.WordTrace]
  refine ⟨36895244256236767442296985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24596829504157844961531323 36895244256236767442296985)
  ·
    refine ⟨27671433192177575581722739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36895244256236767442296985 27671433192177575581722739)
    ·
      refine ⟨41507149788266363372584109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27671433192177575581722739 41507149788266363372584109)
      ·
        refine ⟨15565181170599886264719041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41507149788266363372584109 15565181170599886264719041)
        ·
          refine ⟨11673885877949914698539281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15565181170599886264719041 11673885877949914698539281)
          ·
            refine ⟨8755414408462436023904461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11673885877949914698539281 8755414408462436023904461)
            ·
              refine ⟨3283280403173413508964173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8755414408462436023904461 3283280403173413508964173)
              ·
                refine ⟨1231230151190030065861565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3283280403173413508964173 1231230151190030065861565)
                ·
                  refine ⟨461711306696261274698087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231230151190030065861565 461711306696261274698087)
                  ·
                    rfl

theorem cell20_1011577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_1011577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011577 prefixEnd_1011577 := by exact prefixLift 1011577
  have htrace : WordTrace (prefixWord ++ tailWord_1011577) baseStart_1011577 baseEnd_1011577 := by
    simpa [prefixWord, tailWord_1011577, baseEnd_1011577] using wordTrace_append hprefix tailTrace_1011577
  have hstable : (prefixWord ++ tailWord_1011577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011577).length < 2 ^ (prefixWord ++ tailWord_1011577).sum := by decide
  have hdescent : baseEnd_1011577 < baseStart_1011577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011608 : List Nat := [2, 1, 2, 6, 1, 8]
def baseStart_1011608 : Nat := 118140960795 + 1011608 * 2 ^ 59
def prefixEnd_1011608 : Nat := 4983230072969 + 3 ^ 40 * 1011608 * 2
def baseEnd_1011608 : Nat := 17100942812628257209801

theorem tailTrace_1011608 : CollatzResearch.WordTrace tailWord_1011608 prefixEnd_1011608 17100942812628257209801 := by
  unfold tailWord_1011608
  simp only [CollatzResearch.WordTrace]
  refine ⟨18448187459562229868337739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24597583279416306491116985 18448187459562229868337739)
  ·
    refine ⟨27672281189343344802506609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18448187459562229868337739 27672281189343344802506609)
    ·
      refine ⟨20754210892007508601879957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27672281189343344802506609 20754210892007508601879957)
      ·
        refine ⟨972853635562851965713123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20754210892007508601879957 972853635562851965713123)
        ·
          refine ⟨1459280453344277948569685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972853635562851965713123 1459280453344277948569685)
          ·
            refine ⟨17100942812628257209801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1459280453344277948569685 17100942812628257209801)
            ·
              rfl

theorem cell20_1011608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 8].length) (baseStart_1011608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011608 prefixEnd_1011608 := by exact prefixLift 1011608
  have htrace : WordTrace (prefixWord ++ tailWord_1011608) baseStart_1011608 baseEnd_1011608 := by
    simpa [prefixWord, tailWord_1011608, baseEnd_1011608] using wordTrace_append hprefix tailTrace_1011608
  have hstable : (prefixWord ++ tailWord_1011608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011608).length < 2 ^ (prefixWord ++ tailWord_1011608).sum := by decide
  have hdescent : baseEnd_1011608 < baseStart_1011608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011614 : List Nat := [4, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_1011614 : Nat := 118140960795 + 1011614 * 2 ^ 59
def prefixEnd_1011614 : Nat := 4983230072969 + 3 ^ 40 * 1011614 * 2
def baseEnd_1011614 : Nat := 461728194504453590464603

theorem tailTrace_1011614 : CollatzResearch.WordTrace tailWord_1011614 prefixEnd_1011614 461728194504453590464603 := by
  unfold tailWord_1011614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4612074219637840345174237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24597729171401815174262597 4612074219637840345174237)
  ·
    refine ⟨1729527832364190129440339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4612074219637840345174237 1729527832364190129440339)
    ·
      refine ⟨2594291748546285194160509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1729527832364190129440339 2594291748546285194160509)
      ·
        refine ⟨972859405704856947810191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2594291748546285194160509 972859405704856947810191)
        ·
          refine ⟨1459289108557285421715287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972859405704856947810191 1459289108557285421715287)
          ·
            refine ⟨2188933662835928132572931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459289108557285421715287 2188933662835928132572931)
            ·
              refine ⟨3283400494253892198859397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188933662835928132572931 3283400494253892198859397)
              ·
                refine ⟨615637592672604787286137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3283400494253892198859397 615637592672604787286137)
                ·
                  refine ⟨461728194504453590464603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615637592672604787286137 461728194504453590464603)
                  ·
                    rfl

theorem cell20_1011614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_1011614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011614 prefixEnd_1011614 := by exact prefixLift 1011614
  have htrace : WordTrace (prefixWord ++ tailWord_1011614) baseStart_1011614 baseEnd_1011614 := by
    simpa [prefixWord, tailWord_1011614, baseEnd_1011614] using wordTrace_append hprefix tailTrace_1011614
  have hstable : (prefixWord ++ tailWord_1011614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011614).length < 2 ^ (prefixWord ++ tailWord_1011614).sum := by decide
  have hdescent : baseEnd_1011614 < baseStart_1011614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011643 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 6]
def baseStart_1011643 : Nat := 118140960795 + 1011643 * 2 ^ 59
def prefixEnd_1011643 : Nat := 4983230072969 + 3 ^ 40 * 1011643 * 2
def baseEnd_1011643 : Nat := 461741430894658378497817

theorem tailTrace_1011643 : CollatzResearch.WordTrace tailWord_1011643 prefixEnd_1011643 461741430894658378497817 := by
  unfold tailWord_1011643
  simp only [CollatzResearch.WordTrace]
  refine ⟨36897651473997660714199583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24598434315998440476133055 36897651473997660714199583)
  ·
    refine ⟨55346477210996491071299375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36897651473997660714199583 55346477210996491071299375)
    ·
      refine ⟨83019715816494736606949063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55346477210996491071299375 83019715816494736606949063)
      ·
        refine ⟨124529573724742104910423595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83019715816494736606949063 124529573724742104910423595)
        ·
          refine ⟨186794360587113157365635393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124529573724742104910423595 186794360587113157365635393)
          ·
            refine ⟨140095770440334868024226545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186794360587113157365635393 140095770440334868024226545)
            ·
              refine ⟨105071827830251151018169909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140095770440334868024226545 105071827830251151018169909)
              ·
                refine ⟨9850483859086045407953429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105071827830251151018169909 9850483859086045407953429)
                ·
                  refine ⟨461741430894658378497817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9850483859086045407953429 461741430894658378497817)
                  ·
                    rfl

theorem cell20_1011643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_1011643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011643 prefixEnd_1011643 := by exact prefixLift 1011643
  have htrace : WordTrace (prefixWord ++ tailWord_1011643) baseStart_1011643 baseEnd_1011643 := by
    simpa [prefixWord, tailWord_1011643, baseEnd_1011643] using wordTrace_append hprefix tailTrace_1011643
  have hstable : (prefixWord ++ tailWord_1011643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011643).length < 2 ^ (prefixWord ++ tailWord_1011643).sum := by decide
  have hdescent : baseEnd_1011643 < baseStart_1011643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011656 : List Nat := [2, 1, 3, 1, 4, 2, 2, 3, 2]
def baseStart_1011656 : Nat := 118140960795 + 1011656 * 2 ^ 59
def prefixEnd_1011656 : Nat := 4983230072969 + 3 ^ 40 * 1011656 * 2
def baseEnd_1011656 : Nat := 461747364448888111064431

theorem tailTrace_1011656 : CollatzResearch.WordTrace tailWord_1011656 prefixEnd_1011656 461747364448888111064431 := by
  unfold tailWord_1011656
  simp only [CollatzResearch.WordTrace]
  refine ⟨18449062811475281967211411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24598750415300375956281881 18449062811475281967211411)
  ·
    refine ⟨27673594217212922950817117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18449062811475281967211411 27673594217212922950817117)
    ·
      refine ⟨10377597831454846106556419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27673594217212922950817117 10377597831454846106556419)
      ·
        refine ⟨15566396747182269159834629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10377597831454846106556419 15566396747182269159834629)
        ·
          refine ⟨2918699390096675467468993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15566396747182269159834629 2918699390096675467468993)
          ·
            refine ⟨2189024542572506600601745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2918699390096675467468993 2189024542572506600601745)
            ·
              refine ⟨1641768406929379950451309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189024542572506600601745 1641768406929379950451309)
              ·
                refine ⟨615663152598517481419241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1641768406929379950451309 615663152598517481419241)
                ·
                  refine ⟨461747364448888111064431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615663152598517481419241 461747364448888111064431)
                  ·
                    rfl

theorem cell20_1011656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 2].length) (baseStart_1011656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011656 prefixEnd_1011656 := by exact prefixLift 1011656
  have htrace : WordTrace (prefixWord ++ tailWord_1011656) baseStart_1011656 baseEnd_1011656 := by
    simpa [prefixWord, tailWord_1011656, baseEnd_1011656] using wordTrace_append hprefix tailTrace_1011656
  have hstable : (prefixWord ++ tailWord_1011656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011656).length < 2 ^ (prefixWord ++ tailWord_1011656).sum := by decide
  have hdescent : baseEnd_1011656 < baseStart_1011656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011666 : List Nat := [3, 2, 2, 3, 3, 1, 1, 2, 3]
def baseStart_1011666 : Nat := 118140960795 + 1011666 * 2 ^ 59
def prefixEnd_1011666 : Nat := 4983230072969 + 3 ^ 40 * 1011666 * 2
def baseEnd_1011666 : Nat := 461751928721372520731057

theorem tailTrace_1011666 : CollatzResearch.WordTrace tailWord_1011666 prefixEnd_1011666 461751928721372520731057 := by
  unfold tailWord_1011666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9224622588228583910571713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24598993568609557094857901 9224622588228583910571713)
  ·
    refine ⟨6918466941171437932928785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9224622588228583910571713 6918466941171437932928785)
    ·
      refine ⟨5188850205878578449696589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6918466941171437932928785 5188850205878578449696589)
      ·
        refine ⟨1945818827204466918636221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5188850205878578449696589 1945818827204466918636221)
        ·
          refine ⟨729682060201675094488583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1945818827204466918636221 729682060201675094488583)
          ·
            refine ⟨1094523090302512641732875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729682060201675094488583 1094523090302512641732875)
            ·
              refine ⟨1641784635453768962599313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094523090302512641732875 1641784635453768962599313)
              ·
                refine ⟨1231338476590326721949485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1641784635453768962599313 1231338476590326721949485)
                ·
                  refine ⟨461751928721372520731057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231338476590326721949485 461751928721372520731057)
                  ·
                    rfl

theorem cell20_1011666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_1011666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011666 prefixEnd_1011666 := by exact prefixLift 1011666
  have htrace : WordTrace (prefixWord ++ tailWord_1011666) baseStart_1011666 baseEnd_1011666 := by
    simpa [prefixWord, tailWord_1011666, baseEnd_1011666] using wordTrace_append hprefix tailTrace_1011666
  have hstable : (prefixWord ++ tailWord_1011666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011666).length < 2 ^ (prefixWord ++ tailWord_1011666).sum := by decide
  have hdescent : baseEnd_1011666 < baseStart_1011666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011687 : List Nat := [1, 1, 5, 2, 3, 1, 3, 1, 3]
def baseStart_1011687 : Nat := 118140960795 + 1011687 * 2 ^ 59
def prefixEnd_1011687 : Nat := 4983230072969 + 3 ^ 40 * 1011687 * 2
def baseEnd_1011687 : Nat := 461761513693589781030971

theorem tailTrace_1011687 : CollatzResearch.WordTrace tailWord_1011687 prefixEnd_1011687 461761513693589781030971 := by
  unfold tailWord_1011687
  simp only [CollatzResearch.WordTrace]
  refine ⟨36899256285838256228801315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24599504190558837485867543 36899256285838256228801315)
  ·
    refine ⟨55348884428757384343201973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36899256285838256228801315 55348884428757384343201973)
    ·
      refine ⟨5188957915196004782175185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55348884428757384343201973 5188957915196004782175185)
      ·
        refine ⟨3891718436397003586631389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5188957915196004782175185 3891718436397003586631389)
        ·
          refine ⟨1459394413648876344986771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3891718436397003586631389 1459394413648876344986771)
          ·
            refine ⟨2189091620473314517480157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459394413648876344986771 2189091620473314517480157)
            ·
              refine ⟨820909357677492944055059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2189091620473314517480157 820909357677492944055059)
              ·
                refine ⟨1231364036516239416082589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820909357677492944055059 1231364036516239416082589)
                ·
                  refine ⟨461761513693589781030971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231364036516239416082589 461761513693589781030971)
                  ·
                    rfl

theorem cell20_1011687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 3].length) (baseStart_1011687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011687 prefixEnd_1011687 := by exact prefixLift 1011687
  have htrace : WordTrace (prefixWord ++ tailWord_1011687) baseStart_1011687 baseEnd_1011687 := by
    simpa [prefixWord, tailWord_1011687, baseEnd_1011687] using wordTrace_append hprefix tailTrace_1011687
  have hstable : (prefixWord ++ tailWord_1011687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011687).length < 2 ^ (prefixWord ++ tailWord_1011687).sum := by decide
  have hdescent : baseEnd_1011687 < baseStart_1011687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011705 : List Nat := [1, 2, 1, 3, 1, 5, 1, 6]
def baseStart_1011705 : Nat := 118140960795 + 1011705 * 2 ^ 59
def prefixEnd_1011705 : Nat := 4983230072969 + 3 ^ 40 * 1011705 * 2
def baseEnd_1011705 : Nat := 153923243128020572810299

theorem tailTrace_1011705 : CollatzResearch.WordTrace tailWord_1011705 prefixEnd_1011705 153923243128020572810299 := by
  unfold tailWord_1011705
  simp only [CollatzResearch.WordTrace]
  refine ⟨36899912799773045302956569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24599941866515363535304379 36899912799773045302956569)
  ·
    refine ⟨27674934599829783977217427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36899912799773045302956569 27674934599829783977217427)
    ·
      refine ⟨41512401899744675965826141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27674934599829783977217427 41512401899744675965826141)
      ·
        refine ⟨15567150712404253487184803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41512401899744675965826141 15567150712404253487184803)
        ·
          refine ⟨23350726068606380230777205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15567150712404253487184803 23350726068606380230777205)
          ·
            refine ⟨2189130568931848146635363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23350726068606380230777205 2189130568931848146635363)
            ·
              refine ⟨3283695853397772219953045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189130568931848146635363 3283695853397772219953045)
              ·
                refine ⟨153923243128020572810299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3283695853397772219953045 153923243128020572810299)
                ·
                  rfl

theorem cell20_1011705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_1011705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011705 prefixEnd_1011705 := by exact prefixLift 1011705
  have htrace : WordTrace (prefixWord ++ tailWord_1011705) baseStart_1011705 baseEnd_1011705 := by
    simpa [prefixWord, tailWord_1011705, baseEnd_1011705] using wordTrace_append hprefix tailTrace_1011705
  have hstable : (prefixWord ++ tailWord_1011705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011705).length < 2 ^ (prefixWord ++ tailWord_1011705).sum := by decide
  have hdescent : baseEnd_1011705 < baseStart_1011705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011722 : List Nat := [3, 1, 2, 2, 4, 2, 6]
def baseStart_1011722 : Nat := 118140960795 + 1011722 * 2 ^ 59
def prefixEnd_1011722 : Nat := 4983230072969 + 3 ^ 40 * 1011722 * 2
def baseEnd_1011722 : Nat := 51308609849698357207129

theorem tailTrace_1011722 : CollatzResearch.WordTrace tailWord_1011722 prefixEnd_1011722 51308609849698357207129 := by
  unfold tailWord_1011722
  simp only [CollatzResearch.WordTrace]
  refine ⟨9225133210177864301581355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24600355227140971470883613 9225133210177864301581355)
  ·
    refine ⟨13837699815266796452372033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9225133210177864301581355 13837699815266796452372033)
    ·
      refine ⟨10378274861450097339279025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13837699815266796452372033 10378274861450097339279025)
      ·
        refine ⟨7783706146087573004459269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10378274861450097339279025 7783706146087573004459269)
        ·
          refine ⟨1459444902391419938336113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7783706146087573004459269 1459444902391419938336113)
          ·
            refine ⟨1094583676793564953752085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1459444902391419938336113 1094583676793564953752085)
            ·
              refine ⟨51308609849698357207129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1094583676793564953752085 51308609849698357207129)
              ·
                rfl

theorem cell20_1011722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 6].length) (baseStart_1011722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011722 prefixEnd_1011722 := by exact prefixLift 1011722
  have htrace : WordTrace (prefixWord ++ tailWord_1011722) baseStart_1011722 baseEnd_1011722 := by
    simpa [prefixWord, tailWord_1011722, baseEnd_1011722] using wordTrace_append hprefix tailTrace_1011722
  have hstable : (prefixWord ++ tailWord_1011722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011722).length < 2 ^ (prefixWord ++ tailWord_1011722).sum := by decide
  have hdescent : baseEnd_1011722 < baseStart_1011722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011743 : List Nat := [1, 1, 2, 4, 1, 2, 4, 5]
def baseStart_1011743 : Nat := 118140960795 + 1011743 * 2 ^ 59
def prefixEnd_1011743 : Nat := 4983230072969 + 3 ^ 40 * 1011743 * 2
def baseEnd_1011743 : Nat := 153929024539834158388025

theorem tailTrace_1011743 : CollatzResearch.WordTrace tailWord_1011743 prefixEnd_1011743 153929024539834158388025 := by
  unfold tailWord_1011743
  simp only [CollatzResearch.WordTrace]
  refine ⟨36901298773635377792839883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24600865849090251861893255 36901298773635377792839883)
  ·
    refine ⟨55351948160453066689259825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36901298773635377792839883 55351948160453066689259825)
    ·
      refine ⟨41513961120339800016944869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55351948160453066689259825 41513961120339800016944869)
      ·
        refine ⟨7783867710063712503177163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41513961120339800016944869 7783867710063712503177163)
        ·
          refine ⟨11675801565095568754765745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7783867710063712503177163 11675801565095568754765745)
          ·
            refine ⟨8756851173821676566074309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11675801565095568754765745 8756851173821676566074309)
            ·
              refine ⟨1641909595091564356138933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8756851173821676566074309 1641909595091564356138933)
              ·
                refine ⟨153929024539834158388025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1641909595091564356138933 153929024539834158388025)
                ·
                  rfl

theorem cell20_1011743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_1011743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011743 prefixEnd_1011743 := by exact prefixLift 1011743
  have htrace : WordTrace (prefixWord ++ tailWord_1011743) baseStart_1011743 baseEnd_1011743 := by
    simpa [prefixWord, tailWord_1011743, baseEnd_1011743] using wordTrace_append hprefix tailTrace_1011743
  have hstable : (prefixWord ++ tailWord_1011743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011743).length < 2 ^ (prefixWord ++ tailWord_1011743).sum := by decide
  have hdescent : baseEnd_1011743 < baseStart_1011743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011788 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1011788 : Nat := 118140960795 + 1011788 * 2 ^ 59
def prefixEnd_1011788 : Nat := 4983230072969 + 3 ^ 40 * 1011788 * 2
def baseEnd_1011788 : Nat := 461807612845682318663891

theorem tailTrace_1011788 : CollatzResearch.WordTrace tailWord_1011788 prefixEnd_1011788 461807612845682318663891 := by
  unfold tailWord_1011788
  simp only [CollatzResearch.WordTrace]
  refine ⟨18451470029236175239114009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24601960038981566985485345 18451470029236175239114009)
  ·
    refine ⟨13838602521927131429335507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18451470029236175239114009 13838602521927131429335507)
    ·
      refine ⟨20757903782890697144003261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13838602521927131429335507 20757903782890697144003261)
      ·
        refine ⟨7784213918584011429001223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20757903782890697144003261 7784213918584011429001223)
        ·
          refine ⟨11676320877876017143501835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7784213918584011429001223 11676320877876017143501835)
          ·
            refine ⟨17514481316814025715252753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11676320877876017143501835 17514481316814025715252753)
            ·
              refine ⟨13135860987610519286439565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17514481316814025715252753 13135860987610519286439565)
              ·
                refine ⟨4925947870353944732414837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13135860987610519286439565 4925947870353944732414837)
                ·
                  refine ⟨461807612845682318663891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4925947870353944732414837 461807612845682318663891)
                  ·
                    rfl

theorem cell20_1011788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1011788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011788 prefixEnd_1011788 := by exact prefixLift 1011788
  have htrace : WordTrace (prefixWord ++ tailWord_1011788) baseStart_1011788 baseEnd_1011788 := by
    simpa [prefixWord, tailWord_1011788, baseEnd_1011788] using wordTrace_append hprefix tailTrace_1011788
  have hstable : (prefixWord ++ tailWord_1011788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011788).length < 2 ^ (prefixWord ++ tailWord_1011788).sum := by decide
  have hdescent : baseEnd_1011788 < baseStart_1011788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011843 : List Nat := [1, 1, 1, 3, 3, 3, 3, 2, 3]
def baseStart_1011843 : Nat := 118140960795 + 1011843 * 2 ^ 59
def prefixEnd_1011843 : Nat := 4983230072969 + 3 ^ 40 * 1011843 * 2
def baseEnd_1011843 : Nat := 461832716344346571830333

theorem tailTrace_1011843 : CollatzResearch.WordTrace tailWord_1011843 prefixEnd_1011843 461832716344346571830333 := by
  unfold tailWord_1011843
  simp only [CollatzResearch.WordTrace]
  refine ⟨36904946073273094871480183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24603297382182063247653455 36904946073273094871480183)
  ·
    refine ⟨55357419109909642307220275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36904946073273094871480183 55357419109909642307220275)
    ·
      refine ⟨83036128664864463460830413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55357419109909642307220275 83036128664864463460830413)
      ·
        refine ⟨31138548249324173797811405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83036128664864463460830413 31138548249324173797811405)
        ·
          refine ⟨11676955593496565174179277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31138548249324173797811405 11676955593496565174179277)
          ·
            refine ⟨4378858347561211940317229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11676955593496565174179277 4378858347561211940317229)
            ·
              refine ⟨1642071880335454477618961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4378858347561211940317229 1642071880335454477618961)
              ·
                refine ⟨1231553910251590858214221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642071880335454477618961 1231553910251590858214221)
                ·
                  refine ⟨461832716344346571830333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231553910251590858214221 461832716344346571830333)
                  ·
                    rfl

theorem cell20_1011843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 3].length) (baseStart_1011843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011843 prefixEnd_1011843 := by exact prefixLift 1011843
  have htrace : WordTrace (prefixWord ++ tailWord_1011843) baseStart_1011843 baseEnd_1011843 := by
    simpa [prefixWord, tailWord_1011843, baseEnd_1011843] using wordTrace_append hprefix tailTrace_1011843
  have hstable : (prefixWord ++ tailWord_1011843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011843).length < 2 ^ (prefixWord ++ tailWord_1011843).sum := by decide
  have hdescent : baseEnd_1011843 < baseStart_1011843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011850 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_1011850 : Nat := 118140960795 + 1011850 * 2 ^ 59
def prefixEnd_1011850 : Nat := 4983230072969 + 3 ^ 40 * 1011850 * 2
def baseEnd_1011850 : Nat := 461835911335085658596971

theorem tailTrace_1011850 : CollatzResearch.WordTrace tailWord_1011850 prefixEnd_1011850 461835911335085658596971 := by
  unfold tailWord_1011850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226300346061933766746251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24603467589498490044656669 9226300346061933766746251)
  ·
    refine ⟨13839450519092900650119377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9226300346061933766746251 13839450519092900650119377)
    ·
      refine ⟨10379587889319675487589533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13839450519092900650119377 10379587889319675487589533)
      ·
        refine ⟨3892345458494878307846075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10379587889319675487589533 3892345458494878307846075)
        ·
          refine ⟨5838518187742317461769113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892345458494878307846075 5838518187742317461769113)
          ·
            refine ⟨4378888640806738096326835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5838518187742317461769113 4378888640806738096326835)
            ·
              refine ⟨6568332961210107144490253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378888640806738096326835 6568332961210107144490253)
              ·
                refine ⟨2463124860453790179183845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6568332961210107144490253 2463124860453790179183845)
                ·
                  refine ⟨461835911335085658596971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2463124860453790179183845 461835911335085658596971)
                  ·
                    rfl

theorem cell20_1011850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_1011850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011850 prefixEnd_1011850 := by exact prefixLift 1011850
  have htrace : WordTrace (prefixWord ++ tailWord_1011850) baseStart_1011850 baseEnd_1011850 := by
    simpa [prefixWord, tailWord_1011850, baseEnd_1011850] using wordTrace_append hprefix tailTrace_1011850
  have hstable : (prefixWord ++ tailWord_1011850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011850).length < 2 ^ (prefixWord ++ tailWord_1011850).sum := by decide
  have hdescent : baseEnd_1011850 < baseStart_1011850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011870 : List Nat := [4, 3, 1, 1, 3, 2, 2, 4]
def baseStart_1011870 : Nat := 118140960795 + 1011870 * 2 ^ 59
def prefixEnd_1011870 : Nat := 4983230072969 + 3 ^ 40 * 1011870 * 2
def baseEnd_1011870 : Nat := 153948346626684825976741

theorem tailTrace_1011870 : CollatzResearch.WordTrace tailWord_1011870 prefixEnd_1011870 153948346626684825976741 := by
  unfold tailWord_1011870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4613241355521909810339133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24603953896116852321808709 4613241355521909810339133)
  ·
    refine ⟨1729965508320716178877175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4613241355521909810339133 1729965508320716178877175)
    ·
      refine ⟨2594948262481074268315763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1729965508320716178877175 2594948262481074268315763)
      ·
        refine ⟨3892422393721611402473645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2594948262481074268315763 3892422393721611402473645)
        ·
          refine ⟨1459658397645604275927617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3892422393721611402473645 1459658397645604275927617)
          ·
            refine ⟨1094743798234203206945713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1459658397645604275927617 1094743798234203206945713)
            ·
              refine ⟨821057848675652405209285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094743798234203206945713 821057848675652405209285)
              ·
                refine ⟨153948346626684825976741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 821057848675652405209285 153948346626684825976741)
                ·
                  rfl

theorem cell20_1011870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_1011870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011870 prefixEnd_1011870 := by exact prefixLift 1011870
  have htrace : WordTrace (prefixWord ++ tailWord_1011870) baseStart_1011870 baseEnd_1011870 := by
    simpa [prefixWord, tailWord_1011870, baseEnd_1011870] using wordTrace_append hprefix tailTrace_1011870
  have hstable : (prefixWord ++ tailWord_1011870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011870).length < 2 ^ (prefixWord ++ tailWord_1011870).sum := by decide
  have hdescent : baseEnd_1011870 < baseStart_1011870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011874 : List Nat := [3, 3, 1, 3, 1, 2, 1, 6]
def baseStart_1011874 : Nat := 118140960795 + 1011874 * 2 ^ 59
def prefixEnd_1011874 : Nat := 4983230072969 + 3 ^ 40 * 1011874 * 2
def baseEnd_1011874 : Nat := 153948955196349413932291

theorem tailTrace_1011874 : CollatzResearch.WordTrace tailWord_1011874 prefixEnd_1011874 153948955196349413932291 := by
  unfold tailWord_1011874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226519184040196791464669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24604051157440524777239117 9226519184040196791464669)
  ·
    refine ⟨3459944694015073796799251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9226519184040196791464669 3459944694015073796799251)
    ·
      refine ⟨5189917041022610695198877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3459944694015073796799251 5189917041022610695198877)
      ·
        refine ⟨1946218890383479010699579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5189917041022610695198877 1946218890383479010699579)
        ·
          refine ⟨2919328335575218516049369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946218890383479010699579 2919328335575218516049369)
          ·
            refine ⟨2189496251681413887037027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2919328335575218516049369 2189496251681413887037027)
            ·
              refine ⟨3284244377522120830555541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189496251681413887037027 3284244377522120830555541)
              ·
                refine ⟨153948955196349413932291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3284244377522120830555541 153948955196349413932291)
                ·
                  rfl

theorem cell20_1011874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_1011874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011874 prefixEnd_1011874 := by exact prefixLift 1011874
  have htrace : WordTrace (prefixWord ++ tailWord_1011874) baseStart_1011874 baseEnd_1011874 := by
    simpa [prefixWord, tailWord_1011874, baseEnd_1011874] using wordTrace_append hprefix tailTrace_1011874
  have hstable : (prefixWord ++ tailWord_1011874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011874).length < 2 ^ (prefixWord ++ tailWord_1011874).sum := by decide
  have hdescent : baseEnd_1011874 < baseStart_1011874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011895 : List Nat := [1, 1, 3, 1, 4, 4, 6]
def baseStart_1011895 : Nat := 118140960795 + 1011895 * 2 ^ 59
def prefixEnd_1011895 : Nat := 4983230072969 + 3 ^ 40 * 1011895 * 2
def baseEnd_1011895 : Nat := 51317383395696166899643

theorem tailTrace_1011895 : CollatzResearch.WordTrace tailWord_1011895 prefixEnd_1011895 51317383395696166899643 := by
  unfold tailWord_1011895
  simp only [CollatzResearch.WordTrace]
  refine ⟨36906842669084707752373139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24604561779389805168248759 36906842669084707752373139)
  ·
    refine ⟨55360264003627061628559709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36906842669084707752373139 55360264003627061628559709)
    ·
      refine ⟨20760099001360148110709891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55360264003627061628559709 20760099001360148110709891)
      ·
        refine ⟨31140148502040222166064837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20760099001360148110709891 31140148502040222166064837)
        ·
          refine ⟨5838777844132541656137157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31140148502040222166064837 5838777844132541656137157)
          ·
            refine ⟨1094770845774851560525717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5838777844132541656137157 1094770845774851560525717)
            ·
              refine ⟨51317383395696166899643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1094770845774851560525717 51317383395696166899643)
              ·
                rfl

theorem cell20_1011895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 6].length) (baseStart_1011895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011895 prefixEnd_1011895 := by exact prefixLift 1011895
  have htrace : WordTrace (prefixWord ++ tailWord_1011895) baseStart_1011895 baseEnd_1011895 := by
    simpa [prefixWord, tailWord_1011895, baseEnd_1011895] using wordTrace_append hprefix tailTrace_1011895
  have hstable : (prefixWord ++ tailWord_1011895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011895).length < 2 ^ (prefixWord ++ tailWord_1011895).sum := by decide
  have hdescent : baseEnd_1011895 < baseStart_1011895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011985 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 6]
def baseStart_1011985 : Nat := 118140960795 + 1011985 * 2 ^ 59
def prefixEnd_1011985 : Nat := 4983230072969 + 3 ^ 40 * 1011985 * 2
def baseEnd_1011985 : Nat := 461897529013625189096419

theorem tailTrace_1011985 : CollatzResearch.WordTrace tailWord_1011985 prefixEnd_1011985 461897529013625189096419 := by
  unfold tailWord_1011985
  simp only [CollatzResearch.WordTrace]
  refine ⟨36910125238758653123149409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24606750159172435415432939 36910125238758653123149409)
  ·
    refine ⟨27682593929068989842362057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36910125238758653123149409 27682593929068989842362057)
    ·
      refine ⟨20761945446801742381771543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27682593929068989842362057 20761945446801742381771543)
      ·
        refine ⟨31142918170202613572657315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20761945446801742381771543 31142918170202613572657315)
        ·
          refine ⟨46714377255303920358985973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31142918170202613572657315 46714377255303920358985973)
          ·
            refine ⟨4379472867684742533654935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46714377255303920358985973 4379472867684742533654935)
            ·
              refine ⟨6569209301527113800482403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379472867684742533654935 6569209301527113800482403)
              ·
                refine ⟨9853813952290670700723605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6569209301527113800482403 9853813952290670700723605)
                ·
                  refine ⟨461897529013625189096419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9853813952290670700723605 461897529013625189096419)
                  ·
                    rfl

theorem cell20_1011985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_1011985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1011985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1011985 prefixEnd_1011985 := by exact prefixLift 1011985
  have htrace : WordTrace (prefixWord ++ tailWord_1011985) baseStart_1011985 baseEnd_1011985 := by
    simpa [prefixWord, tailWord_1011985, baseEnd_1011985] using wordTrace_append hprefix tailTrace_1011985
  have hstable : (prefixWord ++ tailWord_1011985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011985).length < 2 ^ (prefixWord ++ tailWord_1011985).sum := by decide
  have hdescent : baseEnd_1011985 < baseStart_1011985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012016 : List Nat := [2, 1, 1, 1, 2, 2, 2, 6, 3]
def baseStart_1012016 : Nat := 118140960795 + 1012016 * 2 ^ 59
def prefixEnd_1012016 : Nat := 4983230072969 + 3 ^ 40 * 1012016 * 2
def baseEnd_1012016 : Nat := 461911678258326859062959

theorem tailTrace_1012016 : CollatzResearch.WordTrace tailWord_1012016 prefixEnd_1012016 461911678258326859062959 := by
  unfold tailWord_1012016
  simp only [CollatzResearch.WordTrace]
  refine ⟨18455627950823172708763951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24607503934430896945018601 18455627950823172708763951)
  ·
    refine ⟨27683441926234759063145927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18455627950823172708763951 27683441926234759063145927)
    ·
      refine ⟨41525162889352138594718891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27683441926234759063145927 41525162889352138594718891)
      ·
        refine ⟨62287744334028207892078337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41525162889352138594718891 62287744334028207892078337)
        ·
          refine ⟨46715808250521155919058753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62287744334028207892078337 46715808250521155919058753)
          ·
            refine ⟨35036856187890866939294065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46715808250521155919058753 35036856187890866939294065)
            ·
              refine ⟨26277642140918150204470549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35036856187890866939294065 26277642140918150204470549)
              ·
                refine ⟨1231764475355538290834557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26277642140918150204470549 1231764475355538290834557)
                ·
                  refine ⟨461911678258326859062959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231764475355538290834557 461911678258326859062959)
                  ·
                    rfl

theorem cell20_1012016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_1012016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012016 prefixEnd_1012016 := by exact prefixLift 1012016
  have htrace : WordTrace (prefixWord ++ tailWord_1012016) baseStart_1012016 baseEnd_1012016 := by
    simpa [prefixWord, tailWord_1012016, baseEnd_1012016] using wordTrace_append hprefix tailTrace_1012016
  have hstable : (prefixWord ++ tailWord_1012016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012016).length < 2 ^ (prefixWord ++ tailWord_1012016).sum := by decide
  have hdescent : baseEnd_1012016 < baseStart_1012016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012053 : List Nat := [1, 3, 2, 2, 5, 1, 1, 3, 2]
def baseStart_1012053 : Nat := 118140960795 + 1012053 * 2 ^ 59
def prefixEnd_1012053 : Nat := 4983230072969 + 3 ^ 40 * 1012053 * 2
def baseEnd_1012053 : Nat := 461928566066519174829475

theorem tailTrace_1012053 : CollatzResearch.WordTrace tailWord_1012053 prefixEnd_1012053 461928566066519174829475 := by
  unfold tailWord_1012053
  simp only [CollatzResearch.WordTrace]
  refine ⟨36912605402512300736624813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24608403601674867157749875 36912605402512300736624813)
  ·
    refine ⟨13842227025942112776234305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36912605402512300736624813 13842227025942112776234305)
    ·
      refine ⟨10381670269456584582175729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13842227025942112776234305 10381670269456584582175729)
      ·
        refine ⟨7786252702092438436631797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10381670269456584582175729 7786252702092438436631797)
        ·
          refine ⟨729961190821166103434231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7786252702092438436631797 729961190821166103434231)
          ·
            refine ⟨1094941786231749155151347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729961190821166103434231 1094941786231749155151347)
            ·
              refine ⟨1642412679347623732727021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094941786231749155151347 1642412679347623732727021)
              ·
                refine ⟨615904754755358899772633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1642412679347623732727021 615904754755358899772633)
                ·
                  refine ⟨461928566066519174829475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615904754755358899772633 461928566066519174829475)
                  ·
                    rfl

theorem cell20_1012053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_1012053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012053 prefixEnd_1012053 := by exact prefixLift 1012053
  have htrace : WordTrace (prefixWord ++ tailWord_1012053) baseStart_1012053 baseEnd_1012053 := by
    simpa [prefixWord, tailWord_1012053, baseEnd_1012053] using wordTrace_append hprefix tailTrace_1012053
  have hstable : (prefixWord ++ tailWord_1012053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012053).length < 2 ^ (prefixWord ++ tailWord_1012053).sum := by decide
  have hdescent : baseEnd_1012053 < baseStart_1012053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012064 : List Nat := [2, 1, 1, 3, 6, 1, 6]
def baseStart_1012064 : Nat := 118140960795 + 1012064 * 2 ^ 59
def prefixEnd_1012064 : Nat := 4983230072969 + 3 ^ 40 * 1012064 * 2
def baseEnd_1012064 : Nat := 51325954085139113940307

theorem tailTrace_1012064 : CollatzResearch.WordTrace tailWord_1012064 prefixEnd_1012064 51325954085139113940307 := by
  unfold tailWord_1012064
  simp only [CollatzResearch.WordTrace]
  refine ⟨18456503302736224807637623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24608671070314966410183497 18456503302736224807637623)
  ·
    refine ⟨27684754954104337211456435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18456503302736224807637623 27684754954104337211456435)
    ·
      refine ⟨41527132431156505817184653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27684754954104337211456435 41527132431156505817184653)
      ·
        refine ⟨15572674661683689681444245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41527132431156505817184653 15572674661683689681444245)
        ·
          refine ⟨729969124766422953817699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15572674661683689681444245 729969124766422953817699)
          ·
            refine ⟨1094953687149634430726549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729969124766422953817699 1094953687149634430726549)
            ·
              refine ⟨51325954085139113940307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1094953687149634430726549 51325954085139113940307)
              ·
                rfl

theorem cell20_1012064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 6].length) (baseStart_1012064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012064 prefixEnd_1012064 := by exact prefixLift 1012064
  have htrace : WordTrace (prefixWord ++ tailWord_1012064) baseStart_1012064 baseEnd_1012064 := by
    simpa [prefixWord, tailWord_1012064, baseEnd_1012064] using wordTrace_append hprefix tailTrace_1012064
  have hstable : (prefixWord ++ tailWord_1012064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012064).length < 2 ^ (prefixWord ++ tailWord_1012064).sum := by decide
  have hdescent : baseEnd_1012064 < baseStart_1012064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012085 : List Nat := [1, 3, 4, 1, 2, 1, 1, 7]
def baseStart_1012085 : Nat := 118140960795 + 1012085 * 2 ^ 59
def prefixEnd_1012085 : Nat := 4983230072969 + 3 ^ 40 * 1012085 * 2
def baseEnd_1012085 : Nat := 153981057246156428587559

theorem tailTrace_1012085 : CollatzResearch.WordTrace tailWord_1012085 prefixEnd_1012085 153981057246156428587559 := by
  unfold tailWord_1012085
  simp only [CollatzResearch.WordTrace]
  refine ⟨36913772538396370201789709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24609181692264246801193139 36913772538396370201789709)
  ·
    refine ⟨13842664701898638825671141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36913772538396370201789709 13842664701898638825671141)
    ·
      refine ⟨2595499631605994779813339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13842664701898638825671141 2595499631605994779813339)
      ·
        refine ⟨3893249447408992169720009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595499631605994779813339 3893249447408992169720009)
        ·
          refine ⟨2919937085556744127290007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3893249447408992169720009 2919937085556744127290007)
          ·
            refine ⟨4379905628335116190935011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919937085556744127290007 4379905628335116190935011)
            ·
              refine ⟨6569858442502674286402517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379905628335116190935011 6569858442502674286402517)
              ·
                refine ⟨153981057246156428587559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6569858442502674286402517 153981057246156428587559)
                ·
                  rfl

theorem cell20_1012085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_1012085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012085 prefixEnd_1012085 := by exact prefixLift 1012085
  have htrace : WordTrace (prefixWord ++ tailWord_1012085) baseStart_1012085 baseEnd_1012085 := by
    simpa [prefixWord, tailWord_1012085, baseEnd_1012085] using wordTrace_append hprefix tailTrace_1012085
  have hstable : (prefixWord ++ tailWord_1012085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012085).length < 2 ^ (prefixWord ++ tailWord_1012085).sum := by decide
  have hdescent : baseEnd_1012085 < baseStart_1012085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012126 : List Nat := [4, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1012126 : Nat := 118140960795 + 1012126 * 2 ^ 59
def prefixEnd_1012126 : Nat := 4983230072969 + 3 ^ 40 * 1012126 * 2
def baseEnd_1012126 : Nat := 461961885255655365395843

theorem tailTrace_1012126 : CollatzResearch.WordTrace tailWord_1012126 prefixEnd_1012126 461961885255655365395843 := by
  unfold tailWord_1012126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4614408491405979275504029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24610178620831889469354821 4614408491405979275504029)
  ·
    refine ⟨1730403184277242228314011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4614408491405979275504029 1730403184277242228314011)
    ·
      refine ⟨2595604776415863342471017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1730403184277242228314011 2595604776415863342471017)
      ·
        refine ⟨1946703582311897506853263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2595604776415863342471017 1946703582311897506853263)
        ·
          refine ⟨2920055373467846260279895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946703582311897506853263 2920055373467846260279895)
          ·
            refine ⟨4380083060201769390419843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920055373467846260279895 4380083060201769390419843)
            ·
              refine ⟨6570124590302654085629765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4380083060201769390419843 6570124590302654085629765)
              ·
                refine ⟨1231898360681747641055581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6570124590302654085629765 1231898360681747641055581)
                ·
                  refine ⟨461961885255655365395843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231898360681747641055581 461961885255655365395843)
                  ·
                    rfl

theorem cell20_1012126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1012126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012126 prefixEnd_1012126 := by exact prefixLift 1012126
  have htrace : WordTrace (prefixWord ++ tailWord_1012126) baseStart_1012126 baseEnd_1012126 := by
    simpa [prefixWord, tailWord_1012126, baseEnd_1012126] using wordTrace_append hprefix tailTrace_1012126
  have hstable : (prefixWord ++ tailWord_1012126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012126).length < 2 ^ (prefixWord ++ tailWord_1012126).sum := by decide
  have hdescent : baseEnd_1012126 < baseStart_1012126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012178 : List Nat := [3, 2, 2, 4, 1, 1, 7]
def baseStart_1012178 : Nat := 118140960795 + 1012178 * 2 ^ 59
def prefixEnd_1012178 : Nat := 4983230072969 + 3 ^ 40 * 1012178 * 2
def baseEnd_1012178 : Nat := 51331735496952699518033

theorem tailTrace_1012178 : CollatzResearch.WordTrace tailWord_1012178 prefixEnd_1012178 51331735496952699518033 := by
  unfold tailWord_1012178
  simp only [CollatzResearch.WordTrace]
  refine ⟨9229291131764861771231297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24611443018039631389950125 9229291131764861771231297)
  ·
    refine ⟨6921968348823646328423473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9229291131764861771231297 6921968348823646328423473)
    ·
      refine ⟨5191476261617734746317605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6921968348823646328423473 5191476261617734746317605)
      ·
        refine ⟨973401799053325264934551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5191476261617734746317605 973401799053325264934551)
        ·
          refine ⟨1460102698579987897401827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973401799053325264934551 1460102698579987897401827)
          ·
            refine ⟨2190154047869981846102741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460102698579987897401827 2190154047869981846102741)
            ·
              refine ⟨51331735496952699518033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2190154047869981846102741 51331735496952699518033)
              ·
                rfl

theorem cell20_1012178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 7].length) (baseStart_1012178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012178 prefixEnd_1012178 := by exact prefixLift 1012178
  have htrace : WordTrace (prefixWord ++ tailWord_1012178) baseStart_1012178 baseEnd_1012178 := by
    simpa [prefixWord, tailWord_1012178, baseEnd_1012178] using wordTrace_append hprefix tailTrace_1012178
  have hstable : (prefixWord ++ tailWord_1012178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012178).length < 2 ^ (prefixWord ++ tailWord_1012178).sum := by decide
  have hdescent : baseEnd_1012178 < baseStart_1012178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012192 : List Nat := [2, 1, 1, 3, 1, 1, 3, 6, 2]
def baseStart_1012192 : Nat := 118140960795 + 1012192 * 2 ^ 59
def prefixEnd_1012192 : Nat := 4983230072969 + 3 ^ 40 * 1012192 * 2
def baseEnd_1012192 : Nat := 461992009454052469195573

theorem tailTrace_1012192 : CollatzResearch.WordTrace tailWord_1012192 prefixEnd_1012192 461992009454052469195573 := by
  unfold tailWord_1012192
  simp only [CollatzResearch.WordTrace]
  refine ⟨18458837574504363737967415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24611783432672484983956553 18458837574504363737967415)
  ·
    refine ⟨27688256361756545606951123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18458837574504363737967415 27688256361756545606951123)
    ·
      refine ⟨41532384542634818410426685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27688256361756545606951123 41532384542634818410426685)
      ·
        refine ⟨15574644203488056903910007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41532384542634818410426685 15574644203488056903910007)
        ·
          refine ⟨23361966305232085355865011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15574644203488056903910007 23361966305232085355865011)
          ·
            refine ⟨35042949457848128033797517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23361966305232085355865011 35042949457848128033797517)
            ·
              refine ⟨13141106046693048012674069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35042949457848128033797517 13141106046693048012674069)
              ·
                refine ⟨615989345938736625594097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13141106046693048012674069 615989345938736625594097)
                ·
                  refine ⟨461992009454052469195573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615989345938736625594097 461992009454052469195573)
                  ·
                    rfl

theorem cell20_1012192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 2].length) (baseStart_1012192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012192 prefixEnd_1012192 := by exact prefixLift 1012192
  have htrace : WordTrace (prefixWord ++ tailWord_1012192) baseStart_1012192 baseEnd_1012192 := by
    simpa [prefixWord, tailWord_1012192, baseEnd_1012192] using wordTrace_append hprefix tailTrace_1012192
  have hstable : (prefixWord ++ tailWord_1012192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012192).length < 2 ^ (prefixWord ++ tailWord_1012192).sum := by decide
  have hdescent : baseEnd_1012192 < baseStart_1012192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012202 : List Nat := [3, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_1012202 : Nat := 118140960795 + 1012202 * 2 ^ 59
def prefixEnd_1012202 : Nat := 4983230072969 + 3 ^ 40 * 1012202 * 2
def baseEnd_1012202 : Nat := 461996573726536878862199

theorem tailTrace_1012202 : CollatzResearch.WordTrace tailWord_1012202 prefixEnd_1012202 461996573726536878862199 := by
  unfold tailWord_1012202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9229509969743124795949715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24612026585981666122532573 9229509969743124795949715)
  ·
    refine ⟨13844264954614687193924573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9229509969743124795949715 13844264954614687193924573)
    ·
      refine ⟨5191599357980507697721715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13844264954614687193924573 5191599357980507697721715)
      ·
        refine ⟨7787399036970761546582573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5191599357980507697721715 7787399036970761546582573)
        ·
          refine ⟨2920274638864035579968465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7787399036970761546582573 2920274638864035579968465)
          ·
            refine ⟨2190205979148026684976349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2920274638864035579968465 2190205979148026684976349)
            ·
              refine ⟨821327242180510006866131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2190205979148026684976349 821327242180510006866131)
              ·
                refine ⟨1231990863270765010299197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821327242180510006866131 1231990863270765010299197)
                ·
                  refine ⟨461996573726536878862199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231990863270765010299197 461996573726536878862199)
                  ·
                    rfl

theorem cell20_1012202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_1012202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012202 prefixEnd_1012202 := by exact prefixLift 1012202
  have htrace : WordTrace (prefixWord ++ tailWord_1012202) baseStart_1012202 baseEnd_1012202 := by
    simpa [prefixWord, tailWord_1012202, baseEnd_1012202] using wordTrace_append hprefix tailTrace_1012202
  have hstable : (prefixWord ++ tailWord_1012202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012202).length < 2 ^ (prefixWord ++ tailWord_1012202).sum := by decide
  have hdescent : baseEnd_1012202 < baseStart_1012202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012227 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 7]
def baseStart_1012227 : Nat := 118140960795 + 1012227 * 2 ^ 59
def prefixEnd_1012227 : Nat := 4983230072969 + 3 ^ 40 * 1012227 * 2
def baseEnd_1012227 : Nat := 462007984407747903028763

theorem tailTrace_1012227 : CollatzResearch.WordTrace tailWord_1012227 prefixEnd_1012227 462007984407747903028763 := by
  unfold tailWord_1012227
  simp only [CollatzResearch.WordTrace]
  refine ⟨36918951703881928453458935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24612634469254618968972623 36918951703881928453458935)
  ·
    refine ⟨55378427555822892680188403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36918951703881928453458935 55378427555822892680188403)
    ·
      refine ⟨83067641333734339020282605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55378427555822892680188403 83067641333734339020282605)
      ·
        refine ⟨31150365500150377132605977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83067641333734339020282605 31150365500150377132605977)
        ·
          refine ⟨23362774125112782849454483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31150365500150377132605977 23362774125112782849454483)
          ·
            refine ⟨35044161187669174274181725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23362774125112782849454483 35044161187669174274181725)
            ·
              refine ⟨13141560445375940352818147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35044161187669174274181725 13141560445375940352818147)
              ·
                refine ⟨19712340668063910529227221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13141560445375940352818147 19712340668063910529227221)
                ·
                  refine ⟨462007984407747903028763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19712340668063910529227221 462007984407747903028763)
                  ·
                    rfl

theorem cell20_1012227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_1012227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012227 prefixEnd_1012227 := by exact prefixLift 1012227
  have htrace : WordTrace (prefixWord ++ tailWord_1012227) baseStart_1012227 baseEnd_1012227 := by
    simpa [prefixWord, tailWord_1012227, baseEnd_1012227] using wordTrace_append hprefix tailTrace_1012227
  have hstable : (prefixWord ++ tailWord_1012227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012227).length < 2 ^ (prefixWord ++ tailWord_1012227).sum := by decide
  have hdescent : baseEnd_1012227 < baseStart_1012227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012261 : List Nat := [1, 3, 1, 2, 2, 1, 6, 1, 3]
def baseStart_1012261 : Nat := 118140960795 + 1012261 * 2 ^ 59
def prefixEnd_1012261 : Nat := 4983230072969 + 3 ^ 40 * 1012261 * 2
def baseEnd_1012261 : Nat := 462023502934194895895291

theorem tailTrace_1012261 : CollatzResearch.WordTrace tailWord_1012261 prefixEnd_1012261 462023502934194895895291 := by
  unfold tailWord_1012261
  simp only [CollatzResearch.WordTrace]
  refine ⟨36920191785758752260196637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24613461190505834840131091 36920191785758752260196637)
  ·
    refine ⟨13845071919659532097573739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36920191785758752260196637 13845071919659532097573739)
    ·
      refine ⟨20767607879489298146360609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13845071919659532097573739 20767607879489298146360609)
      ·
        refine ⟨15575705909616973609770457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20767607879489298146360609 15575705909616973609770457)
        ·
          refine ⟨11681779432212730207327843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15575705909616973609770457 11681779432212730207327843)
          ·
            refine ⟨17522669148319095310991765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11681779432212730207327843 17522669148319095310991765)
            ·
              refine ⟨821375116327457592702739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17522669148319095310991765 821375116327457592702739)
              ·
                refine ⟨1232062674491186389054109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821375116327457592702739 1232062674491186389054109)
                ·
                  refine ⟨462023502934194895895291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232062674491186389054109 462023502934194895895291)
                  ·
                    rfl

theorem cell20_1012261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_1012261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012261 prefixEnd_1012261 := by exact prefixLift 1012261
  have htrace : WordTrace (prefixWord ++ tailWord_1012261) baseStart_1012261 baseEnd_1012261 := by
    simpa [prefixWord, tailWord_1012261, baseEnd_1012261] using wordTrace_append hprefix tailTrace_1012261
  have hstable : (prefixWord ++ tailWord_1012261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012261).length < 2 ^ (prefixWord ++ tailWord_1012261).sum := by decide
  have hdescent : baseEnd_1012261 < baseStart_1012261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012292 : List Nat := [2, 3, 5, 1, 9]
def baseStart_1012292 : Nat := 118140960795 + 1012292 * 2 ^ 59
def prefixEnd_1012292 : Nat := 4983230072969 + 3 ^ 40 * 1012292 * 2
def baseEnd_1012292 : Nat := 5704168545418476121751

theorem tailTrace_1012292 : CollatzResearch.WordTrace tailWord_1012292 prefixEnd_1012292 5704168545418476121751 := by
  unfold tailWord_1012292
  simp only [CollatzResearch.WordTrace]
  refine ⟨18460661224323222277287565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24614214965764296369716753 18460661224323222277287565)
  ·
    refine ⟨6922747959121208353982837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18460661224323222277287565 6922747959121208353982837)
    ·
      refine ⟨649007621167613283185891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6922747959121208353982837 649007621167613283185891)
      ·
        refine ⟨973511431751419924778837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649007621167613283185891 973511431751419924778837)
        ·
          refine ⟨5704168545418476121751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 973511431751419924778837 5704168545418476121751)
          ·
            rfl

theorem cell20_1012292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 9].length) (baseStart_1012292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012292 prefixEnd_1012292 := by exact prefixLift 1012292
  have htrace : WordTrace (prefixWord ++ tailWord_1012292) baseStart_1012292 baseEnd_1012292 := by
    simpa [prefixWord, tailWord_1012292, baseEnd_1012292] using wordTrace_append hprefix tailTrace_1012292
  have hstable : (prefixWord ++ tailWord_1012292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012292).length < 2 ^ (prefixWord ++ tailWord_1012292).sum := by decide
  have hdescent : baseEnd_1012292 < baseStart_1012292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012303 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 5]
def baseStart_1012303 : Nat := 118140960795 + 1012303 * 2 ^ 59
def prefixEnd_1012303 : Nat := 4983230072969 + 3 ^ 40 * 1012303 * 2
def baseEnd_1012303 : Nat := 462042672878629416495119

theorem tailTrace_1012303 : CollatzResearch.WordTrace tailWord_1012303 prefixEnd_1012303 462042672878629416495119 := by
  unfold tailWord_1012303
  simp only [CollatzResearch.WordTrace]
  refine ⟨36921723651606593433225563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24614482434404395622150375 36921723651606593433225563)
  ·
    refine ⟨55382585477409890149838345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36921723651606593433225563 55382585477409890149838345)
    ·
      refine ⟨41536939108057417612378759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55382585477409890149838345 41536939108057417612378759)
      ·
        refine ⟨62305408662086126418568139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41536939108057417612378759 62305408662086126418568139)
        ·
          refine ⟨93458112993129189627852209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62305408662086126418568139 93458112993129189627852209)
          ·
            refine ⟨70093584744846892220889157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93458112993129189627852209 70093584744846892220889157)
            ·
              refine ⟨13142547139658792291416717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70093584744846892220889157 13142547139658792291416717)
              ·
                refine ⟨4928455177372047109281269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13142547139658792291416717 4928455177372047109281269)
                ·
                  refine ⟨462042672878629416495119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4928455177372047109281269 462042672878629416495119)
                  ·
                    rfl

theorem cell20_1012303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_1012303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012303 prefixEnd_1012303 := by exact prefixLift 1012303
  have htrace : WordTrace (prefixWord ++ tailWord_1012303) baseStart_1012303 baseEnd_1012303 := by
    simpa [prefixWord, tailWord_1012303, baseEnd_1012303] using wordTrace_append hprefix tailTrace_1012303
  have hstable : (prefixWord ++ tailWord_1012303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012303).length < 2 ^ (prefixWord ++ tailWord_1012303).sum := by decide
  have hdescent : baseEnd_1012303 < baseStart_1012303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012320 : List Nat := [2, 1, 1, 3, 2, 1, 4, 3, 3]
def baseStart_1012320 : Nat := 118140960795 + 1012320 * 2 ^ 59
def prefixEnd_1012320 : Nat := 4983230072969 + 3 ^ 40 * 1012320 * 2
def baseEnd_1012320 : Nat := 462050432141852912928383

theorem tailTrace_1012320 : CollatzResearch.WordTrace tailWord_1012320 prefixEnd_1012320 462050432141852912928383 := by
  unfold tailWord_1012320
  simp only [CollatzResearch.WordTrace]
  refine ⟨18461171846272502668297207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24614895795030003557729609 18461171846272502668297207)
  ·
    refine ⟨27691757769408754002445811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18461171846272502668297207 27691757769408754002445811)
    ·
      refine ⟨41537636654113131003668717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27691757769408754002445811 41537636654113131003668717)
      ·
        refine ⟨15576613745292424126375769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41537636654113131003668717 15576613745292424126375769)
        ·
          refine ⟨11682460308969318094781827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15576613745292424126375769 11682460308969318094781827)
          ·
            refine ⟨17523690463453977142172741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11682460308969318094781827 17523690463453977142172741)
            ·
              refine ⟨3285691961897620714157389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17523690463453977142172741 3285691961897620714157389)
              ·
                refine ⟨1232134485711607767809021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3285691961897620714157389 1232134485711607767809021)
                ·
                  refine ⟨462050432141852912928383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232134485711607767809021 462050432141852912928383)
                  ·
                    rfl

theorem cell20_1012320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_1012320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012320 prefixEnd_1012320 := by exact prefixLift 1012320
  have htrace : WordTrace (prefixWord ++ tailWord_1012320) baseStart_1012320 baseEnd_1012320 := by
    simpa [prefixWord, tailWord_1012320, baseEnd_1012320] using wordTrace_append hprefix tailTrace_1012320
  have hstable : (prefixWord ++ tailWord_1012320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012320).length < 2 ^ (prefixWord ++ tailWord_1012320).sum := by decide
  have hdescent : baseEnd_1012320 < baseStart_1012320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012375 : List Nat := [1, 1, 3, 3, 2, 1, 5, 1, 3]
def baseStart_1012375 : Nat := 118140960795 + 1012375 * 2 ^ 59
def prefixEnd_1012375 : Nat := 4983230072969 + 3 ^ 40 * 1012375 * 2
def baseEnd_1012375 : Nat := 462075535640517166094825

theorem tailTrace_1012375 : CollatzResearch.WordTrace tailWord_1012375 prefixEnd_1012375 462075535640517166094825 := by
  unfold tailWord_1012375
  simp only [CollatzResearch.WordTrace]
  refine ⟨36924349707345749729846579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24616233138230499819897719 36924349707345749729846579)
  ·
    refine ⟨55386524561018624594769869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36924349707345749729846579 55386524561018624594769869)
    ·
      refine ⟨20769946710381984223038701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55386524561018624594769869 20769946710381984223038701)
      ·
        refine ⟨7788730016393244083639513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20769946710381984223038701 7788730016393244083639513)
        ·
          refine ⟨5841547512294933062729635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7788730016393244083639513 5841547512294933062729635)
          ·
            refine ⟨8762321268442399594094453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841547512294933062729635 8762321268442399594094453)
            ·
              refine ⟨821467618916474961946355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8762321268442399594094453 821467618916474961946355)
              ·
                refine ⟨1232201428374712442919533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821467618916474961946355 1232201428374712442919533)
                ·
                  refine ⟨462075535640517166094825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232201428374712442919533 462075535640517166094825)
                  ·
                    rfl

theorem cell20_1012375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 3].length) (baseStart_1012375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012375 prefixEnd_1012375 := by exact prefixLift 1012375
  have htrace : WordTrace (prefixWord ++ tailWord_1012375) baseStart_1012375 baseEnd_1012375 := by
    simpa [prefixWord, tailWord_1012375, baseEnd_1012375] using wordTrace_append hprefix tailTrace_1012375
  have hstable : (prefixWord ++ tailWord_1012375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012375).length < 2 ^ (prefixWord ++ tailWord_1012375).sum := by decide
  have hdescent : baseEnd_1012375 < baseStart_1012375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012382 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1012382 : Nat := 118140960795 + 1012382 * 2 ^ 59
def prefixEnd_1012382 : Nat := 4983230072969 + 3 ^ 40 * 1012382 * 2
def baseEnd_1012382 : Nat := 462078730631256252861463

theorem tailTrace_1012382 : CollatzResearch.WordTrace tailWord_1012382 prefixEnd_1012382 462078730631256252861463 := by
  unfold tailWord_1012382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615575627290048740668925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24616403345546926616900933 4615575627290048740668925)
  ·
    refine ⟨1730840860233768277750847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4615575627290048740668925 1730840860233768277750847)
    ·
      refine ⟨2596261290350652416626271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1730840860233768277750847 2596261290350652416626271)
      ·
        refine ⟨3894391935525978624939407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596261290350652416626271 3894391935525978624939407)
        ·
          refine ⟨5841587903288967937409111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894391935525978624939407 5841587903288967937409111)
          ·
            refine ⟨8762381854933451906113667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841587903288967937409111 8762381854933451906113667)
            ·
              refine ⟨13143572782400177859170501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8762381854933451906113667 13143572782400177859170501)
              ·
                refine ⟨2464419896700033348594469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13143572782400177859170501 2464419896700033348594469)
                ·
                  refine ⟨462078730631256252861463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2464419896700033348594469 462078730631256252861463)
                  ·
                    rfl

theorem cell20_1012382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1012382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012382 prefixEnd_1012382 := by exact prefixLift 1012382
  have htrace : WordTrace (prefixWord ++ tailWord_1012382) baseStart_1012382 baseEnd_1012382 := by
    simpa [prefixWord, tailWord_1012382, baseEnd_1012382] using wordTrace_append hprefix tailTrace_1012382
  have hstable : (prefixWord ++ tailWord_1012382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012382).length < 2 ^ (prefixWord ++ tailWord_1012382).sum := by decide
  have hdescent : baseEnd_1012382 < baseStart_1012382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012385 : List Nat := [1, 2, 3, 3, 4, 1, 2, 4]
def baseStart_1012385 : Nat := 118140960795 + 1012385 * 2 ^ 59
def prefixEnd_1012385 : Nat := 4983230072969 + 3 ^ 40 * 1012385 * 2
def baseEnd_1012385 : Nat := 154026699971000525253817

theorem tailTrace_1012385 : CollatzResearch.WordTrace tailWord_1012385 prefixEnd_1012385 154026699971000525253817 := by
  unfold tailWord_1012385
  simp only [CollatzResearch.WordTrace]
  refine ⟨36924714437309521437710609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24616476291539680958473739 36924714437309521437710609)
  ·
    refine ⟨27693535827982141078282957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36924714437309521437710609 27693535827982141078282957)
    ·
      refine ⟨10385075935493302904356109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27693535827982141078282957 10385075935493302904356109)
      ·
        refine ⟨3894403475809988589133541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10385075935493302904356109 3894403475809988589133541)
        ·
          refine ⟨730200651714372860462539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3894403475809988589133541 730200651714372860462539)
          ·
            refine ⟨1095300977571559290693809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730200651714372860462539 1095300977571559290693809)
            ·
              refine ⟨821475733178669468020357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1095300977571559290693809 821475733178669468020357)
              ·
                refine ⟨154026699971000525253817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 821475733178669468020357 154026699971000525253817)
                ·
                  rfl

theorem cell20_1012385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 4].length) (baseStart_1012385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012385 prefixEnd_1012385 := by exact prefixLift 1012385
  have htrace : WordTrace (prefixWord ++ tailWord_1012385) baseStart_1012385 baseEnd_1012385 := by
    simpa [prefixWord, tailWord_1012385, baseEnd_1012385] using wordTrace_append hprefix tailTrace_1012385
  have hstable : (prefixWord ++ tailWord_1012385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012385).length < 2 ^ (prefixWord ++ tailWord_1012385).sum := by decide
  have hdescent : baseEnd_1012385 < baseStart_1012385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012399 : List Nat := [1, 1, 2, 1, 2, 7, 1, 3, 2]
def baseStart_1012399 : Nat := 118140960795 + 1012399 * 2 ^ 59
def prefixEnd_1012399 : Nat := 4983230072969 + 3 ^ 40 * 1012399 * 2
def baseEnd_1012399 : Nat := 462086489894479749294727

theorem tailTrace_1012399 : CollatzResearch.WordTrace tailWord_1012399 prefixEnd_1012399 462086489894479749294727 := by
  unfold tailWord_1012399
  simp only [CollatzResearch.WordTrace]
  refine ⟨36925225059258801828720251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24616816706172534552480167 36925225059258801828720251)
  ·
    refine ⟨55387837588888202743080377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36925225059258801828720251 55387837588888202743080377)
    ·
      refine ⟨41540878191666152057310283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55387837588888202743080377 41540878191666152057310283)
      ·
        refine ⟨62311317287499228085965425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41540878191666152057310283 62311317287499228085965425)
        ·
          refine ⟨46733487965624421064474069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62311317287499228085965425 46733487965624421064474069)
          ·
            refine ⟨1095316124194322368698611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 46733487965624421064474069 1095316124194322368698611)
            ·
              refine ⟨1642974186291483553047917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095316124194322368698611 1642974186291483553047917)
              ·
                refine ⟨616115319859306332392969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1642974186291483553047917 616115319859306332392969)
                ·
                  refine ⟨462086489894479749294727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616115319859306332392969 462086489894479749294727)
                  ·
                    rfl

theorem cell20_1012399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 2].length) (baseStart_1012399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012399 prefixEnd_1012399 := by exact prefixLift 1012399
  have htrace : WordTrace (prefixWord ++ tailWord_1012399) baseStart_1012399 baseEnd_1012399 := by
    simpa [prefixWord, tailWord_1012399, baseEnd_1012399] using wordTrace_append hprefix tailTrace_1012399
  have hstable : (prefixWord ++ tailWord_1012399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012399).length < 2 ^ (prefixWord ++ tailWord_1012399).sum := by decide
  have hdescent : baseEnd_1012399 < baseStart_1012399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012420 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_1012420 : Nat := 118140960795 + 1012420 * 2 ^ 59
def prefixEnd_1012420 : Nat := 4983230072969 + 3 ^ 40 * 1012420 * 2
def baseEnd_1012420 : Nat := 462096074866697009594641

theorem tailTrace_1012420 : CollatzResearch.WordTrace tailWord_1012420 prefixEnd_1012420 462096074866697009594641 := by
  unfold tailWord_1012420
  simp only [CollatzResearch.WordTrace]
  refine ⟨18462995496091361207617357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24617327328121814943489809 18462995496091361207617357)
  ·
    refine ⟨6923623311034260452856509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18462995496091361207617357 6923623311034260452856509)
    ·
      refine ⟨2596358741637847669821191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6923623311034260452856509 2596358741637847669821191)
      ·
        refine ⟨3894538112456771504731787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596358741637847669821191 3894538112456771504731787)
        ·
          refine ⟨5841807168685157257097681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894538112456771504731787 5841807168685157257097681)
          ·
            refine ⟨4381355376513867942823261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5841807168685157257097681 4381355376513867942823261)
            ·
              refine ⟨1643008266192700478558723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4381355376513867942823261 1643008266192700478558723)
              ·
                refine ⟨2464512399289050717838085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643008266192700478558723 2464512399289050717838085)
                ·
                  refine ⟨462096074866697009594641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2464512399289050717838085 462096074866697009594641)
                  ·
                    rfl

theorem cell20_1012420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_1012420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012420 prefixEnd_1012420 := by exact prefixLift 1012420
  have htrace : WordTrace (prefixWord ++ tailWord_1012420) baseStart_1012420 baseEnd_1012420 := by
    simpa [prefixWord, tailWord_1012420, baseEnd_1012420] using wordTrace_append hprefix tailTrace_1012420
  have hstable : (prefixWord ++ tailWord_1012420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012420).length < 2 ^ (prefixWord ++ tailWord_1012420).sum := by decide
  have hdescent : baseEnd_1012420 < baseStart_1012420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012430 : List Nat := [4, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_1012430 : Nat := 118140960795 + 1012430 * 2 ^ 59
def prefixEnd_1012430 : Nat := 4983230072969 + 3 ^ 40 * 1012430 * 2
def baseEnd_1012430 : Nat := 462100639139181419261267

theorem tailTrace_1012430 : CollatzResearch.WordTrace tailWord_1012430 prefixEnd_1012430 462100639139181419261267 := by
  unfold tailWord_1012430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615794465268311765387343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24617570481430996082065829 4615794465268311765387343)
  ·
    refine ⟨6923691697902467648081015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4615794465268311765387343 6923691697902467648081015)
    ·
      refine ⟨10385537546853701472121523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6923691697902467648081015 10385537546853701472121523)
      ·
        refine ⟨15578306320280552208182285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10385537546853701472121523 15578306320280552208182285)
        ·
          refine ⟨5841864870105207078068357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15578306320280552208182285 5841864870105207078068357)
          ·
            refine ⟨1095349663144726327137817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5841864870105207078068357 1095349663144726327137817)
            ·
              refine ⟨821512247358544745353363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1095349663144726327137817 821512247358544745353363)
              ·
                refine ⟨1232268371037817118030045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821512247358544745353363 1232268371037817118030045)
                ·
                  refine ⟨462100639139181419261267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232268371037817118030045 462100639139181419261267)
                  ·
                    rfl

theorem cell20_1012430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_1012430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012430 prefixEnd_1012430 := by exact prefixLift 1012430
  have htrace : WordTrace (prefixWord ++ tailWord_1012430) baseStart_1012430 baseEnd_1012430 := by
    simpa [prefixWord, tailWord_1012430, baseEnd_1012430] using wordTrace_append hprefix tailTrace_1012430
  have hstable : (prefixWord ++ tailWord_1012430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012430).length < 2 ^ (prefixWord ++ tailWord_1012430).sum := by decide
  have hdescent : baseEnd_1012430 < baseStart_1012430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012458 : List Nat := [3, 1, 3, 1, 1, 1, 1, 7, 2]
def baseStart_1012458 : Nat := 118140960795 + 1012458 * 2 ^ 59
def prefixEnd_1012458 : Nat := 4983230072969 + 3 ^ 40 * 1012458 * 2
def baseEnd_1012458 : Nat := 462113419102137766327819

theorem tailTrace_1012458 : CollatzResearch.WordTrace tailWord_1012458 prefixEnd_1012458 462113419102137766327819 := by
  unfold tailWord_1012458
  simp only [CollatzResearch.WordTrace]
  refine ⟨9231844241511263726279507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24618251310696703270078685 9231844241511263726279507)
  ·
    refine ⟨13847766362266895589419261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9231844241511263726279507 13847766362266895589419261)
    ·
      refine ⟨5192912385850085846032223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13847766362266895589419261 5192912385850085846032223)
      ·
        refine ⟨7789368578775128769048335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5192912385850085846032223 7789368578775128769048335)
        ·
          refine ⟨11684052868162693153572503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7789368578775128769048335 11684052868162693153572503)
          ·
            refine ⟨17526079302244039730358755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11684052868162693153572503 17526079302244039730358755)
            ·
              refine ⟨26289118953366059595538133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17526079302244039730358755 26289118953366059595538133)
              ·
                refine ⟨616151225469517021770425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26289118953366059595538133 616151225469517021770425)
                ·
                  refine ⟨462113419102137766327819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616151225469517021770425 462113419102137766327819)
                  ·
                    rfl

theorem cell20_1012458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_1012458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012458 prefixEnd_1012458 := by exact prefixLift 1012458
  have htrace : WordTrace (prefixWord ++ tailWord_1012458) baseStart_1012458 baseEnd_1012458 := by
    simpa [prefixWord, tailWord_1012458, baseEnd_1012458] using wordTrace_append hprefix tailTrace_1012458
  have hstable : (prefixWord ++ tailWord_1012458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012458).length < 2 ^ (prefixWord ++ tailWord_1012458).sum := by decide
  have hdescent : baseEnd_1012458 < baseStart_1012458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012472 : List Nat := [2, 1, 2, 1, 1, 2, 6, 2, 3]
def baseStart_1012472 : Nat := 118140960795 + 1012472 * 2 ^ 59
def prefixEnd_1012472 : Nat := 4983230072969 + 3 ^ 40 * 1012472 * 2
def baseEnd_1012472 : Nat := 462119809083615939861095

theorem tailTrace_1012472 : CollatzResearch.WordTrace tailWord_1012472 prefixEnd_1012472 462119809083615939861095 := by
  unfold tailWord_1012472
  simp only [CollatzResearch.WordTrace]
  refine ⟨18463943793997167648063835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24618591725329556864085113 18463943793997167648063835)
  ·
    refine ⟨27695915690995751472095753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18463943793997167648063835 27695915690995751472095753)
    ·
      refine ⟨20771936768246813604071815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27695915690995751472095753 20771936768246813604071815)
      ·
        refine ⟨31157905152370220406107723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20771936768246813604071815 31157905152370220406107723)
        ·
          refine ⟨46736857728555330609161585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31157905152370220406107723 46736857728555330609161585)
          ·
            refine ⟨35052643296416497956871189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46736857728555330609161585 35052643296416497956871189)
            ·
              refine ⟨1643092654519523341728337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35052643296416497956871189 1643092654519523341728337)
              ·
                refine ⟨1232319490889642506296253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643092654519523341728337 1232319490889642506296253)
                ·
                  refine ⟨462119809083615939861095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232319490889642506296253 462119809083615939861095)
                  ·
                    rfl

theorem cell20_1012472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_1012472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012472 prefixEnd_1012472 := by exact prefixLift 1012472
  have htrace : WordTrace (prefixWord ++ tailWord_1012472) baseStart_1012472 baseEnd_1012472 := by
    simpa [prefixWord, tailWord_1012472, baseEnd_1012472] using wordTrace_append hprefix tailTrace_1012472
  have hstable : (prefixWord ++ tailWord_1012472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012472).length < 2 ^ (prefixWord ++ tailWord_1012472).sum := by decide
  have hdescent : baseEnd_1012472 < baseStart_1012472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012482 : List Nat := [3, 4, 1, 1, 1, 4, 1, 5]
def baseStart_1012482 : Nat := 118140960795 + 1012482 * 2 ^ 59
def prefixEnd_1012482 : Nat := 4983230072969 + 3 ^ 40 * 1012482 * 2
def baseEnd_1012482 : Nat := 154041457785366783175907

theorem tailTrace_1012482 : CollatzResearch.WordTrace tailWord_1012482 prefixEnd_1012482 154041457785366783175907 := by
  unfold tailWord_1012482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9232063079489526750997925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24618834878638738002661133 9232063079489526750997925)
  ·
    refine ⟨1731011827404286265812111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9232063079489526750997925 1731011827404286265812111)
    ·
      refine ⟨2596517741106429398718167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1731011827404286265812111 2596517741106429398718167)
      ·
        refine ⟨3894776611659644098077251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596517741106429398718167 3894776611659644098077251)
        ·
          refine ⟨5842164917489466147115877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894776611659644098077251 5842164917489466147115877)
          ·
            refine ⟨1095405922029274902584227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5842164917489466147115877 1095405922029274902584227)
            ·
              refine ⟨1643108883043912353876341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095405922029274902584227 1643108883043912353876341)
              ·
                refine ⟨154041457785366783175907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1643108883043912353876341 154041457785366783175907)
                ·
                  rfl

theorem cell20_1012482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_1012482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012482 prefixEnd_1012482 := by exact prefixLift 1012482
  have htrace : WordTrace (prefixWord ++ tailWord_1012482) baseStart_1012482 baseEnd_1012482 := by
    simpa [prefixWord, tailWord_1012482, baseEnd_1012482] using wordTrace_append hprefix tailTrace_1012482
  have hstable : (prefixWord ++ tailWord_1012482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012482).length < 2 ^ (prefixWord ++ tailWord_1012482).sum := by decide
  have hdescent : baseEnd_1012482 < baseStart_1012482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012562 : List Nat := [3, 2, 2, 1, 1, 2, 3, 6]
def baseStart_1012562 : Nat := 118140960795 + 1012562 * 2 ^ 59
def prefixEnd_1012562 : Nat := 4983230072969 + 3 ^ 40 * 1012562 * 2
def baseEnd_1012562 : Nat := 154053629178658542286909

theorem tailTrace_1012562 : CollatzResearch.WordTrace tailWord_1012562 prefixEnd_1012562 154053629178658542286909 := by
  unfold tailWord_1012562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9232792539417070166725985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24620780105112187111269293 9232792539417070166725985)
  ·
    refine ⟨6924594404562802625044489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9232792539417070166725985 6924594404562802625044489)
    ·
      refine ⟨5193445803422101968783367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6924594404562802625044489 5193445803422101968783367)
      ·
        refine ⟨7790168705133152953175051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5193445803422101968783367 7790168705133152953175051)
        ·
          refine ⟨11685253057699729429762577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7790168705133152953175051 11685253057699729429762577)
          ·
            refine ⟨8763939793274797072321933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11685253057699729429762577 8763939793274797072321933)
            ·
              refine ⟨3286477422478048902120725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8763939793274797072321933 3286477422478048902120725)
              ·
                refine ⟨154053629178658542286909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3286477422478048902120725 154053629178658542286909)
                ·
                  rfl

theorem cell20_1012562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_1012562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012562 prefixEnd_1012562 := by exact prefixLift 1012562
  have htrace : WordTrace (prefixWord ++ tailWord_1012562) baseStart_1012562 baseEnd_1012562 := by
    simpa [prefixWord, tailWord_1012562, baseEnd_1012562] using wordTrace_append hprefix tailTrace_1012562
  have hstable : (prefixWord ++ tailWord_1012562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012562).length < 2 ^ (prefixWord ++ tailWord_1012562).sum := by decide
  have hdescent : baseEnd_1012562 < baseStart_1012562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012569 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 5]
def baseStart_1012569 : Nat := 118140960795 + 1012569 * 2 ^ 59
def prefixEnd_1012569 : Nat := 4983230072969 + 3 ^ 40 * 1012569 * 2
def baseEnd_1012569 : Nat := 462164082526714713627365

theorem tailTrace_1012569 : CollatzResearch.WordTrace tailWord_1012569 prefixEnd_1012569 462164082526714713627365 := by
  unfold tailWord_1012569
  simp only [CollatzResearch.WordTrace]
  refine ⟨36931425468642920862408761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24620950312428613908272507 36931425468642920862408761)
  ·
    refine ⟨27698569101482190646806571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36931425468642920862408761 27698569101482190646806571)
    ·
      refine ⟨41547853652223285970209857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27698569101482190646806571 41547853652223285970209857)
      ·
        refine ⟨31160890239167464477657393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41547853652223285970209857 31160890239167464477657393)
        ·
          refine ⟨23370667679375598358243045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31160890239167464477657393 23370667679375598358243045)
          ·
            refine ⟨4382000189882924692170571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23370667679375598358243045 4382000189882924692170571)
            ·
              refine ⟨6573000284824387038255857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382000189882924692170571 6573000284824387038255857)
              ·
                refine ⟨4929750213618290278691893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6573000284824387038255857 4929750213618290278691893)
                ·
                  refine ⟨462164082526714713627365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4929750213618290278691893 462164082526714713627365)
                  ·
                    rfl

theorem cell20_1012569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_1012569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012569 prefixEnd_1012569 := by exact prefixLift 1012569
  have htrace : WordTrace (prefixWord ++ tailWord_1012569) baseStart_1012569 baseEnd_1012569 := by
    simpa [prefixWord, tailWord_1012569, baseEnd_1012569] using wordTrace_append hprefix tailTrace_1012569
  have hstable : (prefixWord ++ tailWord_1012569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012569).length < 2 ^ (prefixWord ++ tailWord_1012569).sum := by decide
  have hdescent : baseEnd_1012569 < baseStart_1012569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012593 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 4]
def baseStart_1012593 : Nat := 118140960795 + 1012593 * 2 ^ 59
def prefixEnd_1012593 : Nat := 4983230072969 + 3 ^ 40 * 1012593 * 2
def baseEnd_1012593 : Nat := 462175036780677296827267

theorem tailTrace_1012593 : CollatzResearch.WordTrace tailWord_1012593 prefixEnd_1012593 462175036780677296827267 := by
  unfold tailWord_1012593
  simp only [CollatzResearch.WordTrace]
  refine ⟨36932300820555972961282433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24621533880370648640854955 36932300820555972961282433)
  ·
    refine ⟨27699225615416979720961825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36932300820555972961282433 27699225615416979720961825)
    ·
      refine ⟨20774419211562734790721369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27699225615416979720961825 20774419211562734790721369)
      ·
        refine ⟨15580814408672051093041027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20774419211562734790721369 15580814408672051093041027)
        ·
          refine ⟨23371221613008076639561541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15580814408672051093041027 23371221613008076639561541)
          ·
            refine ⟨4382104052439014369917789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23371221613008076639561541 4382104052439014369917789)
            ·
              refine ⟨1643289019664630388719171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4382104052439014369917789 1643289019664630388719171)
              ·
                refine ⟨2464933529496945583078757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643289019664630388719171 2464933529496945583078757)
                ·
                  refine ⟨462175036780677296827267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2464933529496945583078757 462175036780677296827267)
                  ·
                    rfl

theorem cell20_1012593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_1012593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012593 prefixEnd_1012593 := by exact prefixLift 1012593
  have htrace : WordTrace (prefixWord ++ tailWord_1012593) baseStart_1012593 baseEnd_1012593 := by
    simpa [prefixWord, tailWord_1012593, baseEnd_1012593] using wordTrace_append hprefix tailTrace_1012593
  have hstable : (prefixWord ++ tailWord_1012593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012593).length < 2 ^ (prefixWord ++ tailWord_1012593).sum := by decide
  have hdescent : baseEnd_1012593 < baseStart_1012593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012638 : List Nat := [4, 3, 1, 12]
def baseStart_1012638 : Nat := 118140960795 + 1012638 * 2 ^ 59
def prefixEnd_1012638 : Nat := 4983230072969 + 3 ^ 40 * 1012638 * 2
def baseEnd_1012638 : Nat := 1902039407435626091881

theorem tailTrace_1012638 : CollatzResearch.WordTrace tailWord_1012638 prefixEnd_1012638 1902039407435626091881 := by
  unfold tailWord_1012638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4616742763174118205833821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24622628070261963764447045 4616742763174118205833821)
  ·
    refine ⟨1731278536190294327187683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4616742763174118205833821 1731278536190294327187683)
    ·
      refine ⟨2596917804285441490781525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1731278536190294327187683 2596917804285441490781525)
      ·
        refine ⟨1902039407435626091881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2596917804285441490781525 1902039407435626091881)
        ·
          rfl

theorem cell20_1012638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 12].length) (baseStart_1012638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012638 prefixEnd_1012638 := by exact prefixLift 1012638
  have htrace : WordTrace (prefixWord ++ tailWord_1012638) baseStart_1012638 baseEnd_1012638 := by
    simpa [prefixWord, tailWord_1012638, baseEnd_1012638] using wordTrace_append hprefix tailTrace_1012638
  have hstable : (prefixWord ++ tailWord_1012638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012638).length < 2 ^ (prefixWord ++ tailWord_1012638).sum := by decide
  have hdescent : baseEnd_1012638 < baseStart_1012638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012641 : List Nat := [1, 2, 3, 4, 1, 2, 2, 2, 3]
def baseStart_1012641 : Nat := 118140960795 + 1012641 * 2 ^ 59
def prefixEnd_1012641 : Nat := 4983230072969 + 3 ^ 40 * 1012641 * 2
def baseEnd_1012641 : Nat := 462196945288602463227071

theorem tailTrace_1012641 : CollatzResearch.WordTrace tailWord_1012641 prefixEnd_1012641 462196945288602463227071 := by
  unfold tailWord_1012641
  simp only [CollatzResearch.WordTrace]
  refine ⟨36934051524382077159029777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24622701016254718106019851 36934051524382077159029777)
  ·
    refine ⟨27700538643286557869272333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36934051524382077159029777 27700538643286557869272333)
    ·
      refine ⟨10387701991232459200977125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27700538643286557869272333 10387701991232459200977125)
      ·
        refine ⟨1947694123356086100183211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10387701991232459200977125 1947694123356086100183211)
        ·
          refine ⟨2921541185034129150274817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947694123356086100183211 2921541185034129150274817)
          ·
            refine ⟨2191155888775596862706113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2921541185034129150274817 2191155888775596862706113)
            ·
              refine ⟨1643366916581697647029585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2191155888775596862706113 1643366916581697647029585)
              ·
                refine ⟨1232525187436273235272189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643366916581697647029585 1232525187436273235272189)
                ·
                  refine ⟨462196945288602463227071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232525187436273235272189 462196945288602463227071)
                  ·
                    rfl

theorem cell20_1012641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_1012641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012641 prefixEnd_1012641 := by exact prefixLift 1012641
  have htrace : WordTrace (prefixWord ++ tailWord_1012641) baseStart_1012641 baseEnd_1012641 := by
    simpa [prefixWord, tailWord_1012641, baseEnd_1012641] using wordTrace_append hprefix tailTrace_1012641
  have hstable : (prefixWord ++ tailWord_1012641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012641).length < 2 ^ (prefixWord ++ tailWord_1012641).sum := by decide
  have hdescent : baseEnd_1012641 < baseStart_1012641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012659 : List Nat := [1, 1, 1, 2, 3, 1, 2, 9]
def baseStart_1012659 : Nat := 118140960795 + 1012659 * 2 ^ 59
def prefixEnd_1012659 : Nat := 4983230072969 + 3 ^ 40 * 1012659 * 2
def baseEnd_1012659 : Nat := 154068386993024800208999

theorem tailTrace_1012659 : CollatzResearch.WordTrace tailWord_1012659 prefixEnd_1012659 154068386993024800208999 := by
  unfold tailWord_1012659
  simp only [CollatzResearch.WordTrace]
  refine ⟨36934708038316866233185031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24623138692211244155456687 36934708038316866233185031)
  ·
    refine ⟨55402062057475299349777547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36934708038316866233185031 55402062057475299349777547)
    ·
      refine ⟨83103093086212949024666321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55402062057475299349777547 83103093086212949024666321)
      ·
        refine ⟨62327319814659711768499741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83103093086212949024666321 62327319814659711768499741)
        ·
          refine ⟨23372744930497391913187403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62327319814659711768499741 23372744930497391913187403)
          ·
            refine ⟨35059117395746087869781105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23372744930497391913187403 35059117395746087869781105)
            ·
              refine ⟨26294338046809565902335829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35059117395746087869781105 26294338046809565902335829)
              ·
                refine ⟨154068386993024800208999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26294338046809565902335829 154068386993024800208999)
                ·
                  rfl

theorem cell20_1012659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_1012659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012659 prefixEnd_1012659 := by exact prefixLift 1012659
  have htrace : WordTrace (prefixWord ++ tailWord_1012659) baseStart_1012659 baseEnd_1012659 := by
    simpa [prefixWord, tailWord_1012659, baseEnd_1012659] using wordTrace_append hprefix tailTrace_1012659
  have hstable : (prefixWord ++ tailWord_1012659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012659).length < 2 ^ (prefixWord ++ tailWord_1012659).sum := by decide
  have hdescent : baseEnd_1012659 < baseStart_1012659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012686 : List Nat := [4, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_1012686 : Nat := 118140960795 + 1012686 * 2 ^ 59
def prefixEnd_1012686 : Nat := 4983230072969 + 3 ^ 40 * 1012686 * 2
def baseEnd_1012686 : Nat := 462217484514782306726887

theorem tailTrace_1012686 : CollatzResearch.WordTrace tailWord_1012686 prefixEnd_1012686 462217484514782306726887 := by
  unfold tailWord_1012686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4616961601152381230552239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24623795206146033229611941 4616961601152381230552239)
  ·
    refine ⟨6925442401728571845828359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4616961601152381230552239 6925442401728571845828359)
    ·
      refine ⟨10388163602592857768742539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6925442401728571845828359 10388163602592857768742539)
      ·
        refine ⟨15582245403889286653113809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10388163602592857768742539 15582245403889286653113809)
        ·
          refine ⟨11686684052916964989835357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15582245403889286653113809 11686684052916964989835357)
          ·
            refine ⟨4382506519843861871188259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11686684052916964989835357 4382506519843861871188259)
            ·
              refine ⟨6573759779765792806782389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382506519843861871188259 6573759779765792806782389)
              ·
                refine ⟨616289979353043075635849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6573759779765792806782389 616289979353043075635849)
                ·
                  refine ⟨462217484514782306726887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616289979353043075635849 462217484514782306726887)
                  ·
                    rfl

theorem cell20_1012686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_1012686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012686 prefixEnd_1012686 := by exact prefixLift 1012686
  have htrace : WordTrace (prefixWord ++ tailWord_1012686) baseStart_1012686 baseEnd_1012686 := by
    simpa [prefixWord, tailWord_1012686, baseEnd_1012686] using wordTrace_append hprefix tailTrace_1012686
  have hstable : (prefixWord ++ tailWord_1012686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012686).length < 2 ^ (prefixWord ++ tailWord_1012686).sum := by decide
  have hdescent : baseEnd_1012686 < baseStart_1012686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012707 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 4]
def baseStart_1012707 : Nat := 118140960795 + 1012707 * 2 ^ 59
def prefixEnd_1012707 : Nat := 4983230072969 + 3 ^ 40 * 1012707 * 2
def baseEnd_1012707 : Nat := 462227069486999567026801

theorem tailTrace_1012707 : CollatzResearch.WordTrace tailWord_1012707 prefixEnd_1012707 462227069486999567026801 := by
  unfold tailWord_1012707
  simp only [CollatzResearch.WordTrace]
  refine ⟨36936458742142970430932375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24624305828095313620621583 36936458742142970430932375)
  ·
    refine ⟨55404688113214455646398563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36936458742142970430932375 55404688113214455646398563)
    ·
      refine ⟨83107032169821683469597845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55404688113214455646398563 83107032169821683469597845)
      ·
        refine ⟨3895642132960391412637399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83107032169821683469597845 3895642132960391412637399)
        ·
          refine ⟨5843463199440587118956099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3895642132960391412637399 5843463199440587118956099)
          ·
            refine ⟨8765194799160880678434149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843463199440587118956099 8765194799160880678434149)
            ·
              refine ⟨1643474024842665127206403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8765194799160880678434149 1643474024842665127206403)
              ·
                refine ⟨2465211037263997690809605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643474024842665127206403 2465211037263997690809605)
                ·
                  refine ⟨462227069486999567026801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2465211037263997690809605 462227069486999567026801)
                  ·
                    rfl

theorem cell20_1012707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_1012707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012707 prefixEnd_1012707 := by exact prefixLift 1012707
  have htrace : WordTrace (prefixWord ++ tailWord_1012707) baseStart_1012707 baseEnd_1012707 := by
    simpa [prefixWord, tailWord_1012707, baseEnd_1012707] using wordTrace_append hprefix tailTrace_1012707
  have hstable : (prefixWord ++ tailWord_1012707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012707).length < 2 ^ (prefixWord ++ tailWord_1012707).sum := by decide
  have hdescent : baseEnd_1012707 < baseStart_1012707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012754 : List Nat := [3, 2, 5, 1, 1, 1, 3, 2, 2]
def baseStart_1012754 : Nat := 118140960795 + 1012754 * 2 ^ 59
def prefixEnd_1012754 : Nat := 4983230072969 + 3 ^ 40 * 1012754 * 2
def baseEnd_1012754 : Nat := 462248521567676292459943

theorem tailTrace_1012754 : CollatzResearch.WordTrace tailWord_1012754 prefixEnd_1012754 462248521567676292459943 := by
  unfold tailWord_1012754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9234543243243174364473329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24625448648648464971928877 9234543243243174364473329)
  ·
    refine ⟨6925907432432380773354997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9234543243243174364473329 6925907432432380773354997)
    ·
      refine ⟨649303821790535697502031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6925907432432380773354997 649303821790535697502031)
      ·
        refine ⟨973955732685803546253047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649303821790535697502031 973955732685803546253047)
        ·
          refine ⟨1460933599028705319379571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973955732685803546253047 1460933599028705319379571)
          ·
            refine ⟨2191400398543057979069357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460933599028705319379571 2191400398543057979069357)
            ·
              refine ⟨821775149453646742151009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2191400398543057979069357 821775149453646742151009)
              ·
                refine ⟨616331362090235056613257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821775149453646742151009 616331362090235056613257)
                ·
                  refine ⟨462248521567676292459943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616331362090235056613257 462248521567676292459943)
                  ·
                    rfl

theorem cell20_1012754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_1012754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012754 prefixEnd_1012754 := by exact prefixLift 1012754
  have htrace : WordTrace (prefixWord ++ tailWord_1012754) baseStart_1012754 baseEnd_1012754 := by
    simpa [prefixWord, tailWord_1012754, baseEnd_1012754] using wordTrace_append hprefix tailTrace_1012754
  have hstable : (prefixWord ++ tailWord_1012754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012754).length < 2 ^ (prefixWord ++ tailWord_1012754).sum := by decide
  have hdescent : baseEnd_1012754 < baseStart_1012754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012772 : List Nat := [2, 3, 1, 4, 1, 3, 2, 1, 3]
def baseStart_1012772 : Nat := 118140960795 + 1012772 * 2 ^ 59
def prefixEnd_1012772 : Nat := 4983230072969 + 3 ^ 40 * 1012772 * 2
def baseEnd_1012772 : Nat := 462256737258148229859869

theorem tailTrace_1012772 : CollatzResearch.WordTrace tailWord_1012772 prefixEnd_1012772 462256737258148229859869 := by
  unfold tailWord_1012772
  simp only [CollatzResearch.WordTrace]
  refine ⟨18469414743453743266024285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24625886324604991021365713 18469414743453743266024285)
  ·
    refine ⟨6926030528795153724759107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18469414743453743266024285 6926030528795153724759107)
    ·
      refine ⟨10389045793192730587138661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6926030528795153724759107 10389045793192730587138661)
      ·
        refine ⟨1947946086223636985088499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10389045793192730587138661 1947946086223636985088499)
        ·
          refine ⟨2921919129335455477632749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947946086223636985088499 2921919129335455477632749)
          ·
            refine ⟨1095719673500795804112281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2921919129335455477632749 1095719673500795804112281)
            ·
              refine ⟨821789755125596853084211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1095719673500795804112281 821789755125596853084211)
              ·
                refine ⟨1232684632688395279626317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821789755125596853084211 1232684632688395279626317)
                ·
                  refine ⟨462256737258148229859869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232684632688395279626317 462256737258148229859869)
                  ·
                    rfl

theorem cell20_1012772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_1012772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012772 prefixEnd_1012772 := by exact prefixLift 1012772
  have htrace : WordTrace (prefixWord ++ tailWord_1012772) baseStart_1012772 baseEnd_1012772 := by
    simpa [prefixWord, tailWord_1012772, baseEnd_1012772] using wordTrace_append hprefix tailTrace_1012772
  have hstable : (prefixWord ++ tailWord_1012772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012772).length < 2 ^ (prefixWord ++ tailWord_1012772).sum := by decide
  have hdescent : baseEnd_1012772 < baseStart_1012772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012814 : List Nat := [4, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1012814 : Nat := 118140960795 + 1012814 * 2 ^ 59
def prefixEnd_1012814 : Nat := 4983230072969 + 3 ^ 40 * 1012814 * 2
def baseEnd_1012814 : Nat := 462275907202582750459697

theorem tailTrace_1012814 : CollatzResearch.WordTrace tailWord_1012814 prefixEnd_1012814 462275907202582750459697 := by
  unfold tailWord_1012814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4617545169094415963134687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24626907568503551803384997 4617545169094415963134687)
  ·
    refine ⟨6926317753641623944702031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4617545169094415963134687 6926317753641623944702031)
    ·
      refine ⟨10389476630462435917053047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6926317753641623944702031 10389476630462435917053047)
      ·
        refine ⟨15584214945693653875579571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10389476630462435917053047 15584214945693653875579571)
        ·
          refine ⟨23376322418540480813369357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15584214945693653875579571 23376322418540480813369357)
          ·
            refine ⟨8766120906952680305013509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23376322418540480813369357 8766120906952680305013509)
            ·
              refine ⟨1643647670053627557190033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8766120906952680305013509 1643647670053627557190033)
              ·
                refine ⟨1232735752540220667892525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643647670053627557190033 1232735752540220667892525)
                ·
                  refine ⟨462275907202582750459697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232735752540220667892525 462275907202582750459697)
                  ·
                    rfl

theorem cell20_1012814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1012814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012814 prefixEnd_1012814 := by exact prefixLift 1012814
  have htrace : WordTrace (prefixWord ++ tailWord_1012814) baseStart_1012814 baseEnd_1012814 := by
    simpa [prefixWord, tailWord_1012814, baseEnd_1012814] using wordTrace_append hprefix tailTrace_1012814
  have hstable : (prefixWord ++ tailWord_1012814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012814).length < 2 ^ (prefixWord ++ tailWord_1012814).sum := by decide
  have hdescent : baseEnd_1012814 < baseStart_1012814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012845 : List Nat := [1, 5, 1, 1, 2, 3, 3, 4]
def baseStart_1012845 : Nat := 118140960795 + 1012845 * 2 ^ 59
def prefixEnd_1012845 : Nat := 4983230072969 + 3 ^ 40 * 1012845 * 2
def baseEnd_1012845 : Nat := 154096685482428140142079

theorem tailTrace_1012845 : CollatzResearch.WordTrace tailWord_1012845 prefixEnd_1012845 154096685482428140142079 := by
  unfold tailWord_1012845
  simp only [CollatzResearch.WordTrace]
  refine ⟨36941492015643019999455989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24627661343762013332970659 36941492015643019999455989)
  ·
    refine ⟨3463264876466533124948999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36941492015643019999455989 3463264876466533124948999)
    ·
      refine ⟨5194897314699799687423499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3463264876466533124948999 5194897314699799687423499)
      ·
        refine ⟨7792345972049699531135249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5194897314699799687423499 7792345972049699531135249)
        ·
          refine ⟨5844259479037274648351437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7792345972049699531135249 5844259479037274648351437)
          ·
            refine ⟨2191597304638977993131789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5844259479037274648351437 2191597304638977993131789)
            ·
              refine ⟨821848989239616747424421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2191597304638977993131789 821848989239616747424421)
              ·
                refine ⟨154096685482428140142079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 821848989239616747424421 154096685482428140142079)
                ·
                  rfl

theorem cell20_1012845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 4].length) (baseStart_1012845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012845 prefixEnd_1012845 := by exact prefixLift 1012845
  have htrace : WordTrace (prefixWord ++ tailWord_1012845) baseStart_1012845 baseEnd_1012845 := by
    simpa [prefixWord, tailWord_1012845, baseEnd_1012845] using wordTrace_append hprefix tailTrace_1012845
  have hstable : (prefixWord ++ tailWord_1012845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012845).length < 2 ^ (prefixWord ++ tailWord_1012845).sum := by decide
  have hdescent : baseEnd_1012845 < baseStart_1012845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012869 : List Nat := [1, 3, 1, 1, 6, 2, 1, 2, 3]
def baseStart_1012869 : Nat := 118140960795 + 1012869 * 2 ^ 59
def prefixEnd_1012869 : Nat := 4983230072969 + 3 ^ 40 * 1012869 * 2
def baseEnd_1012869 : Nat := 462301010701247003626139

theorem tailTrace_1012869 : CollatzResearch.WordTrace tailWord_1012869 prefixEnd_1012869 462301010701247003626139 := by
  unfold tailWord_1012869
  simp only [CollatzResearch.WordTrace]
  refine ⟨36942367367556072098329661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24628244911704048065553107 36942367367556072098329661)
  ·
    refine ⟨13853387762833527036873623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36942367367556072098329661 13853387762833527036873623)
    ·
      refine ⟨20780081644250290555310435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13853387762833527036873623 20780081644250290555310435)
      ·
        refine ⟨31170122466375435832965653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20780081644250290555310435 31170122466375435832965653)
        ·
          refine ⟨1461099490611348554670265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31170122466375435832965653 1461099490611348554670265)
          ·
            refine ⟨1095824617958511416002699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461099490611348554670265 1095824617958511416002699)
            ·
              refine ⟨1643736926937767124004049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095824617958511416002699 1643736926937767124004049)
              ·
                refine ⟨1232802695203325343003037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643736926937767124004049 1232802695203325343003037)
                ·
                  refine ⟨462301010701247003626139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232802695203325343003037 462301010701247003626139)
                  ·
                    rfl

theorem cell20_1012869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_1012869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012869 prefixEnd_1012869 := by exact prefixLift 1012869
  have htrace : WordTrace (prefixWord ++ tailWord_1012869) baseStart_1012869 baseEnd_1012869 := by
    simpa [prefixWord, tailWord_1012869, baseEnd_1012869] using wordTrace_append hprefix tailTrace_1012869
  have hstable : (prefixWord ++ tailWord_1012869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012869).length < 2 ^ (prefixWord ++ tailWord_1012869).sum := by decide
  have hdescent : baseEnd_1012869 < baseStart_1012869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012873 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 5]
def baseStart_1012873 : Nat := 118140960795 + 1012873 * 2 ^ 59
def prefixEnd_1012873 : Nat := 4983230072969 + 3 ^ 40 * 1012873 * 2
def baseEnd_1012873 : Nat := 462302836410240767492789

theorem tailTrace_1012873 : CollatzResearch.WordTrace tailWord_1012873 prefixEnd_1012873 462302836410240767492789 := by
  unfold tailWord_1012873
  simp only [CollatzResearch.WordTrace]
  refine ⟨36942513259541580781475273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24628342173027720520983515 36942513259541580781475273)
  ·
    refine ⟨27706884944656185586106455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36942513259541580781475273 27706884944656185586106455)
    ·
      refine ⟨41560327416984278379159683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27706884944656185586106455 41560327416984278379159683)
      ·
        refine ⟨62340491125476417568739525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41560327416984278379159683 62340491125476417568739525)
        ·
          refine ⟨11688842086026828294138661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62340491125476417568739525 11688842086026828294138661)
          ·
            refine ⟨2191657891130030305150999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11688842086026828294138661 2191657891130030305150999)
            ·
              refine ⟨3287486836695045457726499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2191657891130030305150999 3287486836695045457726499)
              ·
                refine ⟨4931230255042568186589749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3287486836695045457726499 4931230255042568186589749)
                ·
                  refine ⟨462302836410240767492789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4931230255042568186589749 462302836410240767492789)
                  ·
                    rfl

theorem cell20_1012873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_1012873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012873 prefixEnd_1012873 := by exact prefixLift 1012873
  have htrace : WordTrace (prefixWord ++ tailWord_1012873) baseStart_1012873 baseEnd_1012873 := by
    simpa [prefixWord, tailWord_1012873, baseEnd_1012873] using wordTrace_append hprefix tailTrace_1012873
  have hstable : (prefixWord ++ tailWord_1012873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012873).length < 2 ^ (prefixWord ++ tailWord_1012873).sum := by decide
  have hdescent : baseEnd_1012873 < baseStart_1012873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012914 : List Nat := [3, 2, 1, 1, 1, 4, 3, 3, 2]
def baseStart_1012914 : Nat := 118140960795 + 1012914 * 2 ^ 59
def prefixEnd_1012914 : Nat := 4983230072969 + 3 ^ 40 * 1012914 * 2
def baseEnd_1012914 : Nat := 462321549927426847125955

theorem tailTrace_1012914 : CollatzResearch.WordTrace tailWord_1012914 prefixEnd_1012914 462321549927426847125955 := by
  unfold tailWord_1012914
  simp only [CollatzResearch.WordTrace]
  refine ⟨9236002163098261195929449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24629339101595363189145197 9236002163098261195929449)
  ·
    refine ⟨6927001622323695896947087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9236002163098261195929449 6927001622323695896947087)
    ·
      refine ⟨10390502433485543845420631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6927001622323695896947087 10390502433485543845420631)
      ·
        refine ⟨15585753650228315768130947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10390502433485543845420631 15585753650228315768130947)
        ·
          refine ⟨23378630475342473652196421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15585753650228315768130947 23378630475342473652196421)
          ·
            refine ⟨4383493214126713809786829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23378630475342473652196421 4383493214126713809786829)
            ·
              refine ⟨1643809955297517678670061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4383493214126713809786829 1643809955297517678670061)
              ·
                refine ⟨616428733236569129501273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1643809955297517678670061 616428733236569129501273)
                ·
                  refine ⟨462321549927426847125955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616428733236569129501273 462321549927426847125955)
                  ·
                    rfl

theorem cell20_1012914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_1012914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012914 prefixEnd_1012914 := by exact prefixLift 1012914
  have htrace : WordTrace (prefixWord ++ tailWord_1012914) baseStart_1012914 baseEnd_1012914 := by
    simpa [prefixWord, tailWord_1012914, baseEnd_1012914] using wordTrace_append hprefix tailTrace_1012914
  have hstable : (prefixWord ++ tailWord_1012914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012914).length < 2 ^ (prefixWord ++ tailWord_1012914).sum := by decide
  have hdescent : baseEnd_1012914 < baseStart_1012914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012925 : List Nat := [1, 4, 1, 2, 1, 1, 10]
def baseStart_1012925 : Nat := 118140960795 + 1012925 * 2 ^ 59
def prefixEnd_1012925 : Nat := 4983230072969 + 3 ^ 40 * 1012925 * 2
def baseEnd_1012925 : Nat := 51369618958573299751027

theorem tailTrace_1012925 : CollatzResearch.WordTrace tailWord_1012925 prefixEnd_1012925 51369618958573299751027 := by
  unfold tailWord_1012925
  simp only [CollatzResearch.WordTrace]
  refine ⟨36944409855353193662368229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24629606570235462441578819 36944409855353193662368229)
  ·
    refine ⟨6927076847878723811694043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36944409855353193662368229 6927076847878723811694043)
    ·
      refine ⟨10390615271818085717541065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6927076847878723811694043 10390615271818085717541065)
      ·
        refine ⟨7792961453863564288155799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10390615271818085717541065 7792961453863564288155799)
        ·
          refine ⟨11689442180795346432233699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7792961453863564288155799 11689442180795346432233699)
          ·
            refine ⟨17534163271193019648350549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11689442180795346432233699 17534163271193019648350549)
            ·
              refine ⟨51369618958573299751027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17534163271193019648350549 51369618958573299751027)
              ·
                rfl

theorem cell20_1012925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 10].length) (baseStart_1012925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012925 prefixEnd_1012925 := by exact prefixLift 1012925
  have htrace : WordTrace (prefixWord ++ tailWord_1012925) baseStart_1012925 baseEnd_1012925 := by
    simpa [prefixWord, tailWord_1012925, baseEnd_1012925] using wordTrace_append hprefix tailTrace_1012925
  have hstable : (prefixWord ++ tailWord_1012925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012925).length < 2 ^ (prefixWord ++ tailWord_1012925).sum := by decide
  have hdescent : baseEnd_1012925 < baseStart_1012925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012935 : List Nat := [1, 1, 4, 1, 1, 1, 1, 8, 2]
def baseStart_1012935 : Nat := 118140960795 + 1012935 * 2 ^ 59
def prefixEnd_1012935 : Nat := 4983230072969 + 3 ^ 40 * 1012935 * 2
def baseEnd_1012935 : Nat := 462331134899644107425869

theorem tailTrace_1012935 : CollatzResearch.WordTrace tailWord_1012935 prefixEnd_1012935 462331134899644107425869 := by
  unfold tailWord_1012935
  simp only [CollatzResearch.WordTrace]
  refine ⟨36944774585316965370232259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24629849723544643580154839 36944774585316965370232259)
  ·
    refine ⟨55417161877975448055348389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36944774585316965370232259 55417161877975448055348389)
    ·
      refine ⟨10390717852120396510377823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55417161877975448055348389 10390717852120396510377823)
      ·
        refine ⟨15586076778180594765566735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10390717852120396510377823 15586076778180594765566735)
        ·
          refine ⟨23379115167270892148350103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15586076778180594765566735 23379115167270892148350103)
          ·
            refine ⟨35068672750906338222525155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23379115167270892148350103 35068672750906338222525155)
            ·
              refine ⟨52603009126359507333787733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35068672750906338222525155 52603009126359507333787733)
              ·
                refine ⟨616441513199525476567825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 52603009126359507333787733 616441513199525476567825)
                ·
                  refine ⟨462331134899644107425869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616441513199525476567825 462331134899644107425869)
                  ·
                    rfl

theorem cell20_1012935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 2].length) (baseStart_1012935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1012935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1012935 prefixEnd_1012935 := by exact prefixLift 1012935
  have htrace : WordTrace (prefixWord ++ tailWord_1012935) baseStart_1012935 baseEnd_1012935 := by
    simpa [prefixWord, tailWord_1012935, baseEnd_1012935] using wordTrace_append hprefix tailTrace_1012935
  have hstable : (prefixWord ++ tailWord_1012935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012935).length < 2 ^ (prefixWord ++ tailWord_1012935).sum := by decide
  have hdescent : baseEnd_1012935 < baseStart_1012935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013028 : List Nat := [2, 3, 1, 3, 1, 1, 4, 3, 2]
def baseStart_1013028 : Nat := 118140960795 + 1013028 * 2 ^ 59
def prefixEnd_1013028 : Nat := 4983230072969 + 3 ^ 40 * 1013028 * 2
def baseEnd_1013028 : Nat := 462373582633749117325489

theorem tailTrace_1013028 : CollatzResearch.WordTrace tailWord_1013028 prefixEnd_1013028 462373582633749117325489 := by
  unfold tailWord_1013028
  simp only [CollatzResearch.WordTrace]
  refine ⟨18474083286990021126683869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24632111049320028168911825 18474083286990021126683869)
  ·
    refine ⟨6927781232621257922506451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18474083286990021126683869 6927781232621257922506451)
    ·
      refine ⟨10391671848931886883759677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6927781232621257922506451 10391671848931886883759677)
      ·
        refine ⟨3896876943349457581409879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10391671848931886883759677 3896876943349457581409879)
        ·
          refine ⟨5845315415024186372114819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3896876943349457581409879 5845315415024186372114819)
          ·
            refine ⟨8767973122536279558172229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5845315415024186372114819 8767973122536279558172229)
            ·
              refine ⟨1643994960475552417157293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8767973122536279558172229 1643994960475552417157293)
              ·
                refine ⟨616498110178332156433985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1643994960475552417157293 616498110178332156433985)
                ·
                  refine ⟨462373582633749117325489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616498110178332156433985 462373582633749117325489)
                  ·
                    rfl

theorem cell20_1013028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_1013028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013028 prefixEnd_1013028 := by exact prefixLift 1013028
  have htrace : WordTrace (prefixWord ++ tailWord_1013028) baseStart_1013028 baseEnd_1013028 := by
    simpa [prefixWord, tailWord_1013028, baseEnd_1013028] using wordTrace_append hprefix tailTrace_1013028
  have hstable : (prefixWord ++ tailWord_1013028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013028).length < 2 ^ (prefixWord ++ tailWord_1013028).sum := by decide
  have hdescent : baseEnd_1013028 < baseStart_1013028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013042 : List Nat := [3, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_1013042 : Nat := 118140960795 + 1013042 * 2 ^ 59
def prefixEnd_1013042 : Nat := 4983230072969 + 3 ^ 40 * 1013042 * 2
def baseEnd_1013042 : Nat := 462379972615227290858765

theorem tailTrace_1013042 : CollatzResearch.WordTrace tailWord_1013042 prefixEnd_1013042 462379972615227290858765 := by
  unfold tailWord_1013042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9237169298982330661094345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24632451463952881762918253 9237169298982330661094345)
  ·
    refine ⟨6927876974236747995820759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9237169298982330661094345 6927876974236747995820759)
    ·
      refine ⟨10391815461355121993731139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6927876974236747995820759 10391815461355121993731139)
      ·
        refine ⟨15587723192032682990596709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10391815461355121993731139 15587723192032682990596709)
        ·
          refine ⟨2922698098506128060736883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15587723192032682990596709 2922698098506128060736883)
          ·
            refine ⟨4384047147759192091105325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922698098506128060736883 4384047147759192091105325)
            ·
              refine ⟨1644017680409697034164497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4384047147759192091105325 1644017680409697034164497)
              ·
                refine ⟨1233013260307272775623373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644017680409697034164497 1233013260307272775623373)
                ·
                  refine ⟨462379972615227290858765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233013260307272775623373 462379972615227290858765)
                  ·
                    rfl

theorem cell20_1013042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_1013042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013042 prefixEnd_1013042 := by exact prefixLift 1013042
  have htrace : WordTrace (prefixWord ++ tailWord_1013042) baseStart_1013042 baseEnd_1013042 := by
    simpa [prefixWord, tailWord_1013042, baseEnd_1013042] using wordTrace_append hprefix tailTrace_1013042
  have hstable : (prefixWord ++ tailWord_1013042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013042).length < 2 ^ (prefixWord ++ tailWord_1013042).sum := by decide
  have hdescent : baseEnd_1013042 < baseStart_1013042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013069 : List Nat := [1, 6, 1, 3, 1, 2, 2, 4]
def baseStart_1013069 : Nat := 118140960795 + 1013069 * 2 ^ 59
def prefixEnd_1013069 : Nat := 4983230072969 + 3 ^ 40 * 1013069 * 2
def baseEnd_1013069 : Nat := 154130765383645065652885

theorem tailTrace_1013069 : CollatzResearch.WordTrace tailWord_1013069 prefixEnd_1013069 154130765383645065652885 := by
  unfold tailWord_1013069
  simp only [CollatzResearch.WordTrace]
  refine ⟨36949661966831506255610261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24633107977887670837073507 36949661966831506255610261)
  ·
    refine ⟨1732015404695226855731731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36949661966831506255610261 1732015404695226855731731)
    ·
      refine ⟨2598023107042840283597597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1732015404695226855731731 2598023107042840283597597)
      ·
        refine ⟨974258665141065106349099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2598023107042840283597597 974258665141065106349099)
        ·
          refine ⟨1461387997711597659523649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974258665141065106349099 1461387997711597659523649)
          ·
            refine ⟨1096040998283698244642737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461387997711597659523649 1096040998283698244642737)
            ·
              refine ⟨822030748712773683482053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096040998283698244642737 822030748712773683482053)
              ·
                refine ⟨154130765383645065652885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 822030748712773683482053 154130765383645065652885)
                ·
                  rfl

theorem cell20_1013069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 4].length) (baseStart_1013069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013069 prefixEnd_1013069 := by exact prefixLift 1013069
  have htrace : WordTrace (prefixWord ++ tailWord_1013069) baseStart_1013069 baseEnd_1013069 := by
    simpa [prefixWord, tailWord_1013069, baseEnd_1013069] using wordTrace_append hprefix tailTrace_1013069
  have hstable : (prefixWord ++ tailWord_1013069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013069).length < 2 ^ (prefixWord ++ tailWord_1013069).sum := by decide
  have hdescent : baseEnd_1013069 < baseStart_1013069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013070 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1013070 : Nat := 118140960795 + 1013070 * 2 ^ 59
def prefixEnd_1013070 : Nat := 4983230072969 + 3 ^ 40 * 1013070 * 2
def baseEnd_1013070 : Nat := 462392752578183637925317

theorem tailTrace_1013070 : CollatzResearch.WordTrace tailWord_1013070 prefixEnd_1013070 462392752578183637925317 := by
  unfold tailWord_1013070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618712304978485428299583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24633132293218588950931109 4618712304978485428299583)
  ·
    refine ⟨6928068457467728142449375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4618712304978485428299583 6928068457467728142449375)
    ·
      refine ⟨10392102686201592213674063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6928068457467728142449375 10392102686201592213674063)
      ·
        refine ⟨15588154029302388320511095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10392102686201592213674063 15588154029302388320511095)
        ·
          refine ⟨23382231043953582480766643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15588154029302388320511095 23382231043953582480766643)
          ·
            refine ⟨35073346565930373721149965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23382231043953582480766643 35073346565930373721149965)
            ·
              refine ⟨13152504962223890145431237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35073346565930373721149965 13152504962223890145431237)
              ·
                refine ⟨2466094680416979402268357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13152504962223890145431237 2466094680416979402268357)
                ·
                  refine ⟨462392752578183637925317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2466094680416979402268357 462392752578183637925317)
                  ·
                    rfl

theorem cell20_1013070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1013070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013070 prefixEnd_1013070 := by exact prefixLift 1013070
  have htrace : WordTrace (prefixWord ++ tailWord_1013070) baseStart_1013070 baseEnd_1013070 := by
    simpa [prefixWord, tailWord_1013070, baseEnd_1013070] using wordTrace_append hprefix tailTrace_1013070
  have hstable : (prefixWord ++ tailWord_1013070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013070).length < 2 ^ (prefixWord ++ tailWord_1013070).sum := by decide
  have hdescent : baseEnd_1013070 < baseStart_1013070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013101 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1013101 : Nat := 118140960795 + 1013101 * 2 ^ 59
def prefixEnd_1013101 : Nat := 4983230072969 + 3 ^ 40 * 1013101 * 2
def baseEnd_1013101 : Nat := 462406901822885307891857

theorem tailTrace_1013101 : CollatzResearch.WordTrace tailWord_1013101 prefixEnd_1013101 462406901822885307891857 := by
  unfold tailWord_1013101
  simp only [CollatzResearch.WordTrace]
  refine ⟨36950829102715575720775157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24633886068477050480516771 36950829102715575720775157)
  ·
    refine ⟨3464140228379585223822671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36950829102715575720775157 3464140228379585223822671)
    ·
      refine ⟨5196210342569377835734007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3464140228379585223822671 5196210342569377835734007)
      ·
        refine ⟨7794315513854066753601011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5196210342569377835734007 7794315513854066753601011)
        ·
          refine ⟨11691473270781100130401517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7794315513854066753601011 11691473270781100130401517)
          ·
            refine ⟨4384302476542912548900569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11691473270781100130401517 4384302476542912548900569)
            ·
              refine ⟨3288226857407184411675427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4384302476542912548900569 3288226857407184411675427)
              ·
                refine ⟨4932340286110776617513141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288226857407184411675427 4932340286110776617513141)
                ·
                  refine ⟨462406901822885307891857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4932340286110776617513141 462406901822885307891857)
                  ·
                    rfl

theorem cell20_1013101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1013101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013101 prefixEnd_1013101 := by exact prefixLift 1013101
  have htrace : WordTrace (prefixWord ++ tailWord_1013101) baseStart_1013101 baseEnd_1013101 := by
    simpa [prefixWord, tailWord_1013101, baseEnd_1013101] using wordTrace_append hprefix tailTrace_1013101
  have hstable : (prefixWord ++ tailWord_1013101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013101).length < 2 ^ (prefixWord ++ tailWord_1013101).sum := by decide
  have hdescent : baseEnd_1013101 < baseStart_1013101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013104 : List Nat := [2, 1, 1, 1, 4, 2, 5, 2, 2]
def baseStart_1013104 : Nat := 118140960795 + 1013104 * 2 ^ 59
def prefixEnd_1013104 : Nat := 4983230072969 + 3 ^ 40 * 1013104 * 2
def baseEnd_1013104 : Nat := 462408271104630630791845

theorem tailTrace_1013104 : CollatzResearch.WordTrace tailWord_1013104 prefixEnd_1013104 462408271104630630791845 := by
  unfold tailWord_1013104
  simp only [CollatzResearch.WordTrace]
  refine ⟨18475469260852353616567183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24633959014469804822089577 18475469260852353616567183)
  ·
    refine ⟨27713203891278530424850775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18475469260852353616567183 27713203891278530424850775)
    ·
      refine ⟨41569805836917795637276163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27713203891278530424850775 41569805836917795637276163)
      ·
        refine ⟨62354708755376693455914245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41569805836917795637276163 62354708755376693455914245)
        ·
          refine ⟨11691507891633130022983921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62354708755376693455914245 11691507891633130022983921)
          ·
            refine ⟨8768630918724847517237941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11691507891633130022983921 8768630918724847517237941)
            ·
              refine ⟨822059148630454454741057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8768630918724847517237941 822059148630454454741057)
              ·
                refine ⟨616544361472840841055793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822059148630454454741057 616544361472840841055793)
                ·
                  refine ⟨462408271104630630791845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616544361472840841055793 462408271104630630791845)
                  ·
                    rfl

theorem cell20_1013104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 2].length) (baseStart_1013104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013104 prefixEnd_1013104 := by exact prefixLift 1013104
  have htrace : WordTrace (prefixWord ++ tailWord_1013104) baseStart_1013104 baseEnd_1013104 := by
    simpa [prefixWord, tailWord_1013104, baseEnd_1013104] using wordTrace_append hprefix tailTrace_1013104
  have hstable : (prefixWord ++ tailWord_1013104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013104).length < 2 ^ (prefixWord ++ tailWord_1013104).sum := by decide
  have hdescent : baseEnd_1013104 < baseStart_1013104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013115 : List Nat := [1, 1, 1, 1, 1, 6, 4, 5]
def baseStart_1013115 : Nat := 118140960795 + 1013115 * 2 ^ 59
def prefixEnd_1013115 : Nat := 4983230072969 + 3 ^ 40 * 1013115 * 2
def baseEnd_1013115 : Nat := 154137763934787827141711

theorem tailTrace_1013115 : CollatzResearch.WordTrace tailWord_1013115 prefixEnd_1013115 154137763934787827141711 := by
  unfold tailWord_1013115
  simp only [CollatzResearch.WordTrace]
  refine ⟨36951339724664856111784799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24634226483109904074523199 36951339724664856111784799)
  ·
    refine ⟨55427009586997284167677199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36951339724664856111784799 55427009586997284167677199)
    ·
      refine ⟨83140514380495926251515799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55427009586997284167677199 83140514380495926251515799)
      ·
        refine ⟨124710771570743889377273699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83140514380495926251515799 124710771570743889377273699)
        ·
          refine ⟨187066157356115834065910549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124710771570743889377273699 187066157356115834065910549)
          ·
            refine ⟨8768726126067929721839557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187066157356115834065910549 8768726126067929721839557)
            ·
              refine ⟨1644136148637736822844917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8768726126067929721839557 1644136148637736822844917)
              ·
                refine ⟨154137763934787827141711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1644136148637736822844917 154137763934787827141711)
                ·
                  rfl

theorem cell20_1013115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_1013115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013115 prefixEnd_1013115 := by exact prefixLift 1013115
  have htrace : WordTrace (prefixWord ++ tailWord_1013115) baseStart_1013115 baseEnd_1013115 := by
    simpa [prefixWord, tailWord_1013115, baseEnd_1013115] using wordTrace_append hprefix tailTrace_1013115
  have hstable : (prefixWord ++ tailWord_1013115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013115).length < 2 ^ (prefixWord ++ tailWord_1013115).sum := by decide
  have hdescent : baseEnd_1013115 < baseStart_1013115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013167 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 8]
def baseStart_1013167 : Nat := 118140960795 + 1013167 * 2 ^ 59
def prefixEnd_1013167 : Nat := 4983230072969 + 3 ^ 40 * 1013167 * 2
def baseEnd_1013167 : Nat := 462437026021282411691587

theorem tailTrace_1013167 : CollatzResearch.WordTrace tailWord_1013167 prefixEnd_1013167 462437026021282411691587 := by
  unfold tailWord_1013167
  simp only [CollatzResearch.WordTrace]
  refine ⟨36953236320476468992677755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24635490880317645995118503 36953236320476468992677755)
  ·
    refine ⟨55429854480714703489016633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36953236320476468992677755 55429854480714703489016633)
    ·
      refine ⟨41572390860536027616762475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55429854480714703489016633 41572390860536027616762475)
      ·
        refine ⟨62358586290804041425143713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41572390860536027616762475 62358586290804041425143713)
        ·
          refine ⟨46768939718103031068857785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62358586290804041425143713 46768939718103031068857785)
          ·
            refine ⟨35076704788577273301643339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46768939718103031068857785 35076704788577273301643339)
            ·
              refine ⟨52615057182865909952465009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35076704788577273301643339 52615057182865909952465009)
              ·
                refine ⟨39461292887149432464348757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52615057182865909952465009 39461292887149432464348757)
                ·
                  refine ⟨462437026021282411691587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39461292887149432464348757 462437026021282411691587)
                  ·
                    rfl

theorem cell20_1013167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_1013167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013167 prefixEnd_1013167 := by exact prefixLift 1013167
  have htrace : WordTrace (prefixWord ++ tailWord_1013167) baseStart_1013167 baseEnd_1013167 := by
    simpa [prefixWord, tailWord_1013167, baseEnd_1013167] using wordTrace_append hprefix tailTrace_1013167
  have hstable : (prefixWord ++ tailWord_1013167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013167).length < 2 ^ (prefixWord ++ tailWord_1013167).sum := by decide
  have hdescent : baseEnd_1013167 < baseStart_1013167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013232 : List Nat := [2, 1, 1, 1, 3, 5, 3, 1, 3]
def baseStart_1013232 : Nat := 118140960795 + 1013232 * 2 ^ 59
def prefixEnd_1013232 : Nat := 4983230072969 + 3 ^ 40 * 1013232 * 2
def baseEnd_1013232 : Nat := 462466693792431074524655

theorem tailTrace_1013232 : CollatzResearch.WordTrace tailWord_1013232 prefixEnd_1013232 462466693792431074524655 := by
  unfold tailWord_1013232
  simp only [CollatzResearch.WordTrace]
  refine ⟨18477803532620492546896975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24637071376827323395862633 18477803532620492546896975)
  ·
    refine ⟨27716705298930738820345463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18477803532620492546896975 27716705298930738820345463)
    ·
      refine ⟨41575057948396108230518195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27716705298930738820345463 41575057948396108230518195)
      ·
        refine ⟨62362586922594162345777293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41575057948396108230518195 62362586922594162345777293)
        ·
          refine ⟨23385970095972810879666485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62362586922594162345777293 23385970095972810879666485)
          ·
            refine ⟨2192434696497451019968733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23385970095972810879666485 2192434696497451019968733)
            ·
              refine ⟨822163011186544132488275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2192434696497451019968733 822163011186544132488275)
              ·
                refine ⟨1233244516779816198732413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822163011186544132488275 1233244516779816198732413)
                ·
                  refine ⟨462466693792431074524655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233244516779816198732413 462466693792431074524655)
                  ·
                    rfl

theorem cell20_1013232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_1013232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013232 prefixEnd_1013232 := by exact prefixLift 1013232
  have htrace : WordTrace (prefixWord ++ tailWord_1013232) baseStart_1013232 baseEnd_1013232 := by
    simpa [prefixWord, tailWord_1013232, baseEnd_1013232] using wordTrace_append hprefix tailTrace_1013232
  have hstable : (prefixWord ++ tailWord_1013232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013232).length < 2 ^ (prefixWord ++ tailWord_1013232).sum := by decide
  have hdescent : baseEnd_1013232 < baseStart_1013232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013252 : List Nat := [2, 3, 2, 3, 3, 1, 1, 3, 2]
def baseStart_1013252 : Nat := 118140960795 + 1013252 * 2 ^ 59
def prefixEnd_1013252 : Nat := 4983230072969 + 3 ^ 40 * 1013252 * 2
def baseEnd_1013252 : Nat := 462475822337399893857907

theorem tailTrace_1013252 : CollatzResearch.WordTrace tailWord_1013252 prefixEnd_1013252 462475822337399893857907 := by
  unfold tailWord_1013252
  simp only [CollatzResearch.WordTrace]
  refine ⟨18478168262584264254761005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24637557683445685673014673 18478168262584264254761005)
  ·
    refine ⟨6929313098469099095535377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18478168262584264254761005 6929313098469099095535377)
    ·
      refine ⟨5196984823851824321651533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6929313098469099095535377 5196984823851824321651533)
      ·
        refine ⟨1948869308944434120619325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5196984823851824321651533 1948869308944434120619325)
        ·
          refine ⟨730825990854162795232247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1948869308944434120619325 730825990854162795232247)
          ·
            refine ⟨1096238986281244192848371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730825990854162795232247 1096238986281244192848371)
            ·
              refine ⟨1644358479421866289272557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096238986281244192848371 1644358479421866289272557)
              ·
                refine ⟨616634429783199858477209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1644358479421866289272557 616634429783199858477209)
                ·
                  refine ⟨462475822337399893857907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616634429783199858477209 462475822337399893857907)
                  ·
                    rfl

theorem cell20_1013252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_1013252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013252 prefixEnd_1013252 := by exact prefixLift 1013252
  have htrace : WordTrace (prefixWord ++ tailWord_1013252) baseStart_1013252 baseEnd_1013252 := by
    simpa [prefixWord, tailWord_1013252, baseEnd_1013252] using wordTrace_append hprefix tailTrace_1013252
  have hstable : (prefixWord ++ tailWord_1013252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013252).length < 2 ^ (prefixWord ++ tailWord_1013252).sum := by decide
  have hdescent : baseEnd_1013252 < baseStart_1013252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013267 : List Nat := [1, 1, 1, 2, 1, 8, 6]
def baseStart_1013267 : Nat := 118140960795 + 1013267 * 2 ^ 59
def prefixEnd_1013267 : Nat := 4983230072969 + 3 ^ 40 * 1013267 * 2
def baseEnd_1013267 : Nat := 51386963194014056484205

theorem tailTrace_1013267 : CollatzResearch.WordTrace tailWord_1013267 prefixEnd_1013267 51386963194014056484205 := by
  unfold tailWord_1013267
  simp only [CollatzResearch.WordTrace]
  refine ⟨36956883620114186071318055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24637922413409457380878703 36956883620114186071318055)
  ·
    refine ⟨55435325430171279106977083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36956883620114186071318055 55435325430171279106977083)
    ·
      refine ⟨83152988145256918660465625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55435325430171279106977083 83152988145256918660465625)
      ·
        refine ⟨62364741108942688995349219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83152988145256918660465625 62364741108942688995349219)
        ·
          refine ⟨93547111663414033493023829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62364741108942688995349219 93547111663414033493023829)
          ·
            refine ⟨1096255214805633204996373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 93547111663414033493023829 1096255214805633204996373)
            ·
              refine ⟨51386963194014056484205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1096255214805633204996373 51386963194014056484205)
              ·
                rfl

theorem cell20_1013267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 6].length) (baseStart_1013267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013267 prefixEnd_1013267 := by exact prefixLift 1013267
  have htrace : WordTrace (prefixWord ++ tailWord_1013267) baseStart_1013267 baseEnd_1013267 := by
    simpa [prefixWord, tailWord_1013267, baseEnd_1013267] using wordTrace_append hprefix tailTrace_1013267
  have hstable : (prefixWord ++ tailWord_1013267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013267).length < 2 ^ (prefixWord ++ tailWord_1013267).sum := by decide
  have hdescent : baseEnd_1013267 < baseStart_1013267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013305 : List Nat := [1, 2, 1, 5, 1, 2, 2, 6]
def baseStart_1013305 : Nat := 118140960795 + 1013305 * 2 ^ 59
def prefixEnd_1013305 : Nat := 4983230072969 + 3 ^ 40 * 1013305 * 2
def baseEnd_1013305 : Nat := 154166670993855755030341

theorem tailTrace_1013305 : CollatzResearch.WordTrace tailWord_1013305 prefixEnd_1013305 154166670993855755030341 := by
  unfold tailWord_1013305
  simp only [CollatzResearch.WordTrace]
  refine ⟨36958269593976518561201369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24638846395984345707467579 36958269593976518561201369)
  ·
    refine ⟨27718702195482388920901027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36958269593976518561201369 27718702195482388920901027)
    ·
      refine ⟨41578053293223583381351541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27718702195482388920901027 41578053293223583381351541)
      ·
        refine ⟨3897942496239710942001707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41578053293223583381351541 3897942496239710942001707)
        ·
          refine ⟨5846913744359566413002561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3897942496239710942001707 5846913744359566413002561)
          ·
            refine ⟨4385185308269674809751921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5846913744359566413002561 4385185308269674809751921)
            ·
              refine ⟨3288888981202256107313941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4385185308269674809751921 3288888981202256107313941)
              ·
                refine ⟨154166670993855755030341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3288888981202256107313941 154166670993855755030341)
                ·
                  rfl

theorem cell20_1013305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_1013305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013305 prefixEnd_1013305 := by exact prefixLift 1013305
  have htrace : WordTrace (prefixWord ++ tailWord_1013305) baseStart_1013305 baseEnd_1013305 := by
    simpa [prefixWord, tailWord_1013305, baseEnd_1013305] using wordTrace_append hprefix tailTrace_1013305
  have hstable : (prefixWord ++ tailWord_1013305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013305).length < 2 ^ (prefixWord ++ tailWord_1013305).sum := by decide
  have hdescent : baseEnd_1013305 < baseStart_1013305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013325 : List Nat := [1, 6, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1013325 : Nat := 118140960795 + 1013325 * 2 ^ 59
def prefixEnd_1013325 : Nat := 4983230072969 + 3 ^ 40 * 1013325 * 2
def baseEnd_1013325 : Nat := 462509141526536084424275

theorem tailTrace_1013325 : CollatzResearch.WordTrace tailWord_1013325 prefixEnd_1013325 462509141526536084424275 := by
  unfold tailWord_1013325
  simp only [CollatzResearch.WordTrace]
  refine ⟨36958999053904061976929429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24639332702602707984619619 36958999053904061976929429)
  ·
    refine ⟨1732453080651752905168567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36958999053904061976929429 1732453080651752905168567)
    ·
      refine ⟨2598679620977629357752851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1732453080651752905168567 2598679620977629357752851)
      ·
        refine ⟨3898019431466444036629277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2598679620977629357752851 3898019431466444036629277)
        ·
          refine ⟨1461757286799916513735979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3898019431466444036629277 1461757286799916513735979)
          ·
            refine ⟨2192635930199874770603969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461757286799916513735979 2192635930199874770603969)
            ·
              refine ⟨1644476947649906077952977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2192635930199874770603969 1644476947649906077952977)
              ·
                refine ⟨1233357710737429558464733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644476947649906077952977 1233357710737429558464733)
                ·
                  refine ⟨462509141526536084424275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233357710737429558464733 462509141526536084424275)
                  ·
                    rfl

theorem cell20_1013325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1013325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013325 prefixEnd_1013325 := by exact prefixLift 1013325
  have htrace : WordTrace (prefixWord ++ tailWord_1013325) baseStart_1013325 baseEnd_1013325 := by
    simpa [prefixWord, tailWord_1013325, baseEnd_1013325] using wordTrace_append hprefix tailTrace_1013325
  have hstable : (prefixWord ++ tailWord_1013325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013325).length < 2 ^ (prefixWord ++ tailWord_1013325).sum := by decide
  have hdescent : baseEnd_1013325 < baseStart_1013325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013329 : List Nat := [1, 2, 2, 1, 3, 2, 4, 2, 3]
def baseStart_1013329 : Nat := 118140960795 + 1013329 * 2 ^ 59
def prefixEnd_1013329 : Nat := 4983230072969 + 3 ^ 40 * 1013329 * 2
def baseEnd_1013329 : Nat := 462510967235529848290925

theorem tailTrace_1013329 : CollatzResearch.WordTrace tailWord_1013329 prefixEnd_1013329 462510967235529848290925 := by
  unfold tailWord_1013329
  simp only [CollatzResearch.WordTrace]
  refine ⟨36959144945889570660075041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24639429963926380440050027 36959144945889570660075041)
  ·
    refine ⟨27719358709417177995056281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36959144945889570660075041 27719358709417177995056281)
    ·
      refine ⟨20789519032062883496292211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27719358709417177995056281 20789519032062883496292211)
      ·
        refine ⟨31184278548094325244438317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20789519032062883496292211 31184278548094325244438317)
        ·
          refine ⟨11694104455535371966664369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31184278548094325244438317 11694104455535371966664369)
          ·
            refine ⟨8770578341651528974998277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11694104455535371966664369 8770578341651528974998277)
            ·
              refine ⟨1644483439059661682812177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8770578341651528974998277 1644483439059661682812177)
              ·
                refine ⟨1233362579294746262109133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644483439059661682812177 1233362579294746262109133)
                ·
                  refine ⟨462510967235529848290925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233362579294746262109133 462510967235529848290925)
                  ·
                    rfl

theorem cell20_1013329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_1013329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013329 prefixEnd_1013329 := by exact prefixLift 1013329
  have htrace : WordTrace (prefixWord ++ tailWord_1013329) baseStart_1013329 baseEnd_1013329 := by
    simpa [prefixWord, tailWord_1013329, baseEnd_1013329] using wordTrace_append hprefix tailTrace_1013329
  have hstable : (prefixWord ++ tailWord_1013329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013329).length < 2 ^ (prefixWord ++ tailWord_1013329).sum := by decide
  have hdescent : baseEnd_1013329 < baseStart_1013329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013360 : List Nat := [2, 1, 1, 1, 6, 2, 3, 4]
def baseStart_1013360 : Nat := 118140960795 + 1013360 * 2 ^ 59
def prefixEnd_1013360 : Nat := 4983230072969 + 3 ^ 40 * 1013360 * 2
def baseEnd_1013360 : Nat := 154175038826743839419155

theorem tailTrace_1013360 : CollatzResearch.WordTrace tailWord_1013360 prefixEnd_1013360 154175038826743839419155 := by
  unfold tailWord_1013360
  simp only [CollatzResearch.WordTrace]
  refine ⟨18480137804388631477226767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24640183739184841969635689 18480137804388631477226767)
  ·
    refine ⟨27720206706582947215840151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18480137804388631477226767 27720206706582947215840151)
    ·
      refine ⟨41580310059874420823760227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27720206706582947215840151 41580310059874420823760227)
      ·
        refine ⟨62370465089811631235640341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41580310059874420823760227 62370465089811631235640341)
        ·
          refine ⟨2923615551084920214170641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62370465089811631235640341 2923615551084920214170641)
          ·
            refine ⟨2192711663313690160627981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2923615551084920214170641 2192711663313690160627981)
            ·
              refine ⟨822266873742633810235493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2192711663313690160627981 822266873742633810235493)
              ·
                refine ⟨154175038826743839419155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 822266873742633810235493 154175038826743839419155)
                ·
                  rfl

theorem cell20_1013360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_1013360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013360 prefixEnd_1013360 := by exact prefixLift 1013360
  have htrace : WordTrace (prefixWord ++ tailWord_1013360) baseStart_1013360 baseEnd_1013360 := by
    simpa [prefixWord, tailWord_1013360, baseEnd_1013360] using wordTrace_append hprefix tailTrace_1013360
  have hstable : (prefixWord ++ tailWord_1013360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013360).length < 2 ^ (prefixWord ++ tailWord_1013360).sum := by decide
  have hdescent : baseEnd_1013360 < baseStart_1013360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013384 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 5]
def baseStart_1013384 : Nat := 118140960795 + 1013384 * 2 ^ 59
def prefixEnd_1013384 : Nat := 4983230072969 + 3 ^ 40 * 1013384 * 2
def baseEnd_1013384 : Nat := 462536070734194101457367

theorem tailTrace_1013384 : CollatzResearch.WordTrace tailWord_1013384 prefixEnd_1013384 462536070734194101457367 := by
  unfold tailWord_1013384
  simp only [CollatzResearch.WordTrace]
  refine ⟨18480575480345157526663603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24640767307126876702218137 18480575480345157526663603)
  ·
    refine ⟨27720863220517736289995405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18480575480345157526663603 27720863220517736289995405)
    ·
      refine ⟨10395323707694151108748277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27720863220517736289995405 10395323707694151108748277)
      ·
        refine ⟨974561597596326666445151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10395323707694151108748277 974561597596326666445151)
        ·
          refine ⟨1461842396394489999667727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974561597596326666445151 1461842396394489999667727)
          ·
            refine ⟨2192763594591734999501591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461842396394489999667727 2192763594591734999501591)
            ·
              refine ⟨3289145391887602499252387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192763594591734999501591 3289145391887602499252387)
              ·
                refine ⟨4933718087831403748878581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289145391887602499252387 4933718087831403748878581)
                ·
                  refine ⟨462536070734194101457367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4933718087831403748878581 462536070734194101457367)
                  ·
                    rfl

theorem cell20_1013384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_1013384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013384 prefixEnd_1013384 := by exact prefixLift 1013384
  have htrace : WordTrace (prefixWord ++ tailWord_1013384) baseStart_1013384 baseEnd_1013384 := by
    simpa [prefixWord, tailWord_1013384, baseEnd_1013384] using wordTrace_append hprefix tailTrace_1013384
  have hstable : (prefixWord ++ tailWord_1013384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013384).length < 2 ^ (prefixWord ++ tailWord_1013384).sum := by decide
  have hdescent : baseEnd_1013384 < baseStart_1013384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013388 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_1013388 : Nat := 118140960795 + 1013388 * 2 ^ 59
def prefixEnd_1013388 : Nat := 4983230072969 + 3 ^ 40 * 1013388 * 2
def baseEnd_1013388 : Nat := 462537896443187865324017

theorem tailTrace_1013388 : CollatzResearch.WordTrace tailWord_1013388 prefixEnd_1013388 462537896443187865324017 := by
  unfold tailWord_1013388
  simp only [CollatzResearch.WordTrace]
  refine ⟨18480648426337911868236409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24640864568450549157648545 18480648426337911868236409)
  ·
    refine ⟨13860486319753433901177307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18480648426337911868236409 13860486319753433901177307)
    ·
      refine ⟨20790729479630150851765961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13860486319753433901177307 20790729479630150851765961)
      ·
        refine ⟨15593047109722613138824471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20790729479630150851765961 15593047109722613138824471)
        ·
          refine ⟨23389570664583919708236707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15593047109722613138824471 23389570664583919708236707)
          ·
            refine ⟨35084355996875879562355061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23389570664583919708236707 35084355996875879562355061)
            ·
              refine ⟨3289158374707113708970787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35084355996875879562355061 3289158374707113708970787)
              ·
                refine ⟨4933737562060670563456181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289158374707113708970787 4933737562060670563456181)
                ·
                  refine ⟨462537896443187865324017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4933737562060670563456181 462537896443187865324017)
                  ·
                    rfl

theorem cell20_1013388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_1013388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013388 prefixEnd_1013388 := by exact prefixLift 1013388
  have htrace : WordTrace (prefixWord ++ tailWord_1013388) baseStart_1013388 baseEnd_1013388 := by
    simpa [prefixWord, tailWord_1013388, baseEnd_1013388] using wordTrace_append hprefix tailTrace_1013388
  have hstable : (prefixWord ++ tailWord_1013388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013388).length < 2 ^ (prefixWord ++ tailWord_1013388).sum := by decide
  have hdescent : baseEnd_1013388 < baseStart_1013388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013412 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1013412 : Nat := 118140960795 + 1013412 * 2 ^ 59
def prefixEnd_1013412 : Nat := 4983230072969 + 3 ^ 40 * 1013412 * 2
def baseEnd_1013412 : Nat := 462548850697150448523919

theorem tailTrace_1013412 : CollatzResearch.WordTrace tailWord_1013412 prefixEnd_1013412 462548850697150448523919 := by
  unfold tailWord_1013412
  simp only [CollatzResearch.WordTrace]
  refine ⟨18481086102294437917673245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24641448136392583890230993 18481086102294437917673245)
  ·
    refine ⟨6930407288360414219127467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18481086102294437917673245 6930407288360414219127467)
    ·
      refine ⟨10395610932540621328691201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6930407288360414219127467 10395610932540621328691201)
      ·
        refine ⟨7796708199405465996518401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10395610932540621328691201 7796708199405465996518401)
        ·
          refine ⟨5847531149554099497388801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7796708199405465996518401 5847531149554099497388801)
          ·
            refine ⟨4385648362165574623041601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5847531149554099497388801 4385648362165574623041601)
            ·
              refine ⟨3289236271624180967281201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4385648362165574623041601 3289236271624180967281201)
              ·
                refine ⟨2466927203718135725460901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3289236271624180967281201 2466927203718135725460901)
                ·
                  refine ⟨462548850697150448523919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2466927203718135725460901 462548850697150448523919)
                  ·
                    rfl

theorem cell20_1013412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1013412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013412 prefixEnd_1013412 := by exact prefixLift 1013412
  have htrace : WordTrace (prefixWord ++ tailWord_1013412) baseStart_1013412 baseEnd_1013412 := by
    simpa [prefixWord, tailWord_1013412, baseEnd_1013412] using wordTrace_append hprefix tailTrace_1013412
  have hstable : (prefixWord ++ tailWord_1013412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013412).length < 2 ^ (prefixWord ++ tailWord_1013412).sum := by decide
  have hdescent : baseEnd_1013412 < baseStart_1013412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013426 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1013426 : Nat := 118140960795 + 1013426 * 2 ^ 59
def prefixEnd_1013426 : Nat := 4983230072969 + 3 ^ 40 * 1013426 * 2
def baseEnd_1013426 : Nat := 462555240678628622057195

theorem tailTrace_1013426 : CollatzResearch.WordTrace tailWord_1013426 prefixEnd_1013426 462555240678628622057195 := by
  unfold tailWord_1013426
  simp only [CollatzResearch.WordTrace]
  refine ⟨9240670706634539056589033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24641788551025437484237421 9240670706634539056589033)
  ·
    refine ⟨6930503029975904292441775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9240670706634539056589033 6930503029975904292441775)
    ·
      refine ⟨10395754544963856438662663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6930503029975904292441775 10395754544963856438662663)
      ·
        refine ⟨15593631817445784657993995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10395754544963856438662663 15593631817445784657993995)
        ·
          refine ⟨23390447726168676986990993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15593631817445784657993995 23390447726168676986990993)
          ·
            refine ⟨17542835794626507740243245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23390447726168676986990993 17542835794626507740243245)
            ·
              refine ⟨6578563422984940402591217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17542835794626507740243245 6578563422984940402591217)
              ·
                refine ⟨4933922567238705301943413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6578563422984940402591217 4933922567238705301943413)
                ·
                  refine ⟨462555240678628622057195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4933922567238705301943413 462555240678628622057195)
                  ·
                    rfl

theorem cell20_1013426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1013426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013426 prefixEnd_1013426 := by exact prefixLift 1013426
  have htrace : WordTrace (prefixWord ++ tailWord_1013426) baseStart_1013426 baseEnd_1013426 := by
    simpa [prefixWord, tailWord_1013426, baseEnd_1013426] using wordTrace_append hprefix tailTrace_1013426
  have hstable : (prefixWord ++ tailWord_1013426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013426).length < 2 ^ (prefixWord ++ tailWord_1013426).sum := by decide
  have hdescent : baseEnd_1013426 < baseStart_1013426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013433 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 6]
def baseStart_1013433 : Nat := 118140960795 + 1013433 * 2 ^ 59
def prefixEnd_1013433 : Nat := 4983230072969 + 3 ^ 40 * 1013433 * 2
def baseEnd_1013433 : Nat := 462558435669367708823833

theorem tailTrace_1013433 : CollatzResearch.WordTrace tailWord_1013433 prefixEnd_1013433 462558435669367708823833 := by
  unfold tailWord_1013433
  simp only [CollatzResearch.WordTrace]
  refine ⟨36962938137512796421860953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24641958758341864281240635 36962938137512796421860953)
  ·
    refine ⟨27722203603134597316395715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36962938137512796421860953 27722203603134597316395715)
    ·
      refine ⟨41583305404701895974593573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27722203603134597316395715 41583305404701895974593573)
      ·
        refine ⟨7796869763381605495236295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41583305404701895974593573 7796869763381605495236295)
        ·
          refine ⟨11695304645072408242854443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7796869763381605495236295 11695304645072408242854443)
          ·
            refine ⟨17542956967608612364281665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11695304645072408242854443 17542956967608612364281665)
            ·
              refine ⟨13157217725706459273211249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17542956967608612364281665 13157217725706459273211249)
              ·
                refine ⟨9867913294279844454908437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13157217725706459273211249 9867913294279844454908437)
                ·
                  refine ⟨462558435669367708823833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9867913294279844454908437 462558435669367708823833)
                  ·
                    rfl

theorem cell20_1013433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_1013433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013433 prefixEnd_1013433 := by exact prefixLift 1013433
  have htrace : WordTrace (prefixWord ++ tailWord_1013433) baseStart_1013433 baseEnd_1013433 := by
    simpa [prefixWord, tailWord_1013433, baseEnd_1013433] using wordTrace_append hprefix tailTrace_1013433
  have hstable : (prefixWord ++ tailWord_1013433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013433).length < 2 ^ (prefixWord ++ tailWord_1013433).sum := by decide
  have hdescent : baseEnd_1013433 < baseStart_1013433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013442 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1013442 : Nat := 118140960795 + 1013442 * 2 ^ 59
def prefixEnd_1013442 : Nat := 4983230072969 + 3 ^ 40 * 1013442 * 2
def baseEnd_1013442 : Nat := 462562543514603677523797

theorem tailTrace_1013442 : CollatzResearch.WordTrace tailWord_1013442 prefixEnd_1013442 462562543514603677523797 := by
  unfold tailWord_1013442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9240816598620047739734645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24642177596320127305959053 9240816598620047739734645)
  ·
    refine ⟨866326556120629475600123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9240816598620047739734645 866326556120629475600123)
    ·
      refine ⟨1299489834180944213400185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866326556120629475600123 1299489834180944213400185)
      ·
        refine ⟨974617375635708160050139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1299489834180944213400185 974617375635708160050139)
        ·
          refine ⟨1461926063453562240075209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974617375635708160050139 1461926063453562240075209)
          ·
            refine ⟨1096444547590171680056407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461926063453562240075209 1096444547590171680056407)
            ·
              refine ⟨1644666821385257520084611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096444547590171680056407 1644666821385257520084611)
              ·
                refine ⟨2467000232077886280126917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644666821385257520084611 2467000232077886280126917)
                ·
                  refine ⟨462562543514603677523797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2467000232077886280126917 462562543514603677523797)
                  ·
                    rfl

theorem cell20_1013442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1013442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013442 prefixEnd_1013442 := by exact prefixLift 1013442
  have htrace : WordTrace (prefixWord ++ tailWord_1013442) baseStart_1013442 baseEnd_1013442 := by
    simpa [prefixWord, tailWord_1013442, baseEnd_1013442] using wordTrace_append hprefix tailTrace_1013442
  have hstable : (prefixWord ++ tailWord_1013442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013442).length < 2 ^ (prefixWord ++ tailWord_1013442).sum := by decide
  have hdescent : baseEnd_1013442 < baseStart_1013442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013453 : List Nat := [1, 6, 2, 1, 1, 2, 2, 5]
def baseStart_1013453 : Nat := 118140960795 + 1013453 * 2 ^ 59
def prefixEnd_1013453 : Nat := 4983230072969 + 3 ^ 40 * 1013453 * 2
def baseEnd_1013453 : Nat := 154189188071445509385695

theorem tailTrace_1013453 : CollatzResearch.WordTrace tailWord_1013453 prefixEnd_1013453 154189188071445509385695 := by
  unfold tailWord_1013453
  simp only [CollatzResearch.WordTrace]
  refine ⟨36963667597440339837589013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24642445064960226558392675 36963667597440339837589013)
  ·
    refine ⟨1732671918630015929886985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36963667597440339837589013 1732671918630015929886985)
    ·
      refine ⟨1299503938972511947415239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1732671918630015929886985 1299503938972511947415239)
      ·
        refine ⟨1949255908458767921122859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299503938972511947415239 1949255908458767921122859)
        ·
          refine ⟨2923883862688151881684289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1949255908458767921122859 2923883862688151881684289)
          ·
            refine ⟨2192912897016113911263217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2923883862688151881684289 2192912897016113911263217)
            ·
              refine ⟨1644684672762085433447413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2192912897016113911263217 1644684672762085433447413)
              ·
                refine ⟨154189188071445509385695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1644684672762085433447413 154189188071445509385695)
                ·
                  rfl

theorem cell20_1013453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 5].length) (baseStart_1013453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013453 prefixEnd_1013453 := by exact prefixLift 1013453
  have htrace : WordTrace (prefixWord ++ tailWord_1013453) baseStart_1013453 baseEnd_1013453 := by
    simpa [prefixWord, tailWord_1013453, baseEnd_1013453] using wordTrace_append hprefix tailTrace_1013453
  have hstable : (prefixWord ++ tailWord_1013453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013453).length < 2 ^ (prefixWord ++ tailWord_1013453).sum := by decide
  have hdescent : baseEnd_1013453 < baseStart_1013453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013457 : List Nat := [1, 2, 2, 1, 2, 5, 2, 5]
def baseStart_1013457 : Nat := 118140960795 + 1013457 * 2 ^ 59
def prefixEnd_1013457 : Nat := 4983230072969 + 3 ^ 40 * 1013457 * 2
def baseEnd_1013457 : Nat := 154189796641110097341245

theorem tailTrace_1013457 : CollatzResearch.WordTrace tailWord_1013457 prefixEnd_1013457 154189796641110097341245 := by
  unfold tailWord_1013457
  simp only [CollatzResearch.WordTrace]
  refine ⟨36963813489425848520734625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24642542326283899013823083 36963813489425848520734625)
  ·
    refine ⟨27722860117069386390550969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36963813489425848520734625 27722860117069386390550969)
    ·
      refine ⟨20792145087802039792913227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27722860117069386390550969 20792145087802039792913227)
      ·
        refine ⟨31188217631703059689369841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20792145087802039792913227 31188217631703059689369841)
        ·
          refine ⟨23391163223777294767027381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31188217631703059689369841 23391163223777294767027381)
          ·
            refine ⟨2192921552229121384408817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23391163223777294767027381 2192921552229121384408817)
            ·
              refine ⟨1644691164171841038306613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2192921552229121384408817 1644691164171841038306613)
              ·
                refine ⟨154189796641110097341245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1644691164171841038306613 154189796641110097341245)
                ·
                  rfl

theorem cell20_1013457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_1013457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013457 prefixEnd_1013457 := by exact prefixLift 1013457
  have htrace : WordTrace (prefixWord ++ tailWord_1013457) baseStart_1013457 baseEnd_1013457 := by
    simpa [prefixWord, tailWord_1013457, baseEnd_1013457] using wordTrace_append hprefix tailTrace_1013457
  have hstable : (prefixWord ++ tailWord_1013457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013457).length < 2 ^ (prefixWord ++ tailWord_1013457).sum := by decide
  have hdescent : baseEnd_1013457 < baseStart_1013457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013460 : List Nat := [2, 4, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1013460 : Nat := 118140960795 + 1013460 * 2 ^ 59
def prefixEnd_1013460 : Nat := 4983230072969 + 3 ^ 40 * 1013460 * 2
def baseEnd_1013460 : Nat := 462570759205075614923723

theorem tailTrace_1013460 : CollatzResearch.WordTrace tailWord_1013460 prefixEnd_1013460 462570759205075614923723 := by
  unfold tailWord_1013460
  simp only [CollatzResearch.WordTrace]
  refine ⟨18481961454207490016546917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24642615272276653355395889 18481961454207490016546917)
  ·
    refine ⟨3465367772663904378102547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18481961454207490016546917 3465367772663904378102547)
    ·
      refine ⟨5198051658995856567153821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3465367772663904378102547 5198051658995856567153821)
      ·
        refine ⟨1949269372123446212682683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5198051658995856567153821 1949269372123446212682683)
        ·
          refine ⟨2923904058185169319024025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1949269372123446212682683 2923904058185169319024025)
          ·
            refine ⟨2192928043638876989268019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2923904058185169319024025 2192928043638876989268019)
            ·
              refine ⟨3289392065458315483902029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192928043638876989268019 3289392065458315483902029)
              ·
                refine ⟨1233522024546868306463261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3289392065458315483902029 1233522024546868306463261)
                ·
                  refine ⟨462570759205075614923723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233522024546868306463261 462570759205075614923723)
                  ·
                    rfl

theorem cell20_1013460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1013460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013460 prefixEnd_1013460 := by exact prefixLift 1013460
  have htrace : WordTrace (prefixWord ++ tailWord_1013460) baseStart_1013460 baseEnd_1013460 := by
    simpa [prefixWord, tailWord_1013460, baseEnd_1013460] using wordTrace_append hprefix tailTrace_1013460
  have hstable : (prefixWord ++ tailWord_1013460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013460).length < 2 ^ (prefixWord ++ tailWord_1013460).sum := by decide
  have hdescent : baseEnd_1013460 < baseStart_1013460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013471 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 6]
def baseStart_1013471 : Nat := 118140960795 + 1013471 * 2 ^ 59
def prefixEnd_1013471 : Nat := 4983230072969 + 3 ^ 40 * 1013471 * 2
def baseEnd_1013471 : Nat := 462575779904808465557011

theorem tailTrace_1013471 : CollatzResearch.WordTrace tailWord_1013471 prefixEnd_1013471 462575779904808465557011 := by
  unfold tailWord_1013471
  simp only [CollatzResearch.WordTrace]
  refine ⟨36964324111375128911744267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24642882740916752607829511 36964324111375128911744267)
  ·
    refine ⟨55446486167062693367616401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36964324111375128911744267 55446486167062693367616401)
    ·
      refine ⟨41584864625297020025712301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55446486167062693367616401 41584864625297020025712301)
      ·
        refine ⟨15594324234486382509642113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41584864625297020025712301 15594324234486382509642113)
        ·
          refine ⟨11695743175864786882231585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15594324234486382509642113 11695743175864786882231585)
          ·
            refine ⟨8771807381898590161673689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11695743175864786882231585 8771807381898590161673689)
            ·
              refine ⟨6578855536423942621255267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8771807381898590161673689 6578855536423942621255267)
              ·
                refine ⟨9868283304635913931882901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6578855536423942621255267 9868283304635913931882901)
                ·
                  refine ⟨462575779904808465557011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9868283304635913931882901 462575779904808465557011)
                  ·
                    rfl

theorem cell20_1013471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_1013471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013471 prefixEnd_1013471 := by exact prefixLift 1013471
  have htrace : WordTrace (prefixWord ++ tailWord_1013471) baseStart_1013471 baseEnd_1013471 := by
    simpa [prefixWord, tailWord_1013471, baseEnd_1013471] using wordTrace_append hprefix tailTrace_1013471
  have hstable : (prefixWord ++ tailWord_1013471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013471).length < 2 ^ (prefixWord ++ tailWord_1013471).sum := by decide
  have hdescent : baseEnd_1013471 < baseStart_1013471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013550 : List Nat := [4, 1, 3, 2, 2, 1, 7]
def baseStart_1013550 : Nat := 118140960795 + 1013550 * 2 ^ 59
def prefixEnd_1013550 : Nat := 4983230072969 + 3 ^ 40 * 1013550 * 2
def baseEnd_1013550 : Nat := 51401315295270589102595

theorem tailTrace_1013550 : CollatzResearch.WordTrace tailWord_1013550 prefixEnd_1013550 51401315295270589102595 := by
  unfold tailWord_1013550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620900684761115675483763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24644803652059283602580069 4620900684761115675483763)
  ·
    refine ⟨6931351027141673513225645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4620900684761115675483763 6931351027141673513225645)
    ·
      refine ⟨2599256635178127567459617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6931351027141673513225645 2599256635178127567459617)
      ·
        refine ⟨1949442476383595675594713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2599256635178127567459617 1949442476383595675594713)
        ·
          refine ⟨1462081857287696756696035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1949442476383595675594713 1462081857287696756696035)
          ·
            refine ⟨2193122785931545135044053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462081857287696756696035 2193122785931545135044053)
            ·
              refine ⟨51401315295270589102595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2193122785931545135044053 51401315295270589102595)
              ·
                rfl

theorem cell20_1013550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 7].length) (baseStart_1013550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013550 prefixEnd_1013550 := by exact prefixLift 1013550
  have htrace : WordTrace (prefixWord ++ tailWord_1013550) baseStart_1013550 baseEnd_1013550 := by
    simpa [prefixWord, tailWord_1013550, baseEnd_1013550] using wordTrace_append hprefix tailTrace_1013550
  have hstable : (prefixWord ++ tailWord_1013550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013550).length < 2 ^ (prefixWord ++ tailWord_1013550).sum := by decide
  have hdescent : baseEnd_1013550 < baseStart_1013550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013557 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 5]
def baseStart_1013557 : Nat := 118140960795 + 1013557 * 2 ^ 59
def prefixEnd_1013557 : Nat := 4983230072969 + 3 ^ 40 * 1013557 * 2
def baseEnd_1013557 : Nat := 462615032648174388689993

theorem tailTrace_1013557 : CollatzResearch.WordTrace tailWord_1013557 prefixEnd_1013557 462615032648174388689993 := by
  unfold tailWord_1013557
  simp only [CollatzResearch.WordTrace]
  refine ⟨36967460789063565599374925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24644973859375710399583283 36967460789063565599374925)
  ·
    refine ⟨13862797795898837099765597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36967460789063565599374925 13862797795898837099765597)
    ·
      refine ⟨5198549173462063912412099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13862797795898837099765597 5198549173462063912412099)
      ·
        refine ⟨7797823760193095868618149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5198549173462063912412099 7797823760193095868618149)
        ·
          refine ⟨1462091955036205475365903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7797823760193095868618149 1462091955036205475365903)
          ·
            refine ⟨2193137932554308213048855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462091955036205475365903 2193137932554308213048855)
            ·
              refine ⟨3289706898831462319573283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193137932554308213048855 3289706898831462319573283)
              ·
                refine ⟨4934560348247193479359925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289706898831462319573283 4934560348247193479359925)
                ·
                  refine ⟨462615032648174388689993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4934560348247193479359925 462615032648174388689993)
                  ·
                    rfl

theorem cell20_1013557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_1013557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013557 prefixEnd_1013557 := by exact prefixLift 1013557
  have htrace : WordTrace (prefixWord ++ tailWord_1013557) baseStart_1013557 baseEnd_1013557 := by
    simpa [prefixWord, tailWord_1013557, baseEnd_1013557] using wordTrace_append hprefix tailTrace_1013557
  have hstable : (prefixWord ++ tailWord_1013557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013557).length < 2 ^ (prefixWord ++ tailWord_1013557).sum := by decide
  have hdescent : baseEnd_1013557 < baseStart_1013557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013581 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1013581 : Nat := 118140960795 + 1013581 * 2 ^ 59
def prefixEnd_1013581 : Nat := 4983230072969 + 3 ^ 40 * 1013581 * 2
def baseEnd_1013581 : Nat := 462625986902136971889895

theorem tailTrace_1013581 : CollatzResearch.WordTrace tailWord_1013581 prefixEnd_1013581 462625986902136971889895 := by
  unfold tailWord_1013581
  simp only [CollatzResearch.WordTrace]
  refine ⟨36968336140976617698248597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24645557427317745132165731 36968336140976617698248597)
  ·
    refine ⟨1732890756608278954605403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36968336140976617698248597 1732890756608278954605403)
    ·
      refine ⟨2599336134912418431908105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1732890756608278954605403 2599336134912418431908105)
      ·
        refine ⟨1949502101184313823931079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2599336134912418431908105 1949502101184313823931079)
        ·
          refine ⟨2924253151776470735896619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1949502101184313823931079 2924253151776470735896619)
          ·
            refine ⟨4386379727664706103844929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2924253151776470735896619 4386379727664706103844929)
            ·
              refine ⟨3289784795748529577883697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4386379727664706103844929 3289784795748529577883697)
              ·
                refine ⟨2467338596811397183412773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3289784795748529577883697 2467338596811397183412773)
                ·
                  refine ⟨462625986902136971889895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2467338596811397183412773 462625986902136971889895)
                  ·
                    rfl

theorem cell20_1013581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1013581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013581 prefixEnd_1013581 := by exact prefixLift 1013581
  have htrace : WordTrace (prefixWord ++ tailWord_1013581) baseStart_1013581 baseEnd_1013581 := by
    simpa [prefixWord, tailWord_1013581, baseEnd_1013581] using wordTrace_append hprefix tailTrace_1013581
  have hstable : (prefixWord ++ tailWord_1013581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013581).length < 2 ^ (prefixWord ++ tailWord_1013581).sum := by decide
  have hdescent : baseEnd_1013581 < baseStart_1013581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013588 : List Nat := [2, 4, 1, 1, 3, 1, 4, 4]
def baseStart_1013588 : Nat := 118140960795 + 1013588 * 2 ^ 59
def prefixEnd_1013588 : Nat := 4983230072969 + 3 ^ 40 * 1013588 * 2
def baseEnd_1013588 : Nat := 154209727297625352885511

theorem tailTrace_1013588 : CollatzResearch.WordTrace tailWord_1013588 prefixEnd_1013588 154209727297625352885511 := by
  unfold tailWord_1013588
  simp only [CollatzResearch.WordTrace]
  refine ⟨18484295725975628946876709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24645727634634171929168945 18484295725975628946876709)
  ·
    refine ⟨3465805448620430427539383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18484295725975628946876709 3465805448620430427539383)
    ·
      refine ⟨5198708172930645641309075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3465805448620430427539383 5198708172930645641309075)
      ·
        refine ⟨7798062259395968461963613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5198708172930645641309075 7798062259395968461963613)
        ·
          refine ⟨2924273347273488173236355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7798062259395968461963613 2924273347273488173236355)
          ·
            refine ⟨4386410020910232259854533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2924273347273488173236355 4386410020910232259854533)
            ·
              refine ⟨822451878920668548722725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4386410020910232259854533 822451878920668548722725)
              ·
                refine ⟨154209727297625352885511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 822451878920668548722725 154209727297625352885511)
                ·
                  rfl

theorem cell20_1013588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_1013588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013588 prefixEnd_1013588 := by exact prefixLift 1013588
  have htrace : WordTrace (prefixWord ++ tailWord_1013588) baseStart_1013588 baseEnd_1013588 := by
    simpa [prefixWord, tailWord_1013588, baseEnd_1013588] using wordTrace_append hprefix tailTrace_1013588
  have hstable : (prefixWord ++ tailWord_1013588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013588).length < 2 ^ (prefixWord ++ tailWord_1013588).sum := by decide
  have hdescent : baseEnd_1013588 < baseStart_1013588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013616 : List Nat := [2, 1, 1, 1, 4, 1, 1, 6, 3]
def baseStart_1013616 : Nat := 118140960795 + 1013616 * 2 ^ 59
def prefixEnd_1013616 : Nat := 4983230072969 + 3 ^ 40 * 1013616 * 2
def baseEnd_1013616 : Nat := 462641961855832405723085

theorem tailTrace_1013616 : CollatzResearch.WordTrace tailWord_1013616 prefixEnd_1013616 462641961855832405723085 := by
  unfold tailWord_1013616
  simp only [CollatzResearch.WordTrace]
  refine ⟨18484806347924909337886351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24646408463899879117181801 18484806347924909337886351)
  ·
    refine ⟨27727209521887364006829527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18484806347924909337886351 27727209521887364006829527)
    ·
      refine ⟨41590814282831046010244291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27727209521887364006829527 41590814282831046010244291)
      ·
        refine ⟨62386221424246569015366437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41590814282831046010244291 62386221424246569015366437)
        ·
          refine ⟨11697416517046231690381207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62386221424246569015366437 11697416517046231690381207)
          ·
            refine ⟨17546124775569347535571811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11697416517046231690381207 17546124775569347535571811)
            ·
              refine ⟨26319187163354021303357717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17546124775569347535571811 26319187163354021303357717)
              ·
                refine ⟨1233711898282219748594893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26319187163354021303357717 1233711898282219748594893)
                ·
                  refine ⟨462641961855832405723085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233711898282219748594893 462641961855832405723085)
                  ·
                    rfl

theorem cell20_1013616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_1013616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013616 prefixEnd_1013616 := by exact prefixLift 1013616
  have htrace : WordTrace (prefixWord ++ tailWord_1013616) baseStart_1013616 baseEnd_1013616 := by
    simpa [prefixWord, tailWord_1013616, baseEnd_1013616] using wordTrace_append hprefix tailTrace_1013616
  have hstable : (prefixWord ++ tailWord_1013616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013616).length < 2 ^ (prefixWord ++ tailWord_1013616).sum := by decide
  have hdescent : baseEnd_1013616 < baseStart_1013616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013668 : List Nat := [2, 3, 1, 2, 1, 11]
def baseStart_1013668 : Nat := 118140960795 + 1013668 * 2 ^ 59
def prefixEnd_1013668 : Nat := 4983230072969 + 3 ^ 40 * 1013668 * 2
def baseEnd_1013668 : Nat := 17135766521213012444057

theorem tailTrace_1013668 : CollatzResearch.WordTrace tailWord_1013668 prefixEnd_1013668 17135766521213012444057 := by
  unfold tailWord_1013668
  simp only [CollatzResearch.WordTrace]
  refine ⟨18485754645830715778332829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24647672861107621037777105 18485754645830715778332829)
  ·
    refine ⟨6932157992186518416874811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18485754645830715778332829 6932157992186518416874811)
    ·
      refine ⟨10398236988279777625312217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6932157992186518416874811 10398236988279777625312217)
      ·
        refine ⟨7798677741209833218984163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10398236988279777625312217 7798677741209833218984163)
        ·
          refine ⟨11698016611814749828476245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7798677741209833218984163 11698016611814749828476245)
          ·
            refine ⟨17135766521213012444057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11698016611814749828476245 17135766521213012444057)
            ·
              rfl

theorem cell20_1013668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 11].length) (baseStart_1013668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013668 prefixEnd_1013668 := by exact prefixLift 1013668
  have htrace : WordTrace (prefixWord ++ tailWord_1013668) baseStart_1013668 baseEnd_1013668 := by
    simpa [prefixWord, tailWord_1013668, baseEnd_1013668] using wordTrace_append hprefix tailTrace_1013668
  have hstable : (prefixWord ++ tailWord_1013668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013668).length < 2 ^ (prefixWord ++ tailWord_1013668).sum := by decide
  have hdescent : baseEnd_1013668 < baseStart_1013668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013671 : List Nat := [1, 1, 6, 1, 2, 1, 1, 4, 3]
def baseStart_1013671 : Nat := 118140960795 + 1013671 * 2 ^ 59
def prefixEnd_1013671 : Nat := 4983230072969 + 3 ^ 40 * 1013671 * 2
def baseEnd_1013671 : Nat := 462667065354496658889527

theorem tailTrace_1013671 : CollatzResearch.WordTrace tailWord_1013671 prefixEnd_1013671 462667065354496658889527 := by
  unfold tailWord_1013671
  simp only [CollatzResearch.WordTrace]
  refine ⟨36971618710650563069024867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24647745807100375379349911 36971618710650563069024867)
  ·
    refine ⟨55457428065975844603537301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36971618710650563069024867 55457428065975844603537301)
    ·
      refine ⟨2599566940592617715790811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55457428065975844603537301 2599566940592617715790811)
      ·
        refine ⟨3899350410888926573686217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599566940592617715790811 3899350410888926573686217)
        ·
          refine ⟨2924512808166694930264663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3899350410888926573686217 2924512808166694930264663)
          ·
            refine ⟨4386769212250042395396995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2924512808166694930264663 4386769212250042395396995)
            ·
              refine ⟨6580153818375063593095493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4386769212250042395396995 6580153818375063593095493)
              ·
                refine ⟨1233778840945324423705405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6580153818375063593095493 1233778840945324423705405)
                ·
                  refine ⟨462667065354496658889527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233778840945324423705405 462667065354496658889527)
                  ·
                    rfl

theorem cell20_1013671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 3].length) (baseStart_1013671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013671 prefixEnd_1013671 := by exact prefixLift 1013671
  have htrace : WordTrace (prefixWord ++ tailWord_1013671) baseStart_1013671 baseEnd_1013671 := by
    simpa [prefixWord, tailWord_1013671, baseEnd_1013671] using wordTrace_append hprefix tailTrace_1013671
  have hstable : (prefixWord ++ tailWord_1013671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013671).length < 2 ^ (prefixWord ++ tailWord_1013671).sum := by decide
  have hdescent : baseEnd_1013671 < baseStart_1013671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013685 : List Nat := [1, 3, 3, 2, 1, 2, 3, 5]
def baseStart_1013685 : Nat := 118140960795 + 1013685 * 2 ^ 59
def prefixEnd_1013685 : Nat := 4983230072969 + 3 ^ 40 * 1013685 * 2
def baseEnd_1013685 : Nat := 154224485111991610807601

theorem tailTrace_1013685 : CollatzResearch.WordTrace tailWord_1013685 prefixEnd_1013685 154224485111991610807601 := by
  unfold tailWord_1013685
  simp only [CollatzResearch.WordTrace]
  refine ⟨36972129332599843460034509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24648086221733228973356339 36972129332599843460034509)
  ·
    refine ⟨13864548499724941297512941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36972129332599843460034509 13864548499724941297512941)
    ·
      refine ⟨5199205687396852986567353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13864548499724941297512941 5199205687396852986567353)
      ·
        refine ⟨3899404265547639739925515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5199205687396852986567353 3899404265547639739925515)
        ·
          refine ⟨5849106398321459609888273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3899404265547639739925515 5849106398321459609888273)
          ·
            refine ⟨4386829798741094707416205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5849106398321459609888273 4386829798741094707416205)
            ·
              refine ⟨1645061174527910515281077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4386829798741094707416205 1645061174527910515281077)
              ·
                refine ⟨154224485111991610807601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1645061174527910515281077 154224485111991610807601)
                ·
                  rfl

theorem cell20_1013685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_1013685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013685 prefixEnd_1013685 := by exact prefixLift 1013685
  have htrace : WordTrace (prefixWord ++ tailWord_1013685) baseStart_1013685 baseEnd_1013685 := by
    simpa [prefixWord, tailWord_1013685, baseEnd_1013685] using wordTrace_append hprefix tailTrace_1013685
  have hstable : (prefixWord ++ tailWord_1013685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013685).length < 2 ^ (prefixWord ++ tailWord_1013685).sum := by decide
  have hdescent : baseEnd_1013685 < baseStart_1013685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013706 : List Nat := [3, 1, 2, 1, 2, 1, 2, 8]
def baseStart_1013706 : Nat := 118140960795 + 1013706 * 2 ^ 59
def prefixEnd_1013706 : Nat := 4983230072969 + 3 ^ 40 * 1013706 * 2
def baseEnd_1013706 : Nat := 154227680102730697574239

theorem tailTrace_1013706 : CollatzResearch.WordTrace tailWord_1013706 prefixEnd_1013706 154227680102730697574239 := by
  unfold tailWord_1013706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9243223816380941011637243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24648596843682509364365981 9243223816380941011637243)
  ·
    refine ⟨13864835724571411517455865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9243223816380941011637243 13864835724571411517455865)
    ·
      refine ⟨10398626793428558638091899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13864835724571411517455865 10398626793428558638091899)
      ·
        refine ⟨15597940190142837957137849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10398626793428558638091899 15597940190142837957137849)
        ·
          refine ⟨11698455142607128467853387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15597940190142837957137849 11698455142607128467853387)
          ·
            refine ⟨17547682713910692701780081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11698455142607128467853387 17547682713910692701780081)
            ·
              refine ⟨13160762035433019526335061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17547682713910692701780081 13160762035433019526335061)
              ·
                refine ⟨154227680102730697574239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13160762035433019526335061 154227680102730697574239)
                ·
                  rfl

theorem cell20_1013706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_1013706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013706 prefixEnd_1013706 := by exact prefixLift 1013706
  have htrace : WordTrace (prefixWord ++ tailWord_1013706) baseStart_1013706 baseEnd_1013706 := by
    simpa [prefixWord, tailWord_1013706, baseEnd_1013706] using wordTrace_append hprefix tailTrace_1013706
  have hstable : (prefixWord ++ tailWord_1013706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013706).length < 2 ^ (prefixWord ++ tailWord_1013706).sum := by decide
  have hdescent : baseEnd_1013706 < baseStart_1013706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013788 : List Nat := [2, 2, 3, 1, 3, 2, 3, 2, 2]
def baseStart_1013788 : Nat := 118140960795 + 1013788 * 2 ^ 59
def prefixEnd_1013788 : Nat := 4983230072969 + 3 ^ 40 * 1013788 * 2
def baseEnd_1013788 : Nat := 462720467342564251989049

theorem tailTrace_1013788 : CollatzResearch.WordTrace tailWord_1013788 prefixEnd_1013788 462720467342564251989049 := by
  unfold tailWord_1013788
  simp only [CollatzResearch.WordTrace]
  refine ⟨18487943025613346025517009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24650590700817794700689345 18487943025613346025517009)
  ·
    refine ⟨13865957269210009519137757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18487943025613346025517009 13865957269210009519137757)
    ·
      refine ⟨5199733975953753569676659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13865957269210009519137757 5199733975953753569676659)
      ·
        refine ⟨7799600963930630354514989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5199733975953753569676659 7799600963930630354514989)
        ·
          refine ⟨2924850361473986382943121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7799600963930630354514989 2924850361473986382943121)
          ·
            refine ⟨2193637771105489787207341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2924850361473986382943121 2193637771105489787207341)
            ·
              refine ⟨822614164164558670202753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2193637771105489787207341 822614164164558670202753)
              ·
                refine ⟨616960623123419002652065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822614164164558670202753 616960623123419002652065)
                ·
                  refine ⟨462720467342564251989049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616960623123419002652065 462720467342564251989049)
                  ·
                    rfl

theorem cell20_1013788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_1013788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013788 prefixEnd_1013788 := by exact prefixLift 1013788
  have htrace : WordTrace (prefixWord ++ tailWord_1013788) baseStart_1013788 baseEnd_1013788 := by
    simpa [prefixWord, tailWord_1013788, baseEnd_1013788] using wordTrace_append hprefix tailTrace_1013788
  have hstable : (prefixWord ++ tailWord_1013788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013788).length < 2 ^ (prefixWord ++ tailWord_1013788).sum := by decide
  have hdescent : baseEnd_1013788 < baseStart_1013788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013802 : List Nat := [3, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_1013802 : Nat := 118140960795 + 1013802 * 2 ^ 59
def prefixEnd_1013802 : Nat := 4983230072969 + 3 ^ 40 * 1013802 * 2
def baseEnd_1013802 : Nat := 462726857324042425522325

theorem tailTrace_1013802 : CollatzResearch.WordTrace tailWord_1013802 prefixEnd_1013802 462726857324042425522325 := by
  unfold tailWord_1013802
  simp only [CollatzResearch.WordTrace]
  refine ⟨9244099168293993110510915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24650931115450648294695773 9244099168293993110510915)
  ·
    refine ⟨13866148752440989665766373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9244099168293993110510915 13866148752440989665766373)
    ·
      refine ⟨2599902891082685562331195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13866148752440989665766373 2599902891082685562331195)
      ·
        refine ⟨3899854336624028343496793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599902891082685562331195 3899854336624028343496793)
        ·
          refine ⟨2924890752468021257622595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3899854336624028343496793 2924890752468021257622595)
          ·
            refine ⟨4387336128702031886433893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2924890752468021257622595 4387336128702031886433893)
            ·
              refine ⟨822625524131630978706355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4387336128702031886433893 822625524131630978706355)
              ·
                refine ⟨1233938286197446468059533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822625524131630978706355 1233938286197446468059533)
                ·
                  refine ⟨462726857324042425522325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233938286197446468059533 462726857324042425522325)
                  ·
                    rfl

theorem cell20_1013802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_1013802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013802 prefixEnd_1013802 := by exact prefixLift 1013802
  have htrace : WordTrace (prefixWord ++ tailWord_1013802) baseStart_1013802 baseEnd_1013802 := by
    simpa [prefixWord, tailWord_1013802, baseEnd_1013802] using wordTrace_append hprefix tailTrace_1013802
  have hstable : (prefixWord ++ tailWord_1013802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013802).length < 2 ^ (prefixWord ++ tailWord_1013802).sum := by decide
  have hdescent : baseEnd_1013802 < baseStart_1013802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013813 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1013813 : Nat := 118140960795 + 1013813 * 2 ^ 59
def prefixEnd_1013813 : Nat := 4983230072969 + 3 ^ 40 * 1013813 * 2
def baseEnd_1013813 : Nat := 462731878023775276155613

theorem tailTrace_1013813 : CollatzResearch.WordTrace tailWord_1013813 prefixEnd_1013813 462731878023775276155613 := by
  unfold tailWord_1013813
  simp only [CollatzResearch.WordTrace]
  refine ⟨36976797876136121320694093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24651198584090747547129395 36976797876136121320694093)
  ·
    refine ⟨13866299203551045495260285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36976797876136121320694093 13866299203551045495260285)
    ·
      refine ⟨5199862201331642060722607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13866299203551045495260285 5199862201331642060722607)
      ·
        refine ⟨7799793301997463091083911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5199862201331642060722607 7799793301997463091083911)
        ·
          refine ⟨11699689952996194636625867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7799793301997463091083911 11699689952996194636625867)
          ·
            refine ⟨17549534929494291954938801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11699689952996194636625867 17549534929494291954938801)
            ·
              refine ⟨13162151197120718966204101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17549534929494291954938801 13162151197120718966204101)
              ·
                refine ⟨2467903349460134806163269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13162151197120718966204101 2467903349460134806163269)
                ·
                  refine ⟨462731878023775276155613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2467903349460134806163269 462731878023775276155613)
                  ·
                    rfl

theorem cell20_1013813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1013813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013813 prefixEnd_1013813 := by exact prefixLift 1013813
  have htrace : WordTrace (prefixWord ++ tailWord_1013813) baseStart_1013813 baseEnd_1013813 := by
    simpa [prefixWord, tailWord_1013813, baseEnd_1013813] using wordTrace_append hprefix tailTrace_1013813
  have hstable : (prefixWord ++ tailWord_1013813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013813).length < 2 ^ (prefixWord ++ tailWord_1013813).sum := by decide
  have hdescent : baseEnd_1013813 < baseStart_1013813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013820 : List Nat := [2, 2, 2, 2, 2, 1, 1, 8]
def baseStart_1013820 : Nat := 118140960795 + 1013820 * 2 ^ 59
def prefixEnd_1013820 : Nat := 4983230072969 + 3 ^ 40 * 1013820 * 2
def baseEnd_1013820 : Nat := 154245024338171454307417

theorem tailTrace_1013820 : CollatzResearch.WordTrace tailWord_1013820 prefixEnd_1013820 154245024338171454307417 := by
  unfold tailWord_1013820
  simp only [CollatzResearch.WordTrace]
  refine ⟨18488526593555380758099457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24651368791407174344132609 18488526593555380758099457)
  ·
    refine ⟨13866394945166535568574593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18488526593555380758099457 13866394945166535568574593)
    ·
      refine ⟨10399796208874901676430945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13866394945166535568574593 10399796208874901676430945)
      ·
        refine ⟨7799847156656176257323209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10399796208874901676430945 7799847156656176257323209)
        ·
          refine ⟨5849885367492132192992407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7799847156656176257323209 5849885367492132192992407)
          ·
            refine ⟨8774828051238198289488611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5849885367492132192992407 8774828051238198289488611)
            ·
              refine ⟨13162242076857297434232917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8774828051238198289488611 13162242076857297434232917)
              ·
                refine ⟨154245024338171454307417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13162242076857297434232917 154245024338171454307417)
                ·
                  rfl

theorem cell20_1013820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_1013820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013820 prefixEnd_1013820 := by exact prefixLift 1013820
  have htrace : WordTrace (prefixWord ++ tailWord_1013820) baseStart_1013820 baseEnd_1013820 := by
    simpa [prefixWord, tailWord_1013820, baseEnd_1013820] using wordTrace_append hprefix tailTrace_1013820
  have hstable : (prefixWord ++ tailWord_1013820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013820).length < 2 ^ (prefixWord ++ tailWord_1013820).sum := by decide
  have hdescent : baseEnd_1013820 < baseStart_1013820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013827 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 5]
def baseStart_1013827 : Nat := 118140960795 + 1013827 * 2 ^ 59
def prefixEnd_1013827 : Nat := 4983230072969 + 3 ^ 40 * 1013827 * 2
def baseEnd_1013827 : Nat := 462738268005253449688889

theorem tailTrace_1013827 : CollatzResearch.WordTrace tailWord_1013827 prefixEnd_1013827 462738268005253449688889 := by
  unfold tailWord_1013827
  simp only [CollatzResearch.WordTrace]
  refine ⟨36977308498085401711703735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24651538998723601141135823 36977308498085401711703735)
  ·
    refine ⟨55465962747128102567555603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36977308498085401711703735 55465962747128102567555603)
    ·
      refine ⟨83198944120692153851333405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55465962747128102567555603 83198944120692153851333405)
      ·
        refine ⟨31199604045259557694250027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83198944120692153851333405 31199604045259557694250027)
        ·
          refine ⟨46799406067889336541375041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31199604045259557694250027 46799406067889336541375041)
          ·
            refine ⟨35099554550917002406031281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46799406067889336541375041 35099554550917002406031281)
            ·
              refine ⟨26324665913187751804523461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35099554550917002406031281 26324665913187751804523461)
              ·
                refine ⟨4935874858722703463348149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26324665913187751804523461 4935874858722703463348149)
                ·
                  refine ⟨462738268005253449688889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4935874858722703463348149 462738268005253449688889)
                  ·
                    rfl

theorem cell20_1013827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_1013827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013827 prefixEnd_1013827 := by exact prefixLift 1013827
  have htrace : WordTrace (prefixWord ++ tailWord_1013827) baseStart_1013827 baseEnd_1013827 := by
    simpa [prefixWord, tailWord_1013827, baseEnd_1013827] using wordTrace_append hprefix tailTrace_1013827
  have hstable : (prefixWord ++ tailWord_1013827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013827).length < 2 ^ (prefixWord ++ tailWord_1013827).sum := by decide
  have hdescent : baseEnd_1013827 < baseStart_1013827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013847 : List Nat := [1, 1, 3, 2, 2, 1, 6, 2, 2]
def baseStart_1013847 : Nat := 118140960795 + 1013847 * 2 ^ 59
def prefixEnd_1013847 : Nat := 4983230072969 + 3 ^ 40 * 1013847 * 2
def baseEnd_1013847 : Nat := 462747396550222269022141

theorem tailTrace_1013847 : CollatzResearch.WordTrace tailWord_1013847 prefixEnd_1013847 462747396550222269022141 := by
  unfold tailWord_1013847
  simp only [CollatzResearch.WordTrace]
  refine ⟨36978037958012945127431795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24652025305341963418287863 36978037958012945127431795)
  ·
    refine ⟨55467056937019417691147693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36978037958012945127431795 55467056937019417691147693)
    ·
      refine ⟨20800146351382281634180385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55467056937019417691147693 20800146351382281634180385)
      ·
        refine ⟨15600109763536711225635289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20800146351382281634180385 15600109763536711225635289)
        ·
          refine ⟨11700082322652533419226467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15600109763536711225635289 11700082322652533419226467)
          ·
            refine ⟨17550123483978800128839701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11700082322652533419226467 17550123483978800128839701)
            ·
              refine ⟨822662038311506256039361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17550123483978800128839701 822662038311506256039361)
              ·
                refine ⟨616996528733629692029521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822662038311506256039361 616996528733629692029521)
                ·
                  refine ⟨462747396550222269022141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616996528733629692029521 462747396550222269022141)
                  ·
                    rfl

theorem cell20_1013847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 2].length) (baseStart_1013847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013847 prefixEnd_1013847 := by exact prefixLift 1013847
  have htrace : WordTrace (prefixWord ++ tailWord_1013847) baseStart_1013847 baseEnd_1013847 := by
    simpa [prefixWord, tailWord_1013847, baseEnd_1013847] using wordTrace_append hprefix tailTrace_1013847
  have hstable : (prefixWord ++ tailWord_1013847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013847).length < 2 ^ (prefixWord ++ tailWord_1013847).sum := by decide
  have hdescent : baseEnd_1013847 < baseStart_1013847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013885 : List Nat := [1, 4, 1, 1, 3, 3, 2, 3, 2]
def baseStart_1013885 : Nat := 118140960795 + 1013885 * 2 ^ 59
def prefixEnd_1013885 : Nat := 4983230072969 + 3 ^ 40 * 1013885 * 2
def baseEnd_1013885 : Nat := 462764740785663025755319

theorem tailTrace_1013885 : CollatzResearch.WordTrace tailWord_1013885 prefixEnd_1013885 462764740785663025755319 := by
  unfold tailWord_1013885
  simp only [CollatzResearch.WordTrace]
  refine ⟨36979423931875277617315109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24652949287916851744876739 36979423931875277617315109)
  ·
    refine ⟨6933641987226614553246583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36979423931875277617315109 6933641987226614553246583)
    ·
      refine ⟨10400462980839921829869875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6933641987226614553246583 10400462980839921829869875)
      ·
        refine ⟨15600694471259882744804813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10400462980839921829869875 15600694471259882744804813)
        ·
          refine ⟨5850260426722456029301805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15600694471259882744804813 5850260426722456029301805)
          ·
            refine ⟨2193847660020921010988177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5850260426722456029301805 2193847660020921010988177)
            ·
              refine ⟨1645385745015690758241133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2193847660020921010988177 1645385745015690758241133)
              ·
                refine ⟨617019654380884034340425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1645385745015690758241133 617019654380884034340425)
                ·
                  refine ⟨462764740785663025755319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617019654380884034340425 462764740785663025755319)
                  ·
                    rfl

theorem cell20_1013885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_1013885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013885 prefixEnd_1013885 := by exact prefixLift 1013885
  have htrace : WordTrace (prefixWord ++ tailWord_1013885) baseStart_1013885 baseEnd_1013885 := by
    simpa [prefixWord, tailWord_1013885, baseEnd_1013885] using wordTrace_append hprefix tailTrace_1013885
  have hstable : (prefixWord ++ tailWord_1013885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013885).length < 2 ^ (prefixWord ++ tailWord_1013885).sum := by decide
  have hdescent : baseEnd_1013885 < baseStart_1013885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013906 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_1013906 : Nat := 118140960795 + 1013906 * 2 ^ 59
def prefixEnd_1013906 : Nat := 4983230072969 + 3 ^ 40 * 1013906 * 2
def baseEnd_1013906 : Nat := 462774325757880286055233

theorem tailTrace_1013906 : CollatzResearch.WordTrace tailWord_1013906 prefixEnd_1013906 462774325757880286055233 := by
  unfold tailWord_1013906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9245047466199799550957393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24653459909866132135886381 9245047466199799550957393)
  ·
    refine ⟨6933785599649849663218045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9245047466199799550957393 6933785599649849663218045)
    ·
      refine ⟨2600169599868693623706767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6933785599649849663218045 2600169599868693623706767)
      ·
        refine ⟨3900254399803040435560151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2600169599868693623706767 3900254399803040435560151)
        ·
          refine ⟨5850381599704560653340227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900254399803040435560151 5850381599704560653340227)
          ·
            refine ⟨8775572399556840980010341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850381599704560653340227 8775572399556840980010341)
            ·
              refine ⟨1645419824916907683751939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8775572399556840980010341 1645419824916907683751939)
              ·
                refine ⟨2468129737375361525627909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645419824916907683751939 2468129737375361525627909)
                ·
                  refine ⟨462774325757880286055233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2468129737375361525627909 462774325757880286055233)
                  ·
                    rfl

theorem cell20_1013906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_1013906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013906 prefixEnd_1013906 := by exact prefixLift 1013906
  have htrace : WordTrace (prefixWord ++ tailWord_1013906) baseStart_1013906 baseEnd_1013906 := by
    simpa [prefixWord, tailWord_1013906, baseEnd_1013906] using wordTrace_append hprefix tailTrace_1013906
  have hstable : (prefixWord ++ tailWord_1013906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013906).length < 2 ^ (prefixWord ++ tailWord_1013906).sum := by decide
  have hdescent : baseEnd_1013906 < baseStart_1013906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013930 : List Nat := [3, 1, 5, 1, 2, 1, 1, 6]
def baseStart_1013930 : Nat := 118140960795 + 1013930 * 2 ^ 59
def prefixEnd_1013930 : Nat := 4983230072969 + 3 ^ 40 * 1013930 * 2
def baseEnd_1013930 : Nat := 154261760003947623085045

theorem tailTrace_1013930 : CollatzResearch.WordTrace tailWord_1013930 prefixEnd_1013930 154261760003947623085045 := by
  unfold tailWord_1013930
  simp only [CollatzResearch.WordTrace]
  refine ⟨9245266304178062575675811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24654043477808166868468829 9245266304178062575675811)
  ·
    refine ⟨13867899456267093863513717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9245266304178062575675811 13867899456267093863513717)
    ·
      refine ⟨1300115574025040049704411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13867899456267093863513717 1300115574025040049704411)
      ·
        refine ⟨1950173361037560074556617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300115574025040049704411 1950173361037560074556617)
        ·
          refine ⟨1462630020778170055917463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1950173361037560074556617 1462630020778170055917463)
          ·
            refine ⟨2193945031167255083876195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462630020778170055917463 2193945031167255083876195)
            ·
              refine ⟨3290917546750882625814293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193945031167255083876195 3290917546750882625814293)
              ·
                refine ⟨154261760003947623085045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3290917546750882625814293 154261760003947623085045)
                ·
                  rfl

theorem cell20_1013930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_1013930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013930 prefixEnd_1013930 := by exact prefixLift 1013930
  have htrace : WordTrace (prefixWord ++ tailWord_1013930) baseStart_1013930 baseEnd_1013930 := by
    simpa [prefixWord, tailWord_1013930, baseEnd_1013930] using wordTrace_append hprefix tailTrace_1013930
  have hstable : (prefixWord ++ tailWord_1013930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013930).length < 2 ^ (prefixWord ++ tailWord_1013930).sum := by decide
  have hdescent : baseEnd_1013930 < baseStart_1013930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013954 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1013954 : Nat := 118140960795 + 1013954 * 2 ^ 59
def prefixEnd_1013954 : Nat := 4983230072969 + 3 ^ 40 * 1013954 * 2
def baseEnd_1013954 : Nat := 462796234265805452455037

theorem tailTrace_1013954 : CollatzResearch.WordTrace tailWord_1013954 prefixEnd_1013954 462796234265805452455037 := by
  unfold tailWord_1013954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9245485142156325600394229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24654627045750201601051277 9245485142156325600394229)
  ·
    refine ⟨866764232077155525036959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9245485142156325600394229 866764232077155525036959)
    ·
      refine ⟨1300146348115733287555439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866764232077155525036959 1300146348115733287555439)
      ·
        refine ⟨1950219522173599931333159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300146348115733287555439 1950219522173599931333159)
        ·
          refine ⟨2925329283260399896999739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950219522173599931333159 2925329283260399896999739)
          ·
            refine ⟨4387993924890599845499609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925329283260399896999739 4387993924890599845499609)
            ·
              refine ⟨3290995443667949884124707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4387993924890599845499609 3290995443667949884124707)
              ·
                refine ⟨4936493165501924826187061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290995443667949884124707 4936493165501924826187061)
                ·
                  refine ⟨462796234265805452455037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4936493165501924826187061 462796234265805452455037)
                  ·
                    rfl

theorem cell20_1013954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1013954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1013954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1013954 prefixEnd_1013954 := by exact prefixLift 1013954
  have htrace : WordTrace (prefixWord ++ tailWord_1013954) baseStart_1013954 baseEnd_1013954 := by
    simpa [prefixWord, tailWord_1013954, baseEnd_1013954] using wordTrace_append hprefix tailTrace_1013954
  have hstable : (prefixWord ++ tailWord_1013954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013954).length < 2 ^ (prefixWord ++ tailWord_1013954).sum := by decide
  have hdescent : baseEnd_1013954 < baseStart_1013954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014023 : List Nat := [1, 1, 4, 5, 2, 1, 1, 5]
def baseStart_1014023 : Nat := 118140960795 + 1014023 * 2 ^ 59
def prefixEnd_1014023 : Nat := 4983230072969 + 3 ^ 40 * 1014023 * 2
def baseEnd_1014023 : Nat := 154275909248649293051585

theorem tailTrace_1014023 : CollatzResearch.WordTrace tailWord_1014023 prefixEnd_1014023 154275909248649293051585 := by
  unfold tailWord_1014023
  simp only [CollatzResearch.WordTrace]
  refine ⟨36984457205375327185838723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24656304803583551457225815 36984457205375327185838723)
  ·
    refine ⟨55476685808062990778758085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36984457205375327185838723 55476685808062990778758085)
    ·
      refine ⟨10401878589011810771017141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55476685808062990778758085 10401878589011810771017141)
      ·
        refine ⟨975176117719857259782857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10401878589011810771017141 975176117719857259782857)
        ·
          refine ⟨731382088289892944837143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975176117719857259782857 731382088289892944837143)
          ·
            refine ⟨1097073132434839417255715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731382088289892944837143 1097073132434839417255715)
            ·
              refine ⟨1645609698652259125883573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097073132434839417255715 1645609698652259125883573)
              ·
                refine ⟨154275909248649293051585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1645609698652259125883573 154275909248649293051585)
                ·
                  rfl

theorem cell20_1014023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 5].length) (baseStart_1014023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014023 prefixEnd_1014023 := by exact prefixLift 1014023
  have htrace : WordTrace (prefixWord ++ tailWord_1014023) baseStart_1014023 baseEnd_1014023 := by
    simpa [prefixWord, tailWord_1014023, baseEnd_1014023] using wordTrace_append hprefix tailTrace_1014023
  have hstable : (prefixWord ++ tailWord_1014023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014023).length < 2 ^ (prefixWord ++ tailWord_1014023).sum := by decide
  have hdescent : baseEnd_1014023 < baseStart_1014023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014068 : List Nat := [2, 5, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1014068 : Nat := 118140960795 + 1014068 * 2 ^ 59
def prefixEnd_1014068 : Nat := 4983230072969 + 3 ^ 40 * 1014068 * 2
def baseEnd_1014068 : Nat := 462848266972127722654571

theorem tailTrace_1014068 : CollatzResearch.WordTrace tailWord_1014068 prefixEnd_1014068 462848266972127722654571 := by
  unfold tailWord_1014068
  simp only [CollatzResearch.WordTrace]
  refine ⟨18493049245106149935613429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24657398993474866580817905 18493049245106149935613429)
  ·
    refine ⟨1733723366728701556463759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18493049245106149935613429 1733723366728701556463759)
    ·
      refine ⟨2600585050093052334695639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733723366728701556463759 2600585050093052334695639)
      ·
        refine ⟨3900877575139578502043459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2600585050093052334695639 3900877575139578502043459)
        ·
          refine ⟨5851316362709367753065189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900877575139578502043459 5851316362709367753065189)
          ·
            refine ⟨1097121818008006453699723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5851316362709367753065189 1097121818008006453699723)
            ·
              refine ⟨1645682727012009680549585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097121818008006453699723 1645682727012009680549585)
              ·
                refine ⟨1234262045259007260412189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1645682727012009680549585 1234262045259007260412189)
                ·
                  refine ⟨462848266972127722654571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234262045259007260412189 462848266972127722654571)
                  ·
                    rfl

theorem cell20_1014068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1014068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014068 prefixEnd_1014068 := by exact prefixLift 1014068
  have htrace : WordTrace (prefixWord ++ tailWord_1014068) baseStart_1014068 baseEnd_1014068 := by
    simpa [prefixWord, tailWord_1014068, baseEnd_1014068] using wordTrace_append hprefix tailTrace_1014068
  have hstable : (prefixWord ++ tailWord_1014068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014068).length < 2 ^ (prefixWord ++ tailWord_1014068).sum := by decide
  have hdescent : baseEnd_1014068 < baseStart_1014068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014072 : List Nat := [2, 1, 2, 1, 3, 1, 5, 2, 3]
def baseStart_1014072 : Nat := 118140960795 + 1014072 * 2 ^ 59
def prefixEnd_1014072 : Nat := 4983230072969 + 3 ^ 40 * 1014072 * 2
def baseEnd_1014072 : Nat := 462850092681121486521221

theorem tailTrace_1014072 : CollatzResearch.WordTrace tailWord_1014072 prefixEnd_1014072 462850092681121486521221 := by
  unfold tailWord_1014072
  simp only [CollatzResearch.WordTrace]
  refine ⟨18493122191098904277186235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24657496254798539036248313 18493122191098904277186235)
  ·
    refine ⟨27739683286648356415779353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18493122191098904277186235 27739683286648356415779353)
    ·
      refine ⟨20804762464986267311834515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27739683286648356415779353 20804762464986267311834515)
      ·
        refine ⟨31207143697479400967751773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20804762464986267311834515 31207143697479400967751773)
        ·
          refine ⟨11702678886554775362906915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31207143697479400967751773 11702678886554775362906915)
          ·
            refine ⟨17554018329832163044360373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11702678886554775362906915 17554018329832163044360373)
            ·
              refine ⟨1645689218421765285408785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17554018329832163044360373 1645689218421765285408785)
              ·
                refine ⟨1234266913816323964056589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1645689218421765285408785 1234266913816323964056589)
                ·
                  refine ⟨462850092681121486521221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234266913816323964056589 462850092681121486521221)
                  ·
                    rfl

theorem cell20_1014072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_1014072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014072 prefixEnd_1014072 := by exact prefixLift 1014072
  have htrace : WordTrace (prefixWord ++ tailWord_1014072) baseStart_1014072 baseEnd_1014072 := by
    simpa [prefixWord, tailWord_1014072, baseEnd_1014072] using wordTrace_append hprefix tailTrace_1014072
  have hstable : (prefixWord ++ tailWord_1014072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014072).length < 2 ^ (prefixWord ++ tailWord_1014072).sum := by decide
  have hdescent : baseEnd_1014072 < baseStart_1014072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014079 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 4]
def baseStart_1014079 : Nat := 118140960795 + 1014079 * 2 ^ 59
def prefixEnd_1014079 : Nat := 4983230072969 + 3 ^ 40 * 1014079 * 2
def baseEnd_1014079 : Nat := 462853287671860573287859

theorem tailTrace_1014079 : CollatzResearch.WordTrace tailWord_1014079 prefixEnd_1014079 462853287671860573287859 := by
  unfold tailWord_1014079
  simp only [CollatzResearch.WordTrace]
  refine ⟨36986499693172448749877291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24657666462114965833251527 36986499693172448749877291)
  ·
    refine ⟨55479749539758673124815937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36986499693172448749877291 55479749539758673124815937)
    ·
      refine ⟨41609812154819004843611953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55479749539758673124815937 41609812154819004843611953)
      ·
        refine ⟨31207359116114253632708965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41609812154819004843611953 31207359116114253632708965)
        ·
          refine ⟨5851379834271422556132931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31207359116114253632708965 5851379834271422556132931)
          ·
            refine ⟨8777069751407133834199397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5851379834271422556132931 8777069751407133834199397)
            ·
              refine ⟨1645700578388837593912387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8777069751407133834199397 1645700578388837593912387)
              ·
                refine ⟨2468550867583256390868581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645700578388837593912387 2468550867583256390868581)
                ·
                  refine ⟨462853287671860573287859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2468550867583256390868581 462853287671860573287859)
                  ·
                    rfl

theorem cell20_1014079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_1014079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014079 prefixEnd_1014079 := by exact prefixLift 1014079
  have htrace : WordTrace (prefixWord ++ tailWord_1014079) baseStart_1014079 baseEnd_1014079 := by
    simpa [prefixWord, tailWord_1014079, baseEnd_1014079] using wordTrace_append hprefix tailTrace_1014079
  have hstable : (prefixWord ++ tailWord_1014079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014079).length < 2 ^ (prefixWord ++ tailWord_1014079).sum := by decide
  have hdescent : baseEnd_1014079 < baseStart_1014079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014148 : List Nat := [2, 3, 2, 1, 1, 2, 3, 3, 3]
def baseStart_1014148 : Nat := 118140960795 + 1014148 * 2 ^ 59
def prefixEnd_1014148 : Nat := 4983230072969 + 3 ^ 40 * 1014148 * 2
def baseEnd_1014148 : Nat := 462884781152002999987577

theorem tailTrace_1014148 : CollatzResearch.WordTrace tailWord_1014148 prefixEnd_1014148 462884781152002999987577 := by
  unfold tailWord_1014148
  simp only [CollatzResearch.WordTrace]
  refine ⟨18494508164961236767069549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24659344219948315689426065 18494508164961236767069549)
  ·
    refine ⟨6935440561860463787651081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18494508164961236767069549 6935440561860463787651081)
    ·
      refine ⟨5201580421395347840738311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6935440561860463787651081 5201580421395347840738311)
      ·
        refine ⟨7802370632093021761107467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5201580421395347840738311 7802370632093021761107467)
        ·
          refine ⟨11703555948139532641661201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7802370632093021761107467 11703555948139532641661201)
          ·
            refine ⟨8777666961104649481245901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11703555948139532641661201 8777666961104649481245901)
            ·
              refine ⟨3291625110414243555467213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8777666961104649481245901 3291625110414243555467213)
              ·
                refine ⟨1234359416405341333300205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3291625110414243555467213 1234359416405341333300205)
                ·
                  refine ⟨462884781152002999987577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234359416405341333300205 462884781152002999987577)
                  ·
                    rfl

theorem cell20_1014148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_1014148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014148 prefixEnd_1014148 := by exact prefixLift 1014148
  have htrace : WordTrace (prefixWord ++ tailWord_1014148) baseStart_1014148 baseEnd_1014148 := by
    simpa [prefixWord, tailWord_1014148, baseEnd_1014148] using wordTrace_append hprefix tailTrace_1014148
  have hstable : (prefixWord ++ tailWord_1014148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014148).length < 2 ^ (prefixWord ++ tailWord_1014148).sum := by decide
  have hdescent : baseEnd_1014148 < baseStart_1014148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014248 : List Nat := [2, 1, 4, 1, 1, 3, 2, 4, 2]
def baseStart_1014248 : Nat := 118140960795 + 1014248 * 2 ^ 59
def prefixEnd_1014248 : Nat := 4983230072969 + 3 ^ 40 * 1014248 * 2
def baseEnd_1014248 : Nat := 462930423876847096653835

theorem tailTrace_1014248 : CollatzResearch.WordTrace tailWord_1014248 prefixEnd_1014248 462930423876847096653835 := by
  unfold tailWord_1014248
  simp only [CollatzResearch.WordTrace]
  refine ⟨18496331814780095306389699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24661775753040127075186265 18496331814780095306389699)
  ·
    refine ⟨27744497722170142959584549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18496331814780095306389699 27744497722170142959584549)
    ·
      refine ⟨5202093322906901804922103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27744497722170142959584549 5202093322906901804922103)
      ·
        refine ⟨7803139984360352707383155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5202093322906901804922103 7803139984360352707383155)
        ·
          refine ⟨11704709976540529061074733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7803139984360352707383155 11704709976540529061074733)
          ·
            refine ⟨4389266241202698397903025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11704709976540529061074733 4389266241202698397903025)
            ·
              refine ⟨3291949680902023798427269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4389266241202698397903025 3291949680902023798427269)
              ·
                refine ⟨617240565169129462205113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3291949680902023798427269 617240565169129462205113)
                ·
                  refine ⟨462930423876847096653835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617240565169129462205113 462930423876847096653835)
                  ·
                    rfl

theorem cell20_1014248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 2].length) (baseStart_1014248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014248 prefixEnd_1014248 := by exact prefixLift 1014248
  have htrace : WordTrace (prefixWord ++ tailWord_1014248) baseStart_1014248 baseEnd_1014248 := by
    simpa [prefixWord, tailWord_1014248, baseEnd_1014248] using wordTrace_append hprefix tailTrace_1014248
  have hstable : (prefixWord ++ tailWord_1014248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014248).length < 2 ^ (prefixWord ++ tailWord_1014248).sum := by decide
  have hdescent : baseEnd_1014248 < baseStart_1014248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014258 : List Nat := [3, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_1014258 : Nat := 118140960795 + 1014258 * 2 ^ 59
def prefixEnd_1014258 : Nat := 4983230072969 + 3 ^ 40 * 1014258 * 2
def baseEnd_1014258 : Nat := 462934988149331506320461

theorem tailTrace_1014258 : CollatzResearch.WordTrace tailWord_1014258 prefixEnd_1014258 462934988149331506320461 := by
  unfold tailWord_1014258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9248257089880990580160857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24662018906349308213762285 9248257089880990580160857)
  ·
    refine ⟨6936192817410742935120643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9248257089880990580160857 6936192817410742935120643)
    ·
      refine ⟨10404289226116114402680965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6936192817410742935120643 10404289226116114402680965)
      ·
        refine ⟨1950804229896771450502681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10404289226116114402680965 1950804229896771450502681)
        ·
          refine ⟨1463103172422578587877011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1950804229896771450502681 1463103172422578587877011)
          ·
            refine ⟨2194654758633867881815517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463103172422578587877011 2194654758633867881815517)
            ·
              refine ⟨822995534487700455680819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2194654758633867881815517 822995534487700455680819)
              ·
                refine ⟨1234493301731550683521229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822995534487700455680819 1234493301731550683521229)
                ·
                  refine ⟨462934988149331506320461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234493301731550683521229 462934988149331506320461)
                  ·
                    rfl

theorem cell20_1014258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_1014258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014258 prefixEnd_1014258 := by exact prefixLift 1014258
  have htrace : WordTrace (prefixWord ++ tailWord_1014258) baseStart_1014258 baseEnd_1014258 := by
    simpa [prefixWord, tailWord_1014258, baseEnd_1014258] using wordTrace_append hprefix tailTrace_1014258
  have hstable : (prefixWord ++ tailWord_1014258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014258).length < 2 ^ (prefixWord ++ tailWord_1014258).sum := by decide
  have hdescent : baseEnd_1014258 < baseStart_1014258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014259 : List Nat := [1, 1, 1, 2, 2, 2, 4, 7]
def baseStart_1014259 : Nat := 118140960795 + 1014259 * 2 ^ 59
def prefixEnd_1014259 : Nat := 4983230072969 + 3 ^ 40 * 1014259 * 2
def baseEnd_1014259 : Nat := 154311814858859982429041

theorem tailTrace_1014259 : CollatzResearch.WordTrace tailWord_1014259 prefixEnd_1014259 154311814858859982429041 := by
  unfold tailWord_1014259
  simp only [CollatzResearch.WordTrace]
  refine ⟨36993064832520339491429831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24662043221680226327619887 36993064832520339491429831)
  ·
    refine ⟨55489597248780509237144747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36993064832520339491429831 55489597248780509237144747)
    ·
      refine ⟨83234395873170763855717121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55489597248780509237144747 83234395873170763855717121)
      ·
        refine ⟨62425796904878072891787841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83234395873170763855717121 62425796904878072891787841)
        ·
          refine ⟨46819347678658554668840881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62425796904878072891787841 46819347678658554668840881)
          ·
            refine ⟨35114510758993916001630661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46819347678658554668840881 35114510758993916001630661)
            ·
              refine ⟨6583970767311359250305749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35114510758993916001630661 6583970767311359250305749)
              ·
                refine ⟨154311814858859982429041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6583970767311359250305749 154311814858859982429041)
                ·
                  rfl

theorem cell20_1014259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_1014259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014259 prefixEnd_1014259 := by exact prefixLift 1014259
  have htrace : WordTrace (prefixWord ++ tailWord_1014259) baseStart_1014259 baseEnd_1014259 := by
    simpa [prefixWord, tailWord_1014259, baseEnd_1014259] using wordTrace_append hprefix tailTrace_1014259
  have hstable : (prefixWord ++ tailWord_1014259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014259).length < 2 ^ (prefixWord ++ tailWord_1014259).sum := by decide
  have hdescent : baseEnd_1014259 < baseStart_1014259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014278 : List Nat := [6, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1014278 : Nat := 118140960795 + 1014278 * 2 ^ 59
def prefixEnd_1014278 : Nat := 4983230072969 + 3 ^ 40 * 1014278 * 2
def baseEnd_1014278 : Nat := 462944116694300325653713

theorem tailTrace_1014278 : CollatzResearch.WordTrace tailWord_1014278 prefixEnd_1014278 462944116694300325653713 := by
  unfold tailWord_1014278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156054931857859554261609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24662505212967670490914325 1156054931857859554261609)
  ·
    refine ⟨867041198893394665696207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1156054931857859554261609 867041198893394665696207)
    ·
      refine ⟨1300561798340091998544311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 867041198893394665696207 1300561798340091998544311)
      ·
        refine ⟨1950842697510137997816467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300561798340091998544311 1950842697510137997816467)
        ·
          refine ⟨2926264046265206996724701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950842697510137997816467 2926264046265206996724701)
          ·
            refine ⟨1097349017349452623771763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2926264046265206996724701 1097349017349452623771763)
            ·
              refine ⟨1646023526024178935657645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097349017349452623771763 1646023526024178935657645)
              ·
                refine ⟨617258822259067100871617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1646023526024178935657645 617258822259067100871617)
                ·
                  refine ⟨462944116694300325653713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617258822259067100871617 462944116694300325653713)
                  ·
                    rfl

theorem cell20_1014278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1014278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014278 prefixEnd_1014278 := by exact prefixLift 1014278
  have htrace : WordTrace (prefixWord ++ tailWord_1014278) baseStart_1014278 baseEnd_1014278 := by
    simpa [prefixWord, tailWord_1014278, baseEnd_1014278] using wordTrace_append hprefix tailTrace_1014278
  have hstable : (prefixWord ++ tailWord_1014278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014278).length < 2 ^ (prefixWord ++ tailWord_1014278).sum := by decide
  have hdescent : baseEnd_1014278 < baseStart_1014278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014283 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 5]
def baseStart_1014283 : Nat := 118140960795 + 1014283 * 2 ^ 59
def prefixEnd_1014283 : Nat := 4983230072969 + 3 ^ 40 * 1014283 * 2
def baseEnd_1014283 : Nat := 462946398830542530487025

theorem tailTrace_1014283 : CollatzResearch.WordTrace tailWord_1014283 prefixEnd_1014283 462946398830542530487025 := by
  unfold tailWord_1014283
  simp only [CollatzResearch.WordTrace]
  refine ⟨36993940184433391590303503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24662626789622261060202335 36993940184433391590303503)
  ·
    refine ⟨55490910276650087385455255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36993940184433391590303503 55490910276650087385455255)
    ·
      refine ⟨83236365414975131078182883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55490910276650087385455255 83236365414975131078182883)
      ·
        refine ⟨124854548122462696617274325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83236365414975131078182883 124854548122462696617274325)
        ·
          refine ⟨2926278471620219451967367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 124854548122462696617274325 2926278471620219451967367)
          ·
            refine ⟨4389417707430329177951051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926278471620219451967367 4389417707430329177951051)
            ·
              refine ⟨6584126561145493766926577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4389417707430329177951051 6584126561145493766926577)
              ·
                refine ⟨4938094920859120325194933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6584126561145493766926577 4938094920859120325194933)
                ·
                  refine ⟨462946398830542530487025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4938094920859120325194933 462946398830542530487025)
                  ·
                    rfl

theorem cell20_1014283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_1014283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014283 prefixEnd_1014283 := by exact prefixLift 1014283
  have htrace : WordTrace (prefixWord ++ tailWord_1014283) baseStart_1014283 baseEnd_1014283 := by
    simpa [prefixWord, tailWord_1014283, baseEnd_1014283] using wordTrace_append hprefix tailTrace_1014283
  have hstable : (prefixWord ++ tailWord_1014283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014283).length < 2 ^ (prefixWord ++ tailWord_1014283).sum := by decide
  have hdescent : baseEnd_1014283 < baseStart_1014283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014307 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 4]
def baseStart_1014307 : Nat := 118140960795 + 1014307 * 2 ^ 59
def prefixEnd_1014307 : Nat := 4983230072969 + 3 ^ 40 * 1014307 * 2
def baseEnd_1014307 : Nat := 462957353084505113686927

theorem tailTrace_1014307 : CollatzResearch.WordTrace tailWord_1014307 prefixEnd_1014307 462957353084505113686927 := by
  unfold tailWord_1014307
  simp only [CollatzResearch.WordTrace]
  refine ⟨36994815536346443689177175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24663210357564295792784783 36994815536346443689177175)
  ·
    refine ⟨55492223304519665533765763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36994815536346443689177175 55492223304519665533765763)
    ·
      refine ⟨83238334956779498300648645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55492223304519665533765763 83238334956779498300648645)
      ·
        refine ⟨15607187804396155931371621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83238334956779498300648645 15607187804396155931371621)
        ·
          refine ⟨2926347713324279237132179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15607187804396155931371621 2926347713324279237132179)
          ·
            refine ⟨4389521569986418855698269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926347713324279237132179 4389521569986418855698269)
            ·
              refine ⟨1646070588744907070886851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4389521569986418855698269 1646070588744907070886851)
              ·
                refine ⟨2469105883117360606330277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646070588744907070886851 2469105883117360606330277)
                ·
                  refine ⟨462957353084505113686927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2469105883117360606330277 462957353084505113686927)
                  ·
                    rfl

theorem cell20_1014307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_1014307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014307 prefixEnd_1014307 := by exact prefixLift 1014307
  have htrace : WordTrace (prefixWord ++ tailWord_1014307) baseStart_1014307 baseEnd_1014307 := by
    simpa [prefixWord, tailWord_1014307, baseEnd_1014307] using wordTrace_append hprefix tailTrace_1014307
  have hstable : (prefixWord ++ tailWord_1014307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014307).length < 2 ^ (prefixWord ++ tailWord_1014307).sum := by decide
  have hdescent : baseEnd_1014307 < baseStart_1014307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014314 : List Nat := [3, 1, 4, 1, 1, 2, 1, 7]
def baseStart_1014314 : Nat := 118140960795 + 1014314 * 2 ^ 59
def prefixEnd_1014314 : Nat := 4983230072969 + 3 ^ 40 * 1014314 * 2
def baseEnd_1014314 : Nat := 154320182691748066817855

theorem tailTrace_1014314 : CollatzResearch.WordTrace tailWord_1014314 prefixEnd_1014314 154320182691748066817855 := by
  unfold tailWord_1014314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9248767711830270971170499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24663380564880722589787997 9248767711830270971170499)
  ·
    refine ⟨13873151567745406456755749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9248767711830270971170499 13873151567745406456755749)
    ·
      refine ⟨2601215918952263710641703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13873151567745406456755749 2601215918952263710641703)
      ·
        refine ⟨3901823878428395565962555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2601215918952263710641703 3901823878428395565962555)
        ·
          refine ⟨5852735817642593348943833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3901823878428395565962555 5852735817642593348943833)
          ·
            refine ⟨4389551863231945011707875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5852735817642593348943833 4389551863231945011707875)
            ·
              refine ⟨6584327794847917517561813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4389551863231945011707875 6584327794847917517561813)
              ·
                refine ⟨154320182691748066817855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6584327794847917517561813 154320182691748066817855)
                ·
                  rfl

theorem cell20_1014314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_1014314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014314 prefixEnd_1014314 := by exact prefixLift 1014314
  have htrace : WordTrace (prefixWord ++ tailWord_1014314) baseStart_1014314 baseEnd_1014314 := by
    simpa [prefixWord, tailWord_1014314, baseEnd_1014314] using wordTrace_append hprefix tailTrace_1014314
  have hstable : (prefixWord ++ tailWord_1014314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014314).length < 2 ^ (prefixWord ++ tailWord_1014314).sum := by decide
  have hdescent : baseEnd_1014314 < baseStart_1014314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014328 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_1014328 : Nat := 118140960795 + 1014328 * 2 ^ 59
def prefixEnd_1014328 : Nat := 4983230072969 + 3 ^ 40 * 1014328 * 2
def baseEnd_1014328 : Nat := 462966938056722373986841

theorem tailTrace_1014328 : CollatzResearch.WordTrace tailWord_1014328 prefixEnd_1014328 462966938056722373986841 := by
  unfold tailWord_1014328
  simp only [CollatzResearch.WordTrace]
  refine ⟨18497790734635182137845819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24663720979513576183794425 18497790734635182137845819)
  ·
    refine ⟨27746686101952773206768729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18497790734635182137845819 27746686101952773206768729)
    ·
      refine ⟨20810014576464579905076547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27746686101952773206768729 20810014576464579905076547)
      ·
        refine ⟨31215021864696869857614821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20810014576464579905076547 31215021864696869857614821)
        ·
          refine ⟨5852816599630663098302779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31215021864696869857614821 5852816599630663098302779)
          ·
            refine ⟨8779224899445994647454169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5852816599630663098302779 8779224899445994647454169)
            ·
              refine ⟨6584418674584495985590627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8779224899445994647454169 6584418674584495985590627)
              ·
                refine ⟨9876628011876743978385941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6584418674584495985590627 9876628011876743978385941)
                ·
                  refine ⟨462966938056722373986841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9876628011876743978385941 462966938056722373986841)
                  ·
                    rfl

theorem cell20_1014328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_1014328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014328 prefixEnd_1014328 := by exact prefixLift 1014328
  have htrace : WordTrace (prefixWord ++ tailWord_1014328) baseStart_1014328 baseEnd_1014328 := by
    simpa [prefixWord, tailWord_1014328, baseEnd_1014328] using wordTrace_append hprefix tailTrace_1014328
  have hstable : (prefixWord ++ tailWord_1014328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014328).length < 2 ^ (prefixWord ++ tailWord_1014328).sum := by decide
  have hdescent : baseEnd_1014328 < baseStart_1014328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014335 : List Nat := [1, 1, 2, 2, 3, 2, 1, 8]
def baseStart_1014335 : Nat := 118140960795 + 1014335 * 2 ^ 59
def prefixEnd_1014335 : Nat := 4983230072969 + 3 ^ 40 * 1014335 * 2
def baseEnd_1014335 : Nat := 154323377682487153584493

theorem tailTrace_1014335 : CollatzResearch.WordTrace tailWord_1014335 prefixEnd_1014335 154323377682487153584493 := by
  unfold tailWord_1014335
  simp only [CollatzResearch.WordTrace]
  refine ⟨36995836780245004471196459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24663891186830002980797639 36995836780245004471196459)
  ·
    refine ⟨55493755170367506706794689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36995836780245004471196459 55493755170367506706794689)
    ·
      refine ⟨41620316377775630030096017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55493755170367506706794689 41620316377775630030096017)
      ·
        refine ⟨31215237283331722522572013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41620316377775630030096017 31215237283331722522572013)
        ·
          refine ⟨11705713981249395945964505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31215237283331722522572013 11705713981249395945964505)
          ·
            refine ⟨8779285485937046959473379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11705713981249395945964505 8779285485937046959473379)
            ·
              refine ⟨13168928228905570439210069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8779285485937046959473379 13168928228905570439210069)
              ·
                refine ⟨154323377682487153584493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13168928228905570439210069 154323377682487153584493)
                ·
                  rfl

theorem cell20_1014335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_1014335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014335 prefixEnd_1014335 := by exact prefixLift 1014335
  have htrace : WordTrace (prefixWord ++ tailWord_1014335) baseStart_1014335 baseEnd_1014335 := by
    simpa [prefixWord, tailWord_1014335, baseEnd_1014335] using wordTrace_append hprefix tailTrace_1014335
  have hstable : (prefixWord ++ tailWord_1014335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014335).length < 2 ^ (prefixWord ++ tailWord_1014335).sum := by decide
  have hdescent : baseEnd_1014335 < baseStart_1014335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014400 : List Nat := [2, 1, 1, 2, 1, 6, 2, 3, 2]
def baseStart_1014400 : Nat := 118140960795 + 1014400 * 2 ^ 59
def prefixEnd_1014400 : Nat := 4983230072969 + 3 ^ 40 * 1014400 * 2
def baseEnd_1014400 : Nat := 462999800818610123586547

theorem tailTrace_1014400 : CollatzResearch.WordTrace tailWord_1014400 prefixEnd_1014400 462999800818610123586547 := by
  unfold tailWord_1014400
  simp only [CollatzResearch.WordTrace]
  refine ⟨18499103762504760286156327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24665471683339680381541769 18499103762504760286156327)
  ·
    refine ⟨27748655643757140429234491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18499103762504760286156327 27748655643757140429234491)
    ·
      refine ⟨41622983465635710643851737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27748655643757140429234491 41622983465635710643851737)
      ·
        refine ⟨31217237599226782982888803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41622983465635710643851737 31217237599226782982888803)
        ·
          refine ⟨46825856398840174474333205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31217237599226782982888803 46825856398840174474333205)
          ·
            refine ⟨2194962018695633178484369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46825856398840174474333205 2194962018695633178484369)
            ·
              refine ⟨1646221514021724883863277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2194962018695633178484369 1646221514021724883863277)
              ·
                refine ⟨617333067758146831448729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1646221514021724883863277 617333067758146831448729)
                ·
                  refine ⟨462999800818610123586547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617333067758146831448729 462999800818610123586547)
                  ·
                    rfl

theorem cell20_1014400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 2].length) (baseStart_1014400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014400 prefixEnd_1014400 := by exact prefixLift 1014400
  have htrace : WordTrace (prefixWord ++ tailWord_1014400) baseStart_1014400 baseEnd_1014400 := by
    simpa [prefixWord, tailWord_1014400, baseEnd_1014400] using wordTrace_append hprefix tailTrace_1014400
  have hstable : (prefixWord ++ tailWord_1014400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014400).length < 2 ^ (prefixWord ++ tailWord_1014400).sum := by decide
  have hdescent : baseEnd_1014400 < baseStart_1014400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014410 : List Nat := [3, 1, 2, 3, 4, 1, 1, 2, 3]
def baseStart_1014410 : Nat := 118140960795 + 1014410 * 2 ^ 59
def prefixEnd_1014410 : Nat := 4983230072969 + 3 ^ 40 * 1014410 * 2
def baseEnd_1014410 : Nat := 463004365091094533253173

theorem tailTrace_1014410 : CollatzResearch.WordTrace tailWord_1014410 prefixEnd_1014410 463004365091094533253173 := by
  unfold tailWord_1014410
  simp only [CollatzResearch.WordTrace]
  refine ⟨9249643063743323070044171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24665714836648861520117789 9249643063743323070044171)
  ·
    refine ⟨13874464595614984605066257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9249643063743323070044171 13874464595614984605066257)
    ·
      refine ⟨10405848446711238453799693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13874464595614984605066257 10405848446711238453799693)
      ·
        refine ⟨3902193167516714420174885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10405848446711238453799693 3902193167516714420174885)
        ·
          refine ⟨731661218909383953782791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3902193167516714420174885 731661218909383953782791)
          ·
            refine ⟨1097491828364075930674187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731661218909383953782791 1097491828364075930674187)
            ·
              refine ⟨1646237742546113896011281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097491828364075930674187 1646237742546113896011281)
              ·
                refine ⟨1234678306909585422008461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1646237742546113896011281 1234678306909585422008461)
                ·
                  refine ⟨463004365091094533253173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234678306909585422008461 463004365091094533253173)
                  ·
                    rfl

theorem cell20_1014410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_1014410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014410 prefixEnd_1014410 := by exact prefixLift 1014410
  have htrace : WordTrace (prefixWord ++ tailWord_1014410) baseStart_1014410 baseEnd_1014410 := by
    simpa [prefixWord, tailWord_1014410, baseEnd_1014410] using wordTrace_append hprefix tailTrace_1014410
  have hstable : (prefixWord ++ tailWord_1014410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014410).length < 2 ^ (prefixWord ++ tailWord_1014410).sum := by decide
  have hdescent : baseEnd_1014410 < baseStart_1014410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014445 : List Nat := [1, 5, 2, 1, 1, 2, 4, 4]
def baseStart_1014445 : Nat := 118140960795 + 1014445 * 2 ^ 59
def prefixEnd_1014445 : Nat := 4983230072969 + 3 ^ 40 * 1014445 * 2
def baseEnd_1014445 : Nat := 154340113348263322362121

theorem tailTrace_1014445 : CollatzResearch.WordTrace tailWord_1014445 prefixEnd_1014445 154340113348263322362121 := by
  unfold tailWord_1014445
  simp only [CollatzResearch.WordTrace]
  refine ⟨36999848809846493257700789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24666565873230995505133859 36999848809846493257700789)
  ·
    refine ⟨3468735825923108742909449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36999848809846493257700789 3468735825923108742909449)
    ·
      refine ⟨2601551869442331557182087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3468735825923108742909449 2601551869442331557182087)
      ·
        refine ⟨3902327804163497335773131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2601551869442331557182087 3902327804163497335773131)
        ·
          refine ⟨5853491706245246003659697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902327804163497335773131 5853491706245246003659697)
          ·
            refine ⟨4390118779683934502744773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5853491706245246003659697 4390118779683934502744773)
            ·
              refine ⟨823147271190737719264645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4390118779683934502744773 823147271190737719264645)
              ·
                refine ⟨154340113348263322362121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 823147271190737719264645 154340113348263322362121)
                ·
                  rfl

theorem cell20_1014445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 4].length) (baseStart_1014445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014445 prefixEnd_1014445 := by exact prefixLift 1014445
  have htrace : WordTrace (prefixWord ++ tailWord_1014445) baseStart_1014445 baseEnd_1014445 := by
    simpa [prefixWord, tailWord_1014445, baseEnd_1014445] using wordTrace_append hprefix tailTrace_1014445
  have hstable : (prefixWord ++ tailWord_1014445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014445).length < 2 ^ (prefixWord ++ tailWord_1014445).sum := by decide
  have hdescent : baseEnd_1014445 < baseStart_1014445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014455 : List Nat := [1, 1, 3, 1, 6, 2, 1, 3, 2]
def baseStart_1014455 : Nat := 118140960795 + 1014455 * 2 ^ 59
def prefixEnd_1014455 : Nat := 4983230072969 + 3 ^ 40 * 1014455 * 2
def baseEnd_1014455 : Nat := 463024904317274376752989

theorem tailTrace_1014455 : CollatzResearch.WordTrace tailWord_1014455 prefixEnd_1014455 463024904317274376752989 := by
  unfold tailWord_1014455
  simp only [CollatzResearch.WordTrace]
  refine ⟨37000213539810264965564819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24666809026540176643709879 37000213539810264965564819)
  ·
    refine ⟨55500320309715397448347229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37000213539810264965564819 55500320309715397448347229)
    ·
      refine ⟨20812620116143274043130211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55500320309715397448347229 20812620116143274043130211)
      ·
        refine ⟨31218930174214911064695317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20812620116143274043130211 31218930174214911064695317)
        ·
          refine ⟨1463387351916323956157593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31218930174214911064695317 1463387351916323956157593)
          ·
            refine ⟨1097540513937242967118195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1463387351916323956157593 1097540513937242967118195)
            ·
              refine ⟨1646310770905864450677293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097540513937242967118195 1646310770905864450677293)
              ·
                refine ⟨617366539089699169003985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1646310770905864450677293 617366539089699169003985)
                ·
                  refine ⟨463024904317274376752989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617366539089699169003985 463024904317274376752989)
                  ·
                    rfl

theorem cell20_1014455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 2].length) (baseStart_1014455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014455 prefixEnd_1014455 := by exact prefixLift 1014455
  have htrace : WordTrace (prefixWord ++ tailWord_1014455) baseStart_1014455 baseEnd_1014455 := by
    simpa [prefixWord, tailWord_1014455, baseEnd_1014455] using wordTrace_append hprefix tailTrace_1014455
  have hstable : (prefixWord ++ tailWord_1014455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014455).length < 2 ^ (prefixWord ++ tailWord_1014455).sum := by decide
  have hdescent : baseEnd_1014455 < baseStart_1014455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014476 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 4]
def baseStart_1014476 : Nat := 118140960795 + 1014476 * 2 ^ 59
def prefixEnd_1014476 : Nat := 4983230072969 + 3 ^ 40 * 1014476 * 2
def baseEnd_1014476 : Nat := 463034489289491637052903

theorem tailTrace_1014476 : CollatzResearch.WordTrace tailWord_1014476 prefixEnd_1014476 463034489289491637052903 := by
  unfold tailWord_1014476
  simp only [CollatzResearch.WordTrace]
  refine ⟨18500489736367092776039641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24667319648489457034719521 18500489736367092776039641)
  ·
    refine ⟨13875367302275319582029731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18500489736367092776039641 13875367302275319582029731)
    ·
      refine ⟨20813050953412979373044597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13875367302275319582029731 20813050953412979373044597)
      ·
        refine ⟨1951223526882466816222931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20813050953412979373044597 1951223526882466816222931)
        ·
          refine ⟨2926835290323700224334397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951223526882466816222931 2926835290323700224334397)
          ·
            refine ⟨1097563233871387584125399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2926835290323700224334397 1097563233871387584125399)
            ·
              refine ⟨1646344850807081376188099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097563233871387584125399 1646344850807081376188099)
              ·
                refine ⟨2469517276210622064282149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646344850807081376188099 2469517276210622064282149)
                ·
                  refine ⟨463034489289491637052903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2469517276210622064282149 463034489289491637052903)
                  ·
                    rfl

theorem cell20_1014476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_1014476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014476 prefixEnd_1014476 := by exact prefixLift 1014476
  have htrace : WordTrace (prefixWord ++ tailWord_1014476) baseStart_1014476 baseEnd_1014476 := by
    simpa [prefixWord, tailWord_1014476, baseEnd_1014476] using wordTrace_append hprefix tailTrace_1014476
  have hstable : (prefixWord ++ tailWord_1014476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014476).length < 2 ^ (prefixWord ++ tailWord_1014476).sum := by decide
  have hdescent : baseEnd_1014476 < baseStart_1014476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014487 : List Nat := [1, 1, 3, 2, 1, 4, 1, 7]
def baseStart_1014487 : Nat := 118140960795 + 1014487 * 2 ^ 59
def prefixEnd_1014487 : Nat := 4983230072969 + 3 ^ 40 * 1014487 * 2
def baseEnd_1014487 : Nat := 154346503329741495895397

theorem tailTrace_1014487 : CollatzResearch.WordTrace tailWord_1014487 prefixEnd_1014487 154346503329741495895397 := by
  unfold tailWord_1014487
  simp only [CollatzResearch.WordTrace]
  refine ⟨37001380675694334430729715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24667587117129556287153143 37001380675694334430729715)
  ·
    refine ⟨55502071013541501646094573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37001380675694334430729715 55502071013541501646094573)
    ·
      refine ⟨20813276630078063117285465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55502071013541501646094573 20813276630078063117285465)
      ·
        refine ⟨15609957472558547337964099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20813276630078063117285465 15609957472558547337964099)
        ·
          refine ⟨23414936208837821006946149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15609957472558547337964099 23414936208837821006946149)
          ·
            refine ⟨4390300539157091438802403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23414936208837821006946149 4390300539157091438802403)
            ·
              refine ⟨6585450808735637158203605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390300539157091438802403 6585450808735637158203605)
              ·
                refine ⟨154346503329741495895397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6585450808735637158203605 154346503329741495895397)
                ·
                  rfl

theorem cell20_1014487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_1014487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014487 prefixEnd_1014487 := by exact prefixLift 1014487
  have htrace : WordTrace (prefixWord ++ tailWord_1014487) baseStart_1014487 baseEnd_1014487 := by
    simpa [prefixWord, tailWord_1014487, baseEnd_1014487] using wordTrace_append hprefix tailTrace_1014487
  have hstable : (prefixWord ++ tailWord_1014487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014487).length < 2 ^ (prefixWord ++ tailWord_1014487).sum := by decide
  have hdescent : baseEnd_1014487 < baseStart_1014487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014549 : List Nat := [1, 3, 2, 1, 2, 2, 1, 5, 3]
def baseStart_1014549 : Nat := 118140960795 + 1014549 * 2 ^ 59
def prefixEnd_1014549 : Nat := 4983230072969 + 3 ^ 40 * 1014549 * 2
def baseEnd_1014549 : Nat := 463067808478627827619271

theorem tailTrace_1014549 : CollatzResearch.WordTrace tailWord_1014549 prefixEnd_1014549 463067808478627827619271 := by
  unfold tailWord_1014549
  simp only [CollatzResearch.WordTrace]
  refine ⟨37003642001469719019486701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24669094667646479346324467 37003642001469719019486701)
  ·
    refine ⟨13876365750551144632307513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37003642001469719019486701 13876365750551144632307513)
    ·
      refine ⟨10407274312913358474230635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13876365750551144632307513 10407274312913358474230635)
      ·
        refine ⟨15610911469370037711345953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10407274312913358474230635 15610911469370037711345953)
        ·
          refine ⟨11708183602027528283509465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15610911469370037711345953 11708183602027528283509465)
          ·
            refine ⟨8781137701520646212632099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11708183602027528283509465 8781137701520646212632099)
            ·
              refine ⟨13171706552280969318948149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8781137701520646212632099 13171706552280969318948149)
              ·
                refine ⟨1234847489276340873651389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13171706552280969318948149 1234847489276340873651389)
                ·
                  refine ⟨463067808478627827619271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234847489276340873651389 463067808478627827619271)
                  ·
                    rfl

theorem cell20_1014549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_1014549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014549 prefixEnd_1014549 := by exact prefixLift 1014549
  have htrace : WordTrace (prefixWord ++ tailWord_1014549) baseStart_1014549 baseEnd_1014549 := by
    simpa [prefixWord, tailWord_1014549, baseEnd_1014549] using wordTrace_append hprefix tailTrace_1014549
  have hstable : (prefixWord ++ tailWord_1014549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014549).length < 2 ^ (prefixWord ++ tailWord_1014549).sum := by decide
  have hdescent : baseEnd_1014549 < baseStart_1014549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014556 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_1014556 : Nat := 118140960795 + 1014556 * 2 ^ 59
def prefixEnd_1014556 : Nat := 4983230072969 + 3 ^ 40 * 1014556 * 2
def baseEnd_1014556 : Nat := 463071003469366914385909

theorem tailTrace_1014556 : CollatzResearch.WordTrace tailWord_1014556 prefixEnd_1014556 463071003469366914385909 := by
  unfold tailWord_1014556
  simp only [CollatzResearch.WordTrace]
  refine ⟨18501948656222179607495761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24669264874962906143327681 18501948656222179607495761)
  ·
    refine ⟨13876461492166634705621821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18501948656222179607495761 13876461492166634705621821)
    ·
      refine ⟨5203673059562488014608183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13876461492166634705621821 5203673059562488014608183)
      ·
        refine ⟨7805509589343732021912275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5203673059562488014608183 7805509589343732021912275)
        ·
          refine ⟨11708264384015598032868413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7805509589343732021912275 11708264384015598032868413)
          ·
            refine ⟨4390599144005849262325655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11708264384015598032868413 4390599144005849262325655)
            ·
              refine ⟨6585898716008773893488483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390599144005849262325655 6585898716008773893488483)
              ·
                refine ⟨9878848074013160840232725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6585898716008773893488483 9878848074013160840232725)
                ·
                  refine ⟨463071003469366914385909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9878848074013160840232725 463071003469366914385909)
                  ·
                    rfl

theorem cell20_1014556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_1014556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014556 prefixEnd_1014556 := by exact prefixLift 1014556
  have htrace : WordTrace (prefixWord ++ tailWord_1014556) baseStart_1014556 baseEnd_1014556 := by
    simpa [prefixWord, tailWord_1014556, baseEnd_1014556] using wordTrace_append hprefix tailTrace_1014556
  have hstable : (prefixWord ++ tailWord_1014556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014556).length < 2 ^ (prefixWord ++ tailWord_1014556).sum := by decide
  have hdescent : baseEnd_1014556 < baseStart_1014556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014590 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_1014590 : Nat := 118140960795 + 1014590 * 2 ^ 59
def prefixEnd_1014590 : Nat := 4983230072969 + 3 ^ 40 * 1014590 * 2
def baseEnd_1014590 : Nat := 463086521995813907252437

theorem tailTrace_1014590 : CollatzResearch.WordTrace tailWord_1014590 prefixEnd_1014590 463086521995813907252437 := by
  unfold tailWord_1014590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4625642174290147877716153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24670091596214122014486149 4625642174290147877716153)
  ·
    refine ⟨3469231630717610908287115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4625642174290147877716153 3469231630717610908287115)
    ·
      refine ⟨5203847446076416362430673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3469231630717610908287115 5203847446076416362430673)
      ·
        refine ⟨3902885584557312271823005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5203847446076416362430673 3902885584557312271823005)
        ·
          refine ⟨1463582094208992101933627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3902885584557312271823005 1463582094208992101933627)
          ·
            refine ⟨2195373141313488152900441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463582094208992101933627 2195373141313488152900441)
            ·
              refine ⟨1646529855985116114675331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2195373141313488152900441 1646529855985116114675331)
              ·
                refine ⟨2469794783977674172012997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646529855985116114675331 2469794783977674172012997)
                ·
                  refine ⟨463086521995813907252437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2469794783977674172012997 463086521995813907252437)
                  ·
                    rfl

theorem cell20_1014590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_1014590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014590 prefixEnd_1014590 := by exact prefixLift 1014590
  have htrace : WordTrace (prefixWord ++ tailWord_1014590) baseStart_1014590 baseEnd_1014590 := by
    simpa [prefixWord, tailWord_1014590, baseEnd_1014590] using wordTrace_append hprefix tailTrace_1014590
  have hstable : (prefixWord ++ tailWord_1014590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014590).length < 2 ^ (prefixWord ++ tailWord_1014590).sum := by decide
  have hdescent : baseEnd_1014590 < baseStart_1014590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014618 : List Nat := [3, 1, 1, 2, 1, 4, 4, 4]
def baseStart_1014618 : Nat := 118140960795 + 1014618 * 2 ^ 59
def prefixEnd_1014618 : Nat := 4983230072969 + 3 ^ 40 * 1014618 * 2
def baseEnd_1014618 : Nat := 154366433986256751439663

theorem tailTrace_1014618 : CollatzResearch.WordTrace tailWord_1014618 prefixEnd_1014618 154366433986256751439663 := by
  unfold tailWord_1014618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9251539659554935950937127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24670772425479829202499005 9251539659554935950937127)
  ·
    refine ⟨13877309489332403926405691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9251539659554935950937127 13877309489332403926405691)
    ·
      refine ⟨20815964233998605889608537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13877309489332403926405691 20815964233998605889608537)
      ·
        refine ⟨15611973175498954417206403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20815964233998605889608537 15611973175498954417206403)
        ·
          refine ⟨23417959763248431625809605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15611973175498954417206403 23417959763248431625809605)
          ·
            refine ⟨4390867455609080929839301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23417959763248431625809605 4390867455609080929839301)
            ·
              refine ⟨823287647926702674344869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4390867455609080929839301 823287647926702674344869)
              ·
                refine ⟨154366433986256751439663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 823287647926702674344869 154366433986256751439663)
                ·
                  rfl

theorem cell20_1014618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_1014618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014618 prefixEnd_1014618 := by exact prefixLift 1014618
  have htrace : WordTrace (prefixWord ++ tailWord_1014618) baseStart_1014618 baseEnd_1014618 := by
    simpa [prefixWord, tailWord_1014618, baseEnd_1014618] using wordTrace_append hprefix tailTrace_1014618
  have hstable : (prefixWord ++ tailWord_1014618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014618).length < 2 ^ (prefixWord ++ tailWord_1014618).sum := by decide
  have hdescent : baseEnd_1014618 < baseStart_1014618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014628 : List Nat := [2, 3, 1, 1, 4, 1, 3, 3, 2]
def baseStart_1014628 : Nat := 118140960795 + 1014628 * 2 ^ 59
def prefixEnd_1014628 : Nat := 4983230072969 + 3 ^ 40 * 1014628 * 2
def baseEnd_1014628 : Nat := 463103866231254663985615

theorem tailTrace_1014628 : CollatzResearch.WordTrace tailWord_1014628 prefixEnd_1014628 463103866231254663985615 := by
  unfold tailWord_1014628
  simp only [CollatzResearch.WordTrace]
  refine ⟨18503261684091757755806269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24671015578789010341075025 18503261684091757755806269)
  ·
    refine ⟨6938723131534409158427351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18503261684091757755806269 6938723131534409158427351)
    ·
      refine ⟨10408084697301613737641027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6938723131534409158427351 10408084697301613737641027)
      ·
        refine ⟨15612127045952420606461541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10408084697301613737641027 15612127045952420606461541)
        ·
          refine ⟨2927273821116078863711539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15612127045952420606461541 2927273821116078863711539)
          ·
            refine ⟨4390910731674118295567309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927273821116078863711539 4390910731674118295567309)
            ·
              refine ⟨1646591524377794360837741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4390910731674118295567309 1646591524377794360837741)
              ·
                refine ⟨617471821641672885314153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1646591524377794360837741 617471821641672885314153)
                ·
                  refine ⟨463103866231254663985615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617471821641672885314153 463103866231254663985615)
                  ·
                    rfl

theorem cell20_1014628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_1014628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014628 prefixEnd_1014628 := by exact prefixLift 1014628
  have htrace : WordTrace (prefixWord ++ tailWord_1014628) baseStart_1014628 baseEnd_1014628 := by
    simpa [prefixWord, tailWord_1014628, baseEnd_1014628] using wordTrace_append hprefix tailTrace_1014628
  have hstable : (prefixWord ++ tailWord_1014628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014628).length < 2 ^ (prefixWord ++ tailWord_1014628).sum := by decide
  have hdescent : baseEnd_1014628 < baseStart_1014628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014645 : List Nat := [1, 3, 4, 1, 1, 3, 3, 2, 2]
def baseStart_1014645 : Nat := 118140960795 + 1014645 * 2 ^ 59
def prefixEnd_1014645 : Nat := 4983230072969 + 3 ^ 40 * 1014645 * 2
def baseEnd_1014645 : Nat := 463111625494478160418879

theorem tailTrace_1014645 : CollatzResearch.WordTrace tailWord_1014645 prefixEnd_1014645 463111625494478160418879 := by
  unfold tailWord_1014645
  simp only [CollatzResearch.WordTrace]
  refine ⟨37007143409121927414981389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24671428939414618276654259 37007143409121927414981389)
  ·
    refine ⟨13877678778420722780618021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37007143409121927414981389 13877678778420722780618021)
    ·
      refine ⟨2602064770953885521365879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13877678778420722780618021 2602064770953885521365879)
      ·
        refine ⟨3903097156430828282048819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2602064770953885521365879 3903097156430828282048819)
        ·
          refine ⟨5854645734646242423073229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3903097156430828282048819 5854645734646242423073229)
          ·
            refine ⟨2195492150492340908652461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5854645734646242423073229 2195492150492340908652461)
            ·
              refine ⟨823309556434627840744673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2195492150492340908652461 823309556434627840744673)
              ·
                refine ⟨617482167325970880558505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 823309556434627840744673 617482167325970880558505)
                ·
                  refine ⟨463111625494478160418879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617482167325970880558505 463111625494478160418879)
                  ·
                    rfl

theorem cell20_1014645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_1014645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014645 prefixEnd_1014645 := by exact prefixLift 1014645
  have htrace : WordTrace (prefixWord ++ tailWord_1014645) baseStart_1014645 baseEnd_1014645 := by
    simpa [prefixWord, tailWord_1014645, baseEnd_1014645] using wordTrace_append hprefix tailTrace_1014645
  have hstable : (prefixWord ++ tailWord_1014645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014645).length < 2 ^ (prefixWord ++ tailWord_1014645).sum := by decide
  have hdescent : baseEnd_1014645 < baseStart_1014645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014649 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 4]
def baseStart_1014649 : Nat := 118140960795 + 1014649 * 2 ^ 59
def prefixEnd_1014649 : Nat := 4983230072969 + 3 ^ 40 * 1014649 * 2
def baseEnd_1014649 : Nat := 463113451203471924285529

theorem tailTrace_1014649 : CollatzResearch.WordTrace tailWord_1014649 prefixEnd_1014649 463113451203471924285529 := by
  unfold tailWord_1014649
  simp only [CollatzResearch.WordTrace]
  refine ⟨37007289301107436098127001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24671526200738290732084667 37007289301107436098127001)
  ·
    refine ⟨27755466975830577073595251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37007289301107436098127001 27755466975830577073595251)
    ·
      refine ⟨41633200463745865610392877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27755466975830577073595251 41633200463745865610392877)
      ·
        refine ⟨15612450173904699603897329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41633200463745865610392877 15612450173904699603897329)
        ·
          refine ⟨11709337630428524702922997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15612450173904699603897329 11709337630428524702922997)
          ·
            refine ⟨1097750402852674190899031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11709337630428524702922997 1097750402852674190899031)
            ·
              refine ⟨1646625604279011286348547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097750402852674190899031 1646625604279011286348547)
              ·
                refine ⟨2469938406418516929522821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646625604279011286348547 2469938406418516929522821)
                ·
                  refine ⟨463113451203471924285529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2469938406418516929522821 463113451203471924285529)
                  ·
                    rfl

theorem cell20_1014649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_1014649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014649 prefixEnd_1014649 := by exact prefixLift 1014649
  have htrace : WordTrace (prefixWord ++ tailWord_1014649) baseStart_1014649 baseEnd_1014649 := by
    simpa [prefixWord, tailWord_1014649, baseEnd_1014649] using wordTrace_append hprefix tailTrace_1014649
  have hstable : (prefixWord ++ tailWord_1014649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014649).length < 2 ^ (prefixWord ++ tailWord_1014649).sum := by decide
  have hdescent : baseEnd_1014649 < baseStart_1014649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014677 : List Nat := [1, 3, 2, 1, 1, 4, 2, 6]
def baseStart_1014677 : Nat := 118140960795 + 1014677 * 2 ^ 59
def prefixEnd_1014677 : Nat := 4983230072969 + 3 ^ 40 * 1014677 * 2
def baseEnd_1014677 : Nat := 154375410388809423784027

theorem tailTrace_1014677 : CollatzResearch.WordTrace tailWord_1014677 prefixEnd_1014677 154375410388809423784027 := by
  unfold tailWord_1014677
  simp only [CollatzResearch.WordTrace]
  refine ⟨37008310545005996880146285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24672207030003997920097523 37008310545005996880146285)
  ·
    refine ⟨13878116454377248830054857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37008310545005996880146285 13878116454377248830054857)
    ·
      refine ⟨10408587340782936622541143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13878116454377248830054857 10408587340782936622541143)
      ·
        refine ⟨15612881011174404933811715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10408587340782936622541143 15612881011174404933811715)
        ·
          refine ⟨23419321516761607400717573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15612881011174404933811715 23419321516761607400717573)
          ·
            refine ⟨4391122784392801387634545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23419321516761607400717573 4391122784392801387634545)
            ·
              refine ⟨3293342088294601040725909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4391122784392801387634545 3293342088294601040725909)
              ·
                refine ⟨154375410388809423784027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3293342088294601040725909 154375410388809423784027)
                ·
                  rfl

theorem cell20_1014677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_1014677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014677 prefixEnd_1014677 := by exact prefixLift 1014677
  have htrace : WordTrace (prefixWord ++ tailWord_1014677) baseStart_1014677 baseEnd_1014677 := by
    simpa [prefixWord, tailWord_1014677, baseEnd_1014677] using wordTrace_append hprefix tailTrace_1014677
  have hstable : (prefixWord ++ tailWord_1014677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014677).length < 2 ^ (prefixWord ++ tailWord_1014677).sum := by decide
  have hdescent : baseEnd_1014677 < baseStart_1014677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014732 : List Nat := [2, 2, 1, 4, 1, 1, 5, 4]
def baseStart_1014732 : Nat := 118140960795 + 1014732 * 2 ^ 59
def prefixEnd_1014732 : Nat := 4983230072969 + 3 ^ 40 * 1014732 * 2
def baseEnd_1014732 : Nat := 154383778221697508172841

theorem tailTrace_1014732 : CollatzResearch.WordTrace tailWord_1014732 prefixEnd_1014732 154383778221697508172841 := by
  unfold tailWord_1014732
  simp only [CollatzResearch.WordTrace]
  refine ⟨18505158279903370636699225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24673544373204494182265633 18505158279903370636699225)
  ·
    refine ⟨13878868709927527977524419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18505158279903370636699225 13878868709927527977524419)
    ·
      refine ⟨20818303064891291966286629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13878868709927527977524419 20818303064891291966286629)
      ·
        refine ⟨3903431824667117243678743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20818303064891291966286629 3903431824667117243678743)
        ·
          refine ⟨5855147737000675865518115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3903431824667117243678743 5855147737000675865518115)
          ·
            refine ⟨8782721605501013798277173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5855147737000675865518115 8782721605501013798277173)
            ·
              refine ⟨823380150515720043588485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8782721605501013798277173 823380150515720043588485)
              ·
                refine ⟨154383778221697508172841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 823380150515720043588485 154383778221697508172841)
                ·
                  rfl

theorem cell20_1014732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_1014732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014732 prefixEnd_1014732 := by exact prefixLift 1014732
  have htrace : WordTrace (prefixWord ++ tailWord_1014732) baseStart_1014732 baseEnd_1014732 := by
    simpa [prefixWord, tailWord_1014732, baseEnd_1014732] using wordTrace_append hprefix tailTrace_1014732
  have hstable : (prefixWord ++ tailWord_1014732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014732).length < 2 ^ (prefixWord ++ tailWord_1014732).sum := by decide
  have hdescent : baseEnd_1014732 < baseStart_1014732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014791 : List Nat := [1, 1, 4, 3, 1, 1, 3, 6]
def baseStart_1014791 : Nat := 118140960795 + 1014791 * 2 ^ 59
def prefixEnd_1014791 : Nat := 4983230072969 + 3 ^ 40 * 1014791 * 2
def baseEnd_1014791 : Nat := 154392754624250180517205

theorem tailTrace_1014791 : CollatzResearch.WordTrace tailWord_1014791 prefixEnd_1014791 154392754624250180517205 := by
  unfold tailWord_1014791
  simp only [CollatzResearch.WordTrace]
  refine ⟨37012468466592994349796227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24674978977728662899864151 37012468466592994349796227)
  ·
    refine ⟨55518702699889491524694341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37012468466592994349796227 55518702699889491524694341)
    ·
      refine ⟨10409756756229279660880189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55518702699889491524694341 10409756756229279660880189)
      ·
        refine ⟨3903658783585979872830071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10409756756229279660880189 3903658783585979872830071)
        ·
          refine ⟨5855488175378969809245107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3903658783585979872830071 5855488175378969809245107)
          ·
            refine ⟨8783232263068454713867661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5855488175378969809245107 8783232263068454713867661)
            ·
              refine ⟨3293712098650670517700373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8783232263068454713867661 3293712098650670517700373)
              ·
                refine ⟨154392754624250180517205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3293712098650670517700373 154392754624250180517205)
                ·
                  rfl

theorem cell20_1014791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_1014791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014791 prefixEnd_1014791 := by exact prefixLift 1014791
  have htrace : WordTrace (prefixWord ++ tailWord_1014791) baseStart_1014791 baseEnd_1014791 := by
    simpa [prefixWord, tailWord_1014791, baseEnd_1014791] using wordTrace_append hprefix tailTrace_1014791
  have hstable : (prefixWord ++ tailWord_1014791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014791).length < 2 ^ (prefixWord ++ tailWord_1014791).sum := by decide
  have hdescent : baseEnd_1014791 < baseStart_1014791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014846 : List Nat := [4, 2, 1, 3, 1, 1, 2, 6]
def baseStart_1014846 : Nat := 118140960795 + 1014846 * 2 ^ 59
def prefixEnd_1014846 : Nat := 4983230072969 + 3 ^ 40 * 1014846 * 2
def baseEnd_1014846 : Nat := 154401122457138264906019

theorem tailTrace_1014846 : CollatzResearch.WordTrace tailWord_1014846 prefixEnd_1014846 154401122457138264906019 := by
  unfold tailWord_1014846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4626809310174217342881049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24676316320929159162032261 4626809310174217342881049)
  ·
    refine ⟨3470106982630663007160787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4626809310174217342881049 3470106982630663007160787)
    ·
      refine ⟨5205160473945994510741181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3470106982630663007160787 5205160473945994510741181)
      ·
        refine ⟨1951935177729747941527943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5205160473945994510741181 1951935177729747941527943)
        ·
          refine ⟨2927902766594621912291915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951935177729747941527943 2927902766594621912291915)
          ·
            refine ⟨4391854149891932868437873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927902766594621912291915 4391854149891932868437873)
            ·
              refine ⟨3293890612418949651328405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4391854149891932868437873 3293890612418949651328405)
              ·
                refine ⟨154401122457138264906019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3293890612418949651328405 154401122457138264906019)
                ·
                  rfl

theorem cell20_1014846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_1014846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014846 prefixEnd_1014846 := by exact prefixLift 1014846
  have htrace : WordTrace (prefixWord ++ tailWord_1014846) baseStart_1014846 baseEnd_1014846 := by
    simpa [prefixWord, tailWord_1014846, baseEnd_1014846] using wordTrace_append hprefix tailTrace_1014846
  have hstable : (prefixWord ++ tailWord_1014846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014846).length < 2 ^ (prefixWord ++ tailWord_1014846).sum := by decide
  have hdescent : baseEnd_1014846 < baseStart_1014846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014898 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1014898 : Nat := 118140960795 + 1014898 * 2 ^ 59
def prefixEnd_1014898 : Nat := 4983230072969 + 3 ^ 40 * 1014898 * 2
def baseEnd_1014898 : Nat := 463227101588333724984511

theorem tailTrace_1014898 : CollatzResearch.WordTrace tailWord_1014898 prefixEnd_1014898 463227101588333724984511 := by
  unfold tailWord_1014898
  simp only [CollatzResearch.WordTrace]
  refine ⟨9254092769301337905985337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24677580718136901082627565 9254092769301337905985337)
  ·
    refine ⟨6940569576976003429489003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9254092769301337905985337 6940569576976003429489003)
    ·
      refine ⟨10410854365464005144233505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6940569576976003429489003 10410854365464005144233505)
      ·
        refine ⟨7808140774098003858175129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10410854365464005144233505 7808140774098003858175129)
        ·
          refine ⟨5856105580573502893631347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7808140774098003858175129 5856105580573502893631347)
          ·
            refine ⟨8784158370860254340447021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856105580573502893631347 8784158370860254340447021)
            ·
              refine ⟨3294059389072595377667633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8784158370860254340447021 3294059389072595377667633)
              ·
                refine ⟨2470544541804446533250725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3294059389072595377667633 2470544541804446533250725)
                ·
                  refine ⟨463227101588333724984511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2470544541804446533250725 463227101588333724984511)
                  ·
                    rfl

theorem cell20_1014898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1014898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014898 prefixEnd_1014898 := by exact prefixLift 1014898
  have htrace : WordTrace (prefixWord ++ tailWord_1014898) baseStart_1014898 baseEnd_1014898 := by
    simpa [prefixWord, tailWord_1014898, baseEnd_1014898] using wordTrace_append hprefix tailTrace_1014898
  have hstable : (prefixWord ++ tailWord_1014898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014898).length < 2 ^ (prefixWord ++ tailWord_1014898).sum := by decide
  have hdescent : baseEnd_1014898 < baseStart_1014898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014915 : List Nat := [1, 1, 1, 3, 3, 2, 4, 3, 2]
def baseStart_1014915 : Nat := 118140960795 + 1014915 * 2 ^ 59
def prefixEnd_1014915 : Nat := 4983230072969 + 3 ^ 40 * 1014915 * 2
def baseEnd_1014915 : Nat := 463234860851557221417775

theorem tailTrace_1014915 : CollatzResearch.WordTrace tailWord_1014915 prefixEnd_1014915 463234860851557221417775 := by
  unfold tailWord_1014915
  simp only [CollatzResearch.WordTrace]
  refine ⟨37016991118143763527310199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24677994078762509018206799 37016991118143763527310199)
  ·
    refine ⟨55525486677215645290965299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37016991118143763527310199 55525486677215645290965299)
    ·
      refine ⟨83288230015823467936447949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55525486677215645290965299 83288230015823467936447949)
      ·
        refine ⟨31233086255933800476167981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83288230015823467936447949 31233086255933800476167981)
        ·
          refine ⟨11712407345975175178562993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31233086255933800476167981 11712407345975175178562993)
          ·
            refine ⟨8784305509481381383922245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11712407345975175178562993 8784305509481381383922245)
            ·
              refine ⟨1647057283027759009485421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8784305509481381383922245 1647057283027759009485421)
              ·
                refine ⟨617646481135409628557033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1647057283027759009485421 617646481135409628557033)
                ·
                  refine ⟨463234860851557221417775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617646481135409628557033 463234860851557221417775)
                  ·
                    rfl

theorem cell20_1014915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 2].length) (baseStart_1014915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014915 prefixEnd_1014915 := by exact prefixLift 1014915
  have htrace : WordTrace (prefixWord ++ tailWord_1014915) baseStart_1014915 baseEnd_1014915 := by
    simpa [prefixWord, tailWord_1014915, baseEnd_1014915] using wordTrace_append hprefix tailTrace_1014915
  have hstable : (prefixWord ++ tailWord_1014915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014915).length < 2 ^ (prefixWord ++ tailWord_1014915).sum := by decide
  have hdescent : baseEnd_1014915 < baseStart_1014915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014919 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 8]
def baseStart_1014919 : Nat := 118140960795 + 1014919 * 2 ^ 59
def prefixEnd_1014919 : Nat := 4983230072969 + 3 ^ 40 * 1014919 * 2
def baseEnd_1014919 : Nat := 463236686560550985284425

theorem tailTrace_1014919 : CollatzResearch.WordTrace tailWord_1014919 prefixEnd_1014919 463236686560550985284425 := by
  unfold tailWord_1014919
  simp only [CollatzResearch.WordTrace]
  refine ⟨37017137010129272210455811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24678091340086181473637207 37017137010129272210455811)
  ·
    refine ⟨55525705515193908315683717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37017137010129272210455811 55525705515193908315683717)
    ·
      refine ⟨10411069784098857809190697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55525705515193908315683717 10411069784098857809190697)
      ·
        refine ⟨7808302338074143356893023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10411069784098857809190697 7808302338074143356893023)
        ·
          refine ⟨11712453507111215035339535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7808302338074143356893023 11712453507111215035339535)
          ·
            refine ⟨17568680260666822553009303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11712453507111215035339535 17568680260666822553009303)
            ·
              refine ⟨26353020391000233829513955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17568680260666822553009303 26353020391000233829513955)
              ·
                refine ⟨39529530586500350744270933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26353020391000233829513955 39529530586500350744270933)
                ·
                  refine ⟨463236686560550985284425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39529530586500350744270933 463236686560550985284425)
                  ·
                    rfl

theorem cell20_1014919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_1014919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014919 prefixEnd_1014919 := by exact prefixLift 1014919
  have htrace : WordTrace (prefixWord ++ tailWord_1014919) baseStart_1014919 baseEnd_1014919 := by
    simpa [prefixWord, tailWord_1014919, baseEnd_1014919] using wordTrace_append hprefix tailTrace_1014919
  have hstable : (prefixWord ++ tailWord_1014919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014919).length < 2 ^ (prefixWord ++ tailWord_1014919).sum := by decide
  have hdescent : baseEnd_1014919 < baseStart_1014919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014936 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_1014936 : Nat := 118140960795 + 1014936 * 2 ^ 59
def prefixEnd_1014936 : Nat := 4983230072969 + 3 ^ 40 * 1014936 * 2
def baseEnd_1014936 : Nat := 463244445823774481717689

theorem tailTrace_1014936 : CollatzResearch.WordTrace tailWord_1014936 prefixEnd_1014936 463244445823774481717689 := by
  unfold tailWord_1014936
  simp only [CollatzResearch.WordTrace]
  refine ⟨18508878525533842056912331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24678504700711789409216441 18508878525533842056912331)
  ·
    refine ⟨27763317788300763085368497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18508878525533842056912331 27763317788300763085368497)
    ·
      refine ⟨20822488341225572314026373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27763317788300763085368497 20822488341225572314026373)
      ·
        refine ⟨3904216563979794808879945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20822488341225572314026373 3904216563979794808879945)
        ·
          refine ⟨2928162422984846106659959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3904216563979794808879945 2928162422984846106659959)
          ·
            refine ⟨4392243634477269159989939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2928162422984846106659959 4392243634477269159989939)
            ·
              refine ⟨6588365451715903739984909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392243634477269159989939 6588365451715903739984909)
              ·
                refine ⟨2470637044393463902494341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6588365451715903739984909 2470637044393463902494341)
                ·
                  refine ⟨463244445823774481717689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2470637044393463902494341 463244445823774481717689)
                  ·
                    rfl

theorem cell20_1014936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_1014936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014936 prefixEnd_1014936 := by exact prefixLift 1014936
  have htrace : WordTrace (prefixWord ++ tailWord_1014936) baseStart_1014936 baseEnd_1014936 := by
    simpa [prefixWord, tailWord_1014936, baseEnd_1014936] using wordTrace_append hprefix tailTrace_1014936
  have hstable : (prefixWord ++ tailWord_1014936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014936).length < 2 ^ (prefixWord ++ tailWord_1014936).sum := by decide
  have hdescent : baseEnd_1014936 < baseStart_1014936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015042 : List Nat := [3, 4, 1, 1, 3, 2, 2, 2, 2]
def baseStart_1015042 : Nat := 118140960795 + 1015042 * 2 ^ 59
def prefixEnd_1015042 : Nat := 4983230072969 + 3 ^ 40 * 1015042 * 2
def baseEnd_1015042 : Nat := 463292827112109224183923

theorem tailTrace_1015042 : CollatzResearch.WordTrace tailWord_1015042 prefixEnd_1015042 463292827112109224183923 := by
  unfold tailWord_1015042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9255405797170916054295845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24681082125789109478122253 9255405797170916054295845)
  ·
    refine ⟨1735388586969546760180471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9255405797170916054295845 1735388586969546760180471)
    ·
      refine ⟨2603082880454320140270707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1735388586969546760180471 2603082880454320140270707)
      ·
        refine ⟨3904624320681480210406061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603082880454320140270707 3904624320681480210406061)
        ·
          refine ⟨1464234120255555078902273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3904624320681480210406061 1464234120255555078902273)
          ·
            refine ⟨1098175590191666309176705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1464234120255555078902273 1098175590191666309176705)
            ·
              refine ⟨823631692643749731882529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098175590191666309176705 823631692643749731882529)
              ·
                refine ⟨617723769482812298911897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 823631692643749731882529 617723769482812298911897)
                ·
                  refine ⟨463292827112109224183923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617723769482812298911897 463292827112109224183923)
                  ·
                    rfl

theorem cell20_1015042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_1015042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015042 prefixEnd_1015042 := by exact prefixLift 1015042
  have htrace : WordTrace (prefixWord ++ tailWord_1015042) baseStart_1015042 baseEnd_1015042 := by
    simpa [prefixWord, tailWord_1015042, baseEnd_1015042] using wordTrace_append hprefix tailTrace_1015042
  have hstable : (prefixWord ++ tailWord_1015042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015042).length < 2 ^ (prefixWord ++ tailWord_1015042).sum := by decide
  have hdescent : baseEnd_1015042 < baseStart_1015042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015043 : List Nat := [1, 1, 1, 3, 2, 5, 2, 2, 3]
def baseStart_1015043 : Nat := 118140960795 + 1015043 * 2 ^ 59
def prefixEnd_1015043 : Nat := 4983230072969 + 3 ^ 40 * 1015043 * 2
def baseEnd_1015043 : Nat := 463293283539357665150585

theorem tailTrace_1015043 : CollatzResearch.WordTrace tailWord_1015043 prefixEnd_1015043 463293283539357665150585 := by
  unfold tailWord_1015043
  simp only [CollatzResearch.WordTrace]
  refine ⟨37021659661680041387969783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24681106441120027591979855 37021659661680041387969783)
  ·
    refine ⟨55532489492520062081954675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37021659661680041387969783 55532489492520062081954675)
    ·
      refine ⟨83298734238780093122932013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55532489492520062081954675 83298734238780093122932013)
      ·
        refine ⟨31237025339542534921099505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83298734238780093122932013 31237025339542534921099505)
        ·
          refine ⟨23427769004656901190824629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31237025339542534921099505 23427769004656901190824629)
          ·
            refine ⟨2196353344186584486639809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23427769004656901190824629 2196353344186584486639809)
            ·
              refine ⟨1647265008139938364979857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196353344186584486639809 1647265008139938364979857)
              ·
                refine ⟨1235448756104953773734893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647265008139938364979857 1235448756104953773734893)
                ·
                  refine ⟨463293283539357665150585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235448756104953773734893 463293283539357665150585)
                  ·
                    rfl

theorem cell20_1015043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 3].length) (baseStart_1015043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015043 prefixEnd_1015043 := by exact prefixLift 1015043
  have htrace : WordTrace (prefixWord ++ tailWord_1015043) baseStart_1015043 baseEnd_1015043 := by
    simpa [prefixWord, tailWord_1015043, baseEnd_1015043] using wordTrace_append hprefix tailTrace_1015043
  have hstable : (prefixWord ++ tailWord_1015043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015043).length < 2 ^ (prefixWord ++ tailWord_1015043).sum := by decide
  have hdescent : baseEnd_1015043 < baseStart_1015043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015070 : List Nat := [4, 3, 2, 1, 2, 1, 3, 4]
def baseStart_1015070 : Nat := 118140960795 + 1015070 * 2 ^ 59
def prefixEnd_1015070 : Nat := 4983230072969 + 3 ^ 40 * 1015070 * 2
def baseEnd_1015070 : Nat := 154435202358355190416825

theorem tailTrace_1015070 : CollatzResearch.WordTrace tailWord_1015070 prefixEnd_1015070 154435202358355190416825 := by
  unfold tailWord_1015070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627830554072778124900333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24681762955054816666135109 4627830554072778124900333)
  ·
    refine ⟨1735436457777291796837625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4627830554072778124900333 1735436457777291796837625)
    ·
      refine ⟨1301577343332968847628219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1735436457777291796837625 1301577343332968847628219)
      ·
        refine ⟨1952366014999453271442329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301577343332968847628219 1952366014999453271442329)
        ·
          refine ⟨1464274511249589953581747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1952366014999453271442329 1464274511249589953581747)
          ·
            refine ⟨2196411766874384930372621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464274511249589953581747 2196411766874384930372621)
            ·
              refine ⟨823654412577894348889733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2196411766874384930372621 823654412577894348889733)
              ·
                refine ⟨154435202358355190416825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 823654412577894348889733 154435202358355190416825)
                ·
                  rfl

theorem cell20_1015070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_1015070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015070 prefixEnd_1015070 := by exact prefixLift 1015070
  have htrace : WordTrace (prefixWord ++ tailWord_1015070) baseStart_1015070 baseEnd_1015070 := by
    simpa [prefixWord, tailWord_1015070, baseEnd_1015070] using wordTrace_append hprefix tailTrace_1015070
  have hstable : (prefixWord ++ tailWord_1015070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015070).length < 2 ^ (prefixWord ++ tailWord_1015070).sum := by decide
  have hdescent : baseEnd_1015070 < baseStart_1015070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015094 : List Nat := [5, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_1015094 : Nat := 118140960795 + 1015094 * 2 ^ 59
def prefixEnd_1015094 : Nat := 4983230072969 + 3 ^ 40 * 1015094 * 2
def baseEnd_1015094 : Nat := 463316561329028154450377

theorem tailTrace_1015094 : CollatzResearch.WordTrace tailWord_1015094 prefixEnd_1015094 463316561329028154450377 := by
  unfold tailWord_1015094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2313969986530954818629771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24682346522996851398717557 2313969986530954818629771)
  ·
    refine ⟨3470954979796432227944657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2313969986530954818629771 3470954979796432227944657)
    ·
      refine ⟨2603216234847324170958493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3470954979796432227944657 2603216234847324170958493)
      ·
        refine ⟨976206088067746564109435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2603216234847324170958493 976206088067746564109435)
        ·
          refine ⟨1464309132101619846164153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976206088067746564109435 1464309132101619846164153)
          ·
            refine ⟨1098231849076214884623115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1464309132101619846164153 1098231849076214884623115)
            ·
              refine ⟨1647347773614322326934673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098231849076214884623115 1647347773614322326934673)
              ·
                refine ⟨1235510830210741745201005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647347773614322326934673 1235510830210741745201005)
                ·
                  refine ⟨463316561329028154450377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235510830210741745201005 463316561329028154450377)
                  ·
                    rfl

theorem cell20_1015094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_1015094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015094 prefixEnd_1015094 := by exact prefixLift 1015094
  have htrace : WordTrace (prefixWord ++ tailWord_1015094) baseStart_1015094 baseEnd_1015094 := by
    simpa [prefixWord, tailWord_1015094, baseEnd_1015094] using wordTrace_append hprefix tailTrace_1015094
  have hstable : (prefixWord ++ tailWord_1015094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015094).length < 2 ^ (prefixWord ++ tailWord_1015094).sum := by decide
  have hdescent : baseEnd_1015094 < baseStart_1015094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015105 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 4]
def baseStart_1015105 : Nat := 118140960795 + 1015105 * 2 ^ 59
def prefixEnd_1015105 : Nat := 4983230072969 + 3 ^ 40 * 1015105 * 2
def baseEnd_1015105 : Nat := 463321582028761005083665

theorem tailTrace_1015105 : CollatzResearch.WordTrace tailWord_1015105 prefixEnd_1015105 463321582028761005083665 := by
  unfold tailWord_1015105
  simp only [CollatzResearch.WordTrace]
  refine ⟨37023920987455425976726769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24682613991636950651151179 37023920987455425976726769)
  ·
    refine ⟨27767940740591569482545077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37023920987455425976726769 27767940740591569482545077)
    ·
      refine ⟨2603244444430459638988601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27767940740591569482545077 2603244444430459638988601)
      ·
        refine ⟨1952433333322844729241451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2603244444430459638988601 1952433333322844729241451)
        ·
          refine ⟨2928649999984267093862177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952433333322844729241451 2928649999984267093862177)
          ·
            refine ⟨2196487499988200320396633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2928649999984267093862177 2196487499988200320396633)
            ·
              refine ⟨1647365624991150240297475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196487499988200320396633 1647365624991150240297475)
              ·
                refine ⟨2471048437486725360446213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647365624991150240297475 2471048437486725360446213)
                ·
                  refine ⟨463321582028761005083665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2471048437486725360446213 463321582028761005083665)
                  ·
                    rfl

theorem cell20_1015105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_1015105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015105 prefixEnd_1015105 := by exact prefixLift 1015105
  have htrace : WordTrace (prefixWord ++ tailWord_1015105) baseStart_1015105 baseEnd_1015105 := by
    simpa [prefixWord, tailWord_1015105, baseEnd_1015105] using wordTrace_append hprefix tailTrace_1015105
  have hstable : (prefixWord ++ tailWord_1015105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015105).length < 2 ^ (prefixWord ++ tailWord_1015105).sum := by decide
  have hdescent : baseEnd_1015105 < baseStart_1015105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015140 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1015140 : Nat := 118140960795 + 1015140 * 2 ^ 59
def prefixEnd_1015140 : Nat := 4983230072969 + 3 ^ 40 * 1015140 * 2
def baseEnd_1015140 : Nat := 463337556982456438916855

theorem tailTrace_1015140 : CollatzResearch.WordTrace tailWord_1015140 prefixEnd_1015140 463337556982456438916855 := by
  unfold tailWord_1015140
  simp only [CollatzResearch.WordTrace]
  refine ⟨18512598771164313477125437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24683465028219084636167249 18512598771164313477125437)
  ·
    refine ⟨6942224539186617553922039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18512598771164313477125437 6942224539186617553922039)
    ·
      refine ⟨10413336808779926330883059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6942224539186617553922039 10413336808779926330883059)
      ·
        refine ⟨15620005213169889496324589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10413336808779926330883059 15620005213169889496324589)
        ·
          refine ⟨5857501954938708561121721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15620005213169889496324589 5857501954938708561121721)
          ·
            refine ⟨4393126466204031420841291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5857501954938708561121721 4393126466204031420841291)
            ·
              refine ⟨6589689699306047131261937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4393126466204031420841291 6589689699306047131261937)
              ·
                refine ⟨4942267274479535348446453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6589689699306047131261937 4942267274479535348446453)
                ·
                  refine ⟨463337556982456438916855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4942267274479535348446453 463337556982456438916855)
                  ·
                    rfl

theorem cell20_1015140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1015140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015140 prefixEnd_1015140 := by exact prefixLift 1015140
  have htrace : WordTrace (prefixWord ++ tailWord_1015140) baseStart_1015140 baseEnd_1015140 := by
    simpa [prefixWord, tailWord_1015140, baseEnd_1015140] using wordTrace_append hprefix tailTrace_1015140
  have hstable : (prefixWord ++ tailWord_1015140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015140).length < 2 ^ (prefixWord ++ tailWord_1015140).sum := by decide
  have hdescent : baseEnd_1015140 < baseStart_1015140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015170 : List Nat := [3, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1015170 : Nat := 118140960795 + 1015170 * 2 ^ 59
def prefixEnd_1015170 : Nat := 4983230072969 + 3 ^ 40 * 1015170 * 2
def baseEnd_1015170 : Nat := 463351249799909667916733

theorem tailTrace_1015170 : CollatzResearch.WordTrace tailWord_1015170 prefixEnd_1015170 463351249799909667916733 := by
  unfold tailWord_1015170
  simp only [CollatzResearch.WordTrace]
  refine ⟨9256572933054985519460741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24684194488146628051895309 9256572933054985519460741)
  ·
    refine ⟨1735607424947809784898889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9256572933054985519460741 1735607424947809784898889)
    ·
      refine ⟨1301705568710857338674167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1735607424947809784898889 1301705568710857338674167)
      ·
        refine ⟨1952558353066286008011251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301705568710857338674167 1952558353066286008011251)
        ·
          refine ⟨2928837529599429012016877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952558353066286008011251 2928837529599429012016877)
          ·
            refine ⟨1098314073599785879506329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2928837529599429012016877 1098314073599785879506329)
            ·
              refine ⟨823735555199839409629747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098314073599785879506329 823735555199839409629747)
              ·
                refine ⟨1235603332799759114444621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823735555199839409629747 1235603332799759114444621)
                ·
                  refine ⟨463351249799909667916733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235603332799759114444621 463351249799909667916733)
                  ·
                    rfl

theorem cell20_1015170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1015170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015170 prefixEnd_1015170 := by exact prefixLift 1015170
  have htrace : WordTrace (prefixWord ++ tailWord_1015170) baseStart_1015170 baseEnd_1015170 := by
    simpa [prefixWord, tailWord_1015170, baseEnd_1015170] using wordTrace_append hprefix tailTrace_1015170
  have hstable : (prefixWord ++ tailWord_1015170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015170).length < 2 ^ (prefixWord ++ tailWord_1015170).sum := by decide
  have hdescent : baseEnd_1015170 < baseStart_1015170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015171 : List Nat := [1, 1, 1, 3, 5, 2, 2, 5]
def baseStart_1015171 : Nat := 118140960795 + 1015171 * 2 ^ 59
def prefixEnd_1015171 : Nat := 4983230072969 + 3 ^ 40 * 1015171 * 2
def baseEnd_1015171 : Nat := 154450568742386036294465

theorem tailTrace_1015171 : CollatzResearch.WordTrace tailWord_1015171 prefixEnd_1015171 154450568742386036294465 := by
  unfold tailWord_1015171
  simp only [CollatzResearch.WordTrace]
  refine ⟨37026328205216319248629367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24684218803477546165752911 37026328205216319248629367)
  ·
    refine ⟨55539492307824478872944051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37026328205216319248629367 55539492307824478872944051)
    ·
      refine ⟨83309238461736718309416077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55539492307824478872944051 83309238461736718309416077)
      ·
        refine ⟨31240964423151269366031029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83309238461736718309416077 31240964423151269366031029)
        ·
          refine ⟨2928840414670431503065409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31240964423151269366031029 2928840414670431503065409)
          ·
            refine ⟨2196630311002823627299057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2928840414670431503065409 2196630311002823627299057)
            ·
              refine ⟨1647472733252117720474293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196630311002823627299057 1647472733252117720474293)
              ·
                refine ⟨154450568742386036294465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1647472733252117720474293 154450568742386036294465)
                ·
                  rfl

theorem cell20_1015171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_1015171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015171 prefixEnd_1015171 := by exact prefixLift 1015171
  have htrace : WordTrace (prefixWord ++ tailWord_1015171) baseStart_1015171 baseEnd_1015171 := by
    simpa [prefixWord, tailWord_1015171, baseEnd_1015171] using wordTrace_append hprefix tailTrace_1015171
  have hstable : (prefixWord ++ tailWord_1015171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015171).length < 2 ^ (prefixWord ++ tailWord_1015171).sum := by decide
  have hdescent : baseEnd_1015171 < baseStart_1015171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015223 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 4]
def baseStart_1015223 : Nat := 118140960795 + 1015223 * 2 ^ 59
def prefixEnd_1015223 : Nat := 4983230072969 + 3 ^ 40 * 1015223 * 2
def baseEnd_1015223 : Nat := 463375440444077039149849

theorem tailTrace_1015223 : CollatzResearch.WordTrace tailWord_1015223 prefixEnd_1015223 463375440444077039149849 := by
  unfold tailWord_1015223
  simp only [CollatzResearch.WordTrace]
  refine ⟨37028224801027932129522323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24685483200685288086348215 37028224801027932129522323)
  ·
    refine ⟨55542337201541898194283485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37028224801027932129522323 55542337201541898194283485)
    ·
      refine ⟨20828376450578211822856307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55542337201541898194283485 20828376450578211822856307)
      ·
        refine ⟨31242564675867317734284461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20828376450578211822856307 31242564675867317734284461)
        ·
          refine ⟨11715961753450244150356673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31242564675867317734284461 11715961753450244150356673)
          ·
            refine ⟨8786971315087683112767505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11715961753450244150356673 8786971315087683112767505)
            ·
              refine ⟨6590228486315762334575629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8786971315087683112767505 6590228486315762334575629)
              ·
                refine ⟨2471335682368410875465861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6590228486315762334575629 2471335682368410875465861)
                ·
                  refine ⟨463375440444077039149849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2471335682368410875465861 463375440444077039149849)
                  ·
                    rfl

theorem cell20_1015223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_1015223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015223 prefixEnd_1015223 := by exact prefixLift 1015223
  have htrace : WordTrace (prefixWord ++ tailWord_1015223) baseStart_1015223 baseEnd_1015223 := by
    simpa [prefixWord, tailWord_1015223, baseEnd_1015223] using wordTrace_append hprefix tailTrace_1015223
  have hstable : (prefixWord ++ tailWord_1015223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015223).length < 2 ^ (prefixWord ++ tailWord_1015223).sum := by decide
  have hdescent : baseEnd_1015223 < baseStart_1015223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015257 : List Nat := [1, 2, 1, 2, 4, 3, 2, 3, 2]
def baseStart_1015257 : Nat := 118140960795 + 1015257 * 2 ^ 59
def prefixEnd_1015257 : Nat := 4983230072969 + 3 ^ 40 * 1015257 * 2
def baseEnd_1015257 : Nat := 463390958970524032016377

theorem tailTrace_1015257 : CollatzResearch.WordTrace tailWord_1015257 prefixEnd_1015257 463390958970524032016377 := by
  unfold tailWord_1015257
  simp only [CollatzResearch.WordTrace]
  refine ⟨37029464882904755936260025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24686309921936503957506683 37029464882904755936260025)
  ·
    refine ⟨27772098662178566952195019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37029464882904755936260025 27772098662178566952195019)
    ·
      refine ⟨41658147993267850428292529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27772098662178566952195019 41658147993267850428292529)
      ·
        refine ⟨31243610994950887821219397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41658147993267850428292529 31243610994950887821219397)
        ·
          refine ⟨5858177061553291466478637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31243610994950887821219397 5858177061553291466478637)
          ·
            refine ⟨2196816398082484299929489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5858177061553291466478637 2196816398082484299929489)
            ·
              refine ⟨1647612298561863224947117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196816398082484299929489 1647612298561863224947117)
              ·
                refine ⟨617854611960698709355169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1647612298561863224947117 617854611960698709355169)
                ·
                  refine ⟨463390958970524032016377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617854611960698709355169 463390958970524032016377)
                  ·
                    rfl

theorem cell20_1015257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 2].length) (baseStart_1015257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015257 prefixEnd_1015257 := by exact prefixLift 1015257
  have htrace : WordTrace (prefixWord ++ tailWord_1015257) baseStart_1015257 baseEnd_1015257 := by
    simpa [prefixWord, tailWord_1015257, baseEnd_1015257] using wordTrace_append hprefix tailTrace_1015257
  have hstable : (prefixWord ++ tailWord_1015257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015257).length < 2 ^ (prefixWord ++ tailWord_1015257).sum := by decide
  have hdescent : baseEnd_1015257 < baseStart_1015257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015271 : List Nat := [1, 1, 5, 2, 1, 2, 3, 2, 3]
def baseStart_1015271 : Nat := 118140960795 + 1015271 * 2 ^ 59
def prefixEnd_1015271 : Nat := 4983230072969 + 3 ^ 40 * 1015271 * 2
def baseEnd_1015271 : Nat := 463397348952002205549653

theorem tailTrace_1015271 : CollatzResearch.WordTrace tailWord_1015271 prefixEnd_1015271 463397348952002205549653 := by
  unfold tailWord_1015271
  simp only [CollatzResearch.WordTrace]
  refine ⟨37029975504854036327269667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24686650336569357551513111 37029975504854036327269667)
  ·
    refine ⟨55544963257281054490904501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37029975504854036327269667 55544963257281054490904501)
    ·
      refine ⟨5207340305370098858522297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55544963257281054490904501 5207340305370098858522297)
      ·
        refine ⟨3905505229027574143891723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5207340305370098858522297 3905505229027574143891723)
        ·
          refine ⟨5858257843541361215837585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3905505229027574143891723 5858257843541361215837585)
          ·
            refine ⟨4393693382656020911878189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5858257843541361215837585 4393693382656020911878189)
            ·
              refine ⟨1647635018496007841954321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4393693382656020911878189 1647635018496007841954321)
              ·
                refine ⟨1235726263872005881465741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647635018496007841954321 1235726263872005881465741)
                ·
                  refine ⟨463397348952002205549653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235726263872005881465741 463397348952002205549653)
                  ·
                    rfl

theorem cell20_1015271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 3].length) (baseStart_1015271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015271 prefixEnd_1015271 := by exact prefixLift 1015271
  have htrace : WordTrace (prefixWord ++ tailWord_1015271) baseStart_1015271 baseEnd_1015271 := by
    simpa [prefixWord, tailWord_1015271, baseEnd_1015271] using wordTrace_append hprefix tailTrace_1015271
  have hstable : (prefixWord ++ tailWord_1015271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015271).length < 2 ^ (prefixWord ++ tailWord_1015271).sum := by decide
  have hdescent : baseEnd_1015271 < baseStart_1015271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015278 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_1015278 : Nat := 118140960795 + 1015278 * 2 ^ 59
def prefixEnd_1015278 : Nat := 4983230072969 + 3 ^ 40 * 1015278 * 2
def baseEnd_1015278 : Nat := 463400543942741292316291

theorem tailTrace_1015278 : CollatzResearch.WordTrace tailWord_1015278 prefixEnd_1015278 463400543942741292316291 := by
  unfold tailWord_1015278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4628778851978584565346811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24686820543885784348516325 4628778851978584565346811)
  ·
    refine ⟨6943168277967876848020217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4628778851978584565346811 6943168277967876848020217)
    ·
      refine ⟨5207376208475907636015163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6943168277967876848020217 5207376208475907636015163)
      ·
        refine ⟨7811064312713861454022745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5207376208475907636015163 7811064312713861454022745)
        ·
          refine ⟨5858298234535396090517059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7811064312713861454022745 5858298234535396090517059)
          ·
            refine ⟨8787447351803094135775589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5858298234535396090517059 8787447351803094135775589)
            ·
              refine ⟨1647646378463080150457923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8787447351803094135775589 1647646378463080150457923)
              ·
                refine ⟨2471469567694620225686885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647646378463080150457923 2471469567694620225686885)
                ·
                  refine ⟨463400543942741292316291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2471469567694620225686885 463400543942741292316291)
                  ·
                    rfl

theorem cell20_1015278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_1015278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015278 prefixEnd_1015278 := by exact prefixLift 1015278
  have htrace : WordTrace (prefixWord ++ tailWord_1015278) baseStart_1015278 baseEnd_1015278 := by
    simpa [prefixWord, tailWord_1015278, baseEnd_1015278] using wordTrace_append hprefix tailTrace_1015278
  have hstable : (prefixWord ++ tailWord_1015278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015278).length < 2 ^ (prefixWord ++ tailWord_1015278).sum := by decide
  have hdescent : baseEnd_1015278 < baseStart_1015278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015292 : List Nat := [2, 2, 2, 1, 2, 1, 2, 5, 3]
def baseStart_1015292 : Nat := 118140960795 + 1015292 * 2 ^ 59
def prefixEnd_1015292 : Nat := 4983230072969 + 3 ^ 40 * 1015292 * 2
def baseEnd_1015292 : Nat := 463406933924219465849567

theorem tailTrace_1015292 : CollatzResearch.WordTrace tailWord_1015292 prefixEnd_1015292 463406933924219465849567 := by
  unfold tailWord_1015292
  simp only [CollatzResearch.WordTrace]
  refine ⟨18515370718888978456892065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24687160958518637942522753 18515370718888978456892065)
  ·
    refine ⟨13886528039166733842669049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18515370718888978456892065 13886528039166733842669049)
    ·
      refine ⟨10414896029375050382001787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13886528039166733842669049 10414896029375050382001787)
      ·
        refine ⟨15622344044062575573002681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10414896029375050382001787 15622344044062575573002681)
        ·
          refine ⟨11716758033046931679752011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15622344044062575573002681 11716758033046931679752011)
          ·
            refine ⟨17575137049570397519628017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11716758033046931679752011 17575137049570397519628017)
            ·
              refine ⟨13181352787177798139721013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17575137049570397519628017 13181352787177798139721013)
              ·
                refine ⟨1235751823797918575598845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13181352787177798139721013 1235751823797918575598845)
                ·
                  refine ⟨463406933924219465849567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235751823797918575598845 463406933924219465849567)
                  ·
                    rfl

theorem cell20_1015292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_1015292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015292 prefixEnd_1015292 := by exact prefixLift 1015292
  have htrace : WordTrace (prefixWord ++ tailWord_1015292) baseStart_1015292 baseEnd_1015292 := by
    simpa [prefixWord, tailWord_1015292, baseEnd_1015292] using wordTrace_append hprefix tailTrace_1015292
  have hstable : (prefixWord ++ tailWord_1015292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015292).length < 2 ^ (prefixWord ++ tailWord_1015292).sum := by decide
  have hdescent : baseEnd_1015292 < baseStart_1015292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015313 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 7]
def baseStart_1015313 : Nat := 118140960795 + 1015313 * 2 ^ 59
def prefixEnd_1015313 : Nat := 4983230072969 + 3 ^ 40 * 1015313 * 2
def baseEnd_1015313 : Nat := 463416518896436726149481

theorem tailTrace_1015313 : CollatzResearch.WordTrace tailWord_1015313 prefixEnd_1015313 463416518896436726149481 := by
  unfold tailWord_1015313
  simp only [CollatzResearch.WordTrace]
  refine ⟨37031507370701877500298593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24687671580467918333532395 37031507370701877500298593)
  ·
    refine ⟨27773630528026408125223945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37031507370701877500298593 27773630528026408125223945)
    ·
      refine ⟨20830222896019806093917959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27773630528026408125223945 20830222896019806093917959)
      ·
        refine ⟨31245334344029709140876939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20830222896019806093917959 31245334344029709140876939)
        ·
          refine ⟨46868001516044563711315409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31245334344029709140876939 46868001516044563711315409)
          ·
            refine ⟨35151001137033422783486557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46868001516044563711315409 35151001137033422783486557)
            ·
              refine ⟨13181625426387533543807459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35151001137033422783486557 13181625426387533543807459)
              ·
                refine ⟨19772438139581300315711189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13181625426387533543807459 19772438139581300315711189)
                ·
                  refine ⟨463416518896436726149481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19772438139581300315711189 463416518896436726149481)
                  ·
                    rfl

theorem cell20_1015313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_1015313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015313 prefixEnd_1015313 := by exact prefixLift 1015313
  have htrace : WordTrace (prefixWord ++ tailWord_1015313) baseStart_1015313 baseEnd_1015313 := by
    simpa [prefixWord, tailWord_1015313, baseEnd_1015313] using wordTrace_append hprefix tailTrace_1015313
  have hstable : (prefixWord ++ tailWord_1015313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015313).length < 2 ^ (prefixWord ++ tailWord_1015313).sum := by decide
  have hdescent : baseEnd_1015313 < baseStart_1015313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015330 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1015330 : Nat := 118140960795 + 1015330 * 2 ^ 59
def prefixEnd_1015330 : Nat := 4983230072969 + 3 ^ 40 * 1015330 * 2
def baseEnd_1015330 : Nat := 463424278159660222582745

theorem tailTrace_1015330 : CollatzResearch.WordTrace tailWord_1015330 prefixEnd_1015330 463424278159660222582745 := by
  unfold tailWord_1015330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9258031852910072350916861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24688084941093526269111629 9258031852910072350916861)
  ·
    refine ⟨3471761944841277131593823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9258031852910072350916861 3471761944841277131593823)
    ·
      refine ⟨5207642917261915697390735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3471761944841277131593823 5207642917261915697390735)
      ·
        refine ⟨7811464375892873546086103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5207642917261915697390735 7811464375892873546086103)
        ·
          refine ⟨11717196563839310319129155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7811464375892873546086103 11717196563839310319129155)
          ·
            refine ⟨17575794845758965478693733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11717196563839310319129155 17575794845758965478693733)
            ·
              refine ⟨3295461533579806027255075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17575794845758965478693733 3295461533579806027255075)
              ·
                refine ⟨4943192300369709040882613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295461533579806027255075 4943192300369709040882613)
                ·
                  refine ⟨463424278159660222582745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4943192300369709040882613 463424278159660222582745)
                  ·
                    rfl

theorem cell20_1015330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1015330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015330 prefixEnd_1015330 := by exact prefixLift 1015330
  have htrace : WordTrace (prefixWord ++ tailWord_1015330) baseStart_1015330 baseEnd_1015330 := by
    simpa [prefixWord, tailWord_1015330, baseEnd_1015330] using wordTrace_append hprefix tailTrace_1015330
  have hstable : (prefixWord ++ tailWord_1015330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015330).length < 2 ^ (prefixWord ++ tailWord_1015330).sum := by decide
  have hdescent : baseEnd_1015330 < baseStart_1015330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015347 : List Nat := [1, 1, 1, 2, 4, 3, 4, 1, 3]
def baseStart_1015347 : Nat := 118140960795 + 1015347 * 2 ^ 59
def prefixEnd_1015347 : Nat := 4983230072969 + 3 ^ 40 * 1015347 * 2
def baseEnd_1015347 : Nat := 463432037422883719016009

theorem tailTrace_1015347 : CollatzResearch.WordTrace tailWord_1015347 prefixEnd_1015347 463432037422883719016009 := by
  unfold tailWord_1015347
  simp only [CollatzResearch.WordTrace]
  refine ⟨37032747452578701307036295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24688498301719134204690863 37032747452578701307036295)
  ·
    refine ⟨55549121178868051960554443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37032747452578701307036295 55549121178868051960554443)
    ·
      refine ⟨83323681768302077940831665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55549121178868051960554443 83323681768302077940831665)
      ·
        refine ⟨62492761326226558455623749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83323681768302077940831665 62492761326226558455623749)
        ·
          refine ⟨11717392748667479710429453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62492761326226558455623749 11717392748667479710429453)
          ·
            refine ⟨4394022280750304891411045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11717392748667479710429453 4394022280750304891411045)
            ·
              refine ⟨823879177640682167139571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4394022280750304891411045 823879177640682167139571)
              ·
                refine ⟨1235818766461023250709357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823879177640682167139571 1235818766461023250709357)
                ·
                  refine ⟨463432037422883719016009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235818766461023250709357 463432037422883719016009)
                  ·
                    rfl

theorem cell20_1015347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 3].length) (baseStart_1015347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015347 prefixEnd_1015347 := by exact prefixLift 1015347
  have htrace : WordTrace (prefixWord ++ tailWord_1015347) baseStart_1015347 baseEnd_1015347 := by
    simpa [prefixWord, tailWord_1015347, baseEnd_1015347] using wordTrace_append hprefix tailTrace_1015347
  have hstable : (prefixWord ++ tailWord_1015347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015347).length < 2 ^ (prefixWord ++ tailWord_1015347).sum := by decide
  have hdescent : baseEnd_1015347 < baseStart_1015347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015388 : List Nat := [2, 2, 4, 1, 2, 1, 4, 2, 2]
def baseStart_1015388 : Nat := 118140960795 + 1015388 * 2 ^ 59
def prefixEnd_1015388 : Nat := 4983230072969 + 3 ^ 40 * 1015388 * 2
def baseEnd_1015388 : Nat := 463450750940069798649175

theorem tailTrace_1015388 : CollatzResearch.WordTrace tailWord_1015388 prefixEnd_1015388 463450750940069798649175 := by
  unfold tailWord_1015388
  simp only [CollatzResearch.WordTrace]
  refine ⟨18517121422715082654639409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24689495230286776872852545 18517121422715082654639409)
  ·
    refine ⟨13887841067036311990979557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18517121422715082654639409 13887841067036311990979557)
    ·
      refine ⟨2603970200069308498308667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13887841067036311990979557 2603970200069308498308667)
      ·
        refine ⟨3905955300103962747463001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603970200069308498308667 3905955300103962747463001)
        ·
          refine ⟨2929466475077972060597251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3905955300103962747463001 2929466475077972060597251)
          ·
            refine ⟨4394199712616958090895877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2929466475077972060597251 4394199712616958090895877)
            ·
              refine ⟨823912446115679642042977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4394199712616958090895877 823912446115679642042977)
              ·
                refine ⟨617934334586759731532233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 823912446115679642042977 617934334586759731532233)
                ·
                  refine ⟨463450750940069798649175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617934334586759731532233 463450750940069798649175)
                  ·
                    rfl

theorem cell20_1015388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_1015388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015388 prefixEnd_1015388 := by exact prefixLift 1015388
  have htrace : WordTrace (prefixWord ++ tailWord_1015388) baseStart_1015388 baseEnd_1015388 := by
    simpa [prefixWord, tailWord_1015388, baseEnd_1015388] using wordTrace_append hprefix tailTrace_1015388
  have hstable : (prefixWord ++ tailWord_1015388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015388).length < 2 ^ (prefixWord ++ tailWord_1015388).sum := by decide
  have hdescent : baseEnd_1015388 < baseStart_1015388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015427 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 5]
def baseStart_1015427 : Nat := 118140960795 + 1015427 * 2 ^ 59
def prefixEnd_1015427 : Nat := 4983230072969 + 3 ^ 40 * 1015427 * 2
def baseEnd_1015427 : Nat := 463468551602758996349015

theorem tailTrace_1015427 : CollatzResearch.WordTrace tailWord_1015427 prefixEnd_1015427 463468551602758996349015 := by
  unfold tailWord_1015427
  simp only [CollatzResearch.WordTrace]
  refine ⟨37035665292288874969948535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24690443528192583313299023 37035665292288874969948535)
  ·
    refine ⟨55553497938433312454922803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37035665292288874969948535 55553497938433312454922803)
    ·
      refine ⟨83330246907649968682384205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55553497938433312454922803 83330246907649968682384205)
      ·
        refine ⟨31248842590368738255894077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83330246907649968682384205 31248842590368738255894077)
        ·
          refine ⟨11718315971388276845960279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31248842590368738255894077 11718315971388276845960279)
          ·
            refine ⟨17577473957082415268940419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11718315971388276845960279 17577473957082415268940419)
            ·
              refine ⟨26366210935623622903410629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17577473957082415268940419 26366210935623622903410629)
              ·
                refine ⟨4943664550429429294389493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26366210935623622903410629 4943664550429429294389493)
                ·
                  refine ⟨463468551602758996349015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4943664550429429294389493 463468551602758996349015)
                  ·
                    rfl

theorem cell20_1015427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_1015427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015427 prefixEnd_1015427 := by exact prefixLift 1015427
  have htrace : WordTrace (prefixWord ++ tailWord_1015427) baseStart_1015427 baseEnd_1015427 := by
    simpa [prefixWord, tailWord_1015427, baseEnd_1015427] using wordTrace_append hprefix tailTrace_1015427
  have hstable : (prefixWord ++ tailWord_1015427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015427).length < 2 ^ (prefixWord ++ tailWord_1015427).sum := by decide
  have hdescent : baseEnd_1015427 < baseStart_1015427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015506 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1015506 : Nat := 118140960795 + 1015506 * 2 ^ 59
def prefixEnd_1015506 : Nat := 4983230072969 + 3 ^ 40 * 1015506 * 2
def baseEnd_1015506 : Nat := 463504609355385832715359

theorem tailTrace_1015506 : CollatzResearch.WordTrace tailWord_1015506 prefixEnd_1015506 463504609355385832715359 := by
  unfold tailWord_1015506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9259636664750667865518593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24692364439335114308049581 9259636664750667865518593)
  ·
    refine ⟨6944727498563000899138945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9259636664750667865518593 6944727498563000899138945)
    ·
      refine ⟨5208545623922250674354209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6944727498563000899138945 5208545623922250674354209)
      ·
        refine ⟨3906409217941688005765657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5208545623922250674354209 3906409217941688005765657)
        ·
          refine ⟨2929806913456266004324243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3906409217941688005765657 2929806913456266004324243)
          ·
            refine ⟨4394710370184399006486365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2929806913456266004324243 4394710370184399006486365)
            ·
              refine ⟨1648016388819149627432387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4394710370184399006486365 1648016388819149627432387)
              ·
                refine ⟨2472024583228724441148581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648016388819149627432387 2472024583228724441148581)
                ·
                  refine ⟨463504609355385832715359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2472024583228724441148581 463504609355385832715359)
                  ·
                    rfl

theorem cell20_1015506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1015506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015506 prefixEnd_1015506 := by exact prefixLift 1015506
  have htrace : WordTrace (prefixWord ++ tailWord_1015506) baseStart_1015506 baseEnd_1015506 := by
    simpa [prefixWord, tailWord_1015506, baseEnd_1015506] using wordTrace_append hprefix tailTrace_1015506
  have hstable : (prefixWord ++ tailWord_1015506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015506).length < 2 ^ (prefixWord ++ tailWord_1015506).sum := by decide
  have hdescent : baseEnd_1015506 < baseStart_1015506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015516 : List Nat := [2, 2, 5, 1, 2, 1, 1, 3, 3]
def baseStart_1015516 : Nat := 118140960795 + 1015516 * 2 ^ 59
def prefixEnd_1015516 : Nat := 4983230072969 + 3 ^ 40 * 1015516 * 2
def baseEnd_1015516 : Nat := 463509173627870242381985

theorem tailTrace_1015516 : CollatzResearch.WordTrace tailWord_1015516 prefixEnd_1015516 463509173627870242381985 := by
  unfold tailWord_1015516
  simp only [CollatzResearch.WordTrace]
  refine ⟨18519455694483221584969201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24692607592644295446625601 18519455694483221584969201)
  ·
    refine ⟨13889591770862416188726901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18519455694483221584969201 13889591770862416188726901)
    ·
      refine ⟨1302149228518351517693147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13889591770862416188726901 1302149228518351517693147)
      ·
        refine ⟨1953223842777527276539721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302149228518351517693147 1953223842777527276539721)
        ·
          refine ⟨1464917882083145457404791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1953223842777527276539721 1464917882083145457404791)
          ·
            refine ⟨2197376823124718186107187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464917882083145457404791 2197376823124718186107187)
            ·
              refine ⟨3296065234687077279160781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197376823124718186107187 3296065234687077279160781)
              ·
                refine ⟨1236024463007653979685293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3296065234687077279160781 1236024463007653979685293)
                ·
                  refine ⟨463509173627870242381985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236024463007653979685293 463509173627870242381985)
                  ·
                    rfl

theorem cell20_1015516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_1015516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015516 prefixEnd_1015516 := by exact prefixLift 1015516
  have htrace : WordTrace (prefixWord ++ tailWord_1015516) baseStart_1015516 baseEnd_1015516 := by
    simpa [prefixWord, tailWord_1015516, baseEnd_1015516] using wordTrace_append hprefix tailTrace_1015516
  have hstable : (prefixWord ++ tailWord_1015516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015516).length < 2 ^ (prefixWord ++ tailWord_1015516).sum := by decide
  have hdescent : baseEnd_1015516 < baseStart_1015516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015534 : List Nat := [4, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1015534 : Nat := 118140960795 + 1015534 * 2 ^ 59
def prefixEnd_1015534 : Nat := 4983230072969 + 3 ^ 40 * 1015534 * 2
def baseEnd_1015534 : Nat := 154505796439447393260637

theorem tailTrace_1015534 : CollatzResearch.WordTrace tailWord_1015534 prefixEnd_1015534 154505796439447393260637 := by
  unfold tailWord_1015534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4629945987862654030511707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24693045268600821496062437 4629945987862654030511707)
  ·
    refine ⟨6944918981793981045767561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4629945987862654030511707 6944918981793981045767561)
    ·
      refine ⟨5208689236345485784325671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6944918981793981045767561 5208689236345485784325671)
      ·
        refine ⟨7813033854518228676488507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5208689236345485784325671 7813033854518228676488507)
        ·
          refine ⟨11719550781777343014732761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7813033854518228676488507 11719550781777343014732761)
          ·
            refine ⟨8789663086333007261049571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11719550781777343014732761 8789663086333007261049571)
            ·
              refine ⟨13184494629499510891574357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8789663086333007261049571 13184494629499510891574357)
              ·
                refine ⟨154505796439447393260637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13184494629499510891574357 154505796439447393260637)
                ·
                  rfl

theorem cell20_1015534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1015534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015534 prefixEnd_1015534 := by exact prefixLift 1015534
  have htrace : WordTrace (prefixWord ++ tailWord_1015534) baseStart_1015534 baseEnd_1015534 := by
    simpa [prefixWord, tailWord_1015534, baseEnd_1015534] using wordTrace_append hprefix tailTrace_1015534
  have hstable : (prefixWord ++ tailWord_1015534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015534).length < 2 ^ (prefixWord ++ tailWord_1015534).sum := by decide
  have hdescent : baseEnd_1015534 < baseStart_1015534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015589 : List Nat := [1, 3, 1, 2, 3, 3, 3, 4]
def baseStart_1015589 : Nat := 118140960795 + 1015589 * 2 ^ 59
def prefixEnd_1015589 : Nat := 4983230072969 + 3 ^ 40 * 1015589 * 2
def baseEnd_1015589 : Nat := 154514164272335477649451

theorem tailTrace_1015589 : CollatzResearch.WordTrace tailWord_1015589 prefixEnd_1015589 154514164272335477649451 := by
  unfold tailWord_1015589
  simp only [CollatzResearch.WordTrace]
  refine ⟨37041573917701976637345821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24694382611801317758230547 37041573917701976637345821)
  ·
    refine ⟨13890590219138241239004683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37041573917701976637345821 13890590219138241239004683)
    ·
      refine ⟨20835885328707361858507025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13890590219138241239004683 20835885328707361858507025)
      ·
        refine ⟨15626913996530521393880269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20835885328707361858507025 15626913996530521393880269)
        ·
          refine ⟨5860092748698945522705101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15626913996530521393880269 5860092748698945522705101)
          ·
            refine ⟨2197534780762104571014413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5860092748698945522705101 2197534780762104571014413)
            ·
              refine ⟨824075542785789214130405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2197534780762104571014413 824075542785789214130405)
              ·
                refine ⟨154514164272335477649451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 824075542785789214130405 154514164272335477649451)
                ·
                  rfl

theorem cell20_1015589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 4].length) (baseStart_1015589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015589 prefixEnd_1015589 := by exact prefixLift 1015589
  have htrace : WordTrace (prefixWord ++ tailWord_1015589) baseStart_1015589 baseEnd_1015589 := by
    simpa [prefixWord, tailWord_1015589, baseEnd_1015589] using wordTrace_append hprefix tailTrace_1015589
  have hstable : (prefixWord ++ tailWord_1015589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015589).length < 2 ^ (prefixWord ++ tailWord_1015589).sum := by decide
  have hdescent : baseEnd_1015589 < baseStart_1015589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015609 : List Nat := [1, 2, 1, 7, 2, 1, 1, 2, 3]
def baseStart_1015609 : Nat := 118140960795 + 1015609 * 2 ^ 59
def prefixEnd_1015609 : Nat := 4983230072969 + 3 ^ 40 * 1015609 * 2
def baseEnd_1015609 : Nat := 463551621361975252281605

theorem tailTrace_1015609 : CollatzResearch.WordTrace tailWord_1015609 prefixEnd_1015609 463551621361975252281605 := by
  unfold tailWord_1015609
  simp only [CollatzResearch.WordTrace]
  refine ⟨37042303377629520053073881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24694868918419680035382587 37042303377629520053073881)
  ·
    refine ⟨27781727533222140039805411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37042303377629520053073881 27781727533222140039805411)
    ·
      refine ⟨41672591299833210059708117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27781727533222140039805411 41672591299833210059708117)
      ·
        refine ⟨976701358589840860774409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 41672591299833210059708117 976701358589840860774409)
        ·
          refine ⟨732526018942380645580807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976701358589840860774409 732526018942380645580807)
          ·
            refine ⟨1098789028413570968371211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732526018942380645580807 1098789028413570968371211)
            ·
              refine ⟨1648183542620356452556817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098789028413570968371211 1648183542620356452556817)
              ·
                refine ⟨1236137656965267339417613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648183542620356452556817 1236137656965267339417613)
                ·
                  refine ⟨463551621361975252281605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236137656965267339417613 463551621361975252281605)
                  ·
                    rfl

theorem cell20_1015609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 3].length) (baseStart_1015609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015609 prefixEnd_1015609 := by exact prefixLift 1015609
  have htrace : WordTrace (prefixWord ++ tailWord_1015609) baseStart_1015609 baseEnd_1015609 := by
    simpa [prefixWord, tailWord_1015609, baseEnd_1015609] using wordTrace_append hprefix tailTrace_1015609
  have hstable : (prefixWord ++ tailWord_1015609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015609).length < 2 ^ (prefixWord ++ tailWord_1015609).sum := by decide
  have hdescent : baseEnd_1015609 < baseStart_1015609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015610 : List Nat := [3, 1, 1, 1, 5, 2, 7]
def baseStart_1015610 : Nat := 118140960795 + 1015610 * 2 ^ 59
def prefixEnd_1015610 : Nat := 4983230072969 + 3 ^ 40 * 1015610 * 2
def baseEnd_1015610 : Nat := 51505786421024854805363

theorem tailTrace_1015610 : CollatzResearch.WordTrace tailWord_1015610 prefixEnd_1015610 51505786421024854805363 := by
  unfold tailWord_1015610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9260584962656474305965071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24694893233750598149240189 9260584962656474305965071)
  ·
    refine ⟨13890877443984711458947607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9260584962656474305965071 13890877443984711458947607)
    ·
      refine ⟨20836316165977067188421411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13890877443984711458947607 20836316165977067188421411)
      ·
        refine ⟨31254474248965600782632117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20836316165977067188421411 31254474248965600782632117)
        ·
          refine ⟨2930106960840525073371761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31254474248965600782632117 2930106960840525073371761)
          ·
            refine ⟨2197580220630393805028821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2930106960840525073371761 2197580220630393805028821)
            ·
              refine ⟨51505786421024854805363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2197580220630393805028821 51505786421024854805363)
              ·
                rfl

theorem cell20_1015610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 7].length) (baseStart_1015610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015610 prefixEnd_1015610 := by exact prefixLift 1015610
  have htrace : WordTrace (prefixWord ++ tailWord_1015610) baseStart_1015610 baseEnd_1015610 := by
    simpa [prefixWord, tailWord_1015610, baseEnd_1015610] using wordTrace_append hprefix tailTrace_1015610
  have hstable : (prefixWord ++ tailWord_1015610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015610).length < 2 ^ (prefixWord ++ tailWord_1015610).sum := by decide
  have hdescent : baseEnd_1015610 < baseStart_1015610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015613 : List Nat := [1, 4, 1, 4, 1, 1, 3, 2, 3]
def baseStart_1015613 : Nat := 118140960795 + 1015613 * 2 ^ 59
def prefixEnd_1015613 : Nat := 4983230072969 + 3 ^ 40 * 1015613 * 2
def baseEnd_1015613 : Nat := 463553447070969016148255

theorem tailTrace_1015613 : CollatzResearch.WordTrace tailWord_1015613 prefixEnd_1015613 463553447070969016148255 := by
  unfold tailWord_1015613
  simp only [CollatzResearch.WordTrace]
  refine ⟨37042449269615028736219493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24694966179743352490812995 37042449269615028736219493)
  ·
    refine ⟨6945459238052817888041155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37042449269615028736219493 6945459238052817888041155)
    ·
      refine ⟨10418188857079226832061733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6945459238052817888041155 10418188857079226832061733)
      ·
        refine ⟨1953410410702355031011575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10418188857079226832061733 1953410410702355031011575)
        ·
          refine ⟨2930115616053532546517363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1953410410702355031011575 2930115616053532546517363)
          ·
            refine ⟨4395173424080298819776045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2930115616053532546517363 4395173424080298819776045)
            ·
              refine ⟨1648190034030112057416017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4395173424080298819776045 1648190034030112057416017)
              ·
                refine ⟨1236142525522584043062013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648190034030112057416017 1236142525522584043062013)
                ·
                  refine ⟨463553447070969016148255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236142525522584043062013 463553447070969016148255)
                  ·
                    rfl

theorem cell20_1015613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_1015613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015613 prefixEnd_1015613 := by exact prefixLift 1015613
  have htrace : WordTrace (prefixWord ++ tailWord_1015613) baseStart_1015613 baseEnd_1015613 := by
    simpa [prefixWord, tailWord_1015613, baseEnd_1015613] using wordTrace_append hprefix tailTrace_1015613
  have hstable : (prefixWord ++ tailWord_1015613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015613).length < 2 ^ (prefixWord ++ tailWord_1015613).sum := by decide
  have hdescent : baseEnd_1015613 < baseStart_1015613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015648 : List Nat := [2, 1, 1, 3, 3, 3, 1, 6]
def baseStart_1015648 : Nat := 118140960795 + 1015648 * 2 ^ 59
def prefixEnd_1015648 : Nat := 4983230072969 + 3 ^ 40 * 1015648 * 2
def baseEnd_1015648 : Nat := 154523140674888149993815

theorem tailTrace_1015648 : CollatzResearch.WordTrace tailWord_1015648 prefixEnd_1015648 154523140674888149993815 := by
  unfold tailWord_1015648
  simp only [CollatzResearch.WordTrace]
  refine ⟨18521862912244114856871799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24695817216325486475829065 18521862912244114856871799)
  ·
    refine ⟨27782794368366172285307699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18521862912244114856871799 27782794368366172285307699)
    ·
      refine ⟨41674191552549258427961549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27782794368366172285307699 41674191552549258427961549)
      ·
        refine ⟨15627821832205971910485581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41674191552549258427961549 15627821832205971910485581)
        ·
          refine ⟨5860433187077239466432093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15627821832205971910485581 5860433187077239466432093)
          ·
            refine ⟨2197662445153964799912035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5860433187077239466432093 2197662445153964799912035)
            ·
              refine ⟨3296493667730947199868053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197662445153964799912035 3296493667730947199868053)
              ·
                refine ⟨154523140674888149993815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3296493667730947199868053 154523140674888149993815)
                ·
                  rfl

theorem cell20_1015648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_1015648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015648 prefixEnd_1015648 := by exact prefixLift 1015648
  have htrace : WordTrace (prefixWord ++ tailWord_1015648) baseStart_1015648 baseEnd_1015648 := by
    simpa [prefixWord, tailWord_1015648, baseEnd_1015648] using wordTrace_append hprefix tailTrace_1015648
  have hstable : (prefixWord ++ tailWord_1015648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015648).length < 2 ^ (prefixWord ++ tailWord_1015648).sum := by decide
  have hdescent : baseEnd_1015648 < baseStart_1015648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015655 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 7]
def baseStart_1015655 : Nat := 118140960795 + 1015655 * 2 ^ 59
def prefixEnd_1015655 : Nat := 4983230072969 + 3 ^ 40 * 1015655 * 2
def baseEnd_1015655 : Nat := 463572617015403536748083

theorem tailTrace_1015655 : CollatzResearch.WordTrace tailWord_1015655 prefixEnd_1015655 463572617015403536748083 := by
  unfold tailWord_1015655
  simp only [CollatzResearch.WordTrace]
  refine ⟨37043981135462869909248419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24695987423641913272832279 37043981135462869909248419)
  ·
    refine ⟨55565971703194304863872629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37043981135462869909248419 55565971703194304863872629)
    ·
      refine ⟨5209309847174466080988059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55565971703194304863872629 5209309847174466080988059)
      ·
        refine ⟨7813964770761699121482089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5209309847174466080988059 7813964770761699121482089)
        ·
          refine ⟨5860473578071274341111567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7813964770761699121482089 5860473578071274341111567)
          ·
            refine ⟨8790710367106911511667351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860473578071274341111567 8790710367106911511667351)
            ·
              refine ⟨13186065550660367267501027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8790710367106911511667351 13186065550660367267501027)
              ·
                refine ⟨19779098325990550901251541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13186065550660367267501027 19779098325990550901251541)
                ·
                  refine ⟨463572617015403536748083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19779098325990550901251541 463572617015403536748083)
                  ·
                    rfl

theorem cell20_1015655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_1015655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015655 prefixEnd_1015655 := by exact prefixLift 1015655
  have htrace : WordTrace (prefixWord ++ tailWord_1015655) baseStart_1015655 baseEnd_1015655 := by
    simpa [prefixWord, tailWord_1015655, baseEnd_1015655] using wordTrace_append hprefix tailTrace_1015655
  have hstable : (prefixWord ++ tailWord_1015655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015655).length < 2 ^ (prefixWord ++ tailWord_1015655).sum := by decide
  have hdescent : baseEnd_1015655 < baseStart_1015655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015720 : List Nat := [2, 1, 6, 2, 2, 7]
def baseStart_1015720 : Nat := 118140960795 + 1015720 * 2 ^ 59
def prefixEnd_1015720 : Nat := 4983230072969 + 3 ^ 40 * 1015720 * 2
def baseEnd_1015720 : Nat := 17170454992094525910413

theorem tailTrace_1015720 : CollatzResearch.WordTrace tailWord_1015720 prefixEnd_1015720 17170454992094525910413 := by
  unfold tailWord_1015720
  simp only [CollatzResearch.WordTrace]
  refine ⟨18523175940113693005182307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24697567920151590673576409 18523175940113693005182307)
  ·
    refine ⟨27784763910170539507773461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18523175940113693005182307 27784763910170539507773461)
    ·
      refine ⟨1302410808289244039426881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27784763910170539507773461 1302410808289244039426881)
      ·
        refine ⟨976808106216933029570161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1302410808289244039426881 976808106216933029570161)
        ·
          refine ⟨732606079662699772177621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976808106216933029570161 732606079662699772177621)
          ·
            refine ⟨17170454992094525910413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 732606079662699772177621 17170454992094525910413)
            ·
              rfl

theorem cell20_1015720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 7].length) (baseStart_1015720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015720 prefixEnd_1015720 := by exact prefixLift 1015720
  have htrace : WordTrace (prefixWord ++ tailWord_1015720) baseStart_1015720 baseEnd_1015720 := by
    simpa [prefixWord, tailWord_1015720, baseEnd_1015720] using wordTrace_append hprefix tailTrace_1015720
  have hstable : (prefixWord ++ tailWord_1015720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015720).length < 2 ^ (prefixWord ++ tailWord_1015720).sum := by decide
  have hdescent : baseEnd_1015720 < baseStart_1015720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015741 : List Nat := [1, 4, 1, 2, 3, 3, 1, 5]
def baseStart_1015741 : Nat := 118140960795 + 1015741 * 2 ^ 59
def prefixEnd_1015741 : Nat := 4983230072969 + 3 ^ 40 * 1015741 * 2
def baseEnd_1015741 : Nat := 154537289919589819960355

theorem tailTrace_1015741 : CollatzResearch.WordTrace tailWord_1015741 prefixEnd_1015741 154537289919589819960355 := by
  unfold tailWord_1015741
  simp only [CollatzResearch.WordTrace]
  refine ⟨37047117813151306596879077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24698078542100871064586051 37047117813151306596879077)
  ·
    refine ⟨6946334589965869986914827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37047117813151306596879077 6946334589965869986914827)
    ·
      refine ⟨10419501884948804980372241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6946334589965869986914827 10419501884948804980372241)
      ·
        refine ⟨7814626413711603735279181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10419501884948804980372241 7814626413711603735279181)
        ·
          refine ⟨2930484905141851400729693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7814626413711603735279181 2930484905141851400729693)
          ·
            refine ⟨1098931839428194275273635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2930484905141851400729693 1098931839428194275273635)
            ·
              refine ⟨1648397759142291412910453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098931839428194275273635 1648397759142291412910453)
              ·
                refine ⟨154537289919589819960355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1648397759142291412910453 154537289919589819960355)
                ·
                  rfl

theorem cell20_1015741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 5].length) (baseStart_1015741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015741 prefixEnd_1015741 := by exact prefixLift 1015741
  have htrace : WordTrace (prefixWord ++ tailWord_1015741) baseStart_1015741 baseEnd_1015741 := by
    simpa [prefixWord, tailWord_1015741, baseEnd_1015741] using wordTrace_append hprefix tailTrace_1015741
  have hstable : (prefixWord ++ tailWord_1015741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015741).length < 2 ^ (prefixWord ++ tailWord_1015741).sum := by decide
  have hdescent : baseEnd_1015741 < baseStart_1015741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015789 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1015789 : Nat := 118140960795 + 1015789 * 2 ^ 59
def prefixEnd_1015789 : Nat := 4983230072969 + 3 ^ 40 * 1015789 * 2
def baseEnd_1015789 : Nat := 463633778266694626280869

theorem tailTrace_1015789 : CollatzResearch.WordTrace tailWord_1015789 prefixEnd_1015789 463633778266694626280869 := by
  unfold tailWord_1015789
  simp only [CollatzResearch.WordTrace]
  refine ⟨37048868516977410794626421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24699245677984940529750947 37048868516977410794626421)
  ·
    refine ⟨3473331423466632261996227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37048868516977410794626421 3473331423466632261996227)
    ·
      refine ⟨5209997135199948392994341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3473331423466632261996227 5209997135199948392994341)
      ·
        refine ⟨976874462849990323686439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5209997135199948392994341 976874462849990323686439)
        ·
          refine ⟨1465311694274985485529659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976874462849990323686439 1465311694274985485529659)
          ·
            refine ⟨2197967541412478228294489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465311694274985485529659 2197967541412478228294489)
            ·
              refine ⟨1648475656059358671220867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2197967541412478228294489 1648475656059358671220867)
              ·
                refine ⟨2472713484089038006831301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648475656059358671220867 2472713484089038006831301)
                ·
                  refine ⟨463633778266694626280869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2472713484089038006831301 463633778266694626280869)
                  ·
                    rfl

theorem cell20_1015789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1015789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015789 prefixEnd_1015789 := by exact prefixLift 1015789
  have htrace : WordTrace (prefixWord ++ tailWord_1015789) baseStart_1015789 baseEnd_1015789 := by
    simpa [prefixWord, tailWord_1015789, baseEnd_1015789] using wordTrace_append hprefix tailTrace_1015789
  have hstable : (prefixWord ++ tailWord_1015789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015789).length < 2 ^ (prefixWord ++ tailWord_1015789).sum := by decide
  have hdescent : baseEnd_1015789 < baseStart_1015789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015807 : List Nat := [1, 1, 2, 2, 1, 2, 1, 7, 3]
def baseStart_1015807 : Nat := 118140960795 + 1015807 * 2 ^ 59
def prefixEnd_1015807 : Nat := 4983230072969 + 3 ^ 40 * 1015807 * 2
def baseEnd_1015807 : Nat := 463641993957166563680795

theorem tailTrace_1015807 : CollatzResearch.WordTrace tailWord_1015807 prefixEnd_1015807 463641993957166563680795 := by
  unfold tailWord_1015807
  simp only [CollatzResearch.WordTrace]
  refine ⟨37049525030912199868781675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24699683353941466579187783 37049525030912199868781675)
  ·
    refine ⟨55574287546368299803172513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37049525030912199868781675 55574287546368299803172513)
    ·
      refine ⟨41680715659776224852379385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55574287546368299803172513 41680715659776224852379385)
      ·
        refine ⟨31260536744832168639284539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41680715659776224852379385 31260536744832168639284539)
        ·
          refine ⟨46890805117248252958926809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31260536744832168639284539 46890805117248252958926809)
          ·
            refine ⟨35168103837936189719195107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46890805117248252958926809 35168103837936189719195107)
            ·
              refine ⟨52752155756904284578792661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35168103837936189719195107 52752155756904284578792661)
              ·
                refine ⟨1236378650552444169815453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52752155756904284578792661 1236378650552444169815453)
                ·
                  refine ⟨463641993957166563680795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236378650552444169815453 463641993957166563680795)
                  ·
                    rfl

theorem cell20_1015807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 3].length) (baseStart_1015807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015807 prefixEnd_1015807 := by exact prefixLift 1015807
  have htrace : WordTrace (prefixWord ++ tailWord_1015807) baseStart_1015807 baseEnd_1015807 := by
    simpa [prefixWord, tailWord_1015807, baseEnd_1015807] using wordTrace_append hprefix tailTrace_1015807
  have hstable : (prefixWord ++ tailWord_1015807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015807).length < 2 ^ (prefixWord ++ tailWord_1015807).sum := by decide
  have hdescent : baseEnd_1015807 < baseStart_1015807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015844 : List Nat := [2, 3, 1, 4, 2, 1, 3, 2, 2]
def baseStart_1015844 : Nat := 118140960795 + 1015844 * 2 ^ 59
def prefixEnd_1015844 : Nat := 4983230072969 + 3 ^ 40 * 1015844 * 2
def baseEnd_1015844 : Nat := 463658881765358879447311

theorem tailTrace_1015844 : CollatzResearch.WordTrace tailWord_1015844 prefixEnd_1015844 463658881765358879447311 := by
  unfold tailWord_1015844
  simp only [CollatzResearch.WordTrace]
  refine ⟨18525437265889077593939293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24700583021185436791919057 18525437265889077593939293)
  ·
    refine ⟨6947038974708404097727235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18525437265889077593939293 6947038974708404097727235)
    ·
      refine ⟨10420558462062606146590853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6947038974708404097727235 10420558462062606146590853)
      ·
        refine ⟨1953854711636738652485785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10420558462062606146590853 1953854711636738652485785)
        ·
          refine ⟨1465391033727553989364339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1953854711636738652485785 1465391033727553989364339)
          ·
            refine ⟨2198086550591330984046509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465391033727553989364339 2198086550591330984046509)
            ·
              refine ⟨824282456471749119017441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2198086550591330984046509 824282456471749119017441)
              ·
                refine ⟨618211842353811839263081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 824282456471749119017441 618211842353811839263081)
                ·
                  refine ⟨463658881765358879447311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618211842353811839263081 463658881765358879447311)
                  ·
                    rfl

theorem cell20_1015844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_1015844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015844 prefixEnd_1015844 := by exact prefixLift 1015844
  have htrace : WordTrace (prefixWord ++ tailWord_1015844) baseStart_1015844 baseEnd_1015844 := by
    simpa [prefixWord, tailWord_1015844, baseEnd_1015844] using wordTrace_append hprefix tailTrace_1015844
  have hstable : (prefixWord ++ tailWord_1015844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015844).length < 2 ^ (prefixWord ++ tailWord_1015844).sum := by decide
  have hdescent : baseEnd_1015844 < baseStart_1015844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015845 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 5]
def baseStart_1015845 : Nat := 118140960795 + 1015845 * 2 ^ 59
def prefixEnd_1015845 : Nat := 4983230072969 + 3 ^ 40 * 1015845 * 2
def baseEnd_1015845 : Nat := 463659338192607320413973

theorem tailTrace_1015845 : CollatzResearch.WordTrace tailWord_1015845 prefixEnd_1015845 463659338192607320413973 := by
  unfold tailWord_1015845
  simp only [CollatzResearch.WordTrace]
  refine ⟨37050911004774532358664989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24700607336516354905776659 37050911004774532358664989)
  ·
    refine ⟨13894091626790449634499371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37050911004774532358664989 13894091626790449634499371)
    ·
      refine ⟨20841137440185674451749057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13894091626790449634499371 20841137440185674451749057)
      ·
        refine ⟨15630853080139255838811793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20841137440185674451749057 15630853080139255838811793)
        ·
          refine ⟨11723139810104441879108845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15630853080139255838811793 11723139810104441879108845)
          ·
            refine ⟨4396177428789165704665817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11723139810104441879108845 4396177428789165704665817)
            ·
              refine ⟨3297133071591874278499363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4396177428789165704665817 3297133071591874278499363)
              ·
                refine ⟨4945699607387811417749045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3297133071591874278499363 4945699607387811417749045)
                ·
                  refine ⟨463659338192607320413973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4945699607387811417749045 463659338192607320413973)
                  ·
                    rfl

theorem cell20_1015845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_1015845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015845 prefixEnd_1015845 := by exact prefixLift 1015845
  have htrace : WordTrace (prefixWord ++ tailWord_1015845) baseStart_1015845 baseEnd_1015845 := by
    simpa [prefixWord, tailWord_1015845, baseEnd_1015845] using wordTrace_append hprefix tailTrace_1015845
  have hstable : (prefixWord ++ tailWord_1015845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015845).length < 2 ^ (prefixWord ++ tailWord_1015845).sum := by decide
  have hdescent : baseEnd_1015845 < baseStart_1015845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015852 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_1015852 : Nat := 118140960795 + 1015852 * 2 ^ 59
def prefixEnd_1015852 : Nat := 4983230072969 + 3 ^ 40 * 1015852 * 2
def baseEnd_1015852 : Nat := 463662533183346407180611

theorem tailTrace_1015852 : CollatzResearch.WordTrace tailWord_1015852 prefixEnd_1015852 463662533183346407180611 := by
  unfold tailWord_1015852
  simp only [CollatzResearch.WordTrace]
  refine ⟨18525583157874586277084905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24700777543832781702779873 18525583157874586277084905)
  ·
    refine ⟨13894187368405939707813679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18525583157874586277084905 13894187368405939707813679)
    ·
      refine ⟨20841281052608909561720519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13894187368405939707813679 20841281052608909561720519)
      ·
        refine ⟨31261921578913364342580779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20841281052608909561720519 31261921578913364342580779)
        ·
          refine ⟨46892882368370046513871169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31261921578913364342580779 46892882368370046513871169)
          ·
            refine ⟨35169661776277534885403377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46892882368370046513871169 35169661776277534885403377)
            ·
              refine ⟨26377246332208151164052533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35169661776277534885403377 26377246332208151164052533)
              ·
                refine ⟨2472866843644514171629925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26377246332208151164052533 2472866843644514171629925)
                ·
                  refine ⟨463662533183346407180611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2472866843644514171629925 463662533183346407180611)
                  ·
                    rfl

theorem cell20_1015852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_1015852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015852 prefixEnd_1015852 := by exact prefixLift 1015852
  have htrace : WordTrace (prefixWord ++ tailWord_1015852) baseStart_1015852 baseEnd_1015852 := by
    simpa [prefixWord, tailWord_1015852, baseEnd_1015852] using wordTrace_append hprefix tailTrace_1015852
  have hstable : (prefixWord ++ tailWord_1015852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015852).length < 2 ^ (prefixWord ++ tailWord_1015852).sum := by decide
  have hdescent : baseEnd_1015852 < baseStart_1015852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015859 : List Nat := [1, 1, 1, 2, 4, 1, 3, 7]
def baseStart_1015859 : Nat := 118140960795 + 1015859 * 2 ^ 59
def prefixEnd_1015859 : Nat := 4983230072969 + 3 ^ 40 * 1015859 * 2
def baseEnd_1015859 : Nat := 154555242724695164649083

theorem tailTrace_1015859 : CollatzResearch.WordTrace tailWord_1015859 prefixEnd_1015859 154555242724695164649083 := by
  unfold tailWord_1015859
  simp only [CollatzResearch.WordTrace]
  refine ⟨37051421626723812749674631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24700947751149208499783087 37051421626723812749674631)
  ·
    refine ⟨55577132440085719124511947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37051421626723812749674631 55577132440085719124511947)
    ·
      refine ⟨83365698660128578686767921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55577132440085719124511947 83365698660128578686767921)
      ·
        refine ⟨62524273995096434015075941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83365698660128578686767921 62524273995096434015075941)
        ·
          refine ⟨11723301374080581377826739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62524273995096434015075941 11723301374080581377826739)
          ·
            refine ⟨17584952061120872066740109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11723301374080581377826739 17584952061120872066740109)
            ·
              refine ⟨6594357022920327025027541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17584952061120872066740109 6594357022920327025027541)
              ·
                refine ⟨154555242724695164649083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6594357022920327025027541 154555242724695164649083)
                ·
                  rfl

theorem cell20_1015859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_1015859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015859 prefixEnd_1015859 := by exact prefixLift 1015859
  have htrace : WordTrace (prefixWord ++ tailWord_1015859) baseStart_1015859 baseEnd_1015859 := by
    simpa [prefixWord, tailWord_1015859, baseEnd_1015859] using wordTrace_append hprefix tailTrace_1015859
  have hstable : (prefixWord ++ tailWord_1015859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015859).length < 2 ^ (prefixWord ++ tailWord_1015859).sum := by decide
  have hdescent : baseEnd_1015859 < baseStart_1015859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015900 : List Nat := [2, 2, 4, 1, 1, 2, 1, 4, 3]
def baseStart_1015900 : Nat := 118140960795 + 1015900 * 2 ^ 59
def prefixEnd_1015900 : Nat := 4983230072969 + 3 ^ 40 * 1015900 * 2
def baseEnd_1015900 : Nat := 463684441691271573580415

theorem tailTrace_1015900 : CollatzResearch.WordTrace tailWord_1015900 prefixEnd_1015900 463684441691271573580415 := by
  unfold tailWord_1015900
  simp only [CollatzResearch.WordTrace]
  refine ⟨18526458509787638375958577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24701944679716851167944769 18526458509787638375958577)
  ·
    refine ⟨13894843882340728781968933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18526458509787638375958577 13894843882340728781968933)
    ·
      refine ⟨2605283227938886646619175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13894843882340728781968933 2605283227938886646619175)
      ·
        refine ⟨3907924841908329969928763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2605283227938886646619175 3907924841908329969928763)
        ·
          refine ⟨5861887262862494954893145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3907924841908329969928763 5861887262862494954893145)
          ·
            refine ⟨4396415447146871216169859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5861887262862494954893145 4396415447146871216169859)
            ·
              refine ⟨6594623170720306824254789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396415447146871216169859 6594623170720306824254789)
              ·
                refine ⟨1236491844510057529547773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6594623170720306824254789 1236491844510057529547773)
                ·
                  refine ⟨463684441691271573580415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236491844510057529547773 463684441691271573580415)
                  ·
                    rfl

theorem cell20_1015900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_1015900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015900 prefixEnd_1015900 := by exact prefixLift 1015900
  have htrace : WordTrace (prefixWord ++ tailWord_1015900) baseStart_1015900 baseEnd_1015900 := by
    simpa [prefixWord, tailWord_1015900, baseEnd_1015900] using wordTrace_append hprefix tailTrace_1015900
  have hstable : (prefixWord ++ tailWord_1015900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015900).length < 2 ^ (prefixWord ++ tailWord_1015900).sum := by decide
  have hdescent : baseEnd_1015900 < baseStart_1015900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015921 : List Nat := [1, 2, 2, 2, 1, 1, 3, 5, 3]
def baseStart_1015921 : Nat := 118140960795 + 1015921 * 2 ^ 59
def prefixEnd_1015921 : Nat := 4983230072969 + 3 ^ 40 * 1015921 * 2
def baseEnd_1015921 : Nat := 463694026663488833880329

theorem tailTrace_1015921 : CollatzResearch.WordTrace tailWord_1015921 prefixEnd_1015921 463694026663488833880329 := by
  unfold tailWord_1015921
  simp only [CollatzResearch.WordTrace]
  refine ⟨37053682952499197338431617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24702455301666131558954411 37053682952499197338431617)
  ·
    refine ⟨27790262214374398003823713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37053682952499197338431617 27790262214374398003823713)
    ·
      refine ⟨20842696660780798502867785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27790262214374398003823713 20842696660780798502867785)
      ·
        refine ⟨15632022495585598877150839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20842696660780798502867785 15632022495585598877150839)
        ·
          refine ⟨23448033743378398315726259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15632022495585598877150839 23448033743378398315726259)
          ·
            refine ⟨35172050615067597473589389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23448033743378398315726259 35172050615067597473589389)
            ·
              refine ⟨13189518980650349052596021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35172050615067597473589389 13189518980650349052596021)
              ·
                refine ⟨1236517404435970223680877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13189518980650349052596021 1236517404435970223680877)
                ·
                  refine ⟨463694026663488833880329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236517404435970223680877 463694026663488833880329)
                  ·
                    rfl

theorem cell20_1015921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_1015921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015921 prefixEnd_1015921 := by exact prefixLift 1015921
  have htrace : WordTrace (prefixWord ++ tailWord_1015921) baseStart_1015921 baseEnd_1015921 := by
    simpa [prefixWord, tailWord_1015921, baseEnd_1015921] using wordTrace_append hprefix tailTrace_1015921
  have hstable : (prefixWord ++ tailWord_1015921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015921).length < 2 ^ (prefixWord ++ tailWord_1015921).sum := by decide
  have hdescent : baseEnd_1015921 < baseStart_1015921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015962 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_1015962 : Nat := 118140960795 + 1015962 * 2 ^ 59
def prefixEnd_1015962 : Nat := 4983230072969 + 3 ^ 40 * 1015962 * 2
def baseEnd_1015962 : Nat := 463712740180674913513495

theorem tailTrace_1015962 : CollatzResearch.WordTrace tailWord_1015962 prefixEnd_1015962 463712740180674913513495 := by
  unfold tailWord_1015962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9263794586337665335168535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24703452230233774227116093 9263794586337665335168535)
  ·
    refine ⟨13895691879506498002752803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9263794586337665335168535 13895691879506498002752803)
    ·
      refine ⟨20843537819259747004129205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13895691879506498002752803 20843537819259747004129205)
      ·
        refine ⟨1954081670555601281637113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20843537819259747004129205 1954081670555601281637113)
        ·
          refine ⟨1465561252916700961227835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1954081670555601281637113 1465561252916700961227835)
          ·
            refine ⟨2198341879375051441841753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465561252916700961227835 2198341879375051441841753)
            ·
              refine ⟨1648756409531288581381315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2198341879375051441841753 1648756409531288581381315)
              ·
                refine ⟨2473134614296932872071973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648756409531288581381315 2473134614296932872071973)
                ·
                  refine ⟨463712740180674913513495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2473134614296932872071973 463712740180674913513495)
                  ·
                    rfl

theorem cell20_1015962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_1015962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015962 prefixEnd_1015962 := by exact prefixLift 1015962
  have htrace : WordTrace (prefixWord ++ tailWord_1015962) baseStart_1015962 baseEnd_1015962 := by
    simpa [prefixWord, tailWord_1015962, baseEnd_1015962] using wordTrace_append hprefix tailTrace_1015962
  have hstable : (prefixWord ++ tailWord_1015962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015962).length < 2 ^ (prefixWord ++ tailWord_1015962).sum := by decide
  have hdescent : baseEnd_1015962 < baseStart_1015962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015973 : List Nat := [1, 3, 1, 2, 1, 3, 2, 7]
def baseStart_1015973 : Nat := 118140960795 + 1015973 * 2 ^ 59
def prefixEnd_1015973 : Nat := 4983230072969 + 3 ^ 40 * 1015973 * 2
def baseEnd_1015973 : Nat := 154572586960135921382261

theorem tailTrace_1015973 : CollatzResearch.WordTrace tailWord_1015973 prefixEnd_1015973 154572586960135921382261 := by
  unfold tailWord_1015973
  simp only [CollatzResearch.WordTrace]
  refine ⟨37055579548310810219324573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24703719698873873479549715 37055579548310810219324573)
  ·
    refine ⟨13895842330616553832246715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37055579548310810219324573 13895842330616553832246715)
    ·
      refine ⟨20843763495924830748370073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13895842330616553832246715 20843763495924830748370073)
      ·
        refine ⟨15632822621943623061277555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20843763495924830748370073 15632822621943623061277555)
        ·
          refine ⟨23449233932915434591916333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15632822621943623061277555 23449233932915434591916333)
          ·
            refine ⟨8793462724843287971968625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23449233932915434591916333 8793462724843287971968625)
            ·
              refine ⟨6595097043632465978976469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8793462724843287971968625 6595097043632465978976469)
              ·
                refine ⟨154572586960135921382261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6595097043632465978976469 154572586960135921382261)
                ·
                  rfl

theorem cell20_1015973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_1015973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015973 prefixEnd_1015973 := by exact prefixLift 1015973
  have htrace : WordTrace (prefixWord ++ tailWord_1015973) baseStart_1015973 baseEnd_1015973 := by
    simpa [prefixWord, tailWord_1015973, baseEnd_1015973] using wordTrace_append hprefix tailTrace_1015973
  have hstable : (prefixWord ++ tailWord_1015973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015973).length < 2 ^ (prefixWord ++ tailWord_1015973).sum := by decide
  have hdescent : baseEnd_1015973 < baseStart_1015973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015982 : List Nat := [4, 1, 4, 2, 2, 1, 2, 4]
def baseStart_1015982 : Nat := 118140960795 + 1015982 * 2 ^ 59
def prefixEnd_1015982 : Nat := 4983230072969 + 3 ^ 40 * 1015982 * 2
def baseEnd_1015982 : Nat := 154573956241881244282249

theorem tailTrace_1015982 : CollatzResearch.WordTrace tailWord_1015982 prefixEnd_1015982 154573956241881244282249 := by
  unfold tailWord_1015982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4631988475659775594550275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24703938536852136504268133 4631988475659775594550275)
  ·
    refine ⟨6947982713489663391825413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4631988475659775594550275 6947982713489663391825413)
    ·
      refine ⟨1302746758779311885967265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6947982713489663391825413 1302746758779311885967265)
      ·
        refine ⟨977060069084483914475449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1302746758779311885967265 977060069084483914475449)
        ·
          refine ⟨732795051813362935856587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 977060069084483914475449 732795051813362935856587)
          ·
            refine ⟨1099192577720044403784881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732795051813362935856587 1099192577720044403784881)
            ·
              refine ⟨824394433290033302838661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1099192577720044403784881 824394433290033302838661)
              ·
                refine ⟨154573956241881244282249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 824394433290033302838661 154573956241881244282249)
                ·
                  rfl

theorem cell20_1015982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_1015982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015982 prefixEnd_1015982 := by exact prefixLift 1015982
  have htrace : WordTrace (prefixWord ++ tailWord_1015982) baseStart_1015982 baseEnd_1015982 := by
    simpa [prefixWord, tailWord_1015982, baseEnd_1015982] using wordTrace_append hprefix tailTrace_1015982
  have hstable : (prefixWord ++ tailWord_1015982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015982).length < 2 ^ (prefixWord ++ tailWord_1015982).sum := by decide
  have hdescent : baseEnd_1015982 < baseStart_1015982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015996 : List Nat := [2, 2, 2, 3, 4, 1, 1, 3, 2]
def baseStart_1015996 : Nat := 118140960795 + 1015996 * 2 ^ 59
def prefixEnd_1015996 : Nat := 4983230072969 + 3 ^ 40 * 1015996 * 2
def baseEnd_1015996 : Nat := 463728258707121906380023

theorem tailTrace_1015996 : CollatzResearch.WordTrace tailWord_1015996 prefixEnd_1015996 463728258707121906380023 := by
  unfold tailWord_1015996
  simp only [CollatzResearch.WordTrace]
  refine ⟨18528209213613742573705921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24704278951484990098274561 18528209213613742573705921)
  ·
    refine ⟨13896156910210306930279441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18528209213613742573705921 13896156910210306930279441)
    ·
      refine ⟨10422117682657730197709581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13896156910210306930279441 10422117682657730197709581)
      ·
        refine ⟨3908294130996648824141093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10422117682657730197709581 3908294130996648824141093)
        ·
          refine ⟨732805149561871654526455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3908294130996648824141093 732805149561871654526455)
          ·
            refine ⟨1099207724342807481789683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732805149561871654526455 1099207724342807481789683)
            ·
              refine ⟨1648811586514211222684525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099207724342807481789683 1648811586514211222684525)
              ·
                refine ⟨618304344942829208506697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1648811586514211222684525 618304344942829208506697)
                ·
                  refine ⟨463728258707121906380023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618304344942829208506697 463728258707121906380023)
                  ·
                    rfl

theorem cell20_1015996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_1015996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1015996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1015996 prefixEnd_1015996 := by exact prefixLift 1015996
  have htrace : WordTrace (prefixWord ++ tailWord_1015996) baseStart_1015996 baseEnd_1015996 := by
    simpa [prefixWord, tailWord_1015996, baseEnd_1015996] using wordTrace_append hprefix tailTrace_1015996
  have hstable : (prefixWord ++ tailWord_1015996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015996).length < 2 ^ (prefixWord ++ tailWord_1015996).sum := by decide
  have hdescent : baseEnd_1015996 < baseStart_1015996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016000 : List Nat := [2, 1, 1, 2, 5, 1, 3, 3, 2]
def baseStart_1016000 : Nat := 118140960795 + 1016000 * 2 ^ 59
def prefixEnd_1016000 : Nat := 4983230072969 + 3 ^ 40 * 1016000 * 2
def baseEnd_1016000 : Nat := 463730084416115670246673

theorem tailTrace_1016000 : CollatzResearch.WordTrace tailWord_1016000 prefixEnd_1016000 463730084416115670246673 := by
  unfold tailWord_1016000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18528282159606496915278727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24704376212808662553704969 18528282159606496915278727)
  ·
    refine ⟨27792423239409745372918091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18528282159606496915278727 27792423239409745372918091)
    ·
      refine ⟨41688634859114618059377137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27792423239409745372918091 41688634859114618059377137)
      ·
        refine ⟨31266476144335963544532853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41688634859114618059377137 31266476144335963544532853)
        ·
          refine ⟨2931232138531496582299955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31266476144335963544532853 2931232138531496582299955)
          ·
            refine ⟨4396848207797244873449933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931232138531496582299955 4396848207797244873449933)
            ·
              refine ⟨1648818077923966827543725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4396848207797244873449933 1648818077923966827543725)
              ·
                refine ⟨618306779221487560328897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1648818077923966827543725 618306779221487560328897)
                ·
                  refine ⟨463730084416115670246673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618306779221487560328897 463730084416115670246673)
                  ·
                    rfl

theorem cell20_1016000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 2].length) (baseStart_1016000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016000 prefixEnd_1016000 := by exact prefixLift 1016000
  have htrace : WordTrace (prefixWord ++ tailWord_1016000) baseStart_1016000 baseEnd_1016000 := by
    simpa [prefixWord, tailWord_1016000, baseEnd_1016000] using wordTrace_append hprefix tailTrace_1016000
  have hstable : (prefixWord ++ tailWord_1016000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016000).length < 2 ^ (prefixWord ++ tailWord_1016000).sum := by decide
  have hdescent : baseEnd_1016000 < baseStart_1016000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016042 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1016042 : Nat := 118140960795 + 1016042 * 2 ^ 59
def prefixEnd_1016042 : Nat := 4983230072969 + 3 ^ 40 * 1016042 * 2
def baseEnd_1016042 : Nat := 463749254360550190846501

theorem tailTrace_1016042 : CollatzResearch.WordTrace tailWord_1016042 prefixEnd_1016042 463749254360550190846501 := by
  unfold tailWord_1016042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9264524046265208750896595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24705397456707223335724253 9264524046265208750896595)
  ·
    refine ⟨13896786069397813126344893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9264524046265208750896595 13896786069397813126344893)
    ·
      refine ⟨5211294776024179922379335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13896786069397813126344893 5211294776024179922379335)
      ·
        refine ⟨7816942164036269883569003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5211294776024179922379335 7816942164036269883569003)
        ·
          refine ⟨11725413246054404825353505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7816942164036269883569003 11725413246054404825353505)
          ·
            refine ⟨8794059934540803619015129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11725413246054404825353505 8794059934540803619015129)
            ·
              refine ⟨6595544950905602714261347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8794059934540803619015129 6595544950905602714261347)
              ·
                refine ⟨9893317426358404071392021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6595544950905602714261347 9893317426358404071392021)
                ·
                  refine ⟨463749254360550190846501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9893317426358404071392021 463749254360550190846501)
                  ·
                    rfl

theorem cell20_1016042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1016042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016042 prefixEnd_1016042 := by exact prefixLift 1016042
  have htrace : WordTrace (prefixWord ++ tailWord_1016042) baseStart_1016042 baseEnd_1016042 := by
    simpa [prefixWord, tailWord_1016042, baseEnd_1016042] using wordTrace_append hprefix tailTrace_1016042
  have hstable : (prefixWord ++ tailWord_1016042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016042).length < 2 ^ (prefixWord ++ tailWord_1016042).sum := by decide
  have hdescent : baseEnd_1016042 < baseStart_1016042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016049 : List Nat := [1, 2, 2, 2, 2, 1, 4, 6]
def baseStart_1016049 : Nat := 118140960795 + 1016049 * 2 ^ 59
def prefixEnd_1016049 : Nat := 4983230072969 + 3 ^ 40 * 1016049 * 2
def baseEnd_1016049 : Nat := 154584149783763092537713

theorem tailTrace_1016049 : CollatzResearch.WordTrace tailWord_1016049 prefixEnd_1016049 154584149783763092537713 := by
  unfold tailWord_1016049
  simp only [CollatzResearch.WordTrace]
  refine ⟨37058351496035475199091201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24705567664023650132727467 37058351496035475199091201)
  ·
    refine ⟨27793763622026606399318401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37058351496035475199091201 27793763622026606399318401)
    ·
      refine ⟨20845322716519954799488801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27793763622026606399318401 20845322716519954799488801)
      ·
        refine ⟨15633992037389966099616601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20845322716519954799488801 15633992037389966099616601)
        ·
          refine ⟨11725494028042474574712451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15633992037389966099616601 11725494028042474574712451)
          ·
            refine ⟨17588241042063711862068677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11725494028042474574712451 17588241042063711862068677)
            ·
              refine ⟨3297795195386945974137877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17588241042063711862068677 3297795195386945974137877)
              ·
                refine ⟨154584149783763092537713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3297795195386945974137877 154584149783763092537713)
                ·
                  rfl

theorem cell20_1016049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_1016049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016049 prefixEnd_1016049 := by exact prefixLift 1016049
  have htrace : WordTrace (prefixWord ++ tailWord_1016049) baseStart_1016049 baseEnd_1016049 := by
    simpa [prefixWord, tailWord_1016049, baseEnd_1016049] using wordTrace_append hprefix tailTrace_1016049
  have hstable : (prefixWord ++ tailWord_1016049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016049).length < 2 ^ (prefixWord ++ tailWord_1016049).sum := by decide
  have hdescent : baseEnd_1016049 < baseStart_1016049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016056 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_1016056 : Nat := 118140960795 + 1016056 * 2 ^ 59
def prefixEnd_1016056 : Nat := 4983230072969 + 3 ^ 40 * 1016056 * 2
def baseEnd_1016056 : Nat := 463755644342028364379777

theorem tailTrace_1016056 : CollatzResearch.WordTrace tailWord_1016056 prefixEnd_1016056 463755644342028364379777 := by
  unfold tailWord_1016056
  simp only [CollatzResearch.WordTrace]
  refine ⟨18529303403505057697298011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24705737871340076929730681 18529303403505057697298011)
  ·
    refine ⟨27793955105257586545947017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18529303403505057697298011 27793955105257586545947017)
    ·
      refine ⟨20845466328943189909460263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27793955105257586545947017 20845466328943189909460263)
      ·
        refine ⟨31268199493414784864190395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20845466328943189909460263 31268199493414784864190395)
        ·
          refine ⟨46902299240122177296285593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31268199493414784864190395 46902299240122177296285593)
          ·
            refine ⟨35176724430091632972214195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46902299240122177296285593 35176724430091632972214195)
            ·
              refine ⟨52765086645137449458321293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35176724430091632972214195 52765086645137449458321293)
              ·
                refine ⟨19786907491926543546870485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52765086645137449458321293 19786907491926543546870485)
                ·
                  refine ⟨463755644342028364379777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19786907491926543546870485 463755644342028364379777)
                  ·
                    rfl

theorem cell20_1016056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_1016056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016056 prefixEnd_1016056 := by exact prefixLift 1016056
  have htrace : WordTrace (prefixWord ++ tailWord_1016056) baseStart_1016056 baseEnd_1016056 := by
    simpa [prefixWord, tailWord_1016056, baseEnd_1016056] using wordTrace_append hprefix tailTrace_1016056
  have hstable : (prefixWord ++ tailWord_1016056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016056).length < 2 ^ (prefixWord ++ tailWord_1016056).sum := by decide
  have hdescent : baseEnd_1016056 < baseStart_1016056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016066 : List Nat := [3, 4, 1, 1, 2, 9]
def baseStart_1016066 : Nat := 118140960795 + 1016066 * 2 ^ 59
def prefixEnd_1016066 : Nat := 4983230072969 + 3 ^ 40 * 1016066 * 2
def baseEnd_1016066 : Nat := 17176304022759732372089

theorem tailTrace_1016066 : CollatzResearch.WordTrace tailWord_1016066 prefixEnd_1016066 17176304022759732372089 := by
  unfold tailWord_1016066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9264742884243471775615013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24705981024649258068306701 9264742884243471775615013)
  ·
    refine ⟨1737139290795650957927815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9264742884243471775615013 1737139290795650957927815)
    ·
      refine ⟨2605708936193476436891723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1737139290795650957927815 2605708936193476436891723)
      ·
        refine ⟨3908563404290214655337585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2605708936193476436891723 3908563404290214655337585)
        ·
          refine ⟨2931422553217660991503189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3908563404290214655337585 2931422553217660991503189)
          ·
            refine ⟨17176304022759732372089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2931422553217660991503189 17176304022759732372089)
            ·
              rfl

theorem cell20_1016066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 9].length) (baseStart_1016066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016066 prefixEnd_1016066 := by exact prefixLift 1016066
  have htrace : WordTrace (prefixWord ++ tailWord_1016066) baseStart_1016066 baseEnd_1016066 := by
    simpa [prefixWord, tailWord_1016066, baseEnd_1016066] using wordTrace_append hprefix tailTrace_1016066
  have hstable : (prefixWord ++ tailWord_1016066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016066).length < 2 ^ (prefixWord ++ tailWord_1016066).sum := by decide
  have hdescent : baseEnd_1016066 < baseStart_1016066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016073 : List Nat := [1, 2, 1, 1, 3, 4, 1, 4, 3]
def baseStart_1016073 : Nat := 118140960795 + 1016073 * 2 ^ 59
def prefixEnd_1016073 : Nat := 4983230072969 + 3 ^ 40 * 1016073 * 2
def baseEnd_1016073 : Nat := 463763403605251860813041

theorem tailTrace_1016073 : CollatzResearch.WordTrace tailWord_1016073 prefixEnd_1016073 463763403605251860813041 := by
  unfold tailWord_1016073
  simp only [CollatzResearch.WordTrace]
  refine ⟨37059226847948527297964873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24706151231965684865309915 37059226847948527297964873)
  ·
    refine ⟨27794420135961395473473655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37059226847948527297964873 27794420135961395473473655)
    ·
      refine ⟨41691630203942093210210483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27794420135961395473473655 41691630203942093210210483)
      ·
        refine ⟨62537445305913139815315725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41691630203942093210210483 62537445305913139815315725)
        ·
          refine ⟨23451541989717427430743397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62537445305913139815315725 23451541989717427430743397)
          ·
            refine ⟨4397164123072017643264387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23451541989717427430743397 4397164123072017643264387)
            ·
              refine ⟨6595746184608026464896581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397164123072017643264387 6595746184608026464896581)
              ·
                refine ⟨1236702409614004962168109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6595746184608026464896581 1236702409614004962168109)
                ·
                  refine ⟨463763403605251860813041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236702409614004962168109 463763403605251860813041)
                  ·
                    rfl

theorem cell20_1016073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_1016073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016073 prefixEnd_1016073 := by exact prefixLift 1016073
  have htrace : WordTrace (prefixWord ++ tailWord_1016073) baseStart_1016073 baseEnd_1016073 := by
    simpa [prefixWord, tailWord_1016073, baseEnd_1016073] using wordTrace_append hprefix tailTrace_1016073
  have hstable : (prefixWord ++ tailWord_1016073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016073).length < 2 ^ (prefixWord ++ tailWord_1016073).sum := by decide
  have hdescent : baseEnd_1016073 < baseStart_1016073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016110 : List Nat := [4, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_1016110 : Nat := 118140960795 + 1016110 * 2 ^ 59
def prefixEnd_1016110 : Nat := 4983230072969 + 3 ^ 40 * 1016110 * 2
def baseEnd_1016110 : Nat := 463780291413444176579557

theorem tailTrace_1016110 : CollatzResearch.WordTrace tailWord_1016110 prefixEnd_1016110 463780291413444176579557 := by
  unfold tailWord_1016110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4632572043601810327132723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24707050899209655078041189 4632572043601810327132723)
  ·
    refine ⟨6948858065402715490699085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4632572043601810327132723 6948858065402715490699085)
    ·
      refine ⟨2605821774526018309012157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6948858065402715490699085 2605821774526018309012157)
      ·
        refine ⟨977183165447256865879559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2605821774526018309012157 977183165447256865879559)
        ·
          refine ⟨1465774748170885298819339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977183165447256865879559 1465774748170885298819339)
          ·
            refine ⟨2198662122256327948229009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465774748170885298819339 2198662122256327948229009)
            ·
              refine ⟨1648996591692245961171757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2198662122256327948229009 1648996591692245961171757)
              ·
                refine ⟨618373721884592235439409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1648996591692245961171757 618373721884592235439409)
                ·
                  refine ⟨463780291413444176579557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618373721884592235439409 463780291413444176579557)
                  ·
                    rfl

theorem cell20_1016110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_1016110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016110 prefixEnd_1016110 := by exact prefixLift 1016110
  have htrace : WordTrace (prefixWord ++ tailWord_1016110) baseStart_1016110 baseEnd_1016110 := by
    simpa [prefixWord, tailWord_1016110, baseEnd_1016110] using wordTrace_append hprefix tailTrace_1016110
  have hstable : (prefixWord ++ tailWord_1016110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016110).length < 2 ^ (prefixWord ++ tailWord_1016110).sum := by decide
  have hdescent : baseEnd_1016110 < baseStart_1016110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016135 : List Nat := [1, 1, 4, 1, 2, 2, 1, 6, 2]
def baseStart_1016135 : Nat := 118140960795 + 1016135 * 2 ^ 59
def prefixEnd_1016135 : Nat := 4983230072969 + 3 ^ 40 * 1016135 * 2
def baseEnd_1016135 : Nat := 463791702094655200746121

theorem tailTrace_1016135 : CollatzResearch.WordTrace tailWord_1016135 prefixEnd_1016135 463791702094655200746121 := by
  unfold tailWord_1016135
  simp only [CollatzResearch.WordTrace]
  refine ⟨37061488173723911886721859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24707658782482607924481239 37061488173723911886721859)
  ·
    refine ⟨55592232260585867830082789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37061488173723911886721859 55592232260585867830082789)
    ·
      refine ⟨10423543548859850218140523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55592232260585867830082789 10423543548859850218140523)
      ·
        refine ⟨15635315323289775327210785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10423543548859850218140523 15635315323289775327210785)
        ·
          refine ⟨11726486492467331495408089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15635315323289775327210785 11726486492467331495408089)
          ·
            refine ⟨8794864869350498621556067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11726486492467331495408089 8794864869350498621556067)
            ·
              refine ⟨13192297304025747932334101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8794864869350498621556067 13192297304025747932334101)
              ·
                refine ⟨618388936126206934328161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13192297304025747932334101 618388936126206934328161)
                ·
                  refine ⟨463791702094655200746121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618388936126206934328161 463791702094655200746121)
                  ·
                    rfl

theorem cell20_1016135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 2].length) (baseStart_1016135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016135 prefixEnd_1016135 := by exact prefixLift 1016135
  have htrace : WordTrace (prefixWord ++ tailWord_1016135) baseStart_1016135 baseEnd_1016135 := by
    simpa [prefixWord, tailWord_1016135, baseEnd_1016135] using wordTrace_append hprefix tailTrace_1016135
  have hstable : (prefixWord ++ tailWord_1016135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016135).length < 2 ^ (prefixWord ++ tailWord_1016135).sum := by decide
  have hdescent : baseEnd_1016135 < baseStart_1016135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016163 : List Nat := [1, 1, 1, 5, 2, 1, 3, 6]
def baseStart_1016163 : Nat := 118140960795 + 1016163 * 2 ^ 59
def prefixEnd_1016163 : Nat := 4983230072969 + 3 ^ 40 * 1016163 * 2
def baseEnd_1016163 : Nat := 154601494019203849270891

theorem tailTrace_1016163 : CollatzResearch.WordTrace tailWord_1016163 prefixEnd_1016163 154601494019203849270891 := by
  unfold tailWord_1016163
  simp only [CollatzResearch.WordTrace]
  refine ⟨37062509417622472668741143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24708339611748315112494095 37062509417622472668741143)
  ·
    refine ⟨55593764126433709003111715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37062509417622472668741143 55593764126433709003111715)
    ·
      refine ⟨83390646189650563504667573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55593764126433709003111715 83390646189650563504667573)
      ·
        refine ⟨7817873080279740328562585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83390646189650563504667573 7817873080279740328562585)
        ·
          refine ⟨5863404810209805246421939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7817873080279740328562585 5863404810209805246421939)
          ·
            refine ⟨8795107215314707869632909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5863404810209805246421939 8795107215314707869632909)
            ·
              refine ⟨3298165205743015451112341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8795107215314707869632909 3298165205743015451112341)
              ·
                refine ⟨154601494019203849270891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3298165205743015451112341 154601494019203849270891)
                ·
                  rfl

theorem cell20_1016163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_1016163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016163 prefixEnd_1016163 := by exact prefixLift 1016163
  have htrace : WordTrace (prefixWord ++ tailWord_1016163) baseStart_1016163 baseEnd_1016163 := by
    simpa [prefixWord, tailWord_1016163, baseEnd_1016163] using wordTrace_append hprefix tailTrace_1016163
  have hstable : (prefixWord ++ tailWord_1016163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016163).length < 2 ^ (prefixWord ++ tailWord_1016163).sum := by decide
  have hdescent : baseEnd_1016163 < baseStart_1016163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016201 : List Nat := [1, 2, 1, 1, 6, 1, 1, 7]
def baseStart_1016201 : Nat := 118140960795 + 1016201 * 2 ^ 59
def prefixEnd_1016201 : Nat := 4983230072969 + 3 ^ 40 * 1016201 * 2
def baseEnd_1016201 : Nat := 154607275431017434848617

theorem tailTrace_1016201 : CollatzResearch.WordTrace tailWord_1016201 prefixEnd_1016201 154607275431017434848617 := by
  unfold tailWord_1016201
  simp only [CollatzResearch.WordTrace]
  refine ⟨37063895391484805158624457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24709263594323203439082971 37063895391484805158624457)
  ·
    refine ⟨27797921543613603868968343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37063895391484805158624457 27797921543613603868968343)
    ·
      refine ⟨41696882315420405803452515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27797921543613603868968343 41696882315420405803452515)
      ·
        refine ⟨62545323473130608705178773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41696882315420405803452515 62545323473130608705178773)
        ·
          refine ⟨2931812037802997283055255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62545323473130608705178773 2931812037802997283055255)
          ·
            refine ⟨4397718056704495924582883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931812037802997283055255 4397718056704495924582883)
            ·
              refine ⟨6596577085056743886874325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397718056704495924582883 6596577085056743886874325)
              ·
                refine ⟨154607275431017434848617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6596577085056743886874325 154607275431017434848617)
                ·
                  rfl

theorem cell20_1016201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_1016201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016201 prefixEnd_1016201 := by exact prefixLift 1016201
  have htrace : WordTrace (prefixWord ++ tailWord_1016201) baseStart_1016201 baseEnd_1016201 := by
    simpa [prefixWord, tailWord_1016201, baseEnd_1016201] using wordTrace_append hprefix tailTrace_1016201
  have hstable : (prefixWord ++ tailWord_1016201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016201).length < 2 ^ (prefixWord ++ tailWord_1016201).sum := by decide
  have hdescent : baseEnd_1016201 < baseStart_1016201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016204 : List Nat := [2, 2, 1, 2, 1, 4, 4, 1, 3]
def baseStart_1016204 : Nat := 118140960795 + 1016204 * 2 ^ 59
def prefixEnd_1016204 : Nat := 4983230072969 + 3 ^ 40 * 1016204 * 2
def baseEnd_1016204 : Nat := 463823195574797627445839

theorem tailTrace_1016204 : CollatzResearch.WordTrace tailWord_1016204 prefixEnd_1016204 463823195574797627445839 := by
  unfold tailWord_1016204
  simp only [CollatzResearch.WordTrace]
  refine ⟨18532002405236968335491833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24709336540315957780655777 18532002405236968335491833)
  ·
    refine ⟨13899001803927726251618875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18532002405236968335491833 13899001803927726251618875)
    ·
      refine ⟨20848502705891589377428313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13899001803927726251618875 20848502705891589377428313)
      ·
        refine ⟨15636377029418692033071235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20848502705891589377428313 15636377029418692033071235)
        ·
          refine ⟨23454565544128038049606853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15636377029418692033071235 23454565544128038049606853)
          ·
            refine ⟨4397731039524007134301285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23454565544128038049606853 4397731039524007134301285)
            ·
              refine ⟨824574569910751337681491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4397731039524007134301285 824574569910751337681491)
              ·
                refine ⟨1236861854866127006522237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824574569910751337681491 1236861854866127006522237)
                ·
                  refine ⟨463823195574797627445839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236861854866127006522237 463823195574797627445839)
                  ·
                    rfl

theorem cell20_1016204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_1016204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016204 prefixEnd_1016204 := by exact prefixLift 1016204
  have htrace : WordTrace (prefixWord ++ tailWord_1016204) baseStart_1016204 baseEnd_1016204 := by
    simpa [prefixWord, tailWord_1016204, baseEnd_1016204] using wordTrace_append hprefix tailTrace_1016204
  have hstable : (prefixWord ++ tailWord_1016204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016204).length < 2 ^ (prefixWord ++ tailWord_1016204).sum := by decide
  have hdescent : baseEnd_1016204 < baseStart_1016204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016263 : List Nat := [1, 1, 4, 1, 1, 4, 2, 3, 3]
def baseStart_1016263 : Nat := 118140960795 + 1016263 * 2 ^ 59
def prefixEnd_1016263 : Nat := 4983230072969 + 3 ^ 40 * 1016263 * 2
def baseEnd_1016263 : Nat := 463850124782455644478931

theorem tailTrace_1016263 : CollatzResearch.WordTrace tailWord_1016263 prefixEnd_1016263 463850124782455644478931 := by
  unfold tailWord_1016263
  simp only [CollatzResearch.WordTrace]
  refine ⟨37066156717260189747381443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24710771144840126498254295 37066156717260189747381443)
  ·
    refine ⟨55599235075890284621072165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37066156717260189747381443 55599235075890284621072165)
    ·
      refine ⟨10424856576729428366451031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55599235075890284621072165 10424856576729428366451031)
      ·
        refine ⟨15637284865094142549676547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10424856576729428366451031 15637284865094142549676547)
        ·
          refine ⟨23455927297641213824514821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15637284865094142549676547 23455927297641213824514821)
          ·
            refine ⟨4397986368307727592096529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23455927297641213824514821 4397986368307727592096529)
            ·
              refine ⟨3298489776230795694072397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4397986368307727592096529 3298489776230795694072397)
              ·
                refine ⟨1236933666086548385277149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3298489776230795694072397 1236933666086548385277149)
                ·
                  refine ⟨463850124782455644478931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236933666086548385277149 463850124782455644478931)
                  ·
                    rfl

theorem cell20_1016263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 3].length) (baseStart_1016263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016263 prefixEnd_1016263 := by exact prefixLift 1016263
  have htrace : WordTrace (prefixWord ++ tailWord_1016263) baseStart_1016263 baseEnd_1016263 := by
    simpa [prefixWord, tailWord_1016263, baseEnd_1016263] using wordTrace_append hprefix tailTrace_1016263
  have hstable : (prefixWord ++ tailWord_1016263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016263).length < 2 ^ (prefixWord ++ tailWord_1016263).sum := by decide
  have hdescent : baseEnd_1016263 < baseStart_1016263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016287 : List Nat := [1, 1, 2, 3, 3, 2, 1, 5, 2]
def baseStart_1016287 : Nat := 118140960795 + 1016287 * 2 ^ 59
def prefixEnd_1016287 : Nat := 4983230072969 + 3 ^ 40 * 1016287 * 2
def baseEnd_1016287 : Nat := 463861079036418227678833

theorem tailTrace_1016287 : CollatzResearch.WordTrace tailWord_1016287 prefixEnd_1016287 463861079036418227678833 := by
  unfold tailWord_1016287
  simp only [CollatzResearch.WordTrace]
  refine ⟨37067032069173241846255115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24711354712782161230836743 37067032069173241846255115)
  ·
    refine ⟨55600548103759862769382673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37067032069173241846255115 55600548103759862769382673)
    ·
      refine ⟨41700411077819897077037005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55600548103759862769382673 41700411077819897077037005)
      ·
        refine ⟨15637654154182461403888877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41700411077819897077037005 15637654154182461403888877)
        ·
          refine ⟨5864120307818423026458329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15637654154182461403888877 5864120307818423026458329)
          ·
            refine ⟨4398090230863817269843747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5864120307818423026458329 4398090230863817269843747)
            ·
              refine ⟨6597135346295725904765621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4398090230863817269843747 6597135346295725904765621)
              ·
                refine ⟨618481438715224303571777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6597135346295725904765621 618481438715224303571777)
                ·
                  refine ⟨463861079036418227678833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618481438715224303571777 463861079036418227678833)
                  ·
                    rfl

theorem cell20_1016287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 2].length) (baseStart_1016287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016287 prefixEnd_1016287 := by exact prefixLift 1016287
  have htrace : WordTrace (prefixWord ++ tailWord_1016287) baseStart_1016287 baseEnd_1016287 := by
    simpa [prefixWord, tailWord_1016287, baseEnd_1016287] using wordTrace_append hprefix tailTrace_1016287
  have hstable : (prefixWord ++ tailWord_1016287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016287).length < 2 ^ (prefixWord ++ tailWord_1016287).sum := by decide
  have hdescent : baseEnd_1016287 < baseStart_1016287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016329 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 6]
def baseStart_1016329 : Nat := 118140960795 + 1016329 * 2 ^ 59
def prefixEnd_1016329 : Nat := 4983230072969 + 3 ^ 40 * 1016329 * 2
def baseEnd_1016329 : Nat := 463880248980852748278661

theorem tailTrace_1016329 : CollatzResearch.WordTrace tailWord_1016329 prefixEnd_1016329 463880248980852748278661 := by
  unfold tailWord_1016329
  simp only [CollatzResearch.WordTrace]
  refine ⟨37068563935021083019284041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24712375956680722012856027 37068563935021083019284041)
  ·
    refine ⟨27801422951265812264463031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37068563935021083019284041 27801422951265812264463031)
    ·
      refine ⟨41702134426898718396694547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27801422951265812264463031 41702134426898718396694547)
      ·
        refine ⟨62553201640348077595041821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41702134426898718396694547 62553201640348077595041821)
        ·
          refine ⟨23457450615130529098140683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62553201640348077595041821 23457450615130529098140683)
          ·
            refine ⟨35186175922695793647211025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23457450615130529098140683 35186175922695793647211025)
            ·
              refine ⟨26389631942021845235408269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35186175922695793647211025 26389631942021845235408269)
              ·
                refine ⟨9896111978258191963278101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26389631942021845235408269 9896111978258191963278101)
                ·
                  refine ⟨463880248980852748278661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9896111978258191963278101 463880248980852748278661)
                  ·
                    rfl

theorem cell20_1016329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_1016329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016329 prefixEnd_1016329 := by exact prefixLift 1016329
  have htrace : WordTrace (prefixWord ++ tailWord_1016329) baseStart_1016329 baseEnd_1016329 := by
    simpa [prefixWord, tailWord_1016329, baseEnd_1016329] using wordTrace_append hprefix tailTrace_1016329
  have hstable : (prefixWord ++ tailWord_1016329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016329).length < 2 ^ (prefixWord ++ tailWord_1016329).sum := by decide
  have hdescent : baseEnd_1016329 < baseStart_1016329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016332 : List Nat := [2, 2, 1, 2, 4, 1, 4, 4]
def baseStart_1016332 : Nat := 118140960795 + 1016332 * 2 ^ 59
def prefixEnd_1016332 : Nat := 4983230072969 + 3 ^ 40 * 1016332 * 2
def baseEnd_1016332 : Nat := 154627206087532690392883

theorem tailTrace_1016332 : CollatzResearch.WordTrace tailWord_1016332 prefixEnd_1016332 154627206087532690392883 := by
  unfold tailWord_1016332
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534336677005107265821625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24712448902673476354428833 18534336677005107265821625)
  ·
    refine ⟨13900752507753830449366219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18534336677005107265821625 13900752507753830449366219)
    ·
      refine ⟨20851128761630745674049329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13900752507753830449366219 20851128761630745674049329)
      ·
        refine ⟨15638346571223059255536997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20851128761630745674049329 15638346571223059255536997)
        ·
          refine ⟨2932189982104323610413187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15638346571223059255536997 2932189982104323610413187)
          ·
            refine ⟨4398284973156485415619781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932189982104323610413187 4398284973156485415619781)
            ·
              refine ⟨824678432466841015428709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4398284973156485415619781 824678432466841015428709)
              ·
                refine ⟨154627206087532690392883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 824678432466841015428709 154627206087532690392883)
                ·
                  rfl

theorem cell20_1016332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_1016332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016332 prefixEnd_1016332 := by exact prefixLift 1016332
  have htrace : WordTrace (prefixWord ++ tailWord_1016332) baseStart_1016332 baseEnd_1016332 := by
    simpa [prefixWord, tailWord_1016332, baseEnd_1016332] using wordTrace_append hprefix tailTrace_1016332
  have hstable : (prefixWord ++ tailWord_1016332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016332).length < 2 ^ (prefixWord ++ tailWord_1016332).sum := by decide
  have hdescent : baseEnd_1016332 < baseStart_1016332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016359 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 4]
def baseStart_1016359 : Nat := 118140960795 + 1016359 * 2 ^ 59
def prefixEnd_1016359 : Nat := 4983230072969 + 3 ^ 40 * 1016359 * 2
def baseEnd_1016359 : Nat := 463893941798305977278539

theorem tailTrace_1016359 : CollatzResearch.WordTrace tailWord_1016359 prefixEnd_1016359 463893941798305977278539 := by
  unfold tailWord_1016359
  simp only [CollatzResearch.WordTrace]
  refine ⟨37069658124912398142876131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24713105416608265428584087 37069658124912398142876131)
  ·
    refine ⟨55604487187368597214314197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37069658124912398142876131 55604487187368597214314197)
    ·
      refine ⟨1303230168453951497210489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 55604487187368597214314197 1303230168453951497210489)
      ·
        refine ⟨977422626340463622907867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1303230168453951497210489 977422626340463622907867)
        ·
          refine ⟨1466133939510695434361801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977422626340463622907867 1466133939510695434361801)
          ·
            refine ⟨1099600454633021575771351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1466133939510695434361801 1099600454633021575771351)
            ·
              refine ⟨1649400681949532363657027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099600454633021575771351 1649400681949532363657027)
              ·
                refine ⟨2474101022924298545485541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649400681949532363657027 2474101022924298545485541)
                ·
                  refine ⟨463893941798305977278539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474101022924298545485541 463893941798305977278539)
                  ·
                    rfl

theorem cell20_1016359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 4].length) (baseStart_1016359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016359 prefixEnd_1016359 := by exact prefixLift 1016359
  have htrace : WordTrace (prefixWord ++ tailWord_1016359) baseStart_1016359 baseEnd_1016359 := by
    simpa [prefixWord, tailWord_1016359, baseEnd_1016359] using wordTrace_append hprefix tailTrace_1016359
  have hstable : (prefixWord ++ tailWord_1016359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016359).length < 2 ^ (prefixWord ++ tailWord_1016359).sum := by decide
  have hdescent : baseEnd_1016359 < baseStart_1016359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016377 : List Nat := [1, 2, 1, 5, 1, 1, 3, 3, 3]
def baseStart_1016377 : Nat := 118140960795 + 1016377 * 2 ^ 59
def prefixEnd_1016377 : Nat := 4983230072969 + 3 ^ 40 * 1016377 * 2
def baseEnd_1016377 : Nat := 463902157488777914678465

theorem tailTrace_1016377 : CollatzResearch.WordTrace tailWord_1016377 prefixEnd_1016377 463902157488777914678465 := by
  unfold tailWord_1016377
  simp only [CollatzResearch.WordTrace]
  refine ⟨37070314638847187217031385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24713543092564791478020923 37070314638847187217031385)
  ·
    refine ⟨27802735979135390412773539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37070314638847187217031385 27802735979135390412773539)
    ·
      refine ⟨41704103968703085619160309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27802735979135390412773539 41704103968703085619160309)
      ·
        refine ⟨3909759747065914276796279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41704103968703085619160309 3909759747065914276796279)
        ·
          refine ⟨5864639620598871415194419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909759747065914276796279 5864639620598871415194419)
          ·
            refine ⟨8796959430898307122791629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864639620598871415194419 8796959430898307122791629)
            ·
              refine ⟨3298859786586865171046861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8796959430898307122791629 3298859786586865171046861)
              ·
                refine ⟨1237072419970074439142573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3298859786586865171046861 1237072419970074439142573)
                ·
                  refine ⟨463902157488777914678465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237072419970074439142573 463902157488777914678465)
                  ·
                    rfl

theorem cell20_1016377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_1016377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016377 prefixEnd_1016377 := by exact prefixLift 1016377
  have htrace : WordTrace (prefixWord ++ tailWord_1016377) baseStart_1016377 baseEnd_1016377 := by
    simpa [prefixWord, tailWord_1016377, baseEnd_1016377] using wordTrace_append hprefix tailTrace_1016377
  have hstable : (prefixWord ++ tailWord_1016377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016377).length < 2 ^ (prefixWord ++ tailWord_1016377).sum := by decide
  have hdescent : baseEnd_1016377 < baseStart_1016377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016391 : List Nat := [1, 1, 4, 1, 4, 1, 2, 6]
def baseStart_1016391 : Nat := 118140960795 + 1016391 * 2 ^ 59
def prefixEnd_1016391 : Nat := 4983230072969 + 3 ^ 40 * 1016391 * 2
def baseEnd_1016391 : Nat := 154636182490085362737247

theorem tailTrace_1016391 : CollatzResearch.WordTrace tailWord_1016391 prefixEnd_1016391 154636182490085362737247 := by
  unfold tailWord_1016391
  simp only [CollatzResearch.WordTrace]
  refine ⟨37070825260796467608041027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24713883507197645072027351 37070825260796467608041027)
  ·
    refine ⟨55606237891194701412061541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37070825260796467608041027 55606237891194701412061541)
    ·
      refine ⟨10426169604599006514761539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55606237891194701412061541 10426169604599006514761539)
      ·
        refine ⟨15639254406898509772142309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10426169604599006514761539 15639254406898509772142309)
        ·
          refine ⟨2932360201293470582276683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15639254406898509772142309 2932360201293470582276683)
          ·
            refine ⟨4398540301940205873415025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932360201293470582276683 4398540301940205873415025)
            ·
              refine ⟨3298905226455154405061269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4398540301940205873415025 3298905226455154405061269)
              ·
                refine ⟨154636182490085362737247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3298905226455154405061269 154636182490085362737247)
                ·
                  rfl

theorem cell20_1016391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_1016391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016391 prefixEnd_1016391 := by exact prefixLift 1016391
  have htrace : WordTrace (prefixWord ++ tailWord_1016391) baseStart_1016391 baseEnd_1016391 := by
    simpa [prefixWord, tailWord_1016391, baseEnd_1016391] using wordTrace_append hprefix tailTrace_1016391
  have hstable : (prefixWord ++ tailWord_1016391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016391).length < 2 ^ (prefixWord ++ tailWord_1016391).sum := by decide
  have hdescent : baseEnd_1016391 < baseStart_1016391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016398 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1016398 : Nat := 118140960795 + 1016398 * 2 ^ 59
def prefixEnd_1016398 : Nat := 4983230072969 + 3 ^ 40 * 1016398 * 2
def baseEnd_1016398 : Nat := 463911742460995174978379

theorem tailTrace_1016398 : CollatzResearch.WordTrace tailWord_1016398 prefixEnd_1016398 463911742460995174978379 := by
  unfold tailWord_1016398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4633885071471388475443231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24714053714514071869030565 4633885071471388475443231)
  ·
    refine ⟨6950827607207082713164847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4633885071471388475443231 6950827607207082713164847)
    ·
      refine ⟨10426241410810624069747271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6950827607207082713164847 10426241410810624069747271)
      ·
        refine ⟨15639362116215936104620907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10426241410810624069747271 15639362116215936104620907)
        ·
          refine ⟨23459043174323904156931361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15639362116215936104620907 23459043174323904156931361)
          ·
            refine ⟨17594282380742928117698521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23459043174323904156931361 17594282380742928117698521)
            ·
              refine ⟨13195711785557196088273891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17594282380742928117698521 13195711785557196088273891)
              ·
                refine ⟨19793567678335794132410837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13195711785557196088273891 19793567678335794132410837)
                ·
                  refine ⟨463911742460995174978379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19793567678335794132410837 463911742460995174978379)
                  ·
                    rfl

theorem cell20_1016398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1016398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016398 prefixEnd_1016398 := by exact prefixLift 1016398
  have htrace : WordTrace (prefixWord ++ tailWord_1016398) baseStart_1016398 baseEnd_1016398 := by
    simpa [prefixWord, tailWord_1016398, baseEnd_1016398] using wordTrace_append hprefix tailTrace_1016398
  have hstable : (prefixWord ++ tailWord_1016398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016398).length < 2 ^ (prefixWord ++ tailWord_1016398).sum := by decide
  have hdescent : baseEnd_1016398 < baseStart_1016398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016477 : List Nat := [1, 4, 2, 1, 1, 1, 4, 4, 2]
def baseStart_1016477 : Nat := 118140960795 + 1016477 * 2 ^ 59
def prefixEnd_1016477 : Nat := 4983230072969 + 3 ^ 40 * 1016477 * 2
def baseEnd_1016477 : Nat := 463947800213622011344723

theorem tailTrace_1016477 : CollatzResearch.WordTrace tailWord_1016477 prefixEnd_1016477 463947800213622011344723 := by
  unfold tailWord_1016477
  simp only [CollatzResearch.WordTrace]
  refine ⟨37073961938484904295671685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24715974625656602863781123 37073961938484904295671685)
  ·
    refine ⟨6951367863465919555438441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37073961938484904295671685 6951367863465919555438441)
    ·
      refine ⟨5213525897599439666578831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6951367863465919555438441 5213525897599439666578831)
      ·
        refine ⟨7820288846399159499868247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5213525897599439666578831 7820288846399159499868247)
        ·
          refine ⟨11730433269598739249802371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7820288846399159499868247 11730433269598739249802371)
          ·
            refine ⟨17595649904398108874703557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11730433269598739249802371 17595649904398108874703557)
            ·
              refine ⟨3299184357074645414006917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17595649904398108874703557 3299184357074645414006917)
              ·
                refine ⟨618597066951496015126297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3299184357074645414006917 618597066951496015126297)
                ·
                  refine ⟨463947800213622011344723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618597066951496015126297 463947800213622011344723)
                  ·
                    rfl

theorem cell20_1016477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_1016477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016477 prefixEnd_1016477 := by exact prefixLift 1016477
  have htrace : WordTrace (prefixWord ++ tailWord_1016477) baseStart_1016477 baseEnd_1016477 := by
    simpa [prefixWord, tailWord_1016477, baseEnd_1016477] using wordTrace_append hprefix tailTrace_1016477
  have hstable : (prefixWord ++ tailWord_1016477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016477).length < 2 ^ (prefixWord ++ tailWord_1016477).sum := by decide
  have hdescent : baseEnd_1016477 < baseStart_1016477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016501 : List Nat := [1, 3, 3, 3, 1, 3, 2, 4]
def baseStart_1016501 : Nat := 118140960795 + 1016501 * 2 ^ 59
def prefixEnd_1016501 : Nat := 4983230072969 + 3 ^ 40 * 1016501 * 2
def baseEnd_1016501 : Nat := 154652918155861531514875

theorem tailTrace_1016501 : CollatzResearch.WordTrace tailWord_1016501 prefixEnd_1016501 154652918155861531514875 := by
  unfold tailWord_1016501
  simp only [CollatzResearch.WordTrace]
  refine ⟨37074837290397956394545357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24716558193598637596363571 37074837290397956394545357)
  ·
    refine ⟨13903063983899233647954509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37074837290397956394545357 13903063983899233647954509)
    ·
      refine ⟨5213648993962212617982941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13903063983899233647954509 5213648993962212617982941)
      ·
        refine ⟨1955118372735829731743603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5213648993962212617982941 1955118372735829731743603)
        ·
          refine ⟨2932677559103744597615405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955118372735829731743603 2932677559103744597615405)
          ·
            refine ⟨1099754084663904224105777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2932677559103744597615405 1099754084663904224105777)
            ·
              refine ⟨824815563497928168079333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1099754084663904224105777 824815563497928168079333)
              ·
                refine ⟨154652918155861531514875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 824815563497928168079333 154652918155861531514875)
                ·
                  rfl

theorem cell20_1016501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 4].length) (baseStart_1016501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016501 prefixEnd_1016501 := by exact prefixLift 1016501
  have htrace : WordTrace (prefixWord ++ tailWord_1016501) baseStart_1016501 baseEnd_1016501 := by
    simpa [prefixWord, tailWord_1016501, baseEnd_1016501] using wordTrace_append hprefix tailTrace_1016501
  have hstable : (prefixWord ++ tailWord_1016501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016501).length < 2 ^ (prefixWord ++ tailWord_1016501).sum := by decide
  have hdescent : baseEnd_1016501 < baseStart_1016501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016512 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_1016512 : Nat := 118140960795 + 1016512 * 2 ^ 59
def prefixEnd_1016512 : Nat := 4983230072969 + 3 ^ 40 * 1016512 * 2
def baseEnd_1016512 : Nat := 463963775167317445177913

theorem tailTrace_1016512 : CollatzResearch.WordTrace tailWord_1016512 prefixEnd_1016512 463963775167317445177913 := by
  unfold tailWord_1016512
  simp only [CollatzResearch.WordTrace]
  refine ⟨18537619246679052636597895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24716825662238736848797193 18537619246679052636597895)
  ·
    refine ⟨27806428870018578954896843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18537619246679052636597895 27806428870018578954896843)
    ·
      refine ⟨41709643305027868432345265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27806428870018578954896843 41709643305027868432345265)
      ·
        refine ⟨31282232478770901324258949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41709643305027868432345265 31282232478770901324258949)
        ·
          refine ⟨5865418589769543998298553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31282232478770901324258949 5865418589769543998298553)
          ·
            refine ⟨4399063942327157998723915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5865418589769543998298553 4399063942327157998723915)
            ·
              refine ⟨6598595913490736998085873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4399063942327157998723915 6598595913490736998085873)
              ·
                refine ⟨4948946935118052748564405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6598595913490736998085873 4948946935118052748564405)
                ·
                  refine ⟨463963775167317445177913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4948946935118052748564405 463963775167317445177913)
                  ·
                    rfl

theorem cell20_1016512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_1016512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016512 prefixEnd_1016512 := by exact prefixLift 1016512
  have htrace : WordTrace (prefixWord ++ tailWord_1016512) baseStart_1016512 baseEnd_1016512 := by
    simpa [prefixWord, tailWord_1016512, baseEnd_1016512] using wordTrace_append hprefix tailTrace_1016512
  have hstable : (prefixWord ++ tailWord_1016512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016512).length < 2 ^ (prefixWord ++ tailWord_1016512).sum := by decide
  have hdescent : baseEnd_1016512 < baseStart_1016512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016518 : List Nat := [6, 1, 2, 1, 2, 2, 6]
def baseStart_1016518 : Nat := 118140960795 + 1016518 * 2 ^ 59
def prefixEnd_1016518 : Nat := 4983230072969 + 3 ^ 40 * 1016518 * 2
def baseEnd_1016518 : Nat := 51551834858978676775321

theorem tailTrace_1016518 : CollatzResearch.WordTrace tailWord_1016518 prefixEnd_1016518 51551834858978676775321 := by
  unfold tailWord_1016518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158608041604261509309819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24716971554224245531942805 1158608041604261509309819)
  ·
    refine ⟨1737912062406392263964729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1158608041604261509309819 1737912062406392263964729)
    ·
      refine ⟨1303434046804794197973547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1737912062406392263964729 1303434046804794197973547)
      ·
        refine ⟨1955151070207191296960321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303434046804794197973547 1955151070207191296960321)
        ·
          refine ⟨1466363302655393472720241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1955151070207191296960321 1466363302655393472720241)
          ·
            refine ⟨1099772476991545104540181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1466363302655393472720241 1099772476991545104540181)
            ·
              refine ⟨51551834858978676775321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1099772476991545104540181 51551834858978676775321)
              ·
                rfl

theorem cell20_1016518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 6].length) (baseStart_1016518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016518 prefixEnd_1016518 := by exact prefixLift 1016518
  have htrace : WordTrace (prefixWord ++ tailWord_1016518) baseStart_1016518 baseEnd_1016518 := by
    simpa [prefixWord, tailWord_1016518, baseEnd_1016518] using wordTrace_append hprefix tailTrace_1016518
  have hstable : (prefixWord ++ tailWord_1016518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016518).length < 2 ^ (prefixWord ++ tailWord_1016518).sum := by decide
  have hdescent : baseEnd_1016518 < baseStart_1016518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016532 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 4]
def baseStart_1016532 : Nat := 118140960795 + 1016532 * 2 ^ 59
def prefixEnd_1016532 : Nat := 4983230072969 + 3 ^ 40 * 1016532 * 2
def baseEnd_1016532 : Nat := 463972903712286264511165

theorem tailTrace_1016532 : CollatzResearch.WordTrace tailWord_1016532 prefixEnd_1016532 463972903712286264511165 := by
  unfold tailWord_1016532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18537983976642824344461925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24717311968857099125949233 18537983976642824344461925)
  ·
    refine ⟨3475871995620529564586611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18537983976642824344461925 3475871995620529564586611)
    ·
      refine ⟨5213807993430794346879917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3475871995620529564586611 5213807993430794346879917)
      ·
        refine ⟨1955177997536547880079969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5213807993430794346879917 1955177997536547880079969)
        ·
          refine ⟨1466383498152410910059977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1955177997536547880079969 1466383498152410910059977)
          ·
            refine ⟨1099787623614308182544983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1466383498152410910059977 1099787623614308182544983)
            ·
              refine ⟨1649681435421462273817475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099787623614308182544983 1649681435421462273817475)
              ·
                refine ⟨2474522153132193410726213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649681435421462273817475 2474522153132193410726213)
                ·
                  refine ⟨463972903712286264511165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474522153132193410726213 463972903712286264511165)
                  ·
                    rfl

theorem cell20_1016532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_1016532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016532 prefixEnd_1016532 := by exact prefixLift 1016532
  have htrace : WordTrace (prefixWord ++ tailWord_1016532) baseStart_1016532 baseEnd_1016532 := by
    simpa [prefixWord, tailWord_1016532, baseEnd_1016532] using wordTrace_append hprefix tailTrace_1016532
  have hstable : (prefixWord ++ tailWord_1016532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016532).length < 2 ^ (prefixWord ++ tailWord_1016532).sum := by decide
  have hdescent : baseEnd_1016532 < baseStart_1016532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016536 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_1016536 : Nat := 118140960795 + 1016536 * 2 ^ 59
def prefixEnd_1016536 : Nat := 4983230072969 + 3 ^ 40 * 1016536 * 2
def baseEnd_1016536 : Nat := 463974729421280028377815

theorem tailTrace_1016536 : CollatzResearch.WordTrace tailWord_1016536 prefixEnd_1016536 463974729421280028377815 := by
  unfold tailWord_1016536
  simp only [CollatzResearch.WordTrace]
  refine ⟨18538056922635578686034731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24717409230180771581379641 18538056922635578686034731)
  ·
    refine ⟨27807085383953368029052097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18538056922635578686034731 27807085383953368029052097)
    ·
      refine ⟨20855314037965026021789073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27807085383953368029052097 20855314037965026021789073)
      ·
        refine ⟨15641485528473769516341805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20855314037965026021789073 15641485528473769516341805)
        ·
          refine ⟨5865557073177663568628177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15641485528473769516341805 5865557073177663568628177)
          ·
            refine ⟨4399167804883247676471133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5865557073177663568628177 4399167804883247676471133)
            ·
              refine ⟨1649687926831217878676675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4399167804883247676471133 1649687926831217878676675)
              ·
                refine ⟨2474531890246826818015013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649687926831217878676675 2474531890246826818015013)
                ·
                  refine ⟨463974729421280028377815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474531890246826818015013 463974729421280028377815)
                  ·
                    rfl

theorem cell20_1016536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_1016536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016536 prefixEnd_1016536 := by exact prefixLift 1016536
  have htrace : WordTrace (prefixWord ++ tailWord_1016536) baseStart_1016536 baseEnd_1016536 := by
    simpa [prefixWord, tailWord_1016536, baseEnd_1016536] using wordTrace_append hprefix tailTrace_1016536
  have hstable : (prefixWord ++ tailWord_1016536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016536).length < 2 ^ (prefixWord ++ tailWord_1016536).sum := by decide
  have hdescent : baseEnd_1016536 < baseStart_1016536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016543 : List Nat := [1, 1, 2, 3, 2, 4, 2, 5]
def baseStart_1016543 : Nat := 118140960795 + 1016543 * 2 ^ 59
def prefixEnd_1016543 : Nat := 4983230072969 + 3 ^ 40 * 1016543 * 2
def baseEnd_1016543 : Nat := 154659308137339705048151

theorem tailTrace_1016543 : CollatzResearch.WordTrace tailWord_1016543 prefixEnd_1016543 154659308137339705048151 := by
  unfold tailWord_1016543
  simp only [CollatzResearch.WordTrace]
  refine ⟨37076369156245797567574283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24717579437497198378382855 37076369156245797567574283)
  ·
    refine ⟨55614553734368696351361425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37076369156245797567574283 55614553734368696351361425)
    ·
      refine ⟨41710915300776522263521069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55614553734368696351361425 41710915300776522263521069)
      ·
        refine ⟨15641593237791195848820401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41710915300776522263521069 15641593237791195848820401)
        ·
          refine ⟨11731194928343396886615301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15641593237791195848820401 11731194928343396886615301)
          ·
            refine ⟨2199599049064386916240369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11731194928343396886615301 2199599049064386916240369)
            ·
              refine ⟨1649699286798290187180277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2199599049064386916240369 1649699286798290187180277)
              ·
                refine ⟨154659308137339705048151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1649699286798290187180277 154659308137339705048151)
                ·
                  rfl

theorem cell20_1016543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_1016543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016543 prefixEnd_1016543 := by exact prefixLift 1016543
  have htrace : WordTrace (prefixWord ++ tailWord_1016543) baseStart_1016543 baseEnd_1016543 := by
    simpa [prefixWord, tailWord_1016543, baseEnd_1016543] using wordTrace_append hprefix tailTrace_1016543
  have hstable : (prefixWord ++ tailWord_1016543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016543).length < 2 ^ (prefixWord ++ tailWord_1016543).sum := by decide
  have hdescent : baseEnd_1016543 < baseStart_1016543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016594 : List Nat := [3, 2, 4, 1, 3, 1, 1, 5]
def baseStart_1016594 : Nat := 118140960795 + 1016594 * 2 ^ 59
def prefixEnd_1016594 : Nat := 4983230072969 + 3 ^ 40 * 1016594 * 2
def baseEnd_1016594 : Nat := 154667067400563201481415

theorem tailTrace_1016594 : CollatzResearch.WordTrace tailWord_1016594 prefixEnd_1016594 154667067400563201481415 := by
  unfold tailWord_1016594
  simp only [CollatzResearch.WordTrace]
  refine ⟨9269557319765258319420209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24718819519374022185120557 9269557319765258319420209)
  ·
    refine ⟨6952167989823943739565157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9269557319765258319420209 6952167989823943739565157)
    ·
      refine ⟨1303531498091989451168467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6952167989823943739565157 1303531498091989451168467)
      ·
        refine ⟨1955297247137984176752701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303531498091989451168467 1955297247137984176752701)
        ·
          refine ⟨733236467676744066282263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1955297247137984176752701 733236467676744066282263)
          ·
            refine ⟨1099854701515116099423395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733236467676744066282263 1099854701515116099423395)
            ·
              refine ⟨1649782052272674149135093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099854701515116099423395 1649782052272674149135093)
              ·
                refine ⟨154667067400563201481415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1649782052272674149135093 154667067400563201481415)
                ·
                  rfl

theorem cell20_1016594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_1016594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016594 prefixEnd_1016594 := by exact prefixLift 1016594
  have htrace : WordTrace (prefixWord ++ tailWord_1016594) baseStart_1016594 baseEnd_1016594 := by
    simpa [prefixWord, tailWord_1016594, baseEnd_1016594] using wordTrace_append hprefix tailTrace_1016594
  have hstable : (prefixWord ++ tailWord_1016594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016594).length < 2 ^ (prefixWord ++ tailWord_1016594).sum := by decide
  have hdescent : baseEnd_1016594 < baseStart_1016594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016595 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 4]
def baseStart_1016595 : Nat := 118140960795 + 1016595 * 2 ^ 59
def prefixEnd_1016595 : Nat := 4983230072969 + 3 ^ 40 * 1016595 * 2
def baseEnd_1016595 : Nat := 464001658628938045410907

theorem tailTrace_1016595 : CollatzResearch.WordTrace tailWord_1016595 prefixEnd_1016595 464001658628938045410907 := by
  unfold tailWord_1016595
  simp only [CollatzResearch.WordTrace]
  refine ⟨37078265752057410448467239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24718843834704940298978159 37078265752057410448467239)
  ·
    refine ⟨55617398628086115672700859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37078265752057410448467239 55617398628086115672700859)
    ·
      refine ⟨83426097942129173509051289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55617398628086115672700859 83426097942129173509051289)
      ·
        refine ⟨62569573456596880131788467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83426097942129173509051289 62569573456596880131788467)
        ·
          refine ⟨93854360184895320197682701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62569573456596880131788467 93854360184895320197682701)
          ·
            refine ⟨35195385069335745074131013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93854360184895320197682701 35195385069335745074131013)
            ·
              refine ⟨6599134700500452201399565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35195385069335745074131013 6599134700500452201399565)
              ·
                refine ⟨2474675512687669575524837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6599134700500452201399565 2474675512687669575524837)
                ·
                  refine ⟨464001658628938045410907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474675512687669575524837 464001658628938045410907)
                  ·
                    rfl

theorem cell20_1016595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_1016595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016595 prefixEnd_1016595 := by exact prefixLift 1016595
  have htrace : WordTrace (prefixWord ++ tailWord_1016595) baseStart_1016595 baseEnd_1016595 := by
    simpa [prefixWord, tailWord_1016595, baseEnd_1016595] using wordTrace_append hprefix tailTrace_1016595
  have hstable : (prefixWord ++ tailWord_1016595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016595).length < 2 ^ (prefixWord ++ tailWord_1016595).sum := by decide
  have hdescent : baseEnd_1016595 < baseStart_1016595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016626 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1016626 : Nat := 118140960795 + 1016626 * 2 ^ 59
def prefixEnd_1016626 : Nat := 4983230072969 + 3 ^ 40 * 1016626 * 2
def baseEnd_1016626 : Nat := 464015807873639715377447

theorem tailTrace_1016626 : CollatzResearch.WordTrace tailWord_1016626 prefixEnd_1016626 464015807873639715377447 := by
  unfold tailWord_1016626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9269849103736275685711433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24719597609963401828563821 9269849103736275685711433)
  ·
    refine ⟨6952386827802206764283575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9269849103736275685711433 6952386827802206764283575)
    ·
      refine ⟨10428580241703310146425363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6952386827802206764283575 10428580241703310146425363)
      ·
        refine ⟨15642870362554965219638045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10428580241703310146425363 15642870362554965219638045)
        ·
          refine ⟨5866076385958111957364267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15642870362554965219638045 5866076385958111957364267)
          ·
            refine ⟨8799114578937167936046401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866076385958111957364267 8799114578937167936046401)
            ·
              refine ⟨6599335934202875952034801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8799114578937167936046401 6599335934202875952034801)
              ·
                refine ⟨4949501950652156964026101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6599335934202875952034801 4949501950652156964026101)
                ·
                  refine ⟨464015807873639715377447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4949501950652156964026101 464015807873639715377447)
                  ·
                    rfl

theorem cell20_1016626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1016626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016626 prefixEnd_1016626 := by exact prefixLift 1016626
  have htrace : WordTrace (prefixWord ++ tailWord_1016626) baseStart_1016626 baseEnd_1016626 := by
    simpa [prefixWord, tailWord_1016626, baseEnd_1016626] using wordTrace_append hprefix tailTrace_1016626
  have hstable : (prefixWord ++ tailWord_1016626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016626).length < 2 ^ (prefixWord ++ tailWord_1016626).sum := by decide
  have hdescent : baseEnd_1016626 < baseStart_1016626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016629 : List Nat := [1, 3, 3, 1, 3, 1, 1, 5, 2]
def baseStart_1016629 : Nat := 118140960795 + 1016629 * 2 ^ 59
def prefixEnd_1016629 : Nat := 4983230072969 + 3 ^ 40 * 1016629 * 2
def baseEnd_1016629 : Nat := 464017177155385038277435

theorem tailTrace_1016629 : CollatzResearch.WordTrace tailWord_1016629 prefixEnd_1016629 464017177155385038277435 := by
  unfold tailWord_1016629
  simp only [CollatzResearch.WordTrace]
  refine ⟨37079505833934234255204941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24719670555956156170136627 37079505833934234255204941)
  ·
    refine ⟨13904814687725337845701853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37079505833934234255204941 13904814687725337845701853)
    ·
      refine ⟨5214305507897001692138195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13904814687725337845701853 5214305507897001692138195)
      ·
        refine ⟨7821458261845502538207293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5214305507897001692138195 7821458261845502538207293)
        ·
          refine ⟨2933046848192063451827735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7821458261845502538207293 2933046848192063451827735)
          ·
            refine ⟨4399570272288095177741603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933046848192063451827735 4399570272288095177741603)
            ·
              refine ⟨6599355408432142766612405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4399570272288095177741603 6599355408432142766612405)
              ·
                refine ⟨618689569540513384369913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6599355408432142766612405 618689569540513384369913)
                ·
                  refine ⟨464017177155385038277435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618689569540513384369913 464017177155385038277435)
                  ·
                    rfl

theorem cell20_1016629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_1016629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016629 prefixEnd_1016629 := by exact prefixLift 1016629
  have htrace : WordTrace (prefixWord ++ tailWord_1016629) baseStart_1016629 baseEnd_1016629 := by
    simpa [prefixWord, tailWord_1016629, baseEnd_1016629] using wordTrace_append hprefix tailTrace_1016629
  have hstable : (prefixWord ++ tailWord_1016629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016629).length < 2 ^ (prefixWord ++ tailWord_1016629).sum := by decide
  have hdescent : baseEnd_1016629 < baseStart_1016629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016664 : List Nat := [2, 1, 2, 2, 1, 1, 1, 7, 3]
def baseStart_1016664 : Nat := 118140960795 + 1016664 * 2 ^ 59
def prefixEnd_1016664 : Nat := 4983230072969 + 3 ^ 40 * 1016664 * 2
def baseEnd_1016664 : Nat := 464033152109080472110625

theorem tailTrace_1016664 : CollatzResearch.WordTrace tailWord_1016664 prefixEnd_1016664 464033152109080472110625 := by
  unfold tailWord_1016664
  simp only [CollatzResearch.WordTrace]
  refine ⟨18540391194403717616364523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24720521592538290155152697 18540391194403717616364523)
  ·
    refine ⟨27810586791605576424546785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18540391194403717616364523 27810586791605576424546785)
    ·
      refine ⟨20857940093704182318410089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27810586791605576424546785 20857940093704182318410089)
      ·
        refine ⟨15643455070278136738807567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20857940093704182318410089 15643455070278136738807567)
        ·
          refine ⟨23465182605417205108211351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15643455070278136738807567 23465182605417205108211351)
          ·
            refine ⟨35197773908125807662317027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23465182605417205108211351 35197773908125807662317027)
            ·
              refine ⟨52796660862188711493475541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35197773908125807662317027 52796660862188711493475541)
              ·
                refine ⟨1237421738957547925628333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52796660862188711493475541 1237421738957547925628333)
                ·
                  refine ⟨464033152109080472110625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237421738957547925628333 464033152109080472110625)
                  ·
                    rfl

theorem cell20_1016664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_1016664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016664 prefixEnd_1016664 := by exact prefixLift 1016664
  have htrace : WordTrace (prefixWord ++ tailWord_1016664) baseStart_1016664 baseEnd_1016664 := by
    simpa [prefixWord, tailWord_1016664, baseEnd_1016664] using wordTrace_append hprefix tailTrace_1016664
  have hstable : (prefixWord ++ tailWord_1016664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016664).length < 2 ^ (prefixWord ++ tailWord_1016664).sum := by decide
  have hdescent : baseEnd_1016664 < baseStart_1016664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016671 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 4]
def baseStart_1016671 : Nat := 118140960795 + 1016671 * 2 ^ 59
def prefixEnd_1016671 : Nat := 4983230072969 + 3 ^ 40 * 1016671 * 2
def baseEnd_1016671 : Nat := 464036347099819558877263

theorem tailTrace_1016671 : CollatzResearch.WordTrace tailWord_1016671 prefixEnd_1016671 464036347099819558877263 := by
  unfold tailWord_1016671
  simp only [CollatzResearch.WordTrace]
  refine ⟨37081037699782075428233867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24720691799854716952155911 37081037699782075428233867)
  ·
    refine ⟨55621556549673113142350801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37081037699782075428233867 55621556549673113142350801)
    ·
      refine ⟨41716167412254834856763101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55621556549673113142350801 41716167412254834856763101)
      ·
        refine ⟨15643562779595563071286163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41716167412254834856763101 15643562779595563071286163)
        ·
          refine ⟨23465344169393344606929245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15643562779595563071286163 23465344169393344606929245)
          ·
            refine ⟨8799504063522504227598467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23465344169393344606929245 8799504063522504227598467)
            ·
              refine ⟨13199256095283756341397701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8799504063522504227598467 13199256095283756341397701)
              ·
                refine ⟨2474860517865704314012069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13199256095283756341397701 2474860517865704314012069)
                ·
                  refine ⟨464036347099819558877263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474860517865704314012069 464036347099819558877263)
                  ·
                    rfl

theorem cell20_1016671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_1016671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016671 prefixEnd_1016671 := by exact prefixLift 1016671
  have htrace : WordTrace (prefixWord ++ tailWord_1016671) baseStart_1016671 baseEnd_1016671 := by
    simpa [prefixWord, tailWord_1016671, baseEnd_1016671] using wordTrace_append hprefix tailTrace_1016671
  have hstable : (prefixWord ++ tailWord_1016671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016671).length < 2 ^ (prefixWord ++ tailWord_1016671).sum := by decide
  have hdescent : baseEnd_1016671 < baseStart_1016671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016674 : List Nat := [3, 3, 2, 1, 3, 1, 1, 6]
def baseStart_1016674 : Nat := 118140960795 + 1016674 * 2 ^ 59
def prefixEnd_1016674 : Nat := 4983230072969 + 3 ^ 40 * 1016674 * 2
def baseEnd_1016674 : Nat := 154679238793854960592417

theorem tailTrace_1016674 : CollatzResearch.WordTrace tailWord_1016674 prefixEnd_1016674 154679238793854960592417 := by
  unfold tailWord_1016674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9270286779692801735148269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24720764745847471293728717 9270286779692801735148269)
  ·
    refine ⟨3476357542384800650680601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9270286779692801735148269 3476357542384800650680601)
    ·
      refine ⟨2607268156788600488010451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3476357542384800650680601 2607268156788600488010451)
      ·
        refine ⟨3910902235182900732015677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607268156788600488010451 3910902235182900732015677)
        ·
          refine ⟨1466588338193587774505879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3910902235182900732015677 1466588338193587774505879)
          ·
            refine ⟨2199882507290381661758819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466588338193587774505879 2199882507290381661758819)
            ·
              refine ⟨3299823760935572492638229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199882507290381661758819 3299823760935572492638229)
              ·
                refine ⟨154679238793854960592417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3299823760935572492638229 154679238793854960592417)
                ·
                  rfl

theorem cell20_1016674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_1016674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016674 prefixEnd_1016674 := by exact prefixLift 1016674
  have htrace : WordTrace (prefixWord ++ tailWord_1016674) baseStart_1016674 baseEnd_1016674 := by
    simpa [prefixWord, tailWord_1016674, baseEnd_1016674] using wordTrace_append hprefix tailTrace_1016674
  have hstable : (prefixWord ++ tailWord_1016674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016674).length < 2 ^ (prefixWord ++ tailWord_1016674).sum := by decide
  have hdescent : baseEnd_1016674 < baseStart_1016674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016716 : List Nat := [2, 2, 1, 2, 1, 2, 3, 7]
def baseStart_1016716 : Nat := 118140960795 + 1016716 * 2 ^ 59
def prefixEnd_1016716 : Nat := 4983230072969 + 3 ^ 40 * 1016716 * 2
def baseEnd_1016716 : Nat := 154685628775333134125693

theorem tailTrace_1016716 : CollatzResearch.WordTrace tailWord_1016716 prefixEnd_1016716 154685628775333134125693 := by
  unfold tailWord_1016716
  simp only [CollatzResearch.WordTrace]
  refine ⟨18541339492309524056811001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24721785989746032075748001 18541339492309524056811001)
  ·
    refine ⟨13906004619232143042608251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18541339492309524056811001 13906004619232143042608251)
    ·
      refine ⟨20859006928848214563912377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13906004619232143042608251 20859006928848214563912377)
      ·
        refine ⟨15644255196636160922934283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20859006928848214563912377 15644255196636160922934283)
        ·
          refine ⟨23466382794954241384401425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15644255196636160922934283 23466382794954241384401425)
          ·
            refine ⟨17599787096215681038301069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23466382794954241384401425 17599787096215681038301069)
            ·
              refine ⟨6599920161080880389362901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17599787096215681038301069 6599920161080880389362901)
              ·
                refine ⟨154685628775333134125693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6599920161080880389362901 154685628775333134125693)
                ·
                  rfl

theorem cell20_1016716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_1016716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016716 prefixEnd_1016716 := by exact prefixLift 1016716
  have htrace : WordTrace (prefixWord ++ tailWord_1016716) baseStart_1016716 baseEnd_1016716 := by
    simpa [prefixWord, tailWord_1016716, baseEnd_1016716] using wordTrace_append hprefix tailTrace_1016716
  have hstable : (prefixWord ++ tailWord_1016716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016716).length < 2 ^ (prefixWord ++ tailWord_1016716).sum := by decide
  have hdescent : baseEnd_1016716 < baseStart_1016716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016723 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 7]
def baseStart_1016723 : Nat := 118140960795 + 1016723 * 2 ^ 59
def prefixEnd_1016723 : Nat := 4983230072969 + 3 ^ 40 * 1016723 * 2
def baseEnd_1016723 : Nat := 464060081316738489143717

theorem tailTrace_1016723 : CollatzResearch.WordTrace tailWord_1016723 prefixEnd_1016723 464060081316738489143717 := by
  unfold tailWord_1016723
  simp only [CollatzResearch.WordTrace]
  refine ⟨37082934295593688309126823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24721956197062458872751215 37082934295593688309126823)
  ·
    refine ⟨55624401443390532463690235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37082934295593688309126823 55624401443390532463690235)
    ·
      refine ⟨83436602165085798695535353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55624401443390532463690235 83436602165085798695535353)
      ·
        refine ⟨62577451623814349021651515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83436602165085798695535353 62577451623814349021651515)
        ·
          refine ⟨93866177435721523532477273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62577451623814349021651515 93866177435721523532477273)
          ·
            refine ⟨70399633076791142649357955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93866177435721523532477273 70399633076791142649357955)
            ·
              refine ⟨105599449615186713974036933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70399633076791142649357955 105599449615186713974036933)
              ·
                refine ⟨19799896802847508870131925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105599449615186713974036933 19799896802847508870131925)
                ·
                  refine ⟨464060081316738489143717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19799896802847508870131925 464060081316738489143717)
                  ·
                    rfl

theorem cell20_1016723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_1016723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016723 prefixEnd_1016723 := by exact prefixLift 1016723
  have htrace : WordTrace (prefixWord ++ tailWord_1016723) baseStart_1016723 baseEnd_1016723 := by
    simpa [prefixWord, tailWord_1016723, baseEnd_1016723] using wordTrace_append hprefix tailTrace_1016723
  have hstable : (prefixWord ++ tailWord_1016723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016723).length < 2 ^ (prefixWord ++ tailWord_1016723).sum := by decide
  have hdescent : baseEnd_1016723 < baseStart_1016723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016756 : List Nat := [2, 5, 2, 1, 1, 3, 2, 2, 2]
def baseStart_1016756 : Nat := 118140960795 + 1016756 * 2 ^ 59
def prefixEnd_1016756 : Nat := 4983230072969 + 3 ^ 40 * 1016756 * 2
def baseEnd_1016756 : Nat := 464075143415937041043583

theorem tailTrace_1016756 : CollatzResearch.WordTrace tailWord_1016756 prefixEnd_1016756 464075143415937041043583 := by
  unfold tailWord_1016756
  simp only [CollatzResearch.WordTrace]
  refine ⟨18542068952237067472539061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24722758602982756630052081 18542068952237067472539061)
  ·
    refine ⟨1738318964272225075550537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18542068952237067472539061 1738318964272225075550537)
    ·
      refine ⟨1303739223204168806662903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1738318964272225075550537 1303739223204168806662903)
      ·
        refine ⟨1955608834806253209994355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303739223204168806662903 1955608834806253209994355)
        ·
          refine ⟨2933413252209379814991533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955608834806253209994355 2933413252209379814991533)
          ·
            refine ⟨1100029969578517430621825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2933413252209379814991533 1100029969578517430621825)
            ·
              refine ⟨825022477183888072966369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100029969578517430621825 825022477183888072966369)
              ·
                refine ⟨618766857887916054724777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825022477183888072966369 618766857887916054724777)
                ·
                  refine ⟨464075143415937041043583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618766857887916054724777 464075143415937041043583)
                  ·
                    rfl

theorem cell20_1016756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_1016756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016756 prefixEnd_1016756 := by exact prefixLift 1016756
  have htrace : WordTrace (prefixWord ++ tailWord_1016756) baseStart_1016756 baseEnd_1016756 := by
    simpa [prefixWord, tailWord_1016756, baseEnd_1016756] using wordTrace_append hprefix tailTrace_1016756
  have hstable : (prefixWord ++ tailWord_1016756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016756).length < 2 ^ (prefixWord ++ tailWord_1016756).sum := by decide
  have hdescent : baseEnd_1016756 < baseStart_1016756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016757 : List Nat := [1, 3, 3, 2, 1, 1, 4, 2, 3]
def baseStart_1016757 : Nat := 118140960795 + 1016757 * 2 ^ 59
def prefixEnd_1016757 : Nat := 4983230072969 + 3 ^ 40 * 1016757 * 2
def baseEnd_1016757 : Nat := 464075599843185482010245

theorem tailTrace_1016757 : CollatzResearch.WordTrace tailWord_1016757 prefixEnd_1016757 464075599843185482010245 := by
  unfold tailWord_1016757
  simp only [CollatzResearch.WordTrace]
  refine ⟨37084174377470512115864525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24722782918313674743909683 37084174377470512115864525)
  ·
    refine ⟨13906565391551442043449197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37084174377470512115864525 13906565391551442043449197)
    ·
      refine ⟨5214962021831790766293449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13906565391551442043449197 5214962021831790766293449)
      ·
        refine ⟨3911221516373843074720087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5214962021831790766293449 3911221516373843074720087)
        ·
          refine ⟨5866832274560764612080131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911221516373843074720087 5866832274560764612080131)
          ·
            refine ⟨8800248411841146918120197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866832274560764612080131 8800248411841146918120197)
            ·
              refine ⟨1650046577220215047147537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8800248411841146918120197 1650046577220215047147537)
              ·
                refine ⟨1237534932915161285360653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650046577220215047147537 1237534932915161285360653)
                ·
                  refine ⟨464075599843185482010245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237534932915161285360653 464075599843185482010245)
                  ·
                    rfl

theorem cell20_1016757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_1016757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016757 prefixEnd_1016757 := by exact prefixLift 1016757
  have htrace : WordTrace (prefixWord ++ tailWord_1016757) baseStart_1016757 baseEnd_1016757 := by
    simpa [prefixWord, tailWord_1016757, baseEnd_1016757] using wordTrace_append hprefix tailTrace_1016757
  have hstable : (prefixWord ++ tailWord_1016757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016757).length < 2 ^ (prefixWord ++ tailWord_1016757).sum := by decide
  have hdescent : baseEnd_1016757 < baseStart_1016757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016760 : List Nat := [2, 1, 2, 1, 2, 6, 2, 2, 2]
def baseStart_1016760 : Nat := 118140960795 + 1016760 * 2 ^ 59
def prefixEnd_1016760 : Nat := 4983230072969 + 3 ^ 40 * 1016760 * 2
def baseEnd_1016760 : Nat := 464076969124930804910233

theorem tailTrace_1016760 : CollatzResearch.WordTrace tailWord_1016760 prefixEnd_1016760 464076969124930804910233 := by
  unfold tailWord_1016760
  simp only [CollatzResearch.WordTrace]
  refine ⟨18542141898229821814111867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24722855864306429085482489 18542141898229821814111867)
  ·
    refine ⟨27813212847344732721167801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18542141898229821814111867 27813212847344732721167801)
    ·
      refine ⟨20859909635508549540875851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27813212847344732721167801 20859909635508549540875851)
      ·
        refine ⟨31289864453262824311313777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20859909635508549540875851 31289864453262824311313777)
        ·
          refine ⟨23467398339947118233485333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31289864453262824311313777 23467398339947118233485333)
          ·
            refine ⟨1100034297185021167194625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23467398339947118233485333 1100034297185021167194625)
            ·
              refine ⟨825025722888765875395969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100034297185021167194625 825025722888765875395969)
              ·
                refine ⟨618769292166574406546977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825025722888765875395969 618769292166574406546977)
                ·
                  refine ⟨464076969124930804910233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618769292166574406546977 464076969124930804910233)
                  ·
                    rfl

theorem cell20_1016760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 2].length) (baseStart_1016760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016760 prefixEnd_1016760 := by exact prefixLift 1016760
  have htrace : WordTrace (prefixWord ++ tailWord_1016760) baseStart_1016760 baseEnd_1016760 := by
    simpa [prefixWord, tailWord_1016760, baseEnd_1016760] using wordTrace_append hprefix tailTrace_1016760
  have hstable : (prefixWord ++ tailWord_1016760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016760).length < 2 ^ (prefixWord ++ tailWord_1016760).sum := by decide
  have hdescent : baseEnd_1016760 < baseStart_1016760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016785 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 4]
def baseStart_1016785 : Nat := 118140960795 + 1016785 * 2 ^ 59
def prefixEnd_1016785 : Nat := 4983230072969 + 3 ^ 40 * 1016785 * 2
def baseEnd_1016785 : Nat := 464088379806141829076797

theorem tailTrace_1016785 : CollatzResearch.WordTrace tailWord_1016785 prefixEnd_1016785 464088379806141829076797 := by
  unfold tailWord_1016785
  simp only [CollatzResearch.WordTrace]
  refine ⟨37085195621369072897883809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24723463747579381931922539 37085195621369072897883809)
  ·
    refine ⟨27813896716026804673412857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37085195621369072897883809 27813896716026804673412857)
    ·
      refine ⟨20860422537020103505059643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27813896716026804673412857 20860422537020103505059643)
      ·
        refine ⟨31290633805530155257589465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20860422537020103505059643 31290633805530155257589465)
        ·
          refine ⟨23467975354147616443192099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31290633805530155257589465 23467975354147616443192099)
          ·
            refine ⟨35201963031221424664788149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23467975354147616443192099 35201963031221424664788149)
            ·
              refine ⟨3300184034177008562323889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35201963031221424664788149 3300184034177008562323889)
              ·
                refine ⟨2475138025632756421742917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3300184034177008562323889 2475138025632756421742917)
                ·
                  refine ⟨464088379806141829076797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2475138025632756421742917 464088379806141829076797)
                  ·
                    rfl

theorem cell20_1016785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_1016785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016785 prefixEnd_1016785 := by exact prefixLift 1016785
  have htrace : WordTrace (prefixWord ++ tailWord_1016785) baseStart_1016785 baseEnd_1016785 := by
    simpa [prefixWord, tailWord_1016785, baseEnd_1016785] using wordTrace_append hprefix tailTrace_1016785
  have hstable : (prefixWord ++ tailWord_1016785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016785).length < 2 ^ (prefixWord ++ tailWord_1016785).sum := by decide
  have hdescent : baseEnd_1016785 < baseStart_1016785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016788 : List Nat := [2, 4, 1, 2, 1, 3, 3, 4]
def baseStart_1016788 : Nat := 118140960795 + 1016788 * 2 ^ 59
def prefixEnd_1016788 : Nat := 4983230072969 + 3 ^ 40 * 1016788 * 2
def baseEnd_1016788 : Nat := 154696583029295717325595

theorem tailTrace_1016788 : CollatzResearch.WordTrace tailWord_1016788 prefixEnd_1016788 154696583029295717325595 := by
  unfold tailWord_1016788
  simp only [CollatzResearch.WordTrace]
  refine ⟨18542652520179102205121509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24723536693572136273495345 18542652520179102205121509)
  ·
    refine ⟨3476747347533581663460283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18542652520179102205121509 3476747347533581663460283)
    ·
      refine ⟨5215121021300372495190425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3476747347533581663460283 5215121021300372495190425)
      ·
        refine ⟨3911340765975279371392819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5215121021300372495190425 3911340765975279371392819)
        ·
          refine ⟨5867011148962919057089229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911340765975279371392819 5867011148962919057089229)
          ·
            refine ⟨2200129180861094646408461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5867011148962919057089229 2200129180861094646408461)
            ·
              refine ⟨825048442822910492403173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2200129180861094646408461 825048442822910492403173)
              ·
                refine ⟨154696583029295717325595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825048442822910492403173 154696583029295717325595)
                ·
                  rfl

theorem cell20_1016788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_1016788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016788 prefixEnd_1016788 := by exact prefixLift 1016788
  have htrace : WordTrace (prefixWord ++ tailWord_1016788) baseStart_1016788 baseEnd_1016788 := by
    simpa [prefixWord, tailWord_1016788, baseEnd_1016788] using wordTrace_append hprefix tailTrace_1016788
  have hstable : (prefixWord ++ tailWord_1016788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016788).length < 2 ^ (prefixWord ++ tailWord_1016788).sum := by decide
  have hdescent : baseEnd_1016788 < baseStart_1016788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016864 : List Nat := [2, 1, 1, 7, 1, 2, 6]
def baseStart_1016864 : Nat := 118140960795 + 1016864 * 2 ^ 59
def prefixEnd_1016864 : Nat := 4983230072969 + 3 ^ 40 * 1016864 * 2
def baseEnd_1016864 : Nat := 51569381950974296160349

theorem tailTrace_1016864 : CollatzResearch.WordTrace tailWord_1016864 prefixEnd_1016864 51569381950974296160349 := by
  unfold tailWord_1016864
  simp only [CollatzResearch.WordTrace]
  refine ⟨18544038494041434695004823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24725384658721912926673097 18544038494041434695004823)
  ·
    refine ⟨27816057741062152042507235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18544038494041434695004823 27816057741062152042507235)
    ·
      refine ⟨41724086611593228063760853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27816057741062152042507235 41724086611593228063760853)
      ·
        refine ⟨977908279959216282744395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 41724086611593228063760853 977908279959216282744395)
        ·
          refine ⟨1466862419938824424116593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977908279959216282744395 1466862419938824424116593)
          ·
            refine ⟨1100146814954118318087445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1466862419938824424116593 1100146814954118318087445)
            ·
              refine ⟨51569381950974296160349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1100146814954118318087445 51569381950974296160349)
              ·
                rfl

theorem cell20_1016864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 6].length) (baseStart_1016864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016864 prefixEnd_1016864 := by exact prefixLift 1016864
  have htrace : WordTrace (prefixWord ++ tailWord_1016864) baseStart_1016864 baseEnd_1016864 := by
    simpa [prefixWord, tailWord_1016864, baseEnd_1016864] using wordTrace_append hprefix tailTrace_1016864
  have hstable : (prefixWord ++ tailWord_1016864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016864).length < 2 ^ (prefixWord ++ tailWord_1016864).sum := by decide
  have hdescent : baseEnd_1016864 < baseStart_1016864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016871 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 5]
def baseStart_1016871 : Nat := 118140960795 + 1016871 * 2 ^ 59
def prefixEnd_1016871 : Nat := 4983230072969 + 3 ^ 40 * 1016871 * 2
def baseEnd_1016871 : Nat := 464127632549507752209779

theorem tailTrace_1016871 : CollatzResearch.WordTrace tailWord_1016871 prefixEnd_1016871 464127632549507752209779 := by
  unfold tailWord_1016871
  simp only [CollatzResearch.WordTrace]
  refine ⟨37088332299057509585514467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24725554866038339723676311 37088332299057509585514467)
  ·
    refine ⟨55632498448586264378271701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37088332299057509585514467 55632498448586264378271701)
    ·
      refine ⟨1303886682388740571365743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 55632498448586264378271701 1303886682388740571365743)
      ·
        refine ⟨1955830023583110857048615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303886682388740571365743 1955830023583110857048615)
        ·
          refine ⟨2933745035374666285572923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955830023583110857048615 2933745035374666285572923)
          ·
            refine ⟨4400617553061999428359385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933745035374666285572923 4400617553061999428359385)
            ·
              refine ⟨3300463164796499571269539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4400617553061999428359385 3300463164796499571269539)
              ·
                refine ⟨4950694747194749356904309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300463164796499571269539 4950694747194749356904309)
                ·
                  refine ⟨464127632549507752209779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4950694747194749356904309 464127632549507752209779)
                  ·
                    rfl

theorem cell20_1016871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 5].length) (baseStart_1016871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016871 prefixEnd_1016871 := by exact prefixLift 1016871
  have htrace : WordTrace (prefixWord ++ tailWord_1016871) baseStart_1016871 baseEnd_1016871 := by
    simpa [prefixWord, tailWord_1016871, baseEnd_1016871] using wordTrace_append hprefix tailTrace_1016871
  have hstable : (prefixWord ++ tailWord_1016871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016871).length < 2 ^ (prefixWord ++ tailWord_1016871).sum := by decide
  have hdescent : baseEnd_1016871 < baseStart_1016871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016874 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 4]
def baseStart_1016874 : Nat := 118140960795 + 1016874 * 2 ^ 59
def prefixEnd_1016874 : Nat := 4983230072969 + 3 ^ 40 * 1016874 * 2
def baseEnd_1016874 : Nat := 464129001831253075109767

theorem tailTrace_1016874 : CollatzResearch.WordTrace tailWord_1016874 prefixEnd_1016874 464129001831253075109767 := by
  unfold tailWord_1016874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272110429511660274468419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24725627812031094065249117 9272110429511660274468419)
  ·
    refine ⟨13908165644267490411702629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9272110429511660274468419 13908165644267490411702629)
    ·
      refine ⟨2607781058300154452194243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13908165644267490411702629 2607781058300154452194243)
      ·
        refine ⟨3911671587450231678291365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607781058300154452194243 3911671587450231678291365)
        ·
          refine ⟨733438422646918439679631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3911671587450231678291365 733438422646918439679631)
          ·
            refine ⟨1100157633970377659519447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733438422646918439679631 1100157633970377659519447)
            ·
              refine ⟨1650236450955566489279171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100157633970377659519447 1650236450955566489279171)
              ·
                refine ⟨2475354676433349733918757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650236450955566489279171 2475354676433349733918757)
                ·
                  refine ⟨464129001831253075109767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2475354676433349733918757 464129001831253075109767)
                  ·
                    rfl

theorem cell20_1016874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_1016874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016874 prefixEnd_1016874 := by exact prefixLift 1016874
  have htrace : WordTrace (prefixWord ++ tailWord_1016874) baseStart_1016874 baseEnd_1016874 := by
    simpa [prefixWord, tailWord_1016874, baseEnd_1016874] using wordTrace_append hprefix tailTrace_1016874
  have hstable : (prefixWord ++ tailWord_1016874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016874).length < 2 ^ (prefixWord ++ tailWord_1016874).sum := by decide
  have hdescent : baseEnd_1016874 < baseStart_1016874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016875 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 5]
def baseStart_1016875 : Nat := 118140960795 + 1016875 * 2 ^ 59
def prefixEnd_1016875 : Nat := 4983230072969 + 3 ^ 40 * 1016875 * 2
def baseEnd_1016875 : Nat := 464129458258501516076429

theorem tailTrace_1016875 : CollatzResearch.WordTrace tailWord_1016875 prefixEnd_1016875 464129458258501516076429 := by
  unfold tailWord_1016875
  simp only [CollatzResearch.WordTrace]
  refine ⟨37088478191043018268660079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24725652127362012179106719 37088478191043018268660079)
  ·
    refine ⟨55632717286564527402990119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37088478191043018268660079 55632717286564527402990119)
    ·
      refine ⟨83449075929846791104485179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55632717286564527402990119 83449075929846791104485179)
      ·
        refine ⟨125173613894770186656727769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83449075929846791104485179 125173613894770186656727769)
        ·
          refine ⟨93880210421077639992545827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125173613894770186656727769 93880210421077639992545827)
          ·
            refine ⟨140820315631616459988818741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93880210421077639992545827 140820315631616459988818741)
            ·
              refine ⟨13201904590464043123951757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140820315631616459988818741 13201904590464043123951757)
              ·
                refine ⟨4950714221424016171481909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13201904590464043123951757 4950714221424016171481909)
                ·
                  refine ⟨464129458258501516076429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4950714221424016171481909 464129458258501516076429)
                  ·
                    rfl

theorem cell20_1016875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_1016875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016875 prefixEnd_1016875 := by exact prefixLift 1016875
  have htrace : WordTrace (prefixWord ++ tailWord_1016875) baseStart_1016875 baseEnd_1016875 := by
    simpa [prefixWord, tailWord_1016875, baseEnd_1016875] using wordTrace_append hprefix tailTrace_1016875
  have hstable : (prefixWord ++ tailWord_1016875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016875).length < 2 ^ (prefixWord ++ tailWord_1016875).sum := by decide
  have hdescent : baseEnd_1016875 < baseStart_1016875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
