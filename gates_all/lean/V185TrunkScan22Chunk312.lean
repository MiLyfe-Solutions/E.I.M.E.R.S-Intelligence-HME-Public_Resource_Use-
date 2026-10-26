import V185TrunkScan22Chunk311

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2783261 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2783261 : Nat := 118140960795 + 2783261 * 2 ^ 59
def prefixEnd_2783261 : Nat := 4983230072969 + 3 ^ 40 * 2783261 * 2
def baseEnd_2783261 : Nat := 952767119942360141491681

theorem tailTrace_2783261 : CollatzResearch.WordTrace tailWord_2783261 prefixEnd_2783261 952767119942360141491681 := by
  unfold tailWord_2783261
  simp only [CollatzResearch.WordTrace]
  refine ⟨101513868369728214979909637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67675912246485476653273091 101513868369728214979909637)
  ·
    refine ⟨19033850319324040308733057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101513868369728214979909637 19033850319324040308733057)
    ·
      refine ⟨14275387739493030231549793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19033850319324040308733057 14275387739493030231549793)
      ·
        refine ⟨10706540804619772673662345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14275387739493030231549793 10706540804619772673662345)
        ·
          refine ⟨8029905603464829505246759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10706540804619772673662345 8029905603464829505246759)
          ·
            refine ⟨12044858405197244257870139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8029905603464829505246759 12044858405197244257870139)
            ·
              refine ⟨18067287607795866386805209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12044858405197244257870139 18067287607795866386805209)
              ·
                refine ⟨13550465705846899790103907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18067287607795866386805209 13550465705846899790103907)
                ·
                  refine ⟨20325698558770349685155861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13550465705846899790103907 20325698558770349685155861)
                  ·
                    refine ⟨952767119942360141491681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20325698558770349685155861 952767119942360141491681)
                    ·
                      rfl

theorem cell22_2783261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2783261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783261 prefixEnd_2783261 := by exact prefixLift 2783261
  have htrace : WordTrace (prefixWord ++ tailWord_2783261) baseStart_2783261 baseEnd_2783261 := by
    simpa [prefixWord, tailWord_2783261, baseEnd_2783261] using wordTrace_append hprefix tailTrace_2783261
  have hstable : (prefixWord ++ tailWord_2783261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783261).length < 2 ^ (prefixWord ++ tailWord_2783261).sum := by decide
  have hdescent : baseEnd_2783261 < baseStart_2783261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783308 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 3, 3]
def baseStart_2783308 : Nat := 118140960795 + 2783308 * 2 ^ 59
def prefixEnd_2783308 : Nat := 4983230072969 + 3 ^ 40 * 2783308 * 2
def baseEnd_2783308 : Nat := 952783209002867685566537

theorem tailTrace_2783308 : CollatzResearch.WordTrace tailWord_2783308 prefixEnd_2783308 952783209002867685566537 := by
  unfold tailWord_2783308
  simp only [CollatzResearch.WordTrace]
  refine ⟨50757791300278971003435289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67677055067038628004580385 50757791300278971003435289)
  ·
    refine ⟨38068343475209228252576467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50757791300278971003435289 38068343475209228252576467)
    ·
      refine ⟨57102515212813842378864701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38068343475209228252576467 57102515212813842378864701)
      ·
        refine ⟨21413443204805190892074263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57102515212813842378864701 21413443204805190892074263)
        ·
          refine ⟨32120164807207786338111395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21413443204805190892074263 32120164807207786338111395)
          ·
            refine ⟨48180247210811679507167093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32120164807207786338111395 48180247210811679507167093)
            ·
              refine ⟨4516898176013594953796915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48180247210811679507167093 4516898176013594953796915)
              ·
                refine ⟨6775347264020392430695373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4516898176013594953796915 6775347264020392430695373)
                ·
                  refine ⟨2540755224007647161510765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6775347264020392430695373 2540755224007647161510765)
                  ·
                    refine ⟨952783209002867685566537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2540755224007647161510765 952783209002867685566537)
                    ·
                      rfl

theorem cell22_2783308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_2783308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783308 prefixEnd_2783308 := by exact prefixLift 2783308
  have htrace : WordTrace (prefixWord ++ tailWord_2783308) baseStart_2783308 baseEnd_2783308 := by
    simpa [prefixWord, tailWord_2783308, baseEnd_2783308] using wordTrace_append hprefix tailTrace_2783308
  have hstable : (prefixWord ++ tailWord_2783308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783308).length < 2 ^ (prefixWord ++ tailWord_2783308).sum := by decide
  have hdescent : baseEnd_2783308 < baseStart_2783308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783314 : List Nat := [3, 2, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_2783314 : Nat := 118140960795 + 2783314 * 2 ^ 59
def prefixEnd_2783314 : Nat := 4983230072969 + 3 ^ 40 * 2783314 * 2
def baseEnd_2783314 : Nat := 952785262925485669916519

theorem tailTrace_2783314 : CollatzResearch.WordTrace tailWord_2783314 prefixEnd_2783314 952785262925485669916519 := by
  unfold tailWord_2783314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25378950359634051257897249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67677200959024136687725997 25378950359634051257897249)
  ·
    refine ⟨19034212769725538443422937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25378950359634051257897249 19034212769725538443422937)
    ·
      refine ⟨14275659577294153832567203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19034212769725538443422937 14275659577294153832567203)
      ·
        refine ⟨21413489365941230748850805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14275659577294153832567203 21413489365941230748850805)
        ·
          refine ⟨2007514628056990382704763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21413489365941230748850805 2007514628056990382704763)
          ·
            refine ⟨3011271942085485574057145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007514628056990382704763 3011271942085485574057145)
            ·
              refine ⟨2258453956564114180542859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3011271942085485574057145 2258453956564114180542859)
              ·
                refine ⟨3387680934846171270814289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258453956564114180542859 3387680934846171270814289)
                ·
                  refine ⟨2540760701134628453110717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3387680934846171270814289 2540760701134628453110717)
                  ·
                    refine ⟨952785262925485669916519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2540760701134628453110717 952785262925485669916519)
                    ·
                      rfl

theorem cell22_2783314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_2783314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783314 prefixEnd_2783314 := by exact prefixLift 2783314
  have htrace : WordTrace (prefixWord ++ tailWord_2783314) baseStart_2783314 baseEnd_2783314 := by
    simpa [prefixWord, tailWord_2783314, baseEnd_2783314] using wordTrace_append hprefix tailTrace_2783314
  have hstable : (prefixWord ++ tailWord_2783314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783314).length < 2 ^ (prefixWord ++ tailWord_2783314).sum := by decide
  have hdescent : baseEnd_2783314 < baseStart_2783314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783321 : List Nat := [1, 2, 1, 2, 2, 1, 5, 3, 5]
def baseStart_2783321 : Nat := 118140960795 + 2783321 * 2 ^ 59
def prefixEnd_2783321 : Nat := 4983230072969 + 3 ^ 40 * 2783321 * 2
def baseEnd_2783321 : Nat := 317595886389513328330499

theorem tailTrace_2783321 : CollatzResearch.WordTrace tailWord_2783321 prefixEnd_2783321 317595886389513328330499 := by
  unfold tailWord_2783321
  simp only [CollatzResearch.WordTrace]
  refine ⟨101516056749510845227093817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67677371166340563484729211 101516056749510845227093817)
  ·
    refine ⟨76137042562133133920320363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101516056749510845227093817 76137042562133133920320363)
    ·
      refine ⟨114205563843199700880480545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76137042562133133920320363 114205563843199700880480545)
      ·
        refine ⟨85654172882399775660360409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114205563843199700880480545 85654172882399775660360409)
        ·
          refine ⟨64240629661799831745270307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85654172882399775660360409 64240629661799831745270307)
          ·
            refine ⟨96360944492699747617905461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64240629661799831745270307 96360944492699747617905461)
            ·
              refine ⟨9033838546190601339178637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96360944492699747617905461 9033838546190601339178637)
              ·
                refine ⟨3387689454821475502191989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9033838546190601339178637 3387689454821475502191989)
                ·
                  refine ⟨317595886389513328330499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3387689454821475502191989 317595886389513328330499)
                  ·
                    rfl

theorem cell22_2783321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_2783321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783321 prefixEnd_2783321 := by exact prefixLift 2783321
  have htrace : WordTrace (prefixWord ++ tailWord_2783321) baseStart_2783321 baseEnd_2783321 := by
    simpa [prefixWord, tailWord_2783321, baseEnd_2783321] using wordTrace_append hprefix tailTrace_2783321
  have hstable : (prefixWord ++ tailWord_2783321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783321).length < 2 ^ (prefixWord ++ tailWord_2783321).sum := by decide
  have hdescent : baseEnd_2783321 < baseStart_2783321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783368 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 3, 4]
def baseStart_2783368 : Nat := 118140960795 + 2783368 * 2 ^ 59
def prefixEnd_2783368 : Nat := 4983230072969 + 3 ^ 40 * 2783368 * 2
def baseEnd_2783368 : Nat := 952803748229047529066353

theorem tailTrace_2783368 : CollatzResearch.WordTrace tailWord_2783368 prefixEnd_2783368 952803748229047529066353 := by
  unfold tailWord_2783368
  simp only [CollatzResearch.WordTrace]
  refine ⟨50758885490170286127027379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67678513986893714836036505 50758885490170286127027379)
  ·
    refine ⟨76138328235255429190541069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50758885490170286127027379 76138328235255429190541069)
    ·
      refine ⟨28551873088220785946452901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76138328235255429190541069 28551873088220785946452901)
      ·
        refine ⟨5353476204041397364959919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28551873088220785946452901 5353476204041397364959919)
        ·
          refine ⟨8030214306062096047439879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5353476204041397364959919 8030214306062096047439879)
          ·
            refine ⟨12045321459093144071159819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8030214306062096047439879 12045321459093144071159819)
            ·
              refine ⟨18067982188639716106739729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12045321459093144071159819 18067982188639716106739729)
              ·
                refine ⟨13550986641479787080054797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18067982188639716106739729 13550986641479787080054797)
                ·
                  refine ⟨5081619990554920155020549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13550986641479787080054797 5081619990554920155020549)
                  ·
                    refine ⟨952803748229047529066353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5081619990554920155020549 952803748229047529066353)
                    ·
                      rfl

theorem cell22_2783368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_2783368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783368 prefixEnd_2783368 := by exact prefixLift 2783368
  have htrace : WordTrace (prefixWord ++ tailWord_2783368) baseStart_2783368 baseEnd_2783368 := by
    simpa [prefixWord, tailWord_2783368, baseEnd_2783368] using wordTrace_append hprefix tailTrace_2783368
  have hstable : (prefixWord ++ tailWord_2783368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783368).length < 2 ^ (prefixWord ++ tailWord_2783368).sum := by decide
  have hdescent : baseEnd_2783368 < baseStart_2783368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783383 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 6]
def baseStart_2783383 : Nat := 118140960795 + 2783383 * 2 ^ 59
def prefixEnd_2783383 : Nat := 4983230072969 + 3 ^ 40 * 2783383 * 2
def baseEnd_2783383 : Nat := 317602961011864163313769

theorem tailTrace_2783383 : CollatzResearch.WordTrace tailWord_2783383 prefixEnd_2783383 317602961011864163313769 := by
  unfold tailWord_2783383
  simp only [CollatzResearch.WordTrace]
  refine ⟨101518318075286229815850803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67678878716857486543900535 101518318075286229815850803)
  ·
    refine ⟨152277477112929344723776205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101518318075286229815850803 152277477112929344723776205)
    ·
      refine ⟨57104053917348504271416077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152277477112929344723776205 57104053917348504271416077)
      ·
        refine ⟨21414020219005689101781029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57104053917348504271416077 21414020219005689101781029)
        ·
          refine ⟨4015128791063566706583943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21414020219005689101781029 4015128791063566706583943)
          ·
            refine ⟨6022693186595350059875915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015128791063566706583943 6022693186595350059875915)
            ·
              refine ⟨9034039779893025089813873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6022693186595350059875915 9034039779893025089813873)
              ·
                refine ⟨6775529834919768817360405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9034039779893025089813873 6775529834919768817360405)
                ·
                  refine ⟨317602961011864163313769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6775529834919768817360405 317602961011864163313769)
                  ·
                    rfl

theorem cell22_2783383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 6].length) (baseStart_2783383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783383 prefixEnd_2783383 := by exact prefixLift 2783383
  have htrace : WordTrace (prefixWord ++ tailWord_2783383) baseStart_2783383 baseEnd_2783383 := by
    simpa [prefixWord, tailWord_2783383, baseEnd_2783383] using wordTrace_append hprefix tailTrace_2783383
  have hstable : (prefixWord ++ tailWord_2783383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783383).length < 2 ^ (prefixWord ++ tailWord_2783383).sum := by decide
  have hdescent : baseEnd_2783383 < baseStart_2783383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783402 : List Nat := [3, 1, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2783402 : Nat := 118140960795 + 2783402 * 2 ^ 59
def prefixEnd_2783402 : Nat := 4983230072969 + 3 ^ 40 * 2783402 * 2
def baseEnd_2783402 : Nat := 952815387123882773716249

theorem tailTrace_2783402 : CollatzResearch.WordTrace tailWord_2783402 prefixEnd_2783402 952815387123882773716249 := by
  unfold tailWord_2783402
  simp only [CollatzResearch.WordTrace]
  refine ⟨25379752765554349015198115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67679340708144930707194973 25379752765554349015198115)
  ·
    refine ⟨38069629148331523522797173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25379752765554349015198115 38069629148331523522797173)
    ·
      refine ⟨3569027732656080330262235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38069629148331523522797173 3569027732656080330262235)
      ·
        refine ⟨5353541598984120495393353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3569027732656080330262235 5353541598984120495393353)
        ·
          refine ⟨4015156199238090371545015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5353541598984120495393353 4015156199238090371545015)
          ·
            refine ⟨6022734298857135557317523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015156199238090371545015 6022734298857135557317523)
            ·
              refine ⟨9034101448285703335976285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6022734298857135557317523 9034101448285703335976285)
              ·
                refine ⟨3387788043107138750991107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9034101448285703335976285 3387788043107138750991107)
                ·
                  refine ⟨5081682064660708126486661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387788043107138750991107 5081682064660708126486661)
                  ·
                    refine ⟨952815387123882773716249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5081682064660708126486661 952815387123882773716249)
                    ·
                      rfl

theorem cell22_2783402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2783402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783402 prefixEnd_2783402 := by exact prefixLift 2783402
  have htrace : WordTrace (prefixWord ++ tailWord_2783402) baseStart_2783402 baseEnd_2783402 := by
    simpa [prefixWord, tailWord_2783402, baseEnd_2783402] using wordTrace_append hprefix tailTrace_2783402
  have hstable : (prefixWord ++ tailWord_2783402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783402).length < 2 ^ (prefixWord ++ tailWord_2783402).sum := by decide
  have hdescent : baseEnd_2783402 < baseStart_2783402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783415 : List Nat := [1, 1, 3, 1, 4, 2, 3, 2, 2, 3]
def baseStart_2783415 : Nat := 118140960795 + 2783415 * 2 ^ 59
def prefixEnd_2783415 : Nat := 4983230072969 + 3 ^ 40 * 2783415 * 2
def baseEnd_2783415 : Nat := 952819837289555073141209

theorem tailTrace_2783415 : CollatzResearch.WordTrace tailWord_2783415 prefixEnd_2783415 952819837289555073141209 := by
  unfold tailWord_2783415
  simp only [CollatzResearch.WordTrace]
  refine ⟨101519485211170299281015699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67679656807446866187343799 101519485211170299281015699)
  ·
    refine ⟨152279227816755448921523549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101519485211170299281015699 152279227816755448921523549)
    ·
      refine ⟨57104710431283293345571331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152279227816755448921523549 57104710431283293345571331)
      ·
        refine ⟨85657065646924940018356997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57104710431283293345571331 85657065646924940018356997)
        ·
          refine ⟨16060699808798426253441937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85657065646924940018356997 16060699808798426253441937)
          ·
            refine ⟨12045524856598819690081453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16060699808798426253441937 12045524856598819690081453)
            ·
              refine ⟨4517071821224557383780545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12045524856598819690081453 4517071821224557383780545)
              ·
                refine ⟨3387803865918418037835409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4517071821224557383780545 3387803865918418037835409)
                ·
                  refine ⟨2540852899438813528376557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3387803865918418037835409 2540852899438813528376557)
                  ·
                    refine ⟨952819837289555073141209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2540852899438813528376557 952819837289555073141209)
                    ·
                      rfl

theorem cell22_2783415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_2783415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783415 prefixEnd_2783415 := by exact prefixLift 2783415
  have htrace : WordTrace (prefixWord ++ tailWord_2783415) baseStart_2783415 baseEnd_2783415 := by
    simpa [prefixWord, tailWord_2783415, baseEnd_2783415] using wordTrace_append hprefix tailTrace_2783415
  have hstable : (prefixWord ++ tailWord_2783415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783415).length < 2 ^ (prefixWord ++ tailWord_2783415).sum := by decide
  have hdescent : baseEnd_2783415 < baseStart_2783415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783441 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 2, 6]
def baseStart_2783441 : Nat := 118140960795 + 2783441 * 2 ^ 59
def prefixEnd_2783441 : Nat := 4983230072969 + 3 ^ 40 * 2783441 * 2
def baseEnd_2783441 : Nat := 952828737620899671991129

theorem tailTrace_2783441 : CollatzResearch.WordTrace tailWord_2783441 prefixEnd_2783441 952828737620899671991129 := by
  unfold tailWord_2783441
  simp only [CollatzResearch.WordTrace]
  refine ⟨101520433509076105721462177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67680289006050737147641451 101520433509076105721462177)
  ·
    refine ⟨76140325131807079291096633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101520433509076105721462177 76140325131807079291096633)
    ·
      refine ⟨57105243848855309468322475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76140325131807079291096633 57105243848855309468322475)
      ·
        refine ⟨85657865773282964202483713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57105243848855309468322475 85657865773282964202483713)
        ·
          refine ⟨64243399329962223151862785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85657865773282964202483713 64243399329962223151862785)
          ·
            refine ⟨48182549497471667363897089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64243399329962223151862785 48182549497471667363897089)
            ·
              refine ⟨36136912123103750522922817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48182549497471667363897089 36136912123103750522922817)
              ·
                refine ⟨27102684092327812892192113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36136912123103750522922817 27102684092327812892192113)
                ·
                  refine ⟨20327013069245859669144085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27102684092327812892192113 20327013069245859669144085)
                  ·
                    refine ⟨952828737620899671991129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20327013069245859669144085 952828737620899671991129)
                    ·
                      rfl

theorem cell22_2783441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_2783441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783441 prefixEnd_2783441 := by exact prefixLift 2783441
  have htrace : WordTrace (prefixWord ++ tailWord_2783441) baseStart_2783441 baseEnd_2783441 := by
    simpa [prefixWord, tailWord_2783441, baseEnd_2783441] using wordTrace_append hprefix tailTrace_2783441
  have hstable : (prefixWord ++ tailWord_2783441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783441).length < 2 ^ (prefixWord ++ tailWord_2783441).sum := by decide
  have hdescent : baseEnd_2783441 < baseStart_2783441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783456 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 9]
def baseStart_2783456 : Nat := 118140960795 + 2783456 * 2 ^ 59
def prefixEnd_2783456 : Nat := 4983230072969 + 3 ^ 40 * 2783456 * 2
def baseEnd_2783456 : Nat := 317611290809148210955361

theorem tailTrace_2783456 : CollatzResearch.WordTrace tailWord_2783456 prefixEnd_2783456 317611290809148210955361 := by
  unfold tailWord_2783456
  simp only [CollatzResearch.WordTrace]
  refine ⟨50760490302010881641629111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67680653736014508855505481 50760490302010881641629111)
  ·
    refine ⟨76140735453016322462443667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50760490302010881641629111 76140735453016322462443667)
    ·
      refine ⟨114211103179524483693665501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76140735453016322462443667 114211103179524483693665501)
      ·
        refine ⟨42829163692321681385124563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114211103179524483693665501 42829163692321681385124563)
        ·
          refine ⟨64243745538482522077686845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42829163692321681385124563 64243745538482522077686845)
          ·
            refine ⟨24091404576930945779132567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64243745538482522077686845 24091404576930945779132567)
            ·
              refine ⟨36137106865396418668698851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24091404576930945779132567 36137106865396418668698851)
              ·
                refine ⟨54205660298094628003048277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36137106865396418668698851 54205660298094628003048277)
                ·
                  refine ⟨317611290809148210955361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54205660298094628003048277 317611290809148210955361)
                  ·
                    rfl

theorem cell22_2783456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_2783456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783456 prefixEnd_2783456 := by exact prefixLift 2783456
  have htrace : WordTrace (prefixWord ++ tailWord_2783456) baseStart_2783456 baseEnd_2783456 := by
    simpa [prefixWord, tailWord_2783456, baseEnd_2783456] using wordTrace_append hprefix tailTrace_2783456
  have hstable : (prefixWord ++ tailWord_2783456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783456).length < 2 ^ (prefixWord ++ tailWord_2783456).sum := by decide
  have hdescent : baseEnd_2783456 < baseStart_2783456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783528 : List Nat := [2, 1, 5, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2783528 : Nat := 118140960795 + 2783528 * 2 ^ 59
def prefixEnd_2783528 : Nat := 4983230072969 + 3 ^ 40 * 2783528 * 2
def baseEnd_2783528 : Nat := 952858519498860445065863

theorem tailTrace_2783528 : CollatzResearch.WordTrace tailWord_2783528 prefixEnd_2783528 952858519498860445065863 := by
  unfold tailWord_2783528
  simp only [CollatzResearch.WordTrace]
  refine ⟨50761803329880459789939619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67682404439840613053252825 50761803329880459789939619)
  ·
    refine ⟨76142704994820689684909429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50761803329880459789939619 76142704994820689684909429)
    ·
      refine ⟨7138378593264439657960259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76142704994820689684909429 7138378593264439657960259)
      ·
        refine ⟨10707567889896659486940389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7138378593264439657960259 10707567889896659486940389)
        ·
          refine ⟨2007668979355623653801323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10707567889896659486940389 2007668979355623653801323)
          ·
            refine ⟨3011503469033435480701985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007668979355623653801323 3011503469033435480701985)
            ·
              refine ⟨2258627601775076610526489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3011503469033435480701985 2258627601775076610526489)
              ·
                refine ⟨1693970701331307457894867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2258627601775076610526489 1693970701331307457894867)
                ·
                  refine ⟨2540956051996961186842301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693970701331307457894867 2540956051996961186842301)
                  ·
                    refine ⟨952858519498860445065863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2540956051996961186842301 952858519498860445065863)
                    ·
                      rfl

theorem cell22_2783528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2783528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783528 prefixEnd_2783528 := by exact prefixLift 2783528
  have htrace : WordTrace (prefixWord ++ tailWord_2783528) baseStart_2783528 baseEnd_2783528 := by
    simpa [prefixWord, tailWord_2783528, baseEnd_2783528] using wordTrace_append hprefix tailTrace_2783528
  have hstable : (prefixWord ++ tailWord_2783528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783528).length < 2 ^ (prefixWord ++ tailWord_2783528).sum := by decide
  have hdescent : baseEnd_2783528 < baseStart_2783528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783548 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_2783548 : Nat := 118140960795 + 2783548 * 2 ^ 59
def prefixEnd_2783548 : Nat := 4983230072969 + 3 ^ 40 * 2783548 * 2
def baseEnd_2783548 : Nat := 952865365907587059565801

theorem tailTrace_2783548 : CollatzResearch.WordTrace tailWord_2783548 prefixEnd_2783548 952865365907587059565801 := by
  unfold tailWord_2783548
  simp only [CollatzResearch.WordTrace]
  refine ⟨50762168059844231497803649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67682890746458975330404865 50762168059844231497803649)
  ·
    refine ⟨38071626044883173623352737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50762168059844231497803649 38071626044883173623352737)
    ·
      refine ⟨28553719533662380217514553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38071626044883173623352737 28553719533662380217514553)
      ·
        refine ⟨21415289650246785163135915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28553719533662380217514553 21415289650246785163135915)
        ·
          refine ⟨32122934475370177744703873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21415289650246785163135915 32122934475370177744703873)
          ·
            refine ⟨24092200856527633308527905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32122934475370177744703873 24092200856527633308527905)
            ·
              refine ⟨18069150642395724981395929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24092200856527633308527905 18069150642395724981395929)
              ·
                refine ⟨13551862981796793736046947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18069150642395724981395929 13551862981796793736046947)
                ·
                  refine ⟨20327794472695190604070421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13551862981796793736046947 20327794472695190604070421)
                  ·
                    refine ⟨952865365907587059565801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20327794472695190604070421 952865365907587059565801)
                    ·
                      rfl

theorem cell22_2783548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_2783548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783548 prefixEnd_2783548 := by exact prefixLift 2783548
  have htrace : WordTrace (prefixWord ++ tailWord_2783548) baseStart_2783548 baseEnd_2783548 := by
    simpa [prefixWord, tailWord_2783548, baseEnd_2783548] using wordTrace_append hprefix tailTrace_2783548
  have hstable : (prefixWord ++ tailWord_2783548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783548).length < 2 ^ (prefixWord ++ tailWord_2783548).sum := by decide
  have hdescent : baseEnd_2783548 < baseStart_2783548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783550 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2783550 : Nat := 118140960795 + 2783550 * 2 ^ 59
def prefixEnd_2783550 : Nat := 4983230072969 + 3 ^ 40 * 2783550 * 2
def baseEnd_2783550 : Nat := 952866050548459721015795

theorem tailTrace_2783550 : CollatzResearch.WordTrace tailWord_2783550 prefixEnd_2783550 952866050548459721015795 := by
  unfold tailWord_2783550
  simp only [CollatzResearch.WordTrace]
  refine ⟨12690551133210152167147513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67682939377120811558120069 12690551133210152167147513)
  ·
    refine ⟨9517913349907614125360635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12690551133210152167147513 9517913349907614125360635)
    ·
      refine ⟨14276870024861421188040953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9517913349907614125360635 14276870024861421188040953)
      ·
        refine ⟨10707652518646065891030715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14276870024861421188040953 10707652518646065891030715)
        ·
          refine ⟨16061478777969098836546073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10707652518646065891030715 16061478777969098836546073)
          ·
            refine ⟨12046109083476824127409555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16061478777969098836546073 12046109083476824127409555)
            ·
              refine ⟨18069163625215236191114333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12046109083476824127409555 18069163625215236191114333)
              ·
                refine ⟨6775936359455713571667875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18069163625215236191114333 6775936359455713571667875)
                ·
                  refine ⟨10163904539183570357501813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6775936359455713571667875 10163904539183570357501813)
                  ·
                    refine ⟨952866050548459721015795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10163904539183570357501813 952866050548459721015795)
                    ·
                      rfl

theorem cell22_2783550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2783550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783550 prefixEnd_2783550 := by exact prefixLift 2783550
  have htrace : WordTrace (prefixWord ++ tailWord_2783550) baseStart_2783550 baseEnd_2783550 := by
    simpa [prefixWord, tailWord_2783550, baseEnd_2783550] using wordTrace_append hprefix tailTrace_2783550
  have hstable : (prefixWord ++ tailWord_2783550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783550).length < 2 ^ (prefixWord ++ tailWord_2783550).sum := by decide
  have hdescent : baseEnd_2783550 < baseStart_2783550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783584 : List Nat := [2, 1, 1, 3, 5, 2, 1, 2, 2, 3]
def baseStart_2783584 : Nat := 118140960795 + 2783584 * 2 ^ 59
def prefixEnd_2783584 : Nat := 4983230072969 + 3 ^ 40 * 2783584 * 2
def baseEnd_2783584 : Nat := 952877689443294965665691

theorem tailTrace_2783584 : CollatzResearch.WordTrace tailWord_2783584 prefixEnd_2783584 952877689443294965665691 := by
  unfold tailWord_2783584
  simp only [CollatzResearch.WordTrace]
  refine ⟨50762824573779020571958903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67683766098372027429278537 50762824573779020571958903)
  ·
    refine ⟨76144236860668530857938355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50762824573779020571958903 76144236860668530857938355)
    ·
      refine ⟨114216355291002796286907533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76144236860668530857938355 114216355291002796286907533)
      ·
        refine ⟨42831133234126048607590325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114216355291002796286907533 42831133234126048607590325)
        ·
          refine ⟨4015418740699317056961593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42831133234126048607590325 4015418740699317056961593)
          ·
            refine ⟨3011564055524487792721195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4015418740699317056961593 3011564055524487792721195)
            ·
              refine ⟨4517346083286731689081793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3011564055524487792721195 4517346083286731689081793)
              ·
                refine ⟨3388009562465048766811345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4517346083286731689081793 3388009562465048766811345)
                ·
                  refine ⟨2541007171848786575108509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3388009562465048766811345 2541007171848786575108509)
                  ·
                    refine ⟨952877689443294965665691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2541007171848786575108509 952877689443294965665691)
                    ·
                      rfl

theorem cell22_2783584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 2, 3].length) (baseStart_2783584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783584 prefixEnd_2783584 := by exact prefixLift 2783584
  have htrace : WordTrace (prefixWord ++ tailWord_2783584) baseStart_2783584 baseEnd_2783584 := by
    simpa [prefixWord, tailWord_2783584, baseEnd_2783584] using wordTrace_append hprefix tailTrace_2783584
  have hstable : (prefixWord ++ tailWord_2783584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783584).length < 2 ^ (prefixWord ++ tailWord_2783584).sum := by decide
  have hdescent : baseEnd_2783584 < baseStart_2783584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783646 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2783646 : Nat := 118140960795 + 2783646 * 2 ^ 59
def prefixEnd_2783646 : Nat := 4983230072969 + 3 ^ 40 * 2783646 * 2
def baseEnd_2783646 : Nat := 952898913310347470615501

theorem tailTrace_2783646 : CollatzResearch.WordTrace tailWord_2783646 prefixEnd_2783646 952898913310347470615501 := by
  unfold tailWord_2783646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12690988809166678216584349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67685273648888950488449861 12690988809166678216584349)
  ·
    refine ⟨4759120803437504331219131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12690988809166678216584349 4759120803437504331219131)
    ·
      refine ⟨7138681205156256496828697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4759120803437504331219131 7138681205156256496828697)
      ·
        refine ⟨5354010903867192372621523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7138681205156256496828697 5354010903867192372621523)
        ·
          refine ⟨8031016355800788558932285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5354010903867192372621523 8031016355800788558932285)
          ·
            refine ⟨3011631133425295709599607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8031016355800788558932285 3011631133425295709599607)
            ·
              refine ⟨4517446700137943564399411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3011631133425295709599607 4517446700137943564399411)
              ·
                refine ⟨6776170050206915346599117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4517446700137943564399411 6776170050206915346599117)
                ·
                  refine ⟨2541063768827593254974669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6776170050206915346599117 2541063768827593254974669)
                  ·
                    refine ⟨952898913310347470615501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2541063768827593254974669 952898913310347470615501)
                    ·
                      rfl

theorem cell22_2783646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2783646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783646 prefixEnd_2783646 := by exact prefixLift 2783646
  have htrace : WordTrace (prefixWord ++ tailWord_2783646) baseStart_2783646 baseEnd_2783646 := by
    simpa [prefixWord, tailWord_2783646, baseEnd_2783646] using wordTrace_append hprefix tailTrace_2783646
  have hstable : (prefixWord ++ tailWord_2783646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783646).length < 2 ^ (prefixWord ++ tailWord_2783646).sum := by decide
  have hdescent : baseEnd_2783646 < baseStart_2783646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783702 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2783702 : Nat := 118140960795 + 2783702 * 2 ^ 59
def prefixEnd_2783702 : Nat := 4983230072969 + 3 ^ 40 * 2783702 * 2
def baseEnd_2783702 : Nat := 952918083254781991215329

theorem tailTrace_2783702 : CollatzResearch.WordTrace tailWord_2783702 prefixEnd_2783702 952918083254781991215329 := by
  unfold tailWord_2783702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6345622060070659206044585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67686635307420364864475573 6345622060070659206044585)
  ·
    refine ⟨4759216545052994404533439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6345622060070659206044585 4759216545052994404533439)
    ·
      refine ⟨7138824817579491606800159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4759216545052994404533439 7138824817579491606800159)
      ·
        refine ⟨10708237226369237410200239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7138824817579491606800159 10708237226369237410200239)
        ·
          refine ⟨16062355839553856115300359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10708237226369237410200239 16062355839553856115300359)
          ·
            refine ⟨24093533759330784172950539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16062355839553856115300359 24093533759330784172950539)
            ·
              refine ⟨36140300638996176259425809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24093533759330784172950539 36140300638996176259425809)
              ·
                refine ⟨27105225479247132194569357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36140300638996176259425809 27105225479247132194569357)
                ·
                  refine ⟨10164459554717674572963509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27105225479247132194569357 10164459554717674572963509)
                  ·
                    refine ⟨952918083254781991215329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10164459554717674572963509 952918083254781991215329)
                    ·
                      rfl

theorem cell22_2783702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2783702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783702 prefixEnd_2783702 := by exact prefixLift 2783702
  have htrace : WordTrace (prefixWord ++ tailWord_2783702) baseStart_2783702 baseEnd_2783702 := by
    simpa [prefixWord, tailWord_2783702, baseEnd_2783702] using wordTrace_append hprefix tailTrace_2783702
  have hstable : (prefixWord ++ tailWord_2783702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783702).length < 2 ^ (prefixWord ++ tailWord_2783702).sum := by decide
  have hdescent : baseEnd_2783702 < baseStart_2783702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783783 : List Nat := [1, 1, 7, 2, 2, 1, 2, 6]
def baseStart_2783783 : Nat := 118140960795 + 2783783 * 2 ^ 59
def prefixEnd_2783783 : Nat := 4983230072969 + 3 ^ 40 * 2783783 * 2
def baseEnd_2783783 : Nat := 105882867912236086660009

theorem tailTrace_2783783 : CollatzResearch.WordTrace tailWord_2783783 prefixEnd_2783783 105882867912236086660009 := by
  unfold tailWord_2783783
  simp only [CollatzResearch.WordTrace]
  refine ⟨101532907273837098130412003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67688604849224732086941335 101532907273837098130412003)
  ·
    refine ⟨152299360910755647195618005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101532907273837098130412003 152299360910755647195618005)
    ·
      refine ⟨3569516271345835481147297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 152299360910755647195618005 3569516271345835481147297)
      ·
        refine ⟨2677137203509376610860473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3569516271345835481147297 2677137203509376610860473)
        ·
          refine ⟨2007852902632032458145355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2677137203509376610860473 2007852902632032458145355)
          ·
            refine ⟨3011779353948048687218033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007852902632032458145355 3011779353948048687218033)
            ·
              refine ⟨2258834515461036515413525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3011779353948048687218033 2258834515461036515413525)
              ·
                refine ⟨105882867912236086660009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2258834515461036515413525 105882867912236086660009)
                ·
                  rfl

theorem cell22_2783783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 6].length) (baseStart_2783783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783783 prefixEnd_2783783 := by exact prefixLift 2783783
  have htrace : WordTrace (prefixWord ++ tailWord_2783783) baseStart_2783783 baseEnd_2783783 := by
    simpa [prefixWord, tailWord_2783783, baseEnd_2783783] using wordTrace_append hprefix tailTrace_2783783
  have hstable : (prefixWord ++ tailWord_2783783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783783).length < 2 ^ (prefixWord ++ tailWord_2783783).sum := by decide
  have hdescent : baseEnd_2783783 < baseStart_2783783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783798 : List Nat := [5, 1, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2783798 : Nat := 118140960795 + 2783798 * 2 ^ 59
def prefixEnd_2783798 : Nat := 4983230072969 + 3 ^ 40 * 2783798 * 2
def baseEnd_2783798 : Nat := 952950946016669740815035

theorem tailTrace_2783798 : CollatzResearch.WordTrace tailWord_2783798 prefixEnd_2783798 952950946016669740815035 := by
  unfold tailWord_2783798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6345840898048922230763003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67688969579188503794805365 6345840898048922230763003)
  ·
    refine ⟨9518761347073383346144505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6345840898048922230763003 9518761347073383346144505)
    ·
      refine ⟨7139071010305037509608379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9518761347073383346144505 7139071010305037509608379)
      ·
        refine ⟨10708606515457556264412569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7139071010305037509608379 10708606515457556264412569)
        ·
          refine ⟨8031454886593167198309427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10708606515457556264412569 8031454886593167198309427)
          ·
            refine ⟨12047182329889750797464141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8031454886593167198309427 12047182329889750797464141)
            ·
              refine ⟨4517693373708656549049053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12047182329889750797464141 4517693373708656549049053)
              ·
                refine ⟨1694135015140746205893395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4517693373708656549049053 1694135015140746205893395)
                ·
                  refine ⟨2541202522711119308840093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694135015140746205893395 2541202522711119308840093)
                  ·
                    refine ⟨952950946016669740815035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2541202522711119308840093 952950946016669740815035)
                    ·
                      rfl

theorem cell22_2783798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2783798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783798 prefixEnd_2783798 := by exact prefixLift 2783798
  have htrace : WordTrace (prefixWord ++ tailWord_2783798) baseStart_2783798 baseEnd_2783798 := by
    simpa [prefixWord, tailWord_2783798, baseEnd_2783798] using wordTrace_append hprefix tailTrace_2783798
  have hstable : (prefixWord ++ tailWord_2783798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783798).length < 2 ^ (prefixWord ++ tailWord_2783798).sum := by decide
  have hdescent : baseEnd_2783798 < baseStart_2783798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783807 : List Nat := [1, 1, 2, 2, 3, 2, 1, 5, 1, 4]
def baseStart_2783807 : Nat := 118140960795 + 2783807 * 2 ^ 59
def prefixEnd_2783807 : Nat := 4983230072969 + 3 ^ 40 * 2783807 * 2
def baseEnd_2783807 : Nat := 952954026900596717340007

theorem tailTrace_2783807 : CollatzResearch.WordTrace tailWord_2783807 prefixEnd_2783807 952954026900596717340007 := by
  unfold tailWord_2783807
  simp only [CollatzResearch.WordTrace]
  refine ⟨101533782625750150229285675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67689188417166766819523783 101533782625750150229285675)
  ·
    refine ⟨152300673938625225343928513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101533782625750150229285675 152300673938625225343928513)
    ·
      refine ⟨114225505453968919007946385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152300673938625225343928513 114225505453968919007946385)
      ·
        refine ⟨85669129090476689255959789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114225505453968919007946385 85669129090476689255959789)
        ·
          refine ⟨32125923408928758470984921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85669129090476689255959789 32125923408928758470984921)
          ·
            refine ⟨24094442556696568853238691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32125923408928758470984921 24094442556696568853238691)
            ·
              refine ⟨36141663835044853279858037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24094442556696568853238691 36141663835044853279858037)
              ·
                refine ⟨3388280984535454994986691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36141663835044853279858037 3388280984535454994986691)
                ·
                  refine ⟨5082421476803182492480037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388280984535454994986691 5082421476803182492480037)
                  ·
                    refine ⟨952954026900596717340007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5082421476803182492480037 952954026900596717340007)
                    ·
                      rfl

theorem cell22_2783807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_2783807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783807 prefixEnd_2783807 := by exact prefixLift 2783807
  have htrace : WordTrace (prefixWord ++ tailWord_2783807) baseStart_2783807 baseEnd_2783807 := by
    simpa [prefixWord, tailWord_2783807, baseEnd_2783807] using wordTrace_append hprefix tailTrace_2783807
  have hstable : (prefixWord ++ tailWord_2783807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783807).length < 2 ^ (prefixWord ++ tailWord_2783807).sum := by decide
  have hdescent : baseEnd_2783807 < baseStart_2783807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783822 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_2783822 : Nat := 118140960795 + 2783822 * 2 ^ 59
def prefixEnd_2783822 : Nat := 4983230072969 + 3 ^ 40 * 2783822 * 2
def baseEnd_2783822 : Nat := 317653053902380559404987

theorem tailTrace_2783822 : CollatzResearch.WordTrace tailWord_2783822 prefixEnd_2783822 317653053902380559404987 := by
  unfold tailWord_2783822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12691791215086975973885215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67689553147130538527387813 12691791215086975973885215)
  ·
    refine ⟨19037686822630463960827823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12691791215086975973885215 19037686822630463960827823)
    ·
      refine ⟨28556530233945695941241735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19037686822630463960827823 28556530233945695941241735)
      ·
        refine ⟨42834795350918543911862603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28556530233945695941241735 42834795350918543911862603)
        ·
          refine ⟨64252193026377815867793905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42834795350918543911862603 64252193026377815867793905)
          ·
            refine ⟨48189144769783361900845429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64252193026377815867793905 48189144769783361900845429)
            ·
              refine ⟨4517732322167190178204259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48189144769783361900845429 4517732322167190178204259)
              ·
                refine ⟨6776598483250785267306389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4517732322167190178204259 6776598483250785267306389)
                ·
                  refine ⟨317653053902380559404987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6776598483250785267306389 317653053902380559404987)
                  ·
                    rfl

theorem cell22_2783822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_2783822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783822 prefixEnd_2783822 := by exact prefixLift 2783822
  have htrace : WordTrace (prefixWord ++ tailWord_2783822) baseStart_2783822 baseEnd_2783822 := by
    simpa [prefixWord, tailWord_2783822, baseEnd_2783822] using wordTrace_append hprefix tailTrace_2783822
  have hstable : (prefixWord ++ tailWord_2783822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783822).length < 2 ^ (prefixWord ++ tailWord_2783822).sum := by decide
  have hdescent : baseEnd_2783822 < baseStart_2783822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783852 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_2783852 : Nat := 118140960795 + 2783852 * 2 ^ 59
def prefixEnd_2783852 : Nat := 4983230072969 + 3 ^ 40 * 2783852 * 2
def baseEnd_2783852 : Nat := 952969431320231599964869

theorem tailTrace_2783852 : CollatzResearch.WordTrace tailWord_2783852 prefixEnd_2783852 952969431320231599964869 := by
  unfold tailWord_2783852
  simp only [CollatzResearch.WordTrace]
  refine ⟨50767711955293561457336905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67690282607058081943115873 50767711955293561457336905)
  ·
    refine ⟨38075783966470171093002679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50767711955293561457336905 38075783966470171093002679)
    ·
      refine ⟨57113675949705256639504019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38075783966470171093002679 57113675949705256639504019)
      ·
        refine ⟨85670513924557884959256029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57113675949705256639504019 85670513924557884959256029)
        ·
          refine ⟨32126442721709206859721011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85670513924557884959256029 32126442721709206859721011)
          ·
            refine ⟨48189664082563810289581517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32126442721709206859721011 48189664082563810289581517)
            ·
              refine ⟨18071124030961428858593069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48189664082563810289581517 18071124030961428858593069)
              ·
                refine ⟨6776671511610535821972401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18071124030961428858593069 6776671511610535821972401)
                ·
                  refine ⟨5082503633707901866479301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6776671511610535821972401 5082503633707901866479301)
                  ·
                    refine ⟨952969431320231599964869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5082503633707901866479301 952969431320231599964869)
                    ·
                      rfl

theorem cell22_2783852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_2783852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783852 prefixEnd_2783852 := by exact prefixLift 2783852
  have htrace : WordTrace (prefixWord ++ tailWord_2783852) baseStart_2783852 baseEnd_2783852 := by
    simpa [prefixWord, tailWord_2783852, baseEnd_2783852] using wordTrace_append hprefix tailTrace_2783852
  have hstable : (prefixWord ++ tailWord_2783852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783852).length < 2 ^ (prefixWord ++ tailWord_2783852).sum := by decide
  have hdescent : baseEnd_2783852 < baseStart_2783852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783854 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2783854 : Nat := 118140960795 + 2783854 * 2 ^ 59
def prefixEnd_2783854 : Nat := 4983230072969 + 3 ^ 40 * 2783854 * 2
def baseEnd_2783854 : Nat := 952970115961104261414863

theorem tailTrace_2783854 : CollatzResearch.WordTrace tailWord_2783854 prefixEnd_2783854 952970115961104261414863 := by
  unfold tailWord_2783854
  simp only [CollatzResearch.WordTrace]
  refine ⟨12691937107072484657030827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67690331237719918170831077 12691937107072484657030827)
  ·
    refine ⟨19037905660608726985546241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12691937107072484657030827 19037905660608726985546241)
    ·
      refine ⟨14278429245456545239159681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19037905660608726985546241 14278429245456545239159681)
      ·
        refine ⟨10708821934092408929369761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14278429245456545239159681 10708821934092408929369761)
        ·
          refine ⟨8031616450569306697027321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10708821934092408929369761 8031616450569306697027321)
          ·
            refine ⟨6023712337926980022770491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8031616450569306697027321 6023712337926980022770491)
            ·
              refine ⟨9035568506890470034155737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6023712337926980022770491 9035568506890470034155737)
              ·
                refine ⟨6776676380167852525616803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9035568506890470034155737 6776676380167852525616803)
                ·
                  refine ⟨10165014570251778788425205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776676380167852525616803 10165014570251778788425205)
                  ·
                    refine ⟨952970115961104261414863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10165014570251778788425205 952970115961104261414863)
                    ·
                      rfl

theorem cell22_2783854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2783854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783854 prefixEnd_2783854 := by exact prefixLift 2783854
  have htrace : WordTrace (prefixWord ++ tailWord_2783854) baseStart_2783854 baseEnd_2783854 := by
    simpa [prefixWord, tailWord_2783854, baseEnd_2783854] using wordTrace_append hprefix tailTrace_2783854
  have hstable : (prefixWord ++ tailWord_2783854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783854).length < 2 ^ (prefixWord ++ tailWord_2783854).sum := by decide
  have hdescent : baseEnd_2783854 < baseStart_2783854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783946 : List Nat := [3, 1, 2, 1, 4, 2, 3, 1, 5]
def baseStart_2783946 : Nat := 118140960795 + 2783946 * 2 ^ 59
def prefixEnd_2783946 : Nat := 4983230072969 + 3 ^ 40 * 2783946 * 2
def baseEnd_2783946 : Nat := 317667203147082229371527

theorem tailTrace_2783946 : CollatzResearch.WordTrace tailWord_2783946 prefixEnd_2783946 317667203147082229371527 := by
  unfold tailWord_2783946
  simp only [CollatzResearch.WordTrace]
  refine ⟨25384713093061644242148923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67692568248164384645730461 25384713093061644242148923)
  ·
    refine ⟨38077069639592466363223385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25384713093061644242148923 38077069639592466363223385)
    ·
      refine ⟨28557802229694349772417539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38077069639592466363223385 28557802229694349772417539)
      ·
        refine ⟨42836703344541524658626309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28557802229694349772417539 42836703344541524658626309)
        ·
          refine ⟨8031881877101535873492433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42836703344541524658626309 8031881877101535873492433)
          ·
            refine ⟨6023911407826151905119325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8031881877101535873492433 6023911407826151905119325)
            ·
              refine ⟨2258966777934806964419747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6023911407826151905119325 2258966777934806964419747)
              ·
                refine ⟨3388450166902210446629621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258966777934806964419747 3388450166902210446629621)
                ·
                  refine ⟨317667203147082229371527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3388450166902210446629621 317667203147082229371527)
                  ·
                    rfl

theorem cell22_2783946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_2783946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783946 prefixEnd_2783946 := by exact prefixLift 2783946
  have htrace : WordTrace (prefixWord ++ tailWord_2783946) baseStart_2783946 baseEnd_2783946 := by
    simpa [prefixWord, tailWord_2783946, baseEnd_2783946] using wordTrace_append hprefix tailTrace_2783946
  have hstable : (prefixWord ++ tailWord_2783946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783946).length < 2 ^ (prefixWord ++ tailWord_2783946).sum := by decide
  have hdescent : baseEnd_2783946 < baseStart_2783946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783959 : List Nat := [1, 1, 3, 2, 1, 4, 1, 4, 1, 4]
def baseStart_2783959 : Nat := 118140960795 + 2783959 * 2 ^ 59
def prefixEnd_2783959 : Nat := 4983230072969 + 3 ^ 40 * 2783959 * 2
def baseEnd_2783959 : Nat := 953006059606918987539541

theorem tailTrace_2783959 : CollatzResearch.WordTrace tailWord_2783959 prefixEnd_2783959 953006059606918987539541 := by
  unfold tailWord_2783959
  simp only [CollatzResearch.WordTrace]
  refine ⟨101539326521199480188818931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67692884347466320125879287 101539326521199480188818931)
  ·
    refine ⟨152308989781799220283228397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101539326521199480188818931 152308989781799220283228397)
    ·
      refine ⟨57115871168174707606210649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152308989781799220283228397 57115871168174707606210649)
      ·
        refine ⟨42836903376131030704657987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57115871168174707606210649 42836903376131030704657987)
        ·
          refine ⟨64255355064196546056986981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42836903376131030704657987 64255355064196546056986981)
          ·
            refine ⟨12047879074536852385685059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64255355064196546056986981 12047879074536852385685059)
            ·
              refine ⟨18071818611805278578527589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12047879074536852385685059 18071818611805278578527589)
              ·
                refine ⟨3388465989713489733473923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18071818611805278578527589 3388465989713489733473923)
                ·
                  refine ⟨5082698984570234600210885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388465989713489733473923 5082698984570234600210885)
                  ·
                    refine ⟨953006059606918987539541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5082698984570234600210885 953006059606918987539541)
                    ·
                      rfl

theorem cell22_2783959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_2783959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783959 prefixEnd_2783959 := by exact prefixLift 2783959
  have htrace : WordTrace (prefixWord ++ tailWord_2783959) baseStart_2783959 baseEnd_2783959 := by
    simpa [prefixWord, tailWord_2783959, baseEnd_2783959] using wordTrace_append hprefix tailTrace_2783959
  have hstable : (prefixWord ++ tailWord_2783959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783959).length < 2 ^ (prefixWord ++ tailWord_2783959).sum := by decide
  have hdescent : baseEnd_2783959 < baseStart_2783959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784004 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_2784004 : Nat := 118140960795 + 2784004 * 2 ^ 59
def prefixEnd_2784004 : Nat := 4983230072969 + 3 ^ 40 * 2784004 * 2
def baseEnd_2784004 : Nat := 953021464026553870164403

theorem tailTrace_2784004 : CollatzResearch.WordTrace tailWord_2784004 prefixEnd_2784004 953021464026553870164403 := by
  unfold tailWord_2784004
  simp only [CollatzResearch.WordTrace]
  refine ⟨50770483903018226437103533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67693978537357635249471377 50770483903018226437103533)
  ·
    refine ⟨19038931463631834913913825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50770483903018226437103533 19038931463631834913913825)
    ·
      refine ⟨14279198597723876185435369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19038931463631834913913825 14279198597723876185435369)
      ·
        refine ⟨10709398948292907139076527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14279198597723876185435369 10709398948292907139076527)
        ·
          refine ⟨16064098422439360708614791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10709398948292907139076527 16064098422439360708614791)
          ·
            refine ⟨24096147633659041062922187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16064098422439360708614791 24096147633659041062922187)
            ·
              refine ⟨36144221450488561594383281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24096147633659041062922187 36144221450488561594383281)
              ·
                refine ⟨27108166087866421195787461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36144221450488561594383281 27108166087866421195787461)
                ·
                  refine ⟨5082781141474953974210149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27108166087866421195787461 5082781141474953974210149)
                  ·
                    refine ⟨953021464026553870164403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5082781141474953974210149 953021464026553870164403)
                    ·
                      rfl

theorem cell22_2784004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_2784004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784004 prefixEnd_2784004 := by exact prefixLift 2784004
  have htrace : WordTrace (prefixWord ++ tailWord_2784004) baseStart_2784004 baseEnd_2784004 := by
    simpa [prefixWord, tailWord_2784004, baseEnd_2784004] using wordTrace_append hprefix tailTrace_2784004
  have hstable : (prefixWord ++ tailWord_2784004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784004).length < 2 ^ (prefixWord ++ tailWord_2784004).sum := by decide
  have hdescent : baseEnd_2784004 < baseStart_2784004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784017 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 2, 7]
def baseStart_2784017 : Nat := 118140960795 + 2784017 * 2 ^ 59
def prefixEnd_2784017 : Nat := 4983230072969 + 3 ^ 40 * 2784017 * 2
def baseEnd_2784017 : Nat := 953025914192226169589363

theorem tailTrace_2784017 : CollatzResearch.WordTrace tailWord_2784017 prefixEnd_2784017 953025914192226169589363 := by
  unfold tailWord_2784017
  simp only [CollatzResearch.WordTrace]
  refine ⟨101541441954989356094430305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67694294636659570729620203 101541441954989356094430305)
  ·
    refine ⟨76156081466242017070822729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101541441954989356094430305 76156081466242017070822729)
    ·
      refine ⟨57117061099681512803117047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76156081466242017070822729 57117061099681512803117047)
      ·
        refine ⟨85675591649522269204675571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57117061099681512803117047 85675591649522269204675571)
        ·
          refine ⟨128513387474283403807013357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85675591649522269204675571 128513387474283403807013357)
          ·
            refine ⟨48192520302856276427630009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128513387474283403807013357 48192520302856276427630009)
            ·
              refine ⟨36144390227142207320722507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48192520302856276427630009 36144390227142207320722507)
              ·
                refine ⟨54216585340713310981083761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36144390227142207320722507 54216585340713310981083761)
                ·
                  refine ⟨40662439005534983235812821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54216585340713310981083761 40662439005534983235812821)
                  ·
                    refine ⟨953025914192226169589363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40662439005534983235812821 953025914192226169589363)
                    ·
                      rfl

theorem cell22_2784017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_2784017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784017 prefixEnd_2784017 := by exact prefixLift 2784017
  have htrace : WordTrace (prefixWord ++ tailWord_2784017) baseStart_2784017 baseEnd_2784017 := by
    simpa [prefixWord, tailWord_2784017, baseEnd_2784017] using wordTrace_append hprefix tailTrace_2784017
  have hstable : (prefixWord ++ tailWord_2784017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784017).length < 2 ^ (prefixWord ++ tailWord_2784017).sum := by decide
  have hdescent : baseEnd_2784017 < baseStart_2784017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784042 : List Nat := [3, 1, 4, 3, 1, 2, 2, 2, 4]
def baseStart_2784042 : Nat := 118140960795 + 2784042 * 2 ^ 59
def prefixEnd_2784042 : Nat := 4983230072969 + 3 ^ 40 * 2784042 * 2
def baseEnd_2784042 : Nat := 317678157401044812571429

theorem tailTrace_2784042 : CollatzResearch.WordTrace tailWord_2784042 prefixEnd_2784042 317678157401044812571429 := by
  unfold tailWord_2784042
  simp only [CollatzResearch.WordTrace]
  refine ⟨25385588444974696341022595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67694902519932523576060253 25385588444974696341022595)
  ·
    refine ⟨38078382667462044511533893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25385588444974696341022595 38078382667462044511533893)
    ·
      refine ⟨7139696750149133345912605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38078382667462044511533893 7139696750149133345912605)
      ·
        refine ⟨2677386281305925004717227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7139696750149133345912605 2677386281305925004717227)
        ·
          refine ⟨4016079421958887507075841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677386281305925004717227 4016079421958887507075841)
          ·
            refine ⟨3012059566469165630306881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4016079421958887507075841 3012059566469165630306881)
            ·
              refine ⟨2259044674851874222730161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3012059566469165630306881 2259044674851874222730161)
              ·
                refine ⟨1694283506138905667047621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2259044674851874222730161 1694283506138905667047621)
                ·
                  refine ⟨317678157401044812571429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1694283506138905667047621 317678157401044812571429)
                  ·
                    rfl

theorem cell22_2784042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_2784042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784042 prefixEnd_2784042 := by exact prefixLift 2784042
  have htrace : WordTrace (prefixWord ++ tailWord_2784042) baseStart_2784042 baseEnd_2784042 := by
    simpa [prefixWord, tailWord_2784042, baseEnd_2784042] using wordTrace_append hprefix tailTrace_2784042
  have hstable : (prefixWord ++ tailWord_2784042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784042).length < 2 ^ (prefixWord ++ tailWord_2784042).sum := by decide
  have hdescent : baseEnd_2784042 < baseStart_2784042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784070 : List Nat := [6, 1, 1, 2, 2, 1, 3, 6]
def baseStart_2784070 : Nat := 118140960795 + 2784070 * 2 ^ 59
def prefixEnd_2784070 : Nat := 4983230072969 + 3 ^ 40 * 2784070 * 2
def baseEnd_2784070 : Nat := 105893784130594633112689

theorem tailTrace_2784070 : CollatzResearch.WordTrace tailWord_2784070 prefixEnd_2784070 105893784130594633112689 := by
  unfold tailWord_2784070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173230469493667067065927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67695583349198230764073109 3173230469493667067065927)
  ·
    refine ⟨4759845704240500600598891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3173230469493667067065927 4759845704240500600598891)
    ·
      refine ⟨7139768556360750900898337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4759845704240500600598891 7139768556360750900898337)
      ·
        refine ⟨5354826417270563175673753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7139768556360750900898337 5354826417270563175673753)
        ·
          refine ⟨4016119812952922381755315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5354826417270563175673753 4016119812952922381755315)
          ·
            refine ⟨6024179719429383572632973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016119812952922381755315 6024179719429383572632973)
            ·
              refine ⟨2259067394786018839737365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6024179719429383572632973 2259067394786018839737365)
              ·
                refine ⟨105893784130594633112689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2259067394786018839737365 105893784130594633112689)
                ·
                  rfl

theorem cell22_2784070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_2784070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784070 prefixEnd_2784070 := by exact prefixLift 2784070
  have htrace : WordTrace (prefixWord ++ tailWord_2784070) baseStart_2784070 baseEnd_2784070 := by
    simpa [prefixWord, tailWord_2784070, baseEnd_2784070] using wordTrace_append hprefix tailTrace_2784070
  have hstable : (prefixWord ++ tailWord_2784070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784070).length < 2 ^ (prefixWord ++ tailWord_2784070).sum := by decide
  have hdescent : baseEnd_2784070 < baseStart_2784070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784139 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 1, 6]
def baseStart_2784139 : Nat := 118140960795 + 2784139 * 2 ^ 59
def prefixEnd_2784139 : Nat := 4983230072969 + 3 ^ 40 * 2784139 * 2
def baseEnd_2784139 : Nat := 953067677285458518038989

theorem tailTrace_2784139 : CollatzResearch.WordTrace tailWord_2784139 prefixEnd_2784139 953067677285458518038989 := by
  unfold tailWord_2784139
  simp only [CollatzResearch.WordTrace]
  refine ⟨101545891660547370930371471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67697261107031580620247647 101545891660547370930371471)
  ·
    refine ⟨152318837490821056395557207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101545891660547370930371471 152318837490821056395557207)
    ·
      refine ⟨228478256236231584593335811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152318837490821056395557207 228478256236231584593335811)
      ·
        refine ⟨342717384354347376890003717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228478256236231584593335811 342717384354347376890003717)
        ·
          refine ⟨64259509566440133166875697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 342717384354347376890003717 64259509566440133166875697)
          ·
            refine ⟨48194632174830099875156773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64259509566440133166875697 48194632174830099875156773)
            ·
              refine ⟨9036493532780643726591895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48194632174830099875156773 9036493532780643726591895)
              ·
                refine ⟨13554740299170965589887843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9036493532780643726591895 13554740299170965589887843)
                ·
                  refine ⟨20332110448756448384831765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13554740299170965589887843 20332110448756448384831765)
                  ·
                    refine ⟨953067677285458518038989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20332110448756448384831765 953067677285458518038989)
                    ·
                      rfl

theorem cell22_2784139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 6].length) (baseStart_2784139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784139 prefixEnd_2784139 := by exact prefixLift 2784139
  have htrace : WordTrace (prefixWord ++ tailWord_2784139) baseStart_2784139 baseEnd_2784139 := by
    simpa [prefixWord, tailWord_2784139, baseEnd_2784139] using wordTrace_append hprefix tailTrace_2784139
  have hstable : (prefixWord ++ tailWord_2784139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784139).length < 2 ^ (prefixWord ++ tailWord_2784139).sum := by decide
  have hdescent : baseEnd_2784139 < baseStart_2784139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784186 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 5, 3]
def baseStart_2784186 : Nat := 118140960795 + 2784186 * 2 ^ 59
def prefixEnd_2784186 : Nat := 4983230072969 + 3 ^ 40 * 2784186 * 2
def baseEnd_2784186 : Nat := 953083766345966062113845

theorem tailTrace_2784186 : CollatzResearch.WordTrace tailWord_2784186 prefixEnd_2784186 953083766345966062113845 := by
  unfold tailWord_2784186
  simp only [CollatzResearch.WordTrace]
  refine ⟨25386901472844274489333103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67698403927584731971554941 25386901472844274489333103)
  ·
    refine ⟨38080352209266411733999655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25386901472844274489333103 38080352209266411733999655)
    ·
      refine ⟨57120528313899617600999483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38080352209266411733999655 57120528313899617600999483)
      ·
        refine ⟨85680792470849426401499225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57120528313899617600999483 85680792470849426401499225)
        ·
          refine ⟨64260594353137069801124419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85680792470849426401499225 64260594353137069801124419)
          ·
            refine ⟨96390891529705604701686629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64260594353137069801124419 96390891529705604701686629)
            ·
              refine ⟨18073292161819800881566243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96390891529705604701686629 18073292161819800881566243)
              ·
                refine ⟨27109938242729701322349365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18073292161819800881566243 27109938242729701322349365)
                ·
                  refine ⟨2541556710255909498970253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27109938242729701322349365 2541556710255909498970253)
                  ·
                    refine ⟨953083766345966062113845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2541556710255909498970253 953083766345966062113845)
                    ·
                      rfl

theorem cell22_2784186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_2784186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784186 prefixEnd_2784186 := by exact prefixLift 2784186
  have htrace : WordTrace (prefixWord ++ tailWord_2784186) baseStart_2784186 baseEnd_2784186 := by
    simpa [prefixWord, tailWord_2784186, baseEnd_2784186] using wordTrace_append hprefix tailTrace_2784186
  have hstable : (prefixWord ++ tailWord_2784186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784186).length < 2 ^ (prefixWord ++ tailWord_2784186).sum := by decide
  have hdescent : baseEnd_2784186 < baseStart_2784186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784199 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 9]
def baseStart_2784199 : Nat := 118140960795 + 2784199 * 2 ^ 59
def prefixEnd_2784199 : Nat := 4983230072969 + 3 ^ 40 * 2784199 * 2
def baseEnd_2784199 : Nat := 317696072170546120512935

theorem tailTrace_2784199 : CollatzResearch.WordTrace tailWord_2784199 prefixEnd_2784199 317696072170546120512935 := by
  unfold tailWord_2784199
  simp only [CollatzResearch.WordTrace]
  refine ⟨101548080040330001177555651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67698720026886667451703767 101548080040330001177555651)
  ·
    refine ⟨152322120060495001766333477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101548080040330001177555651 152322120060495001766333477)
    ·
      refine ⟨28560397511342812831187527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152322120060495001766333477 28560397511342812831187527)
      ·
        refine ⟨42840596267014219246781291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28560397511342812831187527 42840596267014219246781291)
        ·
          refine ⟨64260894400521328870171937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42840596267014219246781291 64260894400521328870171937)
          ·
            refine ⟨48195670800390996652628953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64260894400521328870171937 48195670800390996652628953)
            ·
              refine ⟨36146753100293247489471715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48195670800390996652628953 36146753100293247489471715)
              ·
                refine ⟨54220129650439871234207573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36146753100293247489471715 54220129650439871234207573)
                ·
                  refine ⟨317696072170546120512935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54220129650439871234207573 317696072170546120512935)
                  ·
                    rfl

theorem cell22_2784199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 9].length) (baseStart_2784199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784199 prefixEnd_2784199 := by exact prefixLift 2784199
  have htrace : WordTrace (prefixWord ++ tailWord_2784199) baseStart_2784199 baseEnd_2784199 := by
    simpa [prefixWord, tailWord_2784199, baseEnd_2784199] using wordTrace_append hprefix tailTrace_2784199
  have hstable : (prefixWord ++ tailWord_2784199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784199).length < 2 ^ (prefixWord ++ tailWord_2784199).sum := by decide
  have hdescent : baseEnd_2784199 < baseStart_2784199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784205 : List Nat := [1, 6, 3, 1, 1, 10]
def baseStart_2784205 : Nat := 118140960795 + 2784205 * 2 ^ 59
def prefixEnd_2784205 : Nat := 4983230072969 + 3 ^ 40 * 2784205 * 2
def baseEnd_2784205 : Nat := 11766546548571065998627

theorem tailTrace_2784205 : CollatzResearch.WordTrace tailWord_2784205 prefixEnd_2784205 11766546548571065998627 := by
  unfold tailWord_2784205
  simp only [CollatzResearch.WordTrace]
  refine ⟨101548298878308264202274069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67698865918872176134849379 101548298878308264202274069)
  ·
    refine ⟨4760076509920699884481597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101548298878308264202274069 4760076509920699884481597)
    ·
      refine ⟨1785028691220262456680599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4760076509920699884481597 1785028691220262456680599)
      ·
        refine ⟨2677543036830393685020899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785028691220262456680599 2677543036830393685020899)
        ·
          refine ⟨4016314555245590527531349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677543036830393685020899 4016314555245590527531349)
          ·
            refine ⟨11766546548571065998627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4016314555245590527531349 11766546548571065998627)
            ·
              rfl

theorem cell22_2784205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 10].length) (baseStart_2784205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784205 prefixEnd_2784205 := by exact prefixLift 2784205
  have htrace : WordTrace (prefixWord ++ tailWord_2784205) baseStart_2784205 baseEnd_2784205 := by
    simpa [prefixWord, tailWord_2784205, baseEnd_2784205] using wordTrace_append hprefix tailTrace_2784205
  have hstable : (prefixWord ++ tailWord_2784205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784205).length < 2 ^ (prefixWord ++ tailWord_2784205).sum := by decide
  have hdescent : baseEnd_2784205 < baseStart_2784205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784216 : List Nat := [2, 1, 2, 2, 2, 3, 1, 4, 5]
def baseStart_2784216 : Nat := 118140960795 + 2784216 * 2 ^ 59
def prefixEnd_2784216 : Nat := 4983230072969 + 3 ^ 40 * 2784216 * 2
def baseEnd_2784216 : Nat := 317698011986351994621251

theorem tailTrace_2784216 : CollatzResearch.WordTrace tailWord_2784216 prefixEnd_2784216 317698011986351994621251 := by
  unfold tailWord_2784216
  simp only [CollatzResearch.WordTrace]
  refine ⟨50774350040634206540462251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67699133387512275387283001 50774350040634206540462251)
  ·
    refine ⟨76161525060951309810693377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50774350040634206540462251 76161525060951309810693377)
    ·
      refine ⟨57121143795713482358020033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76161525060951309810693377 57121143795713482358020033)
      ·
        refine ⟨42840857846785111768515025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57121143795713482358020033 42840857846785111768515025)
        ·
          refine ⟨32130643385088833826386269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42840857846785111768515025 32130643385088833826386269)
          ·
            refine ⟨12048991269408312684894851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32130643385088833826386269 12048991269408312684894851)
            ·
              refine ⟨18073486904112469027342277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12048991269408312684894851 18073486904112469027342277)
              ·
                refine ⟨3388778794521087942626677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18073486904112469027342277 3388778794521087942626677)
                ·
                  refine ⟨317698011986351994621251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3388778794521087942626677 317698011986351994621251)
                  ·
                    rfl

theorem cell22_2784216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_2784216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784216 prefixEnd_2784216 := by exact prefixLift 2784216
  have htrace : WordTrace (prefixWord ++ tailWord_2784216) baseStart_2784216 baseEnd_2784216 := by
    simpa [prefixWord, tailWord_2784216, baseEnd_2784216] using wordTrace_append hprefix tailTrace_2784216
  have hstable : (prefixWord ++ tailWord_2784216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784216).length < 2 ^ (prefixWord ++ tailWord_2784216).sum := by decide
  have hdescent : baseEnd_2784216 < baseStart_2784216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784231 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 1, 7]
def baseStart_2784231 : Nat := 118140960795 + 2784231 * 2 ^ 59
def prefixEnd_2784231 : Nat := 4983230072969 + 3 ^ 40 * 2784231 * 2
def baseEnd_2784231 : Nat := 953099170765600944738707

theorem tailTrace_2784231 : CollatzResearch.WordTrace tailWord_2784231 prefixEnd_2784231 953099170765600944738707 := by
  unfold tailWord_2784231
  simp only [CollatzResearch.WordTrace]
  refine ⟨101549247176214070642720547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67699498117476047095147031 101549247176214070642720547)
  ·
    refine ⟨152323870764321105964080821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101549247176214070642720547 152323870764321105964080821)
    ·
      refine ⟨14280362884155103684132577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152323870764321105964080821 14280362884155103684132577)
      ·
        refine ⟨10710272163116327763099433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14280362884155103684132577 10710272163116327763099433)
        ·
          refine ⟨8032704122337245822324575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10710272163116327763099433 8032704122337245822324575)
          ·
            refine ⟨12049056183505868733486863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8032704122337245822324575 12049056183505868733486863)
            ·
              refine ⟨18073584275258803100230295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12049056183505868733486863 18073584275258803100230295)
              ·
                refine ⟨27110376412888204650345443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18073584275258803100230295 27110376412888204650345443)
                ·
                  refine ⟨40665564619332306975518165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27110376412888204650345443 40665564619332306975518165)
                  ·
                    refine ⟨953099170765600944738707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40665564619332306975518165 953099170765600944738707)
                    ·
                      rfl

theorem cell22_2784231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_2784231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784231 prefixEnd_2784231 := by exact prefixLift 2784231
  have htrace : WordTrace (prefixWord ++ tailWord_2784231) baseStart_2784231 baseEnd_2784231 := by
    simpa [prefixWord, tailWord_2784231, baseEnd_2784231] using wordTrace_append hprefix tailTrace_2784231
  have hstable : (prefixWord ++ tailWord_2784231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784231).length < 2 ^ (prefixWord ++ tailWord_2784231).sum := by decide
  have hdescent : baseEnd_2784231 < baseStart_2784231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784254 : List Nat := [4, 2, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2784254 : Nat := 118140960795 + 2784254 * 2 ^ 59
def prefixEnd_2784254 : Nat := 4983230072969 + 3 ^ 40 * 2784254 * 2
def baseEnd_2784254 : Nat := 953107044135636551413637

theorem tailTrace_2784254 : CollatzResearch.WordTrace tailWord_2784254 prefixEnd_2784254 953107044135636551413637 := by
  unfold tailWord_2784254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12693760756891343196350977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67700057370087163713871877 12693760756891343196350977)
  ·
    refine ⟨9520320567668507397263233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12693760756891343196350977 9520320567668507397263233)
    ·
      refine ⟨7140240425751380547947425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9520320567668507397263233 7140240425751380547947425)
      ·
        refine ⟨5355180319313535410960569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7140240425751380547947425 5355180319313535410960569)
        ·
          refine ⟨4016385239485151558220427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5355180319313535410960569 4016385239485151558220427)
          ·
            refine ⟨6024577859227727337330641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016385239485151558220427 6024577859227727337330641)
            ·
              refine ⟨4518433394420795502997981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6024577859227727337330641 4518433394420795502997981)
              ·
                refine ⟨1694412522907798313624243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4518433394420795502997981 1694412522907798313624243)
                ·
                  refine ⟨2541618784361697470436365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694412522907798313624243 2541618784361697470436365)
                  ·
                    refine ⟨953107044135636551413637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2541618784361697470436365 953107044135636551413637)
                    ·
                      rfl

theorem cell22_2784254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2784254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784254 prefixEnd_2784254 := by exact prefixLift 2784254
  have htrace : WordTrace (prefixWord ++ tailWord_2784254) baseStart_2784254 baseEnd_2784254 := by
    simpa [prefixWord, tailWord_2784254, baseEnd_2784254] using wordTrace_append hprefix tailTrace_2784254
  have hstable : (prefixWord ++ tailWord_2784254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784254).length < 2 ^ (prefixWord ++ tailWord_2784254).sum := by decide
  have hdescent : baseEnd_2784254 < baseStart_2784254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784263 : List Nat := [1, 1, 4, 3, 1, 1, 3, 3, 1, 4]
def baseStart_2784263 : Nat := 118140960795 + 2784263 * 2 ^ 59
def prefixEnd_2784263 : Nat := 4983230072969 + 3 ^ 40 * 2784263 * 2
def baseEnd_2784263 : Nat := 953110125019563527938609

theorem tailTrace_2784263 : CollatzResearch.WordTrace tailWord_2784263 prefixEnd_2784263 953110125019563527938609 := by
  unfold tailWord_2784263
  simp only [CollatzResearch.WordTrace]
  refine ⟨101550414312098140107885443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67700276208065426738590295 101550414312098140107885443)
  ·
    refine ⟨152325621468147210161828165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101550414312098140107885443 152325621468147210161828165)
    ·
      refine ⟨28561054025277601905342781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152325621468147210161828165 28561054025277601905342781)
      ·
        refine ⟨10710395259479100714503543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28561054025277601905342781 10710395259479100714503543)
        ·
          refine ⟨16065592889218651071755315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10710395259479100714503543 16065592889218651071755315)
          ·
            refine ⟨24098389333827976607632973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16065592889218651071755315 24098389333827976607632973)
            ·
              refine ⟨9036896000185491227862365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24098389333827976607632973 9036896000185491227862365)
              ·
                refine ⟨3388836000069559210448387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9036896000185491227862365 3388836000069559210448387)
                ·
                  refine ⟨5083254000104338815672581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388836000069559210448387 5083254000104338815672581)
                  ·
                    refine ⟨953110125019563527938609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5083254000104338815672581 953110125019563527938609)
                    ·
                      rfl

theorem cell22_2784263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_2784263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784263 prefixEnd_2784263 := by exact prefixLift 2784263
  have htrace : WordTrace (prefixWord ++ tailWord_2784263) baseStart_2784263 baseEnd_2784263 := by
    simpa [prefixWord, tailWord_2784263, baseEnd_2784263] using wordTrace_append hprefix tailTrace_2784263
  have hstable : (prefixWord ++ tailWord_2784263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784263).length < 2 ^ (prefixWord ++ tailWord_2784263).sum := by decide
  have hdescent : baseEnd_2784263 < baseStart_2784263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784291 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 1, 6]
def baseStart_2784291 : Nat := 118140960795 + 2784291 * 2 ^ 59
def prefixEnd_2784291 : Nat := 4983230072969 + 3 ^ 40 * 2784291 * 2
def baseEnd_2784291 : Nat := 953119709991780788238523

theorem tailTrace_2784291 : CollatzResearch.WordTrace tailWord_2784291 prefixEnd_2784291 953119709991780788238523 := by
  unfold tailWord_2784291
  simp only [CollatzResearch.WordTrace]
  refine ⟨101551435555996700889904727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67700957037331133926603151 101551435555996700889904727)
  ·
    refine ⟨152327153333995051334857091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101551435555996700889904727 152327153333995051334857091)
    ·
      refine ⟨228490730000992577002285637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152327153333995051334857091 228490730000992577002285637)
      ·
        refine ⟨42842011875186108187928557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228490730000992577002285637 42842011875186108187928557)
        ·
          refine ⟨16065754453194790570473209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42842011875186108187928557 16065754453194790570473209)
          ·
            refine ⟨12049315839896092927854907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16065754453194790570473209 12049315839896092927854907)
            ·
              refine ⟨18073973759844139391782361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12049315839896092927854907 18073973759844139391782361)
              ·
                refine ⟨13555480319883104543836771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18073973759844139391782361 13555480319883104543836771)
                ·
                  refine ⟨20333220479824656815755157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13555480319883104543836771 20333220479824656815755157)
                  ·
                    refine ⟨953119709991780788238523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20333220479824656815755157 953119709991780788238523)
                    ·
                      rfl

theorem cell22_2784291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_2784291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784291 prefixEnd_2784291 := by exact prefixLift 2784291
  have htrace : WordTrace (prefixWord ++ tailWord_2784291) baseStart_2784291 baseEnd_2784291 := by
    simpa [prefixWord, tailWord_2784291, baseEnd_2784291] using wordTrace_append hprefix tailTrace_2784291
  have hstable : (prefixWord ++ tailWord_2784291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784291).length < 2 ^ (prefixWord ++ tailWord_2784291).sum := by decide
  have hdescent : baseEnd_2784291 < baseStart_2784291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784306 : List Nat := [3, 2, 1, 1, 2, 2, 3, 8]
def baseStart_2784306 : Nat := 118140960795 + 2784306 * 2 ^ 59
def prefixEnd_2784306 : Nat := 4983230072969 + 3 ^ 40 * 2784306 * 2
def baseEnd_2784306 : Nat := 105902760533147305457053

theorem tailTrace_2784306 : CollatzResearch.WordTrace tailWord_2784306 prefixEnd_2784306 105902760533147305457053 := by
  unfold tailWord_2784306
  simp only [CollatzResearch.WordTrace]
  refine ⟨25387995662735589612925193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67701321767294905634467181 25387995662735589612925193)
  ·
    refine ⟨19040996747051692209693895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25387995662735589612925193 19040996747051692209693895)
    ·
      refine ⟨28561495120577538314540843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19040996747051692209693895 28561495120577538314540843)
      ·
        refine ⟨42842242680866307471811265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28561495120577538314540843 42842242680866307471811265)
        ·
          refine ⟨32131682010649730603858449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42842242680866307471811265 32131682010649730603858449)
          ·
            refine ⟨24098761507987297952893837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32131682010649730603858449 24098761507987297952893837)
            ·
              refine ⟨9037035565495236732335189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24098761507987297952893837 9037035565495236732335189)
              ·
                refine ⟨105902760533147305457053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9037035565495236732335189 105902760533147305457053)
                ·
                  rfl

theorem cell22_2784306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_2784306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784306 prefixEnd_2784306 := by exact prefixLift 2784306
  have htrace : WordTrace (prefixWord ++ tailWord_2784306) baseStart_2784306 baseEnd_2784306 := by
    simpa [prefixWord, tailWord_2784306, baseEnd_2784306] using wordTrace_append hprefix tailTrace_2784306
  have hstable : (prefixWord ++ tailWord_2784306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784306).length < 2 ^ (prefixWord ++ tailWord_2784306).sum := by decide
  have hdescent : baseEnd_2784306 < baseStart_2784306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784310 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_2784310 : Nat := 118140960795 + 2784310 * 2 ^ 59
def prefixEnd_2784310 : Nat := 4983230072969 + 3 ^ 40 * 2784310 * 2
def baseEnd_2784310 : Nat := 953126214080071072013465

theorem tailTrace_2784310 : CollatzResearch.WordTrace tailWord_2784310 prefixEnd_2784310 953126214080071072013465 := by
  unfold tailWord_2784310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6347008033932991695927899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67701419028618578089897589 6347008033932991695927899)
  ·
    refine ⟨9520512050899487543891849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6347008033932991695927899 9520512050899487543891849)
    ·
      refine ⟨7140384038174615657918887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9520512050899487543891849 7140384038174615657918887)
      ·
        refine ⟨10710576057261923486878331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7140384038174615657918887 10710576057261923486878331)
        ·
          refine ⟨16065864085892885230317497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10710576057261923486878331 16065864085892885230317497)
          ·
            refine ⟨12049398064419663922738123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16065864085892885230317497 12049398064419663922738123)
            ·
              refine ⟨18074097096629495884107185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12049398064419663922738123 18074097096629495884107185)
              ·
                refine ⟨13555572822472121913080389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18074097096629495884107185 13555572822472121913080389)
                ·
                  refine ⟨2541669904213522858702573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13555572822472121913080389 2541669904213522858702573)
                  ·
                    refine ⟨953126214080071072013465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2541669904213522858702573 953126214080071072013465)
                    ·
                      rfl

theorem cell22_2784310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_2784310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784310 prefixEnd_2784310 := by exact prefixLift 2784310
  have htrace : WordTrace (prefixWord ++ tailWord_2784310) baseStart_2784310 baseEnd_2784310 := by
    simpa [prefixWord, tailWord_2784310, baseEnd_2784310] using wordTrace_append hprefix tailTrace_2784310
  have hstable : (prefixWord ++ tailWord_2784310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784310).length < 2 ^ (prefixWord ++ tailWord_2784310).sum := by decide
  have hdescent : baseEnd_2784310 < baseStart_2784310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784385 : List Nat := [1, 2, 4, 2, 2, 2, 2, 2, 5]
def baseStart_2784385 : Nat := 118140960795 + 2784385 * 2 ^ 59
def prefixEnd_2784385 : Nat := 4983230072969 + 3 ^ 40 * 2784385 * 2
def baseEnd_2784385 : Nat := 317717296037598625462745

theorem tailTrace_2784385 : CollatzResearch.WordTrace tailWord_2784385 prefixEnd_2784385 317717296037598625462745 := by
  unfold tailWord_2784385
  simp only [CollatzResearch.WordTrace]
  refine ⟨101554864017656154943826609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67703242678437436629217739 101554864017656154943826609)
  ·
    refine ⟨76166148013242116207869957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101554864017656154943826609 76166148013242116207869957)
    ·
      refine ⟨14281152752482896788975617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76166148013242116207869957 14281152752482896788975617)
      ·
        refine ⟨10710864564362172591731713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14281152752482896788975617 10710864564362172591731713)
        ·
          refine ⟨8033148423271629443798785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10710864564362172591731713 8033148423271629443798785)
          ·
            refine ⟨6024861317453722082849089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8033148423271629443798785 6024861317453722082849089)
            ·
              refine ⟨4518645988090291562136817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6024861317453722082849089 4518645988090291562136817)
              ·
                refine ⟨3388984491067718671602613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4518645988090291562136817 3388984491067718671602613)
                ·
                  refine ⟨317717296037598625462745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3388984491067718671602613 317717296037598625462745)
                  ·
                    rfl

theorem cell22_2784385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_2784385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784385 prefixEnd_2784385 := by exact prefixLift 2784385
  have htrace : WordTrace (prefixWord ++ tailWord_2784385) baseStart_2784385 baseEnd_2784385 := by
    simpa [prefixWord, tailWord_2784385, baseEnd_2784385] using wordTrace_append hprefix tailTrace_2784385
  have hstable : (prefixWord ++ tailWord_2784385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784385).length < 2 ^ (prefixWord ++ tailWord_2784385).sum := by decide
  have hdescent : baseEnd_2784385 < baseStart_2784385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784396 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 10]
def baseStart_2784396 : Nat := 118140960795 + 2784396 * 2 ^ 59
def prefixEnd_2784396 : Nat := 4983230072969 + 3 ^ 40 * 2784396 * 2
def baseEnd_2784396 : Nat := 317718551212531838121067

theorem tailTrace_2784396 : CollatzResearch.WordTrace tailWord_2784396 prefixEnd_2784396 317718551212531838121067 := by
  unfold tailWord_2784396
  simp only [CollatzResearch.WordTrace]
  refine ⟨50777632610308151911238521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67703510147077535881651361 50777632610308151911238521)
  ·
    refine ⟨38083224457731113933428891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50777632610308151911238521 38083224457731113933428891)
    ·
      refine ⟨57124836686596670900143337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38083224457731113933428891 57124836686596670900143337)
      ·
        refine ⟨42843627514947503175107503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57124836686596670900143337 42843627514947503175107503)
        ·
          refine ⟨64265441272421254762661255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42843627514947503175107503 64265441272421254762661255)
          ·
            refine ⟨96398161908631882143991883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64265441272421254762661255 96398161908631882143991883)
            ·
              refine ⟨144597242862947823215987825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96398161908631882143991883 144597242862947823215987825)
              ·
                refine ⟨108447932147210867411990869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144597242862947823215987825 108447932147210867411990869)
                ·
                  refine ⟨317718551212531838121067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 108447932147210867411990869 317718551212531838121067)
                  ·
                    rfl

theorem cell22_2784396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_2784396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784396 prefixEnd_2784396 := by exact prefixLift 2784396
  have htrace : WordTrace (prefixWord ++ tailWord_2784396) baseStart_2784396 baseEnd_2784396 := by
    simpa [prefixWord, tailWord_2784396, baseEnd_2784396] using wordTrace_append hprefix tailTrace_2784396
  have hstable : (prefixWord ++ tailWord_2784396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784396).length < 2 ^ (prefixWord ++ tailWord_2784396).sum := by decide
  have hdescent : baseEnd_2784396 < baseStart_2784396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784413 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 6]
def baseStart_2784413 : Nat := 118140960795 + 2784413 * 2 ^ 59
def prefixEnd_2784413 : Nat := 4983230072969 + 3 ^ 40 * 2784413 * 2
def baseEnd_2784413 : Nat := 317720491028337712229383

theorem tailTrace_2784413 : CollatzResearch.WordTrace tailWord_2784413 prefixEnd_2784413 317720491028337712229383 := by
  unfold tailWord_2784413
  simp only [CollatzResearch.WordTrace]
  refine ⟨101555885261554715725845893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67703923507703143817230595 101555885261554715725845893)
  ·
    refine ⟨19041728486541509198596105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101555885261554715725845893 19041728486541509198596105)
    ·
      refine ⟨14281296364906131898947079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19041728486541509198596105 14281296364906131898947079)
      ·
        refine ⟨21421944547359197848420619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14281296364906131898947079 21421944547359197848420619)
        ·
          refine ⟨32132916821038796772630929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21421944547359197848420619 32132916821038796772630929)
          ·
            refine ⟨24099687615779097579473197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32132916821038796772630929 24099687615779097579473197)
            ·
              refine ⟨9037382855917161592302449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24099687615779097579473197 9037382855917161592302449)
              ·
                refine ⟨6778037141937871194226837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9037382855917161592302449 6778037141937871194226837)
                ·
                  refine ⟨317720491028337712229383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6778037141937871194226837 317720491028337712229383)
                  ·
                    rfl

theorem cell22_2784413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_2784413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784413 prefixEnd_2784413 := by exact prefixLift 2784413
  have htrace : WordTrace (prefixWord ++ tailWord_2784413) baseStart_2784413 baseEnd_2784413 := by
    simpa [prefixWord, tailWord_2784413, baseEnd_2784413] using wordTrace_append hprefix tailTrace_2784413
  have hstable : (prefixWord ++ tailWord_2784413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784413).length < 2 ^ (prefixWord ++ tailWord_2784413).sum := by decide
  have hdescent : baseEnd_2784413 < baseStart_2784413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784462 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_2784462 : Nat := 118140960795 + 2784462 * 2 ^ 59
def prefixEnd_2784462 : Nat := 4983230072969 + 3 ^ 40 * 2784462 * 2
def baseEnd_2784462 : Nat := 953178246786393342212999

theorem tailTrace_2784462 : CollatzResearch.WordTrace tailWord_2784462 prefixEnd_2784462 953178246786393342212999 := by
  unfold tailWord_2784462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12694709054797149636797455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67705114958918131396253093 12694709054797149636797455)
  ·
    refine ⟨19042063582195724455196183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12694709054797149636797455 19042063582195724455196183)
    ·
      refine ⟨28563095373293586682794275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19042063582195724455196183 28563095373293586682794275)
      ·
        refine ⟨42844643059940380024191413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28563095373293586682794275 42844643059940380024191413)
        ·
          refine ⟨4016685286869410627267945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42844643059940380024191413 4016685286869410627267945)
          ·
            refine ⟨3012513965152057970450959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4016685286869410627267945 3012513965152057970450959)
            ·
              refine ⟨4518770947728086955676439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012513965152057970450959 4518770947728086955676439)
              ·
                refine ⟨6778156421592130433514659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4518770947728086955676439 6778156421592130433514659)
                ·
                  refine ⟨10167234632388195650271989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6778156421592130433514659 10167234632388195650271989)
                  ·
                    refine ⟨953178246786393342212999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10167234632388195650271989 953178246786393342212999)
                    ·
                      rfl

theorem cell22_2784462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_2784462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784462 prefixEnd_2784462 := by exact prefixLift 2784462
  have htrace : WordTrace (prefixWord ++ tailWord_2784462) baseStart_2784462 baseEnd_2784462 := by
    simpa [prefixWord, tailWord_2784462, baseEnd_2784462] using wordTrace_append hprefix tailTrace_2784462
  have hstable : (prefixWord ++ tailWord_2784462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784462).length < 2 ^ (prefixWord ++ tailWord_2784462).sum := by decide
  have hdescent : baseEnd_2784462 < baseStart_2784462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784610 : List Nat := [3, 3, 2, 1, 1, 1, 11]
def baseStart_2784610 : Nat := 118140960795 + 2784610 * 2 ^ 59
def prefixEnd_2784610 : Nat := 4983230072969 + 3 ^ 40 * 2784610 * 2
def baseEnd_2784610 : Nat := 35304774452258158870835

theorem tailTrace_2784610 : CollatzResearch.WordTrace tailWord_2784610 prefixEnd_2784610 35304774452258158870835 := by
  unfold tailWord_2784610
  simp only [CollatzResearch.WordTrace]
  refine ⟨25390767610460254592691821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67708713627894012247178189 25390767610460254592691821)
  ·
    refine ⟨9521537853922595472259433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25390767610460254592691821 9521537853922595472259433)
    ·
      refine ⟨7141153390441946604194575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9521537853922595472259433 7141153390441946604194575)
      ·
        refine ⟨10711730085662919906291863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7141153390441946604194575 10711730085662919906291863)
        ·
          refine ⟨16067595128494379859437795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10711730085662919906291863 16067595128494379859437795)
          ·
            refine ⟨24101392692741569789156693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16067595128494379859437795 24101392692741569789156693)
            ·
              refine ⟨35304774452258158870835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24101392692741569789156693 35304774452258158870835)
              ·
                rfl

theorem cell22_2784610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 11].length) (baseStart_2784610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784610 prefixEnd_2784610 := by exact prefixLift 2784610
  have htrace : WordTrace (prefixWord ++ tailWord_2784610) baseStart_2784610 baseEnd_2784610 := by
    simpa [prefixWord, tailWord_2784610, baseEnd_2784610] using wordTrace_append hprefix tailTrace_2784610
  have hstable : (prefixWord ++ tailWord_2784610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784610).length < 2 ^ (prefixWord ++ tailWord_2784610).sum := by decide
  have hdescent : baseEnd_2784610 < baseStart_2784610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784715 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 3, 5]
def baseStart_2784715 : Nat := 118140960795 + 2784715 * 2 ^ 59
def prefixEnd_2784715 : Nat := 4983230072969 + 3 ^ 40 * 2784715 * 2
def baseEnd_2784715 : Nat := 953264853856785015637223

theorem tailTrace_2784715 : CollatzResearch.WordTrace tailWord_2784715 prefixEnd_2784715 953264853856785015637223 := by
  unfold tailWord_2784715
  simp only [CollatzResearch.WordTrace]
  refine ⟨101566900106460621303339599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67711266737640414202226399 101566900106460621303339599)
  ·
    refine ⟨152350350159690931955009399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101566900106460621303339599 152350350159690931955009399)
    ·
      refine ⟨228525525239536397932514099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152350350159690931955009399 228525525239536397932514099)
      ·
        refine ⟨342788287859304596898771149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228525525239536397932514099 342788287859304596898771149)
        ·
          refine ⟨128545607947239223837039181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342788287859304596898771149 128545607947239223837039181)
          ·
            refine ⟨48204602980214708938889693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128545607947239223837039181 48204602980214708938889693)
            ·
              refine ⟨18076726117580515852083635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48204602980214708938889693 18076726117580515852083635)
              ·
                refine ⟨27115089176370773778125453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18076726117580515852083635 27115089176370773778125453)
                ·
                  refine ⟨10168158441139040166797045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27115089176370773778125453 10168158441139040166797045)
                  ·
                    refine ⟨953264853856785015637223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10168158441139040166797045 953264853856785015637223)
                    ·
                      rfl

theorem cell22_2784715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_2784715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784715 prefixEnd_2784715 := by exact prefixLift 2784715
  have htrace : WordTrace (prefixWord ++ tailWord_2784715) baseStart_2784715 baseEnd_2784715 := by
    simpa [prefixWord, tailWord_2784715, baseEnd_2784715] using wordTrace_append hprefix tailTrace_2784715
  have hstable : (prefixWord ++ tailWord_2784715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784715).length < 2 ^ (prefixWord ++ tailWord_2784715).sum := by decide
  have hdescent : baseEnd_2784715 < baseStart_2784715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784762 : List Nat := [3, 1, 1, 1, 1, 2, 7, 6]
def baseStart_2784762 : Nat := 118140960795 + 2784762 * 2 ^ 59
def prefixEnd_2784762 : Nat := 4983230072969 + 3 ^ 40 * 2784762 * 2
def baseEnd_2784762 : Nat := 105920104768588062190231

theorem tailTrace_2784762 : CollatzResearch.WordTrace tailWord_2784762 prefixEnd_2784762 105920104768588062190231 := by
  unfold tailWord_2784762
  simp only [CollatzResearch.WordTrace]
  refine ⟨25392153584322587082575135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67712409558193565553533693 25392153584322587082575135)
  ·
    refine ⟨38088230376483880623862703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25392153584322587082575135 38088230376483880623862703)
    ·
      refine ⟨57132345564725820935794055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38088230376483880623862703 57132345564725820935794055)
      ·
        refine ⟨85698518347088731403691083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57132345564725820935794055 85698518347088731403691083)
        ·
          refine ⟨128547777520633097105536625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85698518347088731403691083 128547777520633097105536625)
          ·
            refine ⟨96410833140474822829152469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128547777520633097105536625 96410833140474822829152469)
            ·
              refine ⟨2259628901729878660058261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 96410833140474822829152469 2259628901729878660058261)
              ·
                refine ⟨105920104768588062190231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2259628901729878660058261 105920104768588062190231)
                ·
                  rfl

theorem cell22_2784762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_2784762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784762 prefixEnd_2784762 := by exact prefixLift 2784762
  have htrace : WordTrace (prefixWord ++ tailWord_2784762) baseStart_2784762 baseEnd_2784762 := by
    simpa [prefixWord, tailWord_2784762, baseEnd_2784762] using wordTrace_append hprefix tailTrace_2784762
  have hstable : (prefixWord ++ tailWord_2784762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784762).length < 2 ^ (prefixWord ++ tailWord_2784762).sum := by decide
  have hdescent : baseEnd_2784762 < baseStart_2784762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784777 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 5, 3]
def baseStart_2784777 : Nat := 118140960795 + 2784777 * 2 ^ 59
def prefixEnd_2784777 : Nat := 4983230072969 + 3 ^ 40 * 2784777 * 2
def baseEnd_2784777 : Nat := 953286077723837520587033

theorem tailTrace_2784777 : CollatzResearch.WordTrace tailWord_2784777 prefixEnd_2784777 953286077723837520587033 := by
  unfold tailWord_2784777
  simp only [CollatzResearch.WordTrace]
  refine ⟨101569161432236005892096585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67712774288157337261397723 101569161432236005892096585)
  ·
    refine ⟨76176871074177004419072439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101569161432236005892096585 76176871074177004419072439)
    ·
      refine ⟨114265306611265506628608659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76176871074177004419072439 114265306611265506628608659)
      ·
        refine ⟨171397959916898259942912989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114265306611265506628608659 171397959916898259942912989)
        ·
          refine ⟨64274234968836847478592371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171397959916898259942912989 64274234968836847478592371)
          ·
            refine ⟨96411352453255271217888557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64274234968836847478592371 96411352453255271217888557)
            ·
              refine ⟨36154257169970726706708209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96411352453255271217888557 36154257169970726706708209)
              ·
                refine ⟨27115692877478045030031157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36154257169970726706708209 27115692877478045030031157)
                ·
                  refine ⟨2542096207263566721565421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27115692877478045030031157 2542096207263566721565421)
                  ·
                    refine ⟨953286077723837520587033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542096207263566721565421 953286077723837520587033)
                    ·
                      rfl

theorem cell22_2784777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 3].length) (baseStart_2784777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784777 prefixEnd_2784777 := by exact prefixLift 2784777
  have htrace : WordTrace (prefixWord ++ tailWord_2784777) baseStart_2784777 baseEnd_2784777 := by
    simpa [prefixWord, tailWord_2784777, baseEnd_2784777] using wordTrace_append hprefix tailTrace_2784777
  have hstable : (prefixWord ++ tailWord_2784777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784777).length < 2 ^ (prefixWord ++ tailWord_2784777).sum := by decide
  have hdescent : baseEnd_2784777 < baseStart_2784777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784845 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_2784845 : Nat := 118140960795 + 2784845 * 2 ^ 59
def prefixEnd_2784845 : Nat := 4983230072969 + 3 ^ 40 * 2784845 * 2
def baseEnd_2784845 : Nat := 953309355513508009886825

theorem tailTrace_2784845 : CollatzResearch.WordTrace tailWord_2784845 prefixEnd_2784845 953309355513508009886825 := by
  unfold tailWord_2784845
  simp only [CollatzResearch.WordTrace]
  refine ⟨101571641595989653505571989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67714427730659769003714659 101571641595989653505571989)
  ·
    refine ⟨4761170699812015008073687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101571641595989653505571989 4761170699812015008073687)
    ·
      refine ⟨7141756049718022512110531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4761170699812015008073687 7141756049718022512110531)
      ·
        refine ⟨10712634074577033768165797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7141756049718022512110531 10712634074577033768165797)
        ·
          refine ⟨2008618888983193831531087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10712634074577033768165797 2008618888983193831531087)
          ·
            refine ⟨3012928333474790747296631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008618888983193831531087 3012928333474790747296631)
            ·
              refine ⟨4519392500212186120944947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012928333474790747296631 4519392500212186120944947)
              ·
                refine ⟨6779088750318279181417421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4519392500212186120944947 6779088750318279181417421)
                ·
                  refine ⟨2542158281369354693031533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6779088750318279181417421 2542158281369354693031533)
                  ·
                    refine ⟨953309355513508009886825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542158281369354693031533 953309355513508009886825)
                    ·
                      rfl

theorem cell22_2784845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_2784845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784845 prefixEnd_2784845 := by exact prefixLift 2784845
  have htrace : WordTrace (prefixWord ++ tailWord_2784845) baseStart_2784845 baseEnd_2784845 := by
    simpa [prefixWord, tailWord_2784845, baseEnd_2784845] using wordTrace_append hprefix tailTrace_2784845
  have hstable : (prefixWord ++ tailWord_2784845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784845).length < 2 ^ (prefixWord ++ tailWord_2784845).sum := by decide
  have hdescent : baseEnd_2784845 < baseStart_2784845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784897 : List Nat := [1, 2, 4, 2, 1, 12]
def baseStart_2784897 : Nat := 118140960795 + 2784897 * 2 ^ 59
def prefixEnd_2784897 : Nat := 4983230072969 + 3 ^ 40 * 2784897 * 2
def baseEnd_2784897 : Nat := 11769471063903669229465

theorem tailTrace_2784897 : CollatzResearch.WordTrace tailWord_2784897 prefixEnd_2784897 11769471063903669229465 := by
  unfold tailWord_2784897
  simp only [CollatzResearch.WordTrace]
  refine ⟨101573538191801266386464945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67715692127867510924309963 101573538191801266386464945)
  ·
    refine ⟨76180153643850949789848709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101573538191801266386464945 76180153643850949789848709)
    ·
      refine ⟨14283778808222053085596633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76180153643850949789848709 14283778808222053085596633)
      ·
        refine ⟨10712834106166539814197475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14283778808222053085596633 10712834106166539814197475)
        ·
          refine ⟨16069251159249809721296213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10712834106166539814197475 16069251159249809721296213)
          ·
            refine ⟨11769471063903669229465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16069251159249809721296213 11769471063903669229465)
            ·
              rfl

theorem cell22_2784897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 12].length) (baseStart_2784897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784897 prefixEnd_2784897 := by exact prefixLift 2784897
  have htrace : WordTrace (prefixWord ++ tailWord_2784897) baseStart_2784897 baseEnd_2784897 := by
    simpa [prefixWord, tailWord_2784897, baseEnd_2784897] using wordTrace_append hprefix tailTrace_2784897
  have hstable : (prefixWord ++ tailWord_2784897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784897).length < 2 ^ (prefixWord ++ tailWord_2784897).sum := by decide
  have hdescent : baseEnd_2784897 < baseStart_2784897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784901 : List Nat := [1, 3, 1, 1, 4, 1, 4, 2, 2, 3]
def baseStart_2784901 : Nat := 118140960795 + 2784901 * 2 ^ 59
def prefixEnd_2784901 : Nat := 4983230072969 + 3 ^ 40 * 2784901 * 2
def baseEnd_2784901 : Nat := 953328525457942530486653

theorem tailTrace_2784901 : CollatzResearch.WordTrace tailWord_2784901 prefixEnd_2784901 953328525457942530486653 := by
  unfold tailWord_2784901
  simp only [CollatzResearch.WordTrace]
  refine ⟨101573684083786775069610557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67715789389191183379740371 101573684083786775069610557)
  ·
    refine ⟨38090131531420040651103959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101573684083786775069610557 38090131531420040651103959)
    ·
      refine ⟨57135197297130060976655939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38090131531420040651103959 57135197297130060976655939)
      ·
        refine ⟨85702795945695091464983909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57135197297130060976655939 85702795945695091464983909)
        ·
          refine ⟨16069274239817829649684483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85702795945695091464983909 16069274239817829649684483)
          ·
            refine ⟨24103911359726744474526725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16069274239817829649684483 24103911359726744474526725)
            ·
              refine ⟨4519483379948764588973761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24103911359726744474526725 4519483379948764588973761)
              ·
                refine ⟨3389612534961573441730321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4519483379948764588973761 3389612534961573441730321)
                ·
                  refine ⟨2542209401221180081297741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3389612534961573441730321 2542209401221180081297741)
                  ·
                    refine ⟨953328525457942530486653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542209401221180081297741 953328525457942530486653)
                    ·
                      rfl

theorem cell22_2784901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_2784901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784901 prefixEnd_2784901 := by exact prefixLift 2784901
  have htrace : WordTrace (prefixWord ++ tailWord_2784901) baseStart_2784901 baseEnd_2784901 := by
    simpa [prefixWord, tailWord_2784901, baseEnd_2784901] using wordTrace_append hprefix tailTrace_2784901
  have hstable : (prefixWord ++ tailWord_2784901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784901).length < 2 ^ (prefixWord ++ tailWord_2784901).sum := by decide
  have hdescent : baseEnd_2784901 < baseStart_2784901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784903 : List Nat := [1, 1, 4, 2, 1, 5, 2, 2, 4]
def baseStart_2784903 : Nat := 118140960795 + 2784903 * 2 ^ 59
def prefixEnd_2784903 : Nat := 4983230072969 + 3 ^ 40 * 2784903 * 2
def baseEnd_2784903 : Nat := 317776403366271730645549

theorem tailTrace_2784903 : CollatzResearch.WordTrace tailWord_2784903 prefixEnd_2784903 317776403366271730645549 := by
  unfold tailWord_2784903
  simp only [CollatzResearch.WordTrace]
  refine ⟨101573757029779529411183363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67715838019853019607455575 101573757029779529411183363)
  ·
    refine ⟨152360635544669294116775045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101573757029779529411183363 152360635544669294116775045)
    ·
      refine ⟨28567619164625492646895321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152360635544669294116775045 28567619164625492646895321)
      ·
        refine ⟨21425714373469119485171491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28567619164625492646895321 21425714373469119485171491)
        ·
          refine ⟨32138571560203679227757237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21425714373469119485171491 32138571560203679227757237)
          ·
            refine ⟨3012991083769094927602241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32138571560203679227757237 3012991083769094927602241)
            ·
              refine ⟨2259743312826821195701681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3012991083769094927602241 2259743312826821195701681)
              ·
                refine ⟨1694807484620115896776261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2259743312826821195701681 1694807484620115896776261)
                ·
                  refine ⟨317776403366271730645549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1694807484620115896776261 317776403366271730645549)
                  ·
                    rfl

theorem cell22_2784903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 4].length) (baseStart_2784903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784903 prefixEnd_2784903 := by exact prefixLift 2784903
  have htrace : WordTrace (prefixWord ++ tailWord_2784903) baseStart_2784903 baseEnd_2784903 := by
    simpa [prefixWord, tailWord_2784903, baseEnd_2784903] using wordTrace_append hprefix tailTrace_2784903
  have hstable : (prefixWord ++ tailWord_2784903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784903).length < 2 ^ (prefixWord ++ tailWord_2784903).sum := by decide
  have hdescent : baseEnd_2784903 < baseStart_2784903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784974 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_2784974 : Nat := 118140960795 + 2784974 * 2 ^ 59
def prefixEnd_2784974 : Nat := 4983230072969 + 3 ^ 40 * 2784974 * 2
def baseEnd_2784974 : Nat := 953353514849794673411429

theorem tailTrace_2784974 : CollatzResearch.WordTrace tailWord_2784974 prefixEnd_2784974 953353514849794673411429 := by
  unfold tailWord_2784974
  simp only [CollatzResearch.WordTrace]
  refine ⟨12697043326565288567127247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67717564408348205691345317 12697043326565288567127247)
  ·
    refine ⟨19045564989847932850690871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12697043326565288567127247 19045564989847932850690871)
    ·
      refine ⟨28568347484771899276036307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19045564989847932850690871 28568347484771899276036307)
      ·
        refine ⟨42852521227157848914054461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28568347484771899276036307 42852521227157848914054461)
        ·
          refine ⟨16069695460184193342770423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42852521227157848914054461 16069695460184193342770423)
          ·
            refine ⟨24104543190276290014155635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16069695460184193342770423 24104543190276290014155635)
            ·
              refine ⟨36156814785414435021233453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24104543190276290014155635 36156814785414435021233453)
              ·
                refine ⟨13558805544530413132962545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36156814785414435021233453 13558805544530413132962545)
                ·
                  refine ⟨10169104158397809849721909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13558805544530413132962545 10169104158397809849721909)
                  ·
                    refine ⟨953353514849794673411429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10169104158397809849721909 953353514849794673411429)
                    ·
                      rfl

theorem cell22_2784974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_2784974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784974 prefixEnd_2784974 := by exact prefixLift 2784974
  have htrace : WordTrace (prefixWord ++ tailWord_2784974) baseStart_2784974 baseEnd_2784974 := by
    simpa [prefixWord, tailWord_2784974, baseEnd_2784974] using wordTrace_append hprefix tailTrace_2784974
  have hstable : (prefixWord ++ tailWord_2784974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784974).length < 2 ^ (prefixWord ++ tailWord_2784974).sum := by decide
  have hdescent : baseEnd_2784974 < baseStart_2784974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784982 : List Nat := [5, 2, 1, 3, 2, 1, 2, 6]
def baseStart_2784982 : Nat := 118140960795 + 2784982 * 2 ^ 59
def prefixEnd_2784982 : Nat := 4983230072969 + 3 ^ 40 * 2784982 * 2
def baseEnd_2784982 : Nat := 105928472601476146579045

theorem tailTrace_2784982 : CollatzResearch.WordTrace tailWord_2784982 prefixEnd_2784982 105928472601476146579045 := by
  unfold tailWord_2784982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6348539899780832868956825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67717758930995550602206133 6348539899780832868956825)
  ·
    refine ⟨4761404924835624651717619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6348539899780832868956825 4761404924835624651717619)
    ·
      refine ⟨7142107387253436977576429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4761404924835624651717619 7142107387253436977576429)
      ·
        refine ⟨2678290270220038866591161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7142107387253436977576429 2678290270220038866591161)
        ·
          refine ⟨2008717702665029149943371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2678290270220038866591161 2008717702665029149943371)
          ·
            refine ⟨3013076553997543724915057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008717702665029149943371 3013076553997543724915057)
            ·
              refine ⟨2259807415498157793686293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3013076553997543724915057 2259807415498157793686293)
              ·
                refine ⟨105928472601476146579045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2259807415498157793686293 105928472601476146579045)
                ·
                  rfl

theorem cell22_2784982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_2784982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2784982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2784982 prefixEnd_2784982 := by exact prefixLift 2784982
  have htrace : WordTrace (prefixWord ++ tailWord_2784982) baseStart_2784982 baseEnd_2784982 := by
    simpa [prefixWord, tailWord_2784982, baseEnd_2784982] using wordTrace_append hprefix tailTrace_2784982
  have hstable : (prefixWord ++ tailWord_2784982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784982).length < 2 ^ (prefixWord ++ tailWord_2784982).sum := by decide
  have hdescent : baseEnd_2784982 < baseStart_2784982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785006 : List Nat := [4, 1, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_2785006 : Nat := 118140960795 + 2785006 * 2 ^ 59
def prefixEnd_2785006 : Nat := 4983230072969 + 3 ^ 40 * 2785006 * 2
def baseEnd_2785006 : Nat := 953364469103757256611331

theorem tailTrace_2785006 : CollatzResearch.WordTrace tailWord_2785006 prefixEnd_2785006 953364469103757256611331 := by
  unfold tailWord_2785006
  simp only [CollatzResearch.WordTrace]
  refine ⟨12697189218550797250272859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67718342498937585334788581 12697189218550797250272859)
  ·
    refine ⟨19045783827826195875409289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12697189218550797250272859 19045783827826195875409289)
    ·
      refine ⟨14284337870869646906556967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19045783827826195875409289 14284337870869646906556967)
      ·
        refine ⟨21426506806304470359835451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14284337870869646906556967 21426506806304470359835451)
        ·
          refine ⟨32139760209456705539753177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21426506806304470359835451 32139760209456705539753177)
          ·
            refine ⟨24104820157092529154814883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32139760209456705539753177 24104820157092529154814883)
            ·
              refine ⟨36157230235638793732222325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24104820157092529154814883 36157230235638793732222325)
              ·
                refine ⟨3389740334591136912395843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36157230235638793732222325 3389740334591136912395843)
                ·
                  refine ⟨5084610501886705368593765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3389740334591136912395843 5084610501886705368593765)
                  ·
                    refine ⟨953364469103757256611331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5084610501886705368593765 953364469103757256611331)
                    ·
                      rfl

theorem cell22_2785006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_2785006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785006 prefixEnd_2785006 := by exact prefixLift 2785006
  have htrace : WordTrace (prefixWord ++ tailWord_2785006) baseStart_2785006 baseEnd_2785006 := by
    simpa [prefixWord, tailWord_2785006, baseEnd_2785006] using wordTrace_append hprefix tailTrace_2785006
  have hstable : (prefixWord ++ tailWord_2785006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785006).length < 2 ^ (prefixWord ++ tailWord_2785006).sum := by decide
  have hdescent : baseEnd_2785006 < baseStart_2785006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785156 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 6]
def baseStart_2785156 : Nat := 118140960795 + 2785156 * 2 ^ 59
def prefixEnd_2785156 : Nat := 4983230072969 + 3 ^ 40 * 2785156 * 2
def baseEnd_2785156 : Nat := 317805272389735621786957

theorem tailTrace_2785156 : CollatzResearch.WordTrace tailWord_2785156 prefixEnd_2785156 317805272389735621786957 := by
  unfold tailWord_2785156
  simp only [CollatzResearch.WordTrace]
  refine ⟨50791492348931476810071661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67721989798575302413428881 50791492348931476810071661)
  ·
    refine ⟨19046809630849303803776873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50791492348931476810071661 19046809630849303803776873)
    ·
      refine ⟨14285107223136977852832655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19046809630849303803776873 14285107223136977852832655)
      ·
        refine ⟨21427660834705466779248983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14285107223136977852832655 21427660834705466779248983)
        ·
          refine ⟨32141491252058200168873475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21427660834705466779248983 32141491252058200168873475)
          ·
            refine ⟨48212236878087300253310213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32141491252058200168873475 48212236878087300253310213)
            ·
              refine ⟨9039794414641368797495665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48212236878087300253310213 9039794414641368797495665)
              ·
                refine ⟨6779845810981026598121749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9039794414641368797495665 6779845810981026598121749)
                ·
                  refine ⟨317805272389735621786957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6779845810981026598121749 317805272389735621786957)
                  ·
                    rfl

theorem cell22_2785156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_2785156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785156 prefixEnd_2785156 := by exact prefixLift 2785156
  have htrace : WordTrace (prefixWord ++ tailWord_2785156) baseStart_2785156 baseEnd_2785156 := by
    simpa [prefixWord, tailWord_2785156, baseEnd_2785156] using wordTrace_append hprefix tailTrace_2785156
  have hstable : (prefixWord ++ tailWord_2785156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785156).length < 2 ^ (prefixWord ++ tailWord_2785156).sum := by decide
  have hdescent : baseEnd_2785156 < baseStart_2785156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785166 : List Nat := [4, 1, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_2785166 : Nat := 118140960795 + 2785166 * 2 ^ 59
def prefixEnd_2785166 : Nat := 4983230072969 + 3 ^ 40 * 2785166 * 2
def baseEnd_2785166 : Nat := 953419240373570172610841

theorem tailTrace_2785166 : CollatzResearch.WordTrace tailWord_2785166 prefixEnd_2785166 953419240373570172610841 := by
  unfold tailWord_2785166
  simp only [CollatzResearch.WordTrace]
  refine ⟨12697918678478340666000919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67722232951884483552004901 12697918678478340666000919)
  ·
    refine ⟨19046878017717510999001379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12697918678478340666000919 19046878017717510999001379)
    ·
      refine ⟨28570317026576266498502069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19046878017717510999001379 28570317026576266498502069)
      ·
        refine ⟨2678467221241524984234569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28570317026576266498502069 2678467221241524984234569)
        ·
          refine ⟨2008850415931143738175927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2678467221241524984234569 2008850415931143738175927)
          ·
            refine ⟨3013275623896715607263891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008850415931143738175927 3013275623896715607263891)
            ·
              refine ⟨4519913435845073410895837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013275623896715607263891 4519913435845073410895837)
              ·
                refine ⟨1694967538441902529085939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4519913435845073410895837 1694967538441902529085939)
                ·
                  refine ⟨2542451307662853793628909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694967538441902529085939 2542451307662853793628909)
                  ·
                    refine ⟨953419240373570172610841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542451307662853793628909 953419240373570172610841)
                    ·
                      rfl

theorem cell22_2785166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_2785166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785166 prefixEnd_2785166 := by exact prefixLift 2785166
  have htrace : WordTrace (prefixWord ++ tailWord_2785166) baseStart_2785166 baseEnd_2785166 := by
    simpa [prefixWord, tailWord_2785166, baseEnd_2785166] using wordTrace_append hprefix tailTrace_2785166
  have hstable : (prefixWord ++ tailWord_2785166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785166).length < 2 ^ (prefixWord ++ tailWord_2785166).sum := by decide
  have hdescent : baseEnd_2785166 < baseStart_2785166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785188 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_2785188 : Nat := 118140960795 + 2785188 * 2 ^ 59
def prefixEnd_2785188 : Nat := 4983230072969 + 3 ^ 40 * 2785188 * 2
def baseEnd_2785188 : Nat := 953426771423169448560773

theorem tailTrace_2785188 : CollatzResearch.WordTrace tailWord_2785188 prefixEnd_2785188 953426771423169448560773 := by
  unfold tailWord_2785188
  simp only [CollatzResearch.WordTrace]
  refine ⟨50792075916873511542654109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67722767889164682056872145 50792075916873511542654109)
  ·
    refine ⟨19047028468827566828495291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50792075916873511542654109 19047028468827566828495291)
    ·
      refine ⟨28570542703241350242742937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19047028468827566828495291 28570542703241350242742937)
      ·
        refine ⟨21427907027431012682057203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28570542703241350242742937 21427907027431012682057203)
        ·
          refine ⟨32141860541146519023085805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21427907027431012682057203 32141860541146519023085805)
          ·
            refine ⟨12053197702929944633657177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32141860541146519023085805 12053197702929944633657177)
            ·
              refine ⟨9039898277197458475242883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12053197702929944633657177 9039898277197458475242883)
              ·
                refine ⟨13559847415796187712864325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9039898277197458475242883 13559847415796187712864325)
                ·
                  refine ⟨2542471390461785196162061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13559847415796187712864325 2542471390461785196162061)
                  ·
                    refine ⟨953426771423169448560773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542471390461785196162061 953426771423169448560773)
                    ·
                      rfl

theorem cell22_2785188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_2785188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785188 prefixEnd_2785188 := by exact prefixLift 2785188
  have htrace : WordTrace (prefixWord ++ tailWord_2785188) baseStart_2785188 baseEnd_2785188 := by
    simpa [prefixWord, tailWord_2785188, baseEnd_2785188] using wordTrace_append hprefix tailTrace_2785188
  have hstable : (prefixWord ++ tailWord_2785188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785188).length < 2 ^ (prefixWord ++ tailWord_2785188).sum := by decide
  have hdescent : baseEnd_2785188 < baseStart_2785188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785201 : List Nat := [1, 2, 2, 4, 2, 1, 1, 9]
def baseStart_2785201 : Nat := 118140960795 + 2785201 * 2 ^ 59
def prefixEnd_2785201 : Nat := 4983230072969 + 3 ^ 40 * 2785201 * 2
def baseEnd_2785201 : Nat := 105936802398760194220637

theorem tailTrace_2785201 : CollatzResearch.WordTrace tailWord_2785201 prefixEnd_2785201 105936802398760194220637 := by
  unfold tailWord_2785201
  simp only [CollatzResearch.WordTrace]
  refine ⟨101584625982699926305531457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67723083988466617537020971 101584625982699926305531457)
  ·
    refine ⟨76188469487024944729148593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101584625982699926305531457 76188469487024944729148593)
    ·
      refine ⟨57141352115268708546861445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76188469487024944729148593 57141352115268708546861445)
      ·
        refine ⟨10714003521612882852536521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57141352115268708546861445 10714003521612882852536521)
        ·
          refine ⟨8035502641209662139402391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10714003521612882852536521 8035502641209662139402391)
          ·
            refine ⟨12053253961814493209103587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8035502641209662139402391 12053253961814493209103587)
            ·
              refine ⟨18079880942721739813655381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12053253961814493209103587 18079880942721739813655381)
              ·
                refine ⟨105936802398760194220637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18079880942721739813655381 105936802398760194220637)
                ·
                  rfl

theorem cell22_2785201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 9].length) (baseStart_2785201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785201 prefixEnd_2785201 := by exact prefixLift 2785201
  have htrace : WordTrace (prefixWord ++ tailWord_2785201) baseStart_2785201 baseEnd_2785201 := by
    simpa [prefixWord, tailWord_2785201, baseEnd_2785201] using wordTrace_append hprefix tailTrace_2785201
  have hstable : (prefixWord ++ tailWord_2785201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785201).length < 2 ^ (prefixWord ++ tailWord_2785201).sum := by decide
  have hdescent : baseEnd_2785201 < baseStart_2785201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785205 : List Nat := [1, 3, 3, 2, 1, 3, 1, 3, 2, 3]
def baseStart_2785205 : Nat := 118140960795 + 2785205 * 2 ^ 59
def prefixEnd_2785205 : Nat := 4983230072969 + 3 ^ 40 * 2785205 * 2
def baseEnd_2785205 : Nat := 953432590870587070885721

theorem tailTrace_2785205 : CollatzResearch.WordTrace tailWord_2785205 prefixEnd_2785205 953432590870587070885721 := by
  unfold tailWord_2785205
  simp only [CollatzResearch.WordTrace]
  refine ⟨101584771874685434988677069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67723181249790289992451379 101584771874685434988677069)
  ·
    refine ⟨38094289453007038120753901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101584771874685434988677069 38094289453007038120753901)
    ·
      refine ⟨14285358544877639295282713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38094289453007038120753901 14285358544877639295282713)
      ·
        refine ⟨10714018908658229471462035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14285358544877639295282713 10714018908658229471462035)
        ·
          refine ⟨16071028362987344207193053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10714018908658229471462035 16071028362987344207193053)
          ·
            refine ⟨6026635636120254077697395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16071028362987344207193053 6026635636120254077697395)
            ·
              refine ⟨9039953454180381116546093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6026635636120254077697395 9039953454180381116546093)
              ·
                refine ⟨3389982545317642918704785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9039953454180381116546093 3389982545317642918704785)
                ·
                  refine ⟨2542486908988232189028589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3389982545317642918704785 2542486908988232189028589)
                  ·
                    refine ⟨953432590870587070885721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542486908988232189028589 953432590870587070885721)
                    ·
                      rfl

theorem cell22_2785205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_2785205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785205 prefixEnd_2785205 := by exact prefixLift 2785205
  have htrace : WordTrace (prefixWord ++ tailWord_2785205) baseStart_2785205 baseEnd_2785205 := by
    simpa [prefixWord, tailWord_2785205, baseEnd_2785205] using wordTrace_append hprefix tailTrace_2785205
  have hstable : (prefixWord ++ tailWord_2785205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785205).length < 2 ^ (prefixWord ++ tailWord_2785205).sum := by decide
  have hdescent : baseEnd_2785205 < baseStart_2785205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785291 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 8]
def baseStart_2785291 : Nat := 118140960795 + 2785291 * 2 ^ 59
def prefixEnd_2785291 : Nat := 4983230072969 + 3 ^ 40 * 2785291 * 2
def baseEnd_2785291 : Nat := 317820676809370504411819

theorem tailTrace_2785291 : CollatzResearch.WordTrace tailWord_2785291 prefixEnd_2785291 317820676809370504411819 := by
  unfold tailWord_2785291
  simp only [CollatzResearch.WordTrace]
  refine ⟨101587908552373871676307727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67725272368249247784205151 101587908552373871676307727)
  ·
    refine ⟨152381862828560807514461591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101587908552373871676307727 152381862828560807514461591)
    ·
      refine ⟨228572794242841211271692387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152381862828560807514461591 228572794242841211271692387)
      ·
        refine ⟨342859191364261816907538581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228572794242841211271692387 342859191364261816907538581)
        ·
          refine ⟨16071524595199772667540871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 342859191364261816907538581 16071524595199772667540871)
          ·
            refine ⟨24107286892799659001311307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16071524595199772667540871 24107286892799659001311307)
            ·
              refine ⟨36160930339199488501966961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24107286892799659001311307 36160930339199488501966961)
              ·
                refine ⟨27120697754399616376475221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36160930339199488501966961 27120697754399616376475221)
                ·
                  refine ⟨317820676809370504411819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27120697754399616376475221 317820676809370504411819)
                  ·
                    rfl

theorem cell22_2785291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 8].length) (baseStart_2785291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785291 prefixEnd_2785291 := by exact prefixLift 2785291
  have htrace : WordTrace (prefixWord ++ tailWord_2785291) baseStart_2785291 baseEnd_2785291 := by
    simpa [prefixWord, tailWord_2785291, baseEnd_2785291] using wordTrace_append hprefix tailTrace_2785291
  have hstable : (prefixWord ++ tailWord_2785291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785291).length < 2 ^ (prefixWord ++ tailWord_2785291).sum := by decide
  have hdescent : baseEnd_2785291 < baseStart_2785291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785308 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 6]
def baseStart_2785308 : Nat := 118140960795 + 2785308 * 2 ^ 59
def prefixEnd_2785308 : Nat := 4983230072969 + 3 ^ 40 * 2785308 * 2
def baseEnd_2785308 : Nat := 317822616625176378520135

theorem tailTrace_2785308 : CollatzResearch.WordTrace tailWord_2785308 prefixEnd_2785308 317822616625176378520135 := by
  unfold tailWord_2785308
  simp only [CollatzResearch.WordTrace]
  refine ⟨50794264296656141789838289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67725685728874855719784385 50794264296656141789838289)
  ·
    refine ⟨38095698222492106342378717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50794264296656141789838289 38095698222492106342378717)
    ·
      refine ⟨14285886833434539878392019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38095698222492106342378717 14285886833434539878392019)
      ·
        refine ⟨21428830250151809817588029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14285886833434539878392019 21428830250151809817588029)
        ·
          refine ⟨8035811343806928681595511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21428830250151809817588029 8035811343806928681595511)
          ·
            refine ⟨12053717015710393022393267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8035811343806928681595511 12053717015710393022393267)
            ·
              refine ⟨18080575523565589533589901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12053717015710393022393267 18080575523565589533589901)
              ·
                refine ⟨6780215821337096075096213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18080575523565589533589901 6780215821337096075096213)
                ·
                  refine ⟨317822616625176378520135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6780215821337096075096213 317822616625176378520135)
                  ·
                    rfl

theorem cell22_2785308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_2785308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785308 prefixEnd_2785308 := by exact prefixLift 2785308
  have htrace : WordTrace (prefixWord ++ tailWord_2785308) baseStart_2785308 baseEnd_2785308 := by
    simpa [prefixWord, tailWord_2785308, baseEnd_2785308] using wordTrace_append hprefix tailTrace_2785308
  have hstable : (prefixWord ++ tailWord_2785308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785308).length < 2 ^ (prefixWord ++ tailWord_2785308).sum := by decide
  have hdescent : baseEnd_2785308 < baseStart_2785308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785338 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_2785338 : Nat := 118140960795 + 2785338 * 2 ^ 59
def prefixEnd_2785338 : Nat := 4983230072969 + 3 ^ 40 * 2785338 * 2
def baseEnd_2785338 : Nat := 953478119488619057310313

theorem tailTrace_2785338 : CollatzResearch.WordTrace tailWord_2785338 prefixEnd_2785338 953478119488619057310313 := by
  unfold tailWord_2785338
  simp only [CollatzResearch.WordTrace]
  refine ⟨25397405695800899675817167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67726415188802399135512445 25397405695800899675817167)
  ·
    refine ⟨38096108543701349513725751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25397405695800899675817167 38096108543701349513725751)
    ·
      refine ⟨57144162815552024270588627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38096108543701349513725751 57144162815552024270588627)
      ·
        refine ⟨85716244223328036405882941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57144162815552024270588627 85716244223328036405882941)
        ·
          refine ⟨32143591583748013652206103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85716244223328036405882941 32143591583748013652206103)
          ·
            refine ⟨48215387375622020478309155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32143591583748013652206103 48215387375622020478309155)
            ·
              refine ⟨72323081063433030717463733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48215387375622020478309155 72323081063433030717463733)
              ·
                refine ⟨6780288849696846629762225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72323081063433030717463733 6780288849696846629762225)
                ·
                  refine ⟨5085216637272634972321669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6780288849696846629762225 5085216637272634972321669)
                  ·
                    refine ⟨953478119488619057310313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5085216637272634972321669 953478119488619057310313)
                    ·
                      rfl

theorem cell22_2785338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_2785338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785338 prefixEnd_2785338 := by exact prefixLift 2785338
  have htrace : WordTrace (prefixWord ++ tailWord_2785338) baseStart_2785338 baseEnd_2785338 := by
    simpa [prefixWord, tailWord_2785338, baseEnd_2785338] using wordTrace_append hprefix tailTrace_2785338
  have hstable : (prefixWord ++ tailWord_2785338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785338).length < 2 ^ (prefixWord ++ tailWord_2785338).sum := by decide
  have hdescent : baseEnd_2785338 < baseStart_2785338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785357 : List Nat := [1, 6, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_2785357 : Nat := 118140960795 + 2785357 * 2 ^ 59
def prefixEnd_2785357 : Nat := 4983230072969 + 3 ^ 40 * 2785357 * 2
def baseEnd_2785357 : Nat := 953484623576909341085255

theorem tailTrace_2785357 : CollatzResearch.WordTrace tailWord_2785357 prefixEnd_2785357 953484623576909341085255 := by
  unfold tailWord_2785357
  simp only [CollatzResearch.WordTrace]
  refine ⟨101590315770134764948210325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67726877180089843298806883 101590315770134764948210325)
  ·
    refine ⟨4762046051725067106947359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101590315770134764948210325 4762046051725067106947359)
    ·
      refine ⟨7143069077587600660421039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4762046051725067106947359 7143069077587600660421039)
      ·
        refine ⟨10714603616381400990631559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7143069077587600660421039 10714603616381400990631559)
        ·
          refine ⟨16071905424572101485947339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10714603616381400990631559 16071905424572101485947339)
          ·
            refine ⟨24107858136858152228921009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16071905424572101485947339 24107858136858152228921009)
            ·
              refine ⟨18080893602643614171690757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24107858136858152228921009 18080893602643614171690757)
              ·
                refine ⟨3390167550495677657192017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18080893602643614171690757 3390167550495677657192017)
                ·
                  refine ⟨2542625662871758242894013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3390167550495677657192017 2542625662871758242894013)
                  ·
                    refine ⟨953484623576909341085255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542625662871758242894013 953484623576909341085255)
                    ·
                      rfl

theorem cell22_2785357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_2785357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785357 prefixEnd_2785357 := by exact prefixLift 2785357
  have htrace : WordTrace (prefixWord ++ tailWord_2785357) baseStart_2785357 baseEnd_2785357 := by
    simpa [prefixWord, tailWord_2785357, baseEnd_2785357] using wordTrace_append hprefix tailTrace_2785357
  have hstable : (prefixWord ++ tailWord_2785357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785357).length < 2 ^ (prefixWord ++ tailWord_2785357).sum := by decide
  have hdescent : baseEnd_2785357 < baseStart_2785357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785445 : List Nat := [1, 3, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_2785445 : Nat := 118140960795 + 2785445 * 2 ^ 59
def prefixEnd_2785445 : Nat := 4983230072969 + 3 ^ 40 * 2785445 * 2
def baseEnd_2785445 : Nat := 953514747775306444884985

theorem tailTrace_2785445 : CollatzResearch.WordTrace tailWord_2785445 prefixEnd_2785445 953514747775306444884985 := by
  unfold tailWord_2785445
  simp only [CollatzResearch.WordTrace]
  refine ⟨101593525393815955977413789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67729016929210637318275859 101593525393815955977413789)
  ·
    refine ⟨38097572022680983491530171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101593525393815955977413789 38097572022680983491530171)
    ·
      refine ⟨57146358034021475237295257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38097572022680983491530171 57146358034021475237295257)
      ·
        refine ⟨42859768525516106427971443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57146358034021475237295257 42859768525516106427971443)
        ·
          refine ⟨64289652788274159641957165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42859768525516106427971443 64289652788274159641957165)
          ·
            refine ⟨24108619795602809865733937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64289652788274159641957165 24108619795602809865733937)
            ·
              refine ⟨18081464846702107399300453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24108619795602809865733937 18081464846702107399300453)
              ·
                refine ⟨3390274658756645137368835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18081464846702107399300453 3390274658756645137368835)
                ·
                  refine ⟨5085411988134967706053253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390274658756645137368835 5085411988134967706053253)
                  ·
                    refine ⟨953514747775306444884985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5085411988134967706053253 953514747775306444884985)
                    ·
                      rfl

theorem cell22_2785445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_2785445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785445 prefixEnd_2785445 := by exact prefixLift 2785445
  have htrace : WordTrace (prefixWord ++ tailWord_2785445) baseStart_2785445 baseEnd_2785445 := by
    simpa [prefixWord, tailWord_2785445, baseEnd_2785445] using wordTrace_append hprefix tailTrace_2785445
  have hstable : (prefixWord ++ tailWord_2785445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785445).length < 2 ^ (prefixWord ++ tailWord_2785445).sum := by decide
  have hdescent : baseEnd_2785445 < baseStart_2785445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785490 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_2785490 : Nat := 118140960795 + 2785490 * 2 ^ 59
def prefixEnd_2785490 : Nat := 4983230072969 + 3 ^ 40 * 2785490 * 2
def baseEnd_2785490 : Nat := 953530152194941327509847

theorem tailTrace_2785490 : CollatzResearch.WordTrace tailWord_2785490 prefixEnd_2785490 953530152194941327509847 := by
  unfold tailWord_2785490
  simp only [CollatzResearch.WordTrace]
  refine ⟨25398791669663232165700481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67730111119101952441867949 25398791669663232165700481)
  ·
    refine ⟨19049093752247424124275361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25398791669663232165700481 19049093752247424124275361)
    ·
      refine ⟨14286820314185568093206521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19049093752247424124275361 14286820314185568093206521)
      ·
        refine ⟨10715115235639176069904891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14286820314185568093206521 10715115235639176069904891)
        ·
          refine ⟨16072672853458764104857337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10715115235639176069904891 16072672853458764104857337)
          ·
            refine ⟨12054504640094073078643003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16072672853458764104857337 12054504640094073078643003)
            ·
              refine ⟨18081756960141109617964505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12054504640094073078643003 18081756960141109617964505)
              ·
                refine ⟨13561317720105832213473379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18081756960141109617964505 13561317720105832213473379)
                ·
                  refine ⟨20341976580158748320210069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13561317720105832213473379 20341976580158748320210069)
                  ·
                    refine ⟨953530152194941327509847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20341976580158748320210069 953530152194941327509847)
                    ·
                      rfl

theorem cell22_2785490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_2785490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785490 prefixEnd_2785490 := by exact prefixLift 2785490
  have htrace : WordTrace (prefixWord ++ tailWord_2785490) baseStart_2785490 baseEnd_2785490 := by
    simpa [prefixWord, tailWord_2785490, baseEnd_2785490] using wordTrace_append hprefix tailTrace_2785490
  have hstable : (prefixWord ++ tailWord_2785490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785490).length < 2 ^ (prefixWord ++ tailWord_2785490).sum := by decide
  have hdescent : baseEnd_2785490 < baseStart_2785490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785503 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 1, 9]
def baseStart_2785503 : Nat := 118140960795 + 2785503 * 2 ^ 59
def prefixEnd_2785503 : Nat := 4983230072969 + 3 ^ 40 * 2785503 * 2
def baseEnd_2785503 : Nat := 953534602360613626934807

theorem tailTrace_2785503 : CollatzResearch.WordTrace tailWord_2785503 prefixEnd_2785503 953534602360613626934807 := by
  unfold tailWord_2785503
  simp only [CollatzResearch.WordTrace]
  refine ⟨101595640827605831883025163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67730427218403887922016775 101595640827605831883025163)
  ·
    refine ⟨152393461241408747824537745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101595640827605831883025163 152393461241408747824537745)
    ·
      refine ⟨114295095931056560868403309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152393461241408747824537745 114295095931056560868403309)
      ·
        refine ⟨42860660974146210325651241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114295095931056560868403309 42860660974146210325651241)
        ·
          refine ⟨32145495730609657744238431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42860660974146210325651241 32145495730609657744238431)
          ·
            refine ⟨48218243595914486616357647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32145495730609657744238431 48218243595914486616357647)
            ·
              refine ⟨72327365393871729924536471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48218243595914486616357647 72327365393871729924536471)
              ·
                refine ⟨108491048090807594886804707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72327365393871729924536471 108491048090807594886804707)
                ·
                  refine ⟨162736572136211392330207061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108491048090807594886804707 162736572136211392330207061)
                  ·
                    refine ⟨953534602360613626934807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 162736572136211392330207061 953534602360613626934807)
                    ·
                      rfl

theorem cell22_2785503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_2785503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785503 prefixEnd_2785503 := by exact prefixLift 2785503
  have htrace : WordTrace (prefixWord ++ tailWord_2785503) baseStart_2785503 baseEnd_2785503 := by
    simpa [prefixWord, tailWord_2785503, baseEnd_2785503] using wordTrace_append hprefix tailTrace_2785503
  have hstable : (prefixWord ++ tailWord_2785503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785503).length < 2 ^ (prefixWord ++ tailWord_2785503).sum := by decide
  have hdescent : baseEnd_2785503 < baseStart_2785503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785520 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 5, 3]
def baseStart_2785520 : Nat := 118140960795 + 2785520 * 2 ^ 59
def prefixEnd_2785520 : Nat := 4983230072969 + 3 ^ 40 * 2785520 * 2
def baseEnd_2785520 : Nat := 953540421808031249259755

theorem tailTrace_2785520 : CollatzResearch.WordTrace tailWord_2785520 prefixEnd_2785520 953540421808031249259755 := by
  unfold tailWord_2785520
  simp only [CollatzResearch.WordTrace]
  refine ⟨50798130434272121893197007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67730840579029495857596009 50798130434272121893197007)
  ·
    refine ⟨76197195651408182839795511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50798130434272121893197007 76197195651408182839795511)
    ·
      refine ⟨114295793477112274259693267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76197195651408182839795511 114295793477112274259693267)
      ·
        refine ⟨171443690215668411389539901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114295793477112274259693267 171443690215668411389539901)
        ·
          refine ⟨64291383830875654271077463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171443690215668411389539901 64291383830875654271077463)
          ·
            refine ⟨96437075746313481406616195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64291383830875654271077463 96437075746313481406616195)
            ·
              refine ⟨144655613619470222109924293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96437075746313481406616195 144655613619470222109924293)
              ·
                refine ⟨27122927553650666645610805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144655613619470222109924293 27122927553650666645610805)
                ·
                  refine ⟨2542774458154749998026013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27122927553650666645610805 2542774458154749998026013)
                  ·
                    refine ⟨953540421808031249259755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542774458154749998026013 953540421808031249259755)
                    ·
                      rfl

theorem cell22_2785520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 3].length) (baseStart_2785520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785520 prefixEnd_2785520 := by exact prefixLift 2785520
  have htrace : WordTrace (prefixWord ++ tailWord_2785520) baseStart_2785520 baseEnd_2785520 := by
    simpa [prefixWord, tailWord_2785520, baseEnd_2785520] using wordTrace_append hprefix tailTrace_2785520
  have hstable : (prefixWord ++ tailWord_2785520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785520).length < 2 ^ (prefixWord ++ tailWord_2785520).sum := by decide
  have hdescent : baseEnd_2785520 < baseStart_2785520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785543 : List Nat := [1, 1, 4, 5, 1, 2, 2, 1, 2, 3]
def baseStart_2785543 : Nat := 118140960795 + 2785543 * 2 ^ 59
def prefixEnd_2785543 : Nat := 4983230072969 + 3 ^ 40 * 2785543 * 2
def baseEnd_2785543 : Nat := 953548295178066855934685

theorem tailTrace_2785543 : CollatzResearch.WordTrace tailWord_2785543 prefixEnd_2785543 953548295178066855934685 := by
  unfold tailWord_2785543
  simp only [CollatzResearch.WordTrace]
  refine ⟨101597099747460918714481283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67731399831640612476320855 101597099747460918714481283)
  ·
    refine ⟨152395649621191378071721925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101597099747460918714481283 152395649621191378071721925)
    ·
      refine ⟨28574184303973383388447861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152395649621191378071721925 28574184303973383388447861)
      ·
        refine ⟨2678829778497504692666987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28574184303973383388447861 2678829778497504692666987)
        ·
          refine ⟨4018244667746257039000481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2678829778497504692666987 4018244667746257039000481)
          ·
            refine ⟨3013683500809692779250361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4018244667746257039000481 3013683500809692779250361)
            ·
              refine ⟨2260262625607269584437771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3013683500809692779250361 2260262625607269584437771)
              ·
                refine ⟨3390393938410904376656657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260262625607269584437771 3390393938410904376656657)
                ·
                  refine ⟨2542795453808178282492493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3390393938410904376656657 2542795453808178282492493)
                  ·
                    refine ⟨953548295178066855934685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542795453808178282492493 953548295178066855934685)
                    ·
                      rfl

theorem cell22_2785543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_2785543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785543 prefixEnd_2785543 := by exact prefixLift 2785543
  have htrace : WordTrace (prefixWord ++ tailWord_2785543) baseStart_2785543 baseEnd_2785543 := by
    simpa [prefixWord, tailWord_2785543, baseEnd_2785543] using wordTrace_append hprefix tailTrace_2785543
  have hstable : (prefixWord ++ tailWord_2785543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785543).length < 2 ^ (prefixWord ++ tailWord_2785543).sum := by decide
  have hdescent : baseEnd_2785543 < baseStart_2785543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785588 : List Nat := [2, 5, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_2785588 : Nat := 118140960795 + 2785588 * 2 ^ 59
def prefixEnd_2785588 : Nat := 4983230072969 + 3 ^ 40 * 2785588 * 2
def baseEnd_2785588 : Nat := 953563699597701738559547

theorem tailTrace_2785588 : CollatzResearch.WordTrace tailWord_2785588 prefixEnd_2785588 953563699597701738559547 := by
  unfold tailWord_2785588
  simp only [CollatzResearch.WordTrace]
  refine ⟨50799370516148945699934709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67732494021531927599912945 50799370516148945699934709)
  ·
    refine ⟨4762440985888963659368879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50799370516148945699934709 4762440985888963659368879)
    ·
      refine ⟨7143661478833445489053319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4762440985888963659368879 7143661478833445489053319)
      ·
        refine ⟨10715492218250168233579979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7143661478833445489053319 10715492218250168233579979)
        ·
          refine ⟨16073238327375252350369969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10715492218250168233579979 16073238327375252350369969)
          ·
            refine ⟨12054928745531439262777477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16073238327375252350369969 12054928745531439262777477)
            ·
              refine ⟨2260299139787144861770777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12054928745531439262777477 2260299139787144861770777)
              ·
                refine ⟨1695224354840358646328083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2260299139787144861770777 1695224354840358646328083)
                ·
                  refine ⟨2542836532260537969492125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695224354840358646328083 2542836532260537969492125)
                  ·
                    refine ⟨953563699597701738559547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542836532260537969492125 953563699597701738559547)
                    ·
                      rfl

theorem cell22_2785588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_2785588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785588 prefixEnd_2785588 := by exact prefixLift 2785588
  have htrace : WordTrace (prefixWord ++ tailWord_2785588) baseStart_2785588 baseEnd_2785588 := by
    simpa [prefixWord, tailWord_2785588, baseEnd_2785588] using wordTrace_append hprefix tailTrace_2785588
  have hstable : (prefixWord ++ tailWord_2785588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785588).length < 2 ^ (prefixWord ++ tailWord_2785588).sum := by decide
  have hdescent : baseEnd_2785588 < baseStart_2785588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785644 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 4, 3]
def baseStart_2785644 : Nat := 118140960795 + 2785644 * 2 ^ 59
def prefixEnd_2785644 : Nat := 4983230072969 + 3 ^ 40 * 2785644 * 2
def baseEnd_2785644 : Nat := 953582869542136259159375

theorem tailTrace_2785644 : CollatzResearch.WordTrace tailWord_2785644 prefixEnd_2785644 953582869542136259159375 := by
  unfold tailWord_2785644
  simp only [CollatzResearch.WordTrace]
  refine ⟨50800391760047506481953993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67733855680063341975938657 50800391760047506481953993)
  ·
    refine ⟨38100293820035629861465495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50800391760047506481953993 38100293820035629861465495)
    ·
      refine ⟨57150440730053444792198243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38100293820035629861465495 57150440730053444792198243)
      ·
        refine ⟨85725661095080167188297365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57150440730053444792198243 85725661095080167188297365)
        ·
          refine ⟨4018390363831882836951439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85725661095080167188297365 4018390363831882836951439)
          ·
            refine ⟨6027585545747824255427159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4018390363831882836951439 6027585545747824255427159)
            ·
              refine ⟨9041378318621736383140739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6027585545747824255427159 9041378318621736383140739)
              ·
                refine ⟨13562067477932604574711109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9041378318621736383140739 13562067477932604574711109)
                ·
                  refine ⟨2542887652112363357758333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13562067477932604574711109 2542887652112363357758333)
                  ·
                    refine ⟨953582869542136259159375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542887652112363357758333 953582869542136259159375)
                    ·
                      rfl

theorem cell22_2785644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_2785644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785644 prefixEnd_2785644 := by exact prefixLift 2785644
  have htrace : WordTrace (prefixWord ++ tailWord_2785644) baseStart_2785644 baseEnd_2785644 := by
    simpa [prefixWord, tailWord_2785644, baseEnd_2785644] using wordTrace_append hprefix tailTrace_2785644
  have hstable : (prefixWord ++ tailWord_2785644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785644).length < 2 ^ (prefixWord ++ tailWord_2785644).sum := by decide
  have hdescent : baseEnd_2785644 < baseStart_2785644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785661 : List Nat := [1, 4, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_2785661 : Nat := 118140960795 + 2785661 * 2 ^ 59
def prefixEnd_2785661 : Nat := 4983230072969 + 3 ^ 40 * 2785661 * 2
def baseEnd_2785661 : Nat := 953588688989553881484323

theorem tailTrace_2785661 : CollatzResearch.WordTrace tailWord_2785661 prefixEnd_2785661 953588688989553881484323 := by
  unfold tailWord_2785661
  simp only [CollatzResearch.WordTrace]
  refine ⟨101601403561033424867276837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67734269040688949911517891 101601403561033424867276837)
  ·
    refine ⟨19050263167693767162614407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101601403561033424867276837 19050263167693767162614407)
    ·
      refine ⟨28575394751540650743921611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19050263167693767162614407 28575394751540650743921611)
      ·
        refine ⟨42863092127310976115882417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28575394751540650743921611 42863092127310976115882417)
        ·
          refine ⟨32147319095483232086911813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42863092127310976115882417 32147319095483232086911813)
          ·
            refine ⟨6027622330403106016295965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32147319095483232086911813 6027622330403106016295965)
            ·
              refine ⟨2260358373901164756110987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6027622330403106016295965 2260358373901164756110987)
              ·
                refine ⟨3390537560851747134166481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260358373901164756110987 3390537560851747134166481)
                ·
                  refine ⟨2542903170638810350624861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3390537560851747134166481 2542903170638810350624861)
                  ·
                    refine ⟨953588688989553881484323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542903170638810350624861 953588688989553881484323)
                    ·
                      rfl

theorem cell22_2785661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_2785661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785661 prefixEnd_2785661 := by exact prefixLift 2785661
  have htrace : WordTrace (prefixWord ++ tailWord_2785661) baseStart_2785661 baseEnd_2785661 := by
    simpa [prefixWord, tailWord_2785661, baseEnd_2785661] using wordTrace_append hprefix tailTrace_2785661
  have hstable : (prefixWord ++ tailWord_2785661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785661).length < 2 ^ (prefixWord ++ tailWord_2785661).sum := by decide
  have hdescent : baseEnd_2785661 < baseStart_2785661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785674 : List Nat := [3, 1, 2, 5, 1, 1, 1, 8]
def baseStart_2785674 : Nat := 118140960795 + 2785674 * 2 ^ 59
def prefixEnd_2785674 : Nat := 4983230072969 + 3 ^ 40 * 2785674 * 2
def baseEnd_2785674 : Nat := 105954793239469575656587

theorem tailTrace_2785674 : CollatzResearch.WordTrace tailWord_2785674 prefixEnd_2785674 105954793239469575656587 := by
  unfold tailWord_2785674
  simp only [CollatzResearch.WordTrace]
  refine ⟨25400469427496582021875019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67734585139990885391666717 25400469427496582021875019)
  ·
    refine ⟨38100704141244873032812529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25400469427496582021875019 38100704141244873032812529)
    ·
      refine ⟨28575528105933654774609397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38100704141244873032812529 28575528105933654774609397)
      ·
        refine ⟨2678955759931280135119631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28575528105933654774609397 2678955759931280135119631)
        ·
          refine ⟨4018433639896920202679447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2678955759931280135119631 4018433639896920202679447)
          ·
            refine ⟨6027650459845380304019171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4018433639896920202679447 6027650459845380304019171)
            ·
              refine ⟨9041475689768070456028757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6027650459845380304019171 9041475689768070456028757)
              ·
                refine ⟨105954793239469575656587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9041475689768070456028757 105954793239469575656587)
                ·
                  rfl

theorem cell22_2785674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_2785674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785674 prefixEnd_2785674 := by exact prefixLift 2785674
  have htrace : WordTrace (prefixWord ++ tailWord_2785674) baseStart_2785674 baseEnd_2785674 := by
    simpa [prefixWord, tailWord_2785674, baseEnd_2785674] using wordTrace_append hprefix tailTrace_2785674
  have hstable : (prefixWord ++ tailWord_2785674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785674).length < 2 ^ (prefixWord ++ tailWord_2785674).sum := by decide
  have hdescent : baseEnd_2785674 < baseStart_2785674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785715 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 1, 10]
def baseStart_2785715 : Nat := 118140960795 + 2785715 * 2 ^ 59
def prefixEnd_2785715 : Nat := 4983230072969 + 3 ^ 40 * 2785715 * 2
def baseEnd_2785715 : Nat := 953607174293115740634157

theorem tailTrace_2785715 : CollatzResearch.WordTrace tailWord_2785715 prefixEnd_2785715 953607174293115740634157 := by
  unfold tailWord_2785715
  simp only [CollatzResearch.WordTrace]
  refine ⟨101603373102837792089742599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67735582068558528059828399 101603373102837792089742599)
  ·
    refine ⟨152405059654256688134613899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101603373102837792089742599 152405059654256688134613899)
    ·
      refine ⟨228607589481385032201920849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152405059654256688134613899 228607589481385032201920849)
      ·
        refine ⟨171455692111038774151440637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228607589481385032201920849 171455692111038774151440637)
        ·
          refine ⟨64295884541639540306790239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171455692111038774151440637 64295884541639540306790239)
          ·
            refine ⟨96443826812459310460185359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64295884541639540306790239 96443826812459310460185359)
            ·
              refine ⟨144665740218688965690278039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96443826812459310460185359 144665740218688965690278039)
              ·
                refine ⟨216998610328033448535417059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144665740218688965690278039 216998610328033448535417059)
                ·
                  refine ⟨325497915492050172803125589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216998610328033448535417059 325497915492050172803125589)
                  ·
                    refine ⟨953607174293115740634157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 325497915492050172803125589 953607174293115740634157)
                    ·
                      rfl

theorem cell22_2785715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_2785715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785715 prefixEnd_2785715 := by exact prefixLift 2785715
  have htrace : WordTrace (prefixWord ++ tailWord_2785715) baseStart_2785715 baseEnd_2785715 := by
    simpa [prefixWord, tailWord_2785715, baseEnd_2785715] using wordTrace_append hprefix tailTrace_2785715
  have hstable : (prefixWord ++ tailWord_2785715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785715).length < 2 ^ (prefixWord ++ tailWord_2785715).sum := by decide
  have hdescent : baseEnd_2785715 < baseStart_2785715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785719 : List Nat := [1, 1, 3, 1, 3, 3, 4, 1, 5]
def baseStart_2785719 : Nat := 118140960795 + 2785719 * 2 ^ 59
def prefixEnd_2785719 : Nat := 4983230072969 + 3 ^ 40 * 2785719 * 2
def baseEnd_2785719 : Nat := 317869514524953687844715

theorem tailTrace_2785719 : CollatzResearch.WordTrace tailWord_2785719 prefixEnd_2785719 317869514524953687844715 := by
  unfold tailWord_2785719
  simp only [CollatzResearch.WordTrace]
  refine ⟨101603518994823300772888211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67735679329882200515258807 101603518994823300772888211)
  ·
    refine ⟨152405278492234951159332317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101603518994823300772888211 152405278492234951159332317)
    ·
      refine ⟨57151979434588106684749619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152405278492234951159332317 57151979434588106684749619)
      ·
        refine ⟨85727969151882160027124429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57151979434588106684749619 85727969151882160027124429)
        ·
          refine ⟨32147988431955810010171661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85727969151882160027124429 32147988431955810010171661)
          ·
            refine ⟨12055495661983428753814373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32147988431955810010171661 12055495661983428753814373)
            ·
              refine ⟨2260405436621892891340195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12055495661983428753814373 2260405436621892891340195)
              ·
                refine ⟨3390608154932839337010293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260405436621892891340195 3390608154932839337010293)
                ·
                  refine ⟨317869514524953687844715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3390608154932839337010293 317869514524953687844715)
                  ·
                    rfl

theorem cell22_2785719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 5].length) (baseStart_2785719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785719 prefixEnd_2785719 := by exact prefixLift 2785719
  have htrace : WordTrace (prefixWord ++ tailWord_2785719) baseStart_2785719 baseEnd_2785719 := by
    simpa [prefixWord, tailWord_2785719, baseEnd_2785719] using wordTrace_append hprefix tailTrace_2785719
  have hstable : (prefixWord ++ tailWord_2785719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785719).length < 2 ^ (prefixWord ++ tailWord_2785719).sum := by decide
  have hdescent : baseEnd_2785719 < baseStart_2785719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785777 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 1, 6]
def baseStart_2785777 : Nat := 118140960795 + 2785777 * 2 ^ 59
def prefixEnd_2785777 : Nat := 4983230072969 + 3 ^ 40 * 2785777 * 2
def baseEnd_2785777 : Nat := 953628398160168245583967

theorem tailTrace_2785777 : CollatzResearch.WordTrace tailWord_2785777 prefixEnd_2785777 953628398160168245583967 := by
  unfold tailWord_2785777
  simp only [CollatzResearch.WordTrace]
  refine ⟨101605634428613176678499585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67737089619075451118999723 101605634428613176678499585)
  ·
    refine ⟨76204225821459882508874689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101605634428613176678499585 76204225821459882508874689)
    ·
      refine ⟨57153169366094911881656017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76204225821459882508874689 57153169366094911881656017)
      ·
        refine ⟨42864877024571183911242013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57153169366094911881656017 42864877024571183911242013)
        ·
          refine ⟨16074328884214193966715755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42864877024571183911242013 16074328884214193966715755)
          ·
            refine ⟨24111493326321290950073633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16074328884214193966715755 24111493326321290950073633)
            ·
              refine ⟨18083619994740968212555225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24111493326321290950073633 18083619994740968212555225)
              ·
                refine ⟨13562714996055726159416419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18083619994740968212555225 13562714996055726159416419)
                ·
                  refine ⟨20344072494083589239124629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13562714996055726159416419 20344072494083589239124629)
                  ·
                    refine ⟨953628398160168245583967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20344072494083589239124629 953628398160168245583967)
                    ·
                      rfl

theorem cell22_2785777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_2785777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785777 prefixEnd_2785777 := by exact prefixLift 2785777
  have htrace : WordTrace (prefixWord ++ tailWord_2785777) baseStart_2785777 baseEnd_2785777 := by
    simpa [prefixWord, tailWord_2785777, baseEnd_2785777] using wordTrace_append hprefix tailTrace_2785777
  have hstable : (prefixWord ++ tailWord_2785777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785777).length < 2 ^ (prefixWord ++ tailWord_2785777).sum := by decide
  have hdescent : baseEnd_2785777 < baseStart_2785777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785779 : List Nat := [1, 1, 1, 2, 2, 2, 3, 5, 2, 3]
def baseStart_2785779 : Nat := 118140960795 + 2785779 * 2 ^ 59
def prefixEnd_2785779 : Nat := 4983230072969 + 3 ^ 40 * 2785779 * 2
def baseEnd_2785779 : Nat := 953629082801040907033961

theorem tailTrace_2785779 : CollatzResearch.WordTrace tailWord_2785779 prefixEnd_2785779 953629082801040907033961 := by
  unfold tailWord_2785779
  simp only [CollatzResearch.WordTrace]
  refine ⟨101605707374605931020072391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67737138249737287346714927 101605707374605931020072391)
  ·
    refine ⟨152408561061908896530108587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101605707374605931020072391 152408561061908896530108587)
    ·
      refine ⟨228612841592863344795162881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152408561061908896530108587 228612841592863344795162881)
      ·
        refine ⟨171459631194647508596372161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228612841592863344795162881 171459631194647508596372161)
        ·
          refine ⟨128594723395985631447279121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171459631194647508596372161 128594723395985631447279121)
          ·
            refine ⟨96446042546989223585459341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128594723395985631447279121 96446042546989223585459341)
            ·
              refine ⟨36167265955120958844547253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96446042546989223585459341 36167265955120958844547253)
              ·
                refine ⟨3390681183292589891676305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36167265955120958844547253 3390681183292589891676305)
                ·
                  refine ⟨2543010887469442418757229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3390681183292589891676305 2543010887469442418757229)
                  ·
                    refine ⟨953629082801040907033961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2543010887469442418757229 953629082801040907033961)
                    ·
                      rfl

theorem cell22_2785779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 3].length) (baseStart_2785779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785779 prefixEnd_2785779 := by exact prefixLift 2785779
  have htrace : WordTrace (prefixWord ++ tailWord_2785779) baseStart_2785779 baseEnd_2785779 := by
    simpa [prefixWord, tailWord_2785779, baseEnd_2785779] using wordTrace_append hprefix tailTrace_2785779
  have hstable : (prefixWord ++ tailWord_2785779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785779).length < 2 ^ (prefixWord ++ tailWord_2785779).sum := by decide
  have hdescent : baseEnd_2785779 < baseStart_2785779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785781 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 6]
def baseStart_2785781 : Nat := 118140960795 + 2785781 * 2 ^ 59
def prefixEnd_2785781 : Nat := 4983230072969 + 3 ^ 40 * 2785781 * 2
def baseEnd_2785781 : Nat := 317876589147304522827985

theorem tailTrace_2785781 : CollatzResearch.WordTrace tailWord_2785781 prefixEnd_2785781 317876589147304522827985 := by
  unfold tailWord_2785781
  simp only [CollatzResearch.WordTrace]
  refine ⟨101605780320598685361645197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67737186880399123574430131 101605780320598685361645197)
  ·
    refine ⟨38102167620224507010616949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101605780320598685361645197 38102167620224507010616949)
    ·
      refine ⟨3572078214396047532245339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38102167620224507010616949 3572078214396047532245339)
      ·
        refine ⟨5358117321594071298368009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3572078214396047532245339 5358117321594071298368009)
        ·
          refine ⟨4018587991195553473776007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5358117321594071298368009 4018587991195553473776007)
          ·
            refine ⟨6027881986793330210664011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4018587991195553473776007 6027881986793330210664011)
            ·
              refine ⟨9041822980189995315996017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6027881986793330210664011 9041822980189995315996017)
              ·
                refine ⟨6781367235142496486997013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9041822980189995315996017 6781367235142496486997013)
                ·
                  refine ⟨317876589147304522827985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6781367235142496486997013 317876589147304522827985)
                  ·
                    rfl

theorem cell22_2785781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_2785781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785781 prefixEnd_2785781 := by exact prefixLift 2785781
  have htrace : WordTrace (prefixWord ++ tailWord_2785781) baseStart_2785781 baseEnd_2785781 := by
    simpa [prefixWord, tailWord_2785781, baseEnd_2785781] using wordTrace_append hprefix tailTrace_2785781
  have hstable : (prefixWord ++ tailWord_2785781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785781).length < 2 ^ (prefixWord ++ tailWord_2785781).sum := by decide
  have hdescent : baseEnd_2785781 < baseStart_2785781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785860 : List Nat := [2, 3, 5, 1, 2, 1, 8]
def baseStart_2785860 : Nat := 118140960795 + 2785860 * 2 ^ 59
def prefixEnd_2785860 : Nat := 4983230072969 + 3 ^ 40 * 2785860 * 2
def baseEnd_2785860 : Nat := 35320622620606803546619

theorem tailTrace_2785860 : CollatzResearch.WordTrace tailWord_2785860 prefixEnd_2785860 35320622620606803546619 := by
  unfold tailWord_2785860
  simp only [CollatzResearch.WordTrace]
  refine ⟨50804330843656240926885517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67739107791541654569180689 50804330843656240926885517)
  ·
    refine ⟨19051624066371090347582069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50804330843656240926885517 19051624066371090347582069)
    ·
      refine ⟨1786089756222289720085819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19051624066371090347582069 1786089756222289720085819)
      ·
        refine ⟨2679134634333434580128729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786089756222289720085819 2679134634333434580128729)
        ·
          refine ⟨2009350975750075935096547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2679134634333434580128729 2009350975750075935096547)
          ·
            refine ⟨3014026463625113902644821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009350975750075935096547 3014026463625113902644821)
            ·
              refine ⟨35320622620606803546619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3014026463625113902644821 35320622620606803546619)
              ·
                rfl

theorem cell22_2785860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 8].length) (baseStart_2785860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785860 prefixEnd_2785860 := by exact prefixLift 2785860
  have htrace : WordTrace (prefixWord ++ tailWord_2785860) baseStart_2785860 baseEnd_2785860 := by
    simpa [prefixWord, tailWord_2785860, baseEnd_2785860] using wordTrace_append hprefix tailTrace_2785860
  have hstable : (prefixWord ++ tailWord_2785860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785860).length < 2 ^ (prefixWord ++ tailWord_2785860).sum := by decide
  have hdescent : baseEnd_2785860 < baseStart_2785860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785901 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_2785901 : Nat := 118140960795 + 2785901 * 2 ^ 59
def prefixEnd_2785901 : Nat := 4983230072969 + 3 ^ 40 * 2785901 * 2
def baseEnd_2785901 : Nat := 953670845894273255483587

theorem tailTrace_2785901 : CollatzResearch.WordTrace tailWord_2785901 prefixEnd_2785901 953670845894273255483587 := by
  unfold tailWord_2785901
  simp only [CollatzResearch.WordTrace]
  refine ⟨101610157080163945856013557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67740104720109297237342371 101610157080163945856013557)
  ·
    refine ⟨9525952226265369924001271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101610157080163945856013557 9525952226265369924001271)
    ·
      refine ⟨14288928339398054886001907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9525952226265369924001271 14288928339398054886001907)
      ·
        refine ⟨21433392509097082329002861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14288928339398054886001907 21433392509097082329002861)
        ·
          refine ⟨8037522190911405873376073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21433392509097082329002861 8037522190911405873376073)
          ·
            refine ⟨6028141643183554405032055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8037522190911405873376073 6028141643183554405032055)
            ·
              refine ⟨9042212464775331607548083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6028141643183554405032055 9042212464775331607548083)
              ·
                refine ⟨13563318697162997411322125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9042212464775331607548083 13563318697162997411322125)
                ·
                  refine ⟨5086244511436124029245797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13563318697162997411322125 5086244511436124029245797)
                  ·
                    refine ⟨953670845894273255483587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5086244511436124029245797 953670845894273255483587)
                    ·
                      rfl

theorem cell22_2785901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_2785901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785901 prefixEnd_2785901 := by exact prefixLift 2785901
  have htrace : WordTrace (prefixWord ++ tailWord_2785901) baseStart_2785901 baseEnd_2785901 := by
    simpa [prefixWord, tailWord_2785901, baseEnd_2785901] using wordTrace_append hprefix tailTrace_2785901
  have hstable : (prefixWord ++ tailWord_2785901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785901).length < 2 ^ (prefixWord ++ tailWord_2785901).sum := by decide
  have hdescent : baseEnd_2785901 < baseStart_2785901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785922 : List Nat := [3, 4, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2785922 : Nat := 118140960795 + 2785922 * 2 ^ 59
def prefixEnd_2785922 : Nat := 4983230072969 + 3 ^ 40 * 2785922 * 2
def baseEnd_2785922 : Nat := 317892678207812066902841

theorem tailTrace_2785922 : CollatzResearch.WordTrace tailWord_2785922 prefixEnd_2785922 317892678207812066902841 := by
  unfold tailWord_2785922
  simp only [CollatzResearch.WordTrace]
  refine ⟨25402730753271966610632005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67740615342058577628352013 25402730753271966610632005)
  ·
    refine ⟨4763012016238493739493501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25402730753271966610632005 4763012016238493739493501)
    ·
      refine ⟨1786129506089435152310063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4763012016238493739493501 1786129506089435152310063)
      ·
        refine ⟨2679194259134152728465095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786129506089435152310063 2679194259134152728465095)
        ·
          refine ⟨4018791388701229092697643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2679194259134152728465095 4018791388701229092697643)
          ·
            refine ⟨6028187083051843639046465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4018791388701229092697643 6028187083051843639046465)
            ·
              refine ⟨4521140312288882729284849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6028187083051843639046465 4521140312288882729284849)
              ·
                refine ⟨3390855234216662046963637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4521140312288882729284849 3390855234216662046963637)
                ·
                  refine ⟨317892678207812066902841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3390855234216662046963637 317892678207812066902841)
                  ·
                    rfl

theorem cell22_2785922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2785922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785922 prefixEnd_2785922 := by exact prefixLift 2785922
  have htrace : WordTrace (prefixWord ++ tailWord_2785922) baseStart_2785922 baseEnd_2785922 := by
    simpa [prefixWord, tailWord_2785922, baseEnd_2785922] using wordTrace_append hprefix tailTrace_2785922
  have hstable : (prefixWord ++ tailWord_2785922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785922).length < 2 ^ (prefixWord ++ tailWord_2785922).sum := by decide
  have hdescent : baseEnd_2785922 < baseStart_2785922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785948 : List Nat := [2, 2, 3, 2, 2, 1, 2, 3, 2, 3]
def baseStart_2785948 : Nat := 118140960795 + 2785948 * 2 ^ 59
def prefixEnd_2785948 : Nat := 4983230072969 + 3 ^ 40 * 2785948 * 2
def baseEnd_2785948 : Nat := 953686934954780799558443

theorem tailTrace_2785948 : CollatzResearch.WordTrace tailWord_2785948 prefixEnd_2785948 953686934954780799558443 := by
  unfold tailWord_2785948
  simp only [CollatzResearch.WordTrace]
  refine ⟨50805935655496836441487249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67741247540662448588649665 50805935655496836441487249)
  ·
    refine ⟨38104451741622627331115437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50805935655496836441487249 38104451741622627331115437)
    ·
      refine ⟨14289169403108485249168289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38104451741622627331115437 14289169403108485249168289)
      ·
        refine ⟨10716877052331363936876217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14289169403108485249168289 10716877052331363936876217)
        ·
          refine ⟨8037657789248522952657163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10716877052331363936876217 8037657789248522952657163)
          ·
            refine ⟨12056486683872784428985745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8037657789248522952657163 12056486683872784428985745)
            ·
              refine ⟨9042365012904588321739309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12056486683872784428985745 9042365012904588321739309)
              ·
                refine ⟨3390886879839220620652241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9042365012904588321739309 3390886879839220620652241)
                ·
                  refine ⟨2543165159879415465489181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3390886879839220620652241 2543165159879415465489181)
                  ·
                    refine ⟨953686934954780799558443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2543165159879415465489181 953686934954780799558443)
                    ·
                      rfl

theorem cell22_2785948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_2785948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2785948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2785948 prefixEnd_2785948 := by exact prefixLift 2785948
  have htrace : WordTrace (prefixWord ++ tailWord_2785948) baseStart_2785948 baseEnd_2785948 := by
    simpa [prefixWord, tailWord_2785948, baseEnd_2785948] using wordTrace_append hprefix tailTrace_2785948
  have hstable : (prefixWord ++ tailWord_2785948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785948).length < 2 ^ (prefixWord ++ tailWord_2785948).sum := by decide
  have hdescent : baseEnd_2785948 < baseStart_2785948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786102 : List Nat := [5, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_2786102 : Nat := 118140960795 + 2786102 * 2 ^ 59
def prefixEnd_2786102 : Nat := 4983230072969 + 3 ^ 40 * 2786102 * 2
def baseEnd_2786102 : Nat := 317913217433991910402657

theorem tailTrace_2786102 : CollatzResearch.WordTrace tailWord_2786102 prefixEnd_2786102 317913217433991910402657 := by
  unfold tailWord_2786102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6351093009527234824005035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67744992101623838122720373 6351093009527234824005035)
  ·
    refine ⟨9526639514290852236007553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6351093009527234824005035 9526639514290852236007553)
    ·
      refine ⟨7144979635718139177005665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9526639514290852236007553 7144979635718139177005665)
      ·
        refine ⟨5358734726788604382754249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7144979635718139177005665 5358734726788604382754249)
        ·
          refine ⟨4019051045091453287065687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5358734726788604382754249 4019051045091453287065687)
          ·
            refine ⟨6028576567637179930598531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4019051045091453287065687 6028576567637179930598531)
            ·
              refine ⟨9042864851455769895897797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6028576567637179930598531 9042864851455769895897797)
              ·
                refine ⟨1695537159647956855480837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9042864851455769895897797 1695537159647956855480837)
                ·
                  refine ⟨317913217433991910402657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1695537159647956855480837 317913217433991910402657)
                  ·
                    rfl

theorem cell22_2786102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_2786102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786102 prefixEnd_2786102 := by exact prefixLift 2786102
  have htrace : WordTrace (prefixWord ++ tailWord_2786102) baseStart_2786102 baseEnd_2786102 := by
    simpa [prefixWord, tailWord_2786102, baseEnd_2786102] using wordTrace_append hprefix tailTrace_2786102
  have hstable : (prefixWord ++ tailWord_2786102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786102).length < 2 ^ (prefixWord ++ tailWord_2786102).sum := by decide
  have hdescent : baseEnd_2786102 < baseStart_2786102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786132 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_2786132 : Nat := 118140960795 + 2786132 * 2 ^ 59
def prefixEnd_2786132 : Nat := 4983230072969 + 3 ^ 40 * 2786132 * 2
def baseEnd_2786132 : Nat := 953749921915065652957879

theorem tailTrace_2786132 : CollatzResearch.WordTrace tailWord_2786132 prefixEnd_2786132 953749921915065652957879 := by
  unfold tailWord_2786132
  simp only [CollatzResearch.WordTrace]
  refine ⟨50809291171163536153836325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67745721561551381538448433 50809291171163536153836325)
  ·
    refine ⟨9526742094593163028844311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50809291171163536153836325 9526742094593163028844311)
    ·
      refine ⟨14290113141889744543266467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9526742094593163028844311 14290113141889744543266467)
      ·
        refine ⟨21435169712834616814899701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14290113141889744543266467 21435169712834616814899701)
        ·
          refine ⟨2009547160578245326396847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21435169712834616814899701 2009547160578245326396847)
          ·
            refine ⟨3014320740867367989595271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009547160578245326396847 3014320740867367989595271)
            ·
              refine ⟨4521481111301051984392907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3014320740867367989595271 4521481111301051984392907)
              ·
                refine ⟨6782221666951577976589361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4521481111301051984392907 6782221666951577976589361)
                ·
                  refine ⟨5086666250213683482442021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6782221666951577976589361 5086666250213683482442021)
                  ·
                    refine ⟨953749921915065652957879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5086666250213683482442021 953749921915065652957879)
                    ·
                      rfl

theorem cell22_2786132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_2786132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786132 prefixEnd_2786132 := by exact prefixLift 2786132
  have htrace : WordTrace (prefixWord ++ tailWord_2786132) baseStart_2786132 baseEnd_2786132 := by
    simpa [prefixWord, tailWord_2786132, baseEnd_2786132] using wordTrace_append hprefix tailTrace_2786132
  have hstable : (prefixWord ++ tailWord_2786132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786132).length < 2 ^ (prefixWord ++ tailWord_2786132).sum := by decide
  have hdescent : baseEnd_2786132 < baseStart_2786132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786156 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_2786156 : Nat := 118140960795 + 2786156 * 2 ^ 59
def prefixEnd_2786156 : Nat := 4983230072969 + 3 ^ 40 * 2786156 * 2
def baseEnd_2786156 : Nat := 953758137605537590357805

theorem tailTrace_2786156 : CollatzResearch.WordTrace tailWord_2786156 prefixEnd_2786156 953758137605537590357805 := by
  unfold tailWord_2786156
  simp only [CollatzResearch.WordTrace]
  refine ⟨50809728847120062203273161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67746305129493416271030881 50809728847120062203273161)
  ·
    refine ⟨38107296635340046652454871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50809728847120062203273161 38107296635340046652454871)
    ·
      refine ⟨57160944953010069978682307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38107296635340046652454871 57160944953010069978682307)
      ·
        refine ⟨85741417429515104968023461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57160944953010069978682307 85741417429515104968023461)
        ·
          refine ⟨16076515768034082181504399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85741417429515104968023461 16076515768034082181504399)
          ·
            refine ⟨24114773652051123272256599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16076515768034082181504399 24114773652051123272256599)
            ·
              refine ⟨36172160478076684908384899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24114773652051123272256599 36172160478076684908384899)
              ·
                refine ⟨54258240717115027362577349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36172160478076684908384899 54258240717115027362577349)
                ·
                  refine ⟨10173420134459067630483253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54258240717115027362577349 10173420134459067630483253)
                  ·
                    refine ⟨953758137605537590357805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10173420134459067630483253 953758137605537590357805)
                    ·
                      rfl

theorem cell22_2786156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_2786156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786156 prefixEnd_2786156 := by exact prefixLift 2786156
  have htrace : WordTrace (prefixWord ++ tailWord_2786156) baseStart_2786156 baseEnd_2786156 := by
    simpa [prefixWord, tailWord_2786156, baseEnd_2786156] using wordTrace_append hprefix tailTrace_2786156
  have hstable : (prefixWord ++ tailWord_2786156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786156).length < 2 ^ (prefixWord ++ tailWord_2786156).sum := by decide
  have hdescent : baseEnd_2786156 < baseStart_2786156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786171 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 5, 4]
def baseStart_2786171 : Nat := 118140960795 + 2786171 * 2 ^ 59
def prefixEnd_2786171 : Nat := 4983230072969 + 3 ^ 40 * 2786171 * 2
def baseEnd_2786171 : Nat := 953763272412082551232759

theorem tailTrace_2786171 : CollatzResearch.WordTrace tailWord_2786171 prefixEnd_2786171 953763272412082551232759 := by
  unfold tailWord_2786171
  simp only [CollatzResearch.WordTrace]
  refine ⟨101620004789185781968342367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67746669859457187978894911 101620004789185781968342367)
  ·
    refine ⟨152430007183778672952513551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101620004789185781968342367 152430007183778672952513551)
    ·
      refine ⟨228645010775668009428770327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152430007183778672952513551 228645010775668009428770327)
      ·
        refine ⟨342967516163502014143155491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228645010775668009428770327 342967516163502014143155491)
        ·
          refine ⟨514451274245253021214733237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342967516163502014143155491 514451274245253021214733237)
          ·
            refine ⟨48229806960492470738881241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 514451274245253021214733237 48229806960492470738881241)
            ·
              refine ⟨36172355220369353054160931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48229806960492470738881241 36172355220369353054160931)
              ·
                refine ⟨54258532830554029581241397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36172355220369353054160931 54258532830554029581241397)
                ·
                  refine ⟨5086737452864440273241381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54258532830554029581241397 5086737452864440273241381)
                  ·
                    refine ⟨953763272412082551232759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5086737452864440273241381 953763272412082551232759)
                    ·
                      rfl

theorem cell22_2786171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 4].length) (baseStart_2786171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786171 prefixEnd_2786171 := by exact prefixLift 2786171
  have htrace : WordTrace (prefixWord ++ tailWord_2786171) baseStart_2786171 baseEnd_2786171 := by
    simpa [prefixWord, tailWord_2786171, baseEnd_2786171] using wordTrace_append hprefix tailTrace_2786171
  have hstable : (prefixWord ++ tailWord_2786171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786171).length < 2 ^ (prefixWord ++ tailWord_2786171).sum := by decide
  have hdescent : baseEnd_2786171 < baseStart_2786171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786188 : List Nat := [2, 2, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_2786188 : Nat := 118140960795 + 2786188 * 2 ^ 59
def prefixEnd_2786188 : Nat := 4983230072969 + 3 ^ 40 * 2786188 * 2
def baseEnd_2786188 : Nat := 953769091859500173557707

theorem tailTrace_2786188 : CollatzResearch.WordTrace tailWord_2786188 prefixEnd_2786188 953769091859500173557707 := by
  unfold tailWord_2786188
  simp only [CollatzResearch.WordTrace]
  refine ⟨50810312415062096935855609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67747083220082795914474145 50810312415062096935855609)
  ·
    refine ⟨38107734311296572701891707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50810312415062096935855609 38107734311296572701891707)
    ·
      refine ⟨57161601466944859052837561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38107734311296572701891707 57161601466944859052837561)
      ·
        refine ⟨42871201100208644289628171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57161601466944859052837561 42871201100208644289628171)
        ·
          refine ⟨64306801650312966434442257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42871201100208644289628171 64306801650312966434442257)
          ·
            refine ⟨48230101237734724825831693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64306801650312966434442257 48230101237734724825831693)
            ·
              refine ⟨18086287964150521809686885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48230101237734724825831693 18086287964150521809686885)
              ·
                refine ⟨3391178993278222839316291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18086287964150521809686885 3391178993278222839316291)
                ·
                  refine ⟨5086768489917334258974437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391178993278222839316291 5086768489917334258974437)
                  ·
                    refine ⟨953769091859500173557707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5086768489917334258974437 953769091859500173557707)
                    ·
                      rfl

theorem cell22_2786188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_2786188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786188 prefixEnd_2786188 := by exact prefixLift 2786188
  have htrace : WordTrace (prefixWord ++ tailWord_2786188) baseStart_2786188 baseEnd_2786188 := by
    simpa [prefixWord, tailWord_2786188, baseEnd_2786188] using wordTrace_append hprefix tailTrace_2786188
  have hstable : (prefixWord ++ tailWord_2786188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786188).length < 2 ^ (prefixWord ++ tailWord_2786188).sum := by decide
  have hdescent : baseEnd_2786188 < baseStart_2786188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786201 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 3, 5]
def baseStart_2786201 : Nat := 118140960795 + 2786201 * 2 ^ 59
def prefixEnd_2786201 : Nat := 4983230072969 + 3 ^ 40 * 2786201 * 2
def baseEnd_2786201 : Nat := 953773542025172472982667

theorem tailTrace_2786201 : CollatzResearch.WordTrace tailWord_2786201 prefixEnd_2786201 953773542025172472982667 := by
  unfold tailWord_2786201
  simp only [CollatzResearch.WordTrace]
  refine ⟨101621098979077097091934457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67747399319384731394622971 101621098979077097091934457)
  ·
    refine ⟨76215824234307822818950843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101621098979077097091934457 76215824234307822818950843)
    ·
      refine ⟨114323736351461734228426265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76215824234307822818950843 114323736351461734228426265)
      ·
        refine ⟨85742802263596300671319699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114323736351461734228426265 85742802263596300671319699)
        ·
          refine ⟨128614203395394451006979549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85742802263596300671319699 128614203395394451006979549)
          ·
            refine ⟨48230326273272919127617331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128614203395394451006979549 48230326273272919127617331)
            ·
              refine ⟨72345489409909378691425997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48230326273272919127617331 72345489409909378691425997)
              ·
                refine ⟨27129558528716017009284749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72345489409909378691425997 27129558528716017009284749)
                ·
                  refine ⟨10173584448268506378481781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27129558528716017009284749 10173584448268506378481781)
                  ·
                    refine ⟨953773542025172472982667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10173584448268506378481781 953773542025172472982667)
                    ·
                      rfl

theorem cell22_2786201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_2786201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786201 prefixEnd_2786201 := by exact prefixLift 2786201
  have htrace : WordTrace (prefixWord ++ tailWord_2786201) baseStart_2786201 baseEnd_2786201 := by
    simpa [prefixWord, tailWord_2786201, baseEnd_2786201] using wordTrace_append hprefix tailTrace_2786201
  have hstable : (prefixWord ++ tailWord_2786201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786201).length < 2 ^ (prefixWord ++ tailWord_2786201).sum := by decide
  have hdescent : baseEnd_2786201 < baseStart_2786201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786231 : List Nat := [1, 1, 3, 1, 3, 1, 3, 9]
def baseStart_2786231 : Nat := 118140960795 + 2786231 * 2 ^ 59
def prefixEnd_2786231 : Nat := 4983230072969 + 3 ^ 40 * 2786231 * 2
def baseEnd_2786231 : Nat := 105975979070918043859175

theorem tailTrace_2786231 : CollatzResearch.WordTrace tailWord_2786231 prefixEnd_2786231 105975979070918043859175 := by
  unfold tailWord_2786231
  simp only [CollatzResearch.WordTrace]
  refine ⟨101622193168968412215526547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67748128779312274810351031 101622193168968412215526547)
  ·
    refine ⟨152433289753452618323289821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101622193168968412215526547 152433289753452618323289821)
    ·
      refine ⟨57162483657544731871233683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152433289753452618323289821 57162483657544731871233683)
      ·
        refine ⟨85743725486317097806850525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57162483657544731871233683 85743725486317097806850525)
        ·
          refine ⟨32153897057368911677568947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85743725486317097806850525 32153897057368911677568947)
          ·
            refine ⟨48230845586053367516353421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32153897057368911677568947 48230845586053367516353421)
            ·
              refine ⟨18086567094770012818632533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48230845586053367516353421 18086567094770012818632533)
              ·
                refine ⟨105975979070918043859175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18086567094770012818632533 105975979070918043859175)
                ·
                  rfl

theorem cell22_2786231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 9].length) (baseStart_2786231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786231 prefixEnd_2786231 := by exact prefixLift 2786231
  have htrace : WordTrace (prefixWord ++ tailWord_2786231) baseStart_2786231 baseEnd_2786231 := by
    simpa [prefixWord, tailWord_2786231, baseEnd_2786231] using wordTrace_append hprefix tailTrace_2786231
  have hstable : (prefixWord ++ tailWord_2786231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786231).length < 2 ^ (prefixWord ++ tailWord_2786231).sum := by decide
  have hdescent : baseEnd_2786231 < baseStart_2786231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786263 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 7, 3]
def baseStart_2786263 : Nat := 118140960795 + 2786263 * 2 ^ 59
def prefixEnd_2786263 : Nat := 4983230072969 + 3 ^ 40 * 2786263 * 2
def baseEnd_2786263 : Nat := 953794765892224977932477

theorem tailTrace_2786263 : CollatzResearch.WordTrace tailWord_2786263 prefixEnd_2786263 953794765892224977932477 := by
  unfold tailWord_2786263
  simp only [CollatzResearch.WordTrace]
  refine ⟨101623360304852481680691443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67748906869901654453794295 101623360304852481680691443)
  ·
    refine ⟨152435040457278722521037165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101623360304852481680691443 152435040457278722521037165)
    ·
      refine ⟨57163140171479520945388937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152435040457278722521037165 57163140171479520945388937)
      ·
        refine ⟨42872355128609640709041703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57163140171479520945388937 42872355128609640709041703)
        ·
          refine ⟨64308532692914461063562555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42872355128609640709041703 64308532692914461063562555)
          ·
            refine ⟨96462799039371691595343833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64308532692914461063562555 96462799039371691595343833)
            ·
              refine ⟨72347099279528768696507875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96462799039371691595343833 72347099279528768696507875)
              ·
                refine ⟨108520648919293153044761813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72347099279528768696507875 108520648919293153044761813)
                ·
                  refine ⟨2543452709045933274486605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 108520648919293153044761813 2543452709045933274486605)
                  ·
                    refine ⟨953794765892224977932477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2543452709045933274486605 953794765892224977932477)
                    ·
                      rfl

theorem cell22_2786263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_2786263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786263 prefixEnd_2786263 := by exact prefixLift 2786263
  have htrace : WordTrace (prefixWord ++ tailWord_2786263) baseStart_2786263 baseEnd_2786263 := by
    simpa [prefixWord, tailWord_2786263, baseEnd_2786263] using wordTrace_append hprefix tailTrace_2786263
  have hstable : (prefixWord ++ tailWord_2786263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786263).length < 2 ^ (prefixWord ++ tailWord_2786263).sum := by decide
  have hdescent : baseEnd_2786263 < baseStart_2786263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786314 : List Nat := [3, 1, 2, 2, 3, 2, 2, 3, 1, 3]
def baseStart_2786314 : Nat := 118140960795 + 2786314 * 2 ^ 59
def prefixEnd_2786314 : Nat := 4983230072969 + 3 ^ 40 * 2786314 * 2
def baseEnd_2786314 : Nat := 953812224234477844907321

theorem tailTrace_2786314 : CollatzResearch.WordTrace tailWord_2786314 prefixEnd_2786314 953812224234477844907321 := by
  unfold tailWord_2786314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25406305106916929347699499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67750146951778478260531997 25406305106916929347699499)
  ·
    refine ⟨38109457660375394021549249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25406305106916929347699499 38109457660375394021549249)
    ·
      refine ⟨28582093245281545516161937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38109457660375394021549249 28582093245281545516161937)
      ·
        refine ⟨21436569933961159137121453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28582093245281545516161937 21436569933961159137121453)
        ·
          refine ⟨8038713725235434676420545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21436569933961159137121453 8038713725235434676420545)
          ·
            refine ⟨6029035293926576007315409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8038713725235434676420545 6029035293926576007315409)
            ·
              refine ⟨4521776470444932005486557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6029035293926576007315409 4521776470444932005486557)
              ·
                refine ⟨1695666176416849502057459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4521776470444932005486557 1695666176416849502057459)
                ·
                  refine ⟨2543499264625274253086189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695666176416849502057459 2543499264625274253086189)
                  ·
                    refine ⟨953812224234477844907321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2543499264625274253086189 953812224234477844907321)
                    ·
                      rfl

theorem cell22_2786314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_2786314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786314 prefixEnd_2786314 := by exact prefixLift 2786314
  have htrace : WordTrace (prefixWord ++ tailWord_2786314) baseStart_2786314 baseEnd_2786314 := by
    simpa [prefixWord, tailWord_2786314, baseEnd_2786314] using wordTrace_append hprefix tailTrace_2786314
  have hstable : (prefixWord ++ tailWord_2786314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786314).length < 2 ^ (prefixWord ++ tailWord_2786314).sum := by decide
  have hdescent : baseEnd_2786314 < baseStart_2786314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786327 : List Nat := [1, 1, 3, 5, 1, 3, 1, 2, 5]
def baseStart_2786327 : Nat := 118140960795 + 2786327 * 2 ^ 59
def prefixEnd_2786327 : Nat := 4983230072969 + 3 ^ 40 * 2786327 * 2
def baseEnd_2786327 : Nat := 317938891466716714777427

theorem tailTrace_2786327 : CollatzResearch.WordTrace tailWord_2786327 prefixEnd_2786327 317938891466716714777427 := by
  unfold tailWord_2786327
  simp only [CollatzResearch.WordTrace]
  refine ⟨101625694576620620611021235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67750463051080413740680823 101625694576620620611021235)
  ·
    refine ⟨152438541864930930916531853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101625694576620620611021235 152438541864930930916531853)
    ·
      refine ⟨57164453199349099093699445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152438541864930930916531853 57164453199349099093699445)
      ·
        refine ⟨5359167487438978040034323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57164453199349099093699445 5359167487438978040034323)
        ·
          refine ⟨8038751231158467060051485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359167487438978040034323 8038751231158467060051485)
          ·
            refine ⟨3014531711684425147519307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8038751231158467060051485 3014531711684425147519307)
            ·
              refine ⟨4521797567526637721278961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3014531711684425147519307 4521797567526637721278961)
              ·
                refine ⟨3391348175644978290959221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4521797567526637721278961 3391348175644978290959221)
                ·
                  refine ⟨317938891466716714777427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3391348175644978290959221 317938891466716714777427)
                  ·
                    rfl

theorem cell22_2786327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 5].length) (baseStart_2786327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786327 prefixEnd_2786327 := by exact prefixLift 2786327
  have htrace : WordTrace (prefixWord ++ tailWord_2786327) baseStart_2786327 baseEnd_2786327 := by
    simpa [prefixWord, tailWord_2786327, baseEnd_2786327] using wordTrace_append hprefix tailTrace_2786327
  have hstable : (prefixWord ++ tailWord_2786327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786327).length < 2 ^ (prefixWord ++ tailWord_2786327).sum := by decide
  have hdescent : baseEnd_2786327 < baseStart_2786327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786368 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 1, 6]
def baseStart_2786368 : Nat := 118140960795 + 2786368 * 2 ^ 59
def prefixEnd_2786368 : Nat := 4983230072969 + 3 ^ 40 * 2786368 * 2
def baseEnd_2786368 : Nat := 953830709538039704057155

theorem tailTrace_2786368 : CollatzResearch.WordTrace tailWord_2786368 prefixEnd_2786368 953830709538039704057155 := by
  unfold tailWord_2786368
  simp only [CollatzResearch.WordTrace]
  refine ⟨50813594984736042306631879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67751459979648056408842505 50813594984736042306631879)
  ·
    refine ⟨76220392477104063459947819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50813594984736042306631879 76220392477104063459947819)
    ·
      refine ⟨114330588715656095189921729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76220392477104063459947819 114330588715656095189921729)
      ·
        refine ⟨85747941536742071392441297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114330588715656095189921729 85747941536742071392441297)
        ·
          refine ⟨64310956152556553544330973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85747941536742071392441297 64310956152556553544330973)
          ·
            refine ⟨24116608557208707579124115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64310956152556553544330973 24116608557208707579124115)
            ·
              refine ⟨36174912835813061368686173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24116608557208707579124115 36174912835813061368686173)
              ·
                refine ⟨13565592313429898013257315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36174912835813061368686173 13565592313429898013257315)
                ·
                  refine ⟨20348388470144847019885973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13565592313429898013257315 20348388470144847019885973)
                  ·
                    refine ⟨953830709538039704057155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20348388470144847019885973 953830709538039704057155)
                    ·
                      rfl

theorem cell22_2786368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_2786368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786368 prefixEnd_2786368 := by exact prefixLift 2786368
  have htrace : WordTrace (prefixWord ++ tailWord_2786368) baseStart_2786368 baseEnd_2786368 := by
    simpa [prefixWord, tailWord_2786368, baseEnd_2786368] using wordTrace_append hprefix tailTrace_2786368
  have hstable : (prefixWord ++ tailWord_2786368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786368).length < 2 ^ (prefixWord ++ tailWord_2786368).sum := by decide
  have hdescent : baseEnd_2786368 < baseStart_2786368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786374 : List Nat := [6, 1, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2786374 : Nat := 118140960795 + 2786374 * 2 ^ 59
def prefixEnd_2786374 : Nat := 4983230072969 + 3 ^ 40 * 2786374 * 2
def baseEnd_2786374 : Nat := 953832763460657688407137

theorem tailTrace_2786374 : CollatzResearch.WordTrace tailWord_2786374 prefixEnd_2786374 953832763460657688407137 := by
  unfold tailWord_2786374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3175856525232823363686943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67751605871633565091988117 3175856525232823363686943)
  ·
    refine ⟨4763784787849235045530415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3175856525232823363686943 4763784787849235045530415)
    ·
      refine ⟨7145677181773852568295623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4763784787849235045530415 7145677181773852568295623)
      ·
        refine ⟨10718515772660778852443435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7145677181773852568295623 10718515772660778852443435)
        ·
          refine ⟨16077773658991168278665153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10718515772660778852443435 16077773658991168278665153)
          ·
            refine ⟨12058330244243376208998865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16077773658991168278665153 12058330244243376208998865)
            ·
              refine ⟨9043747683182532156749149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12058330244243376208998865 9043747683182532156749149)
              ·
                refine ⟨3391405381193449558780931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9043747683182532156749149 3391405381193449558780931)
                ·
                  refine ⟨5087108071790174338171397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391405381193449558780931 5087108071790174338171397)
                  ·
                    refine ⟨953832763460657688407137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5087108071790174338171397 953832763460657688407137)
                    ·
                      rfl

theorem cell22_2786374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2786374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786374 prefixEnd_2786374 := by exact prefixLift 2786374
  have htrace : WordTrace (prefixWord ++ tailWord_2786374) baseStart_2786374 baseEnd_2786374 := by
    simpa [prefixWord, tailWord_2786374, baseEnd_2786374] using wordTrace_append hprefix tailTrace_2786374
  have hstable : (prefixWord ++ tailWord_2786374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786374).length < 2 ^ (prefixWord ++ tailWord_2786374).sum := by decide
  have hdescent : baseEnd_2786374 < baseStart_2786374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786415 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 5, 3]
def baseStart_2786415 : Nat := 118140960795 + 2786415 * 2 ^ 59
def prefixEnd_2786415 : Nat := 4983230072969 + 3 ^ 40 * 2786415 * 2
def baseEnd_2786415 : Nat := 953846798598547248132011

theorem tailTrace_2786415 : CollatzResearch.WordTrace tailWord_2786415 prefixEnd_2786415 953846798598547248132011 := by
  unfold tailWord_2786415
  simp only [CollatzResearch.WordTrace]
  refine ⟨101628904200301811640224699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67752602800201207760149799 101628904200301811640224699)
  ·
    refine ⟨152443356300452717460337049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101628904200301811640224699 152443356300452717460337049)
    ·
      refine ⟨114332517225339538095252787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152443356300452717460337049 114332517225339538095252787)
      ·
        refine ⟨171498775838009307142879181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114332517225339538095252787 171498775838009307142879181)
        ·
          refine ⟨64312040939253490178579693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171498775838009307142879181 64312040939253490178579693)
          ·
            refine ⟨24117015352220058816967385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64312040939253490178579693 24117015352220058816967385)
            ·
              refine ⟨18087761514165044112725539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24117015352220058816967385 18087761514165044112725539)
              ·
                refine ⟨27131642271247566169088309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18087761514165044112725539 27131642271247566169088309)
                ·
                  refine ⟨2543591462929459328352029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27131642271247566169088309 2543591462929459328352029)
                  ·
                    refine ⟨953846798598547248132011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2543591462929459328352029 953846798598547248132011)
                    ·
                      rfl

theorem cell22_2786415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 3].length) (baseStart_2786415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786415 prefixEnd_2786415 := by exact prefixLift 2786415
  have htrace : WordTrace (prefixWord ++ tailWord_2786415) baseStart_2786415 baseEnd_2786415 := by
    simpa [prefixWord, tailWord_2786415, baseEnd_2786415] using wordTrace_append hprefix tailTrace_2786415
  have hstable : (prefixWord ++ tailWord_2786415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786415).length < 2 ^ (prefixWord ++ tailWord_2786415).sum := by decide
  have hdescent : baseEnd_2786415 < baseStart_2786415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786443 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 3, 7]
def baseStart_2786443 : Nat := 118140960795 + 2786443 * 2 ^ 59
def prefixEnd_2786443 : Nat := 4983230072969 + 3 ^ 40 * 2786443 * 2
def baseEnd_2786443 : Nat := 953856383570764508431925

theorem tailTrace_2786443 : CollatzResearch.WordTrace tailWord_2786443 prefixEnd_2786443 953856383570764508431925 := by
  unfold tailWord_2786443
  simp only [CollatzResearch.WordTrace]
  refine ⟨101629925444200372422243983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67753283629466914948162655 101629925444200372422243983)
  ·
    refine ⟨152444888166300558633365975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101629925444200372422243983 152444888166300558633365975)
    ·
      refine ⟨228667332249450837950048963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152444888166300558633365975 228667332249450837950048963)
      ·
        refine ⟨343000998374176256925073445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228667332249450837950048963 343000998374176256925073445)
        ·
          refine ⟨64312687195158048173451271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 343000998374176256925073445 64312687195158048173451271)
          ·
            refine ⟨96469030792737072260176907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64312687195158048173451271 96469030792737072260176907)
            ·
              refine ⟨144703546189105608390265361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96469030792737072260176907 144703546189105608390265361)
              ·
                refine ⟨108527659641829206292699021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144703546189105608390265361 108527659641829206292699021)
                ·
                  refine ⟨40697872365685952359762133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108527659641829206292699021 40697872365685952359762133)
                  ·
                    refine ⟨953856383570764508431925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40697872365685952359762133 953856383570764508431925)
                    ·
                      rfl

theorem cell22_2786443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_2786443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786443 prefixEnd_2786443 := by exact prefixLift 2786443
  have htrace : WordTrace (prefixWord ++ tailWord_2786443) baseStart_2786443 baseEnd_2786443 := by
    simpa [prefixWord, tailWord_2786443, baseEnd_2786443] using wordTrace_append hprefix tailTrace_2786443
  have hstable : (prefixWord ++ tailWord_2786443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786443).length < 2 ^ (prefixWord ++ tailWord_2786443).sum := by decide
  have hdescent : baseEnd_2786443 < baseStart_2786443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786460 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_2786460 : Nat := 118140960795 + 2786460 * 2 ^ 59
def prefixEnd_2786460 : Nat := 4983230072969 + 3 ^ 40 * 2786460 * 2
def baseEnd_2786460 : Nat := 953862203018182130756873

theorem tailTrace_2786460 : CollatzResearch.WordTrace tailWord_2786460 prefixEnd_2786460 953862203018182130756873 := by
  unfold tailWord_2786460
  simp only [CollatzResearch.WordTrace]
  refine ⟨50815272742569392162806417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67753696990092522883741889 50815272742569392162806417)
  ·
    refine ⟨38111454556927044122104813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50815272742569392162806417 38111454556927044122104813)
    ·
      refine ⟨14291795458847641545789305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38111454556927044122104813 14291795458847641545789305)
      ·
        refine ⟨10718846594135731159341979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14291795458847641545789305 10718846594135731159341979)
        ·
          refine ⟨16078269891203596739012969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10718846594135731159341979 16078269891203596739012969)
          ·
            refine ⟨12058702418402697554259727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16078269891203596739012969 12058702418402697554259727)
            ·
              refine ⟨18088053627604046331389591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12058702418402697554259727 18088053627604046331389591)
              ·
                refine ⟨27132080441406069497084387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18088053627604046331389591 27132080441406069497084387)
                ·
                  refine ⟨40698120662109104245626581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27132080441406069497084387 40698120662109104245626581)
                  ·
                    refine ⟨953862203018182130756873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40698120662109104245626581 953862203018182130756873)
                    ·
                      rfl

theorem cell22_2786460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_2786460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786460 prefixEnd_2786460 := by exact prefixLift 2786460
  have htrace : WordTrace (prefixWord ++ tailWord_2786460) baseStart_2786460 baseEnd_2786460 := by
    simpa [prefixWord, tailWord_2786460, baseEnd_2786460] using wordTrace_append hprefix tailTrace_2786460
  have hstable : (prefixWord ++ tailWord_2786460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786460).length < 2 ^ (prefixWord ++ tailWord_2786460).sum := by decide
  have hdescent : baseEnd_2786460 < baseStart_2786460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786541 : List Nat := [1, 5, 1, 2, 2, 3, 1, 3, 4]
def baseStart_2786541 : Nat := 118140960795 + 2786541 * 2 ^ 59
def prefixEnd_2786541 : Nat := 4983230072969 + 3 ^ 40 * 2786541 * 2
def baseEnd_2786541 : Nat := 317963310324508306493875

theorem tailTrace_2786541 : CollatzResearch.WordTrace tailWord_2786541 prefixEnd_2786541 317963310324508306493875 := by
  unfold tailWord_2786541
  simp only [CollatzResearch.WordTrace]
  refine ⟨101633499797845335159311477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67755666531896890106207651 101633499797845335159311477)
  ·
    refine ⟨9528140606048000171185451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101633499797845335159311477 9528140606048000171185451)
    ·
      refine ⟨14292210909072000256778177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9528140606048000171185451 14292210909072000256778177)
      ·
        refine ⟨10719158181804000192583633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14292210909072000256778177 10719158181804000192583633)
        ·
          refine ⟨8039368636353000144437725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10719158181804000192583633 8039368636353000144437725)
          ·
            refine ⟨3014763238632375054164147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8039368636353000144437725 3014763238632375054164147)
            ·
              refine ⟨4522144857948562581246221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3014763238632375054164147 4522144857948562581246221)
              ·
                refine ⟨1695804321730710967967333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4522144857948562581246221 1695804321730710967967333)
                ·
                  refine ⟨317963310324508306493875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1695804321730710967967333 317963310324508306493875)
                  ·
                    rfl

theorem cell22_2786541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_2786541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786541 prefixEnd_2786541 := by exact prefixLift 2786541
  have htrace : WordTrace (prefixWord ++ tailWord_2786541) baseStart_2786541 baseEnd_2786541 := by
    simpa [prefixWord, tailWord_2786541, baseEnd_2786541] using wordTrace_append hprefix tailTrace_2786541
  have hstable : (prefixWord ++ tailWord_2786541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786541).length < 2 ^ (prefixWord ++ tailWord_2786541).sum := by decide
  have hdescent : baseEnd_2786541 < baseStart_2786541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786565 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_2786565 : Nat := 118140960795 + 2786565 * 2 ^ 59
def prefixEnd_2786565 : Nat := 4983230072969 + 3 ^ 40 * 2786565 * 2
def baseEnd_2786565 : Nat := 953898146663996856881551

theorem tailTrace_2786565 : CollatzResearch.WordTrace tailWord_2786565 prefixEnd_2786565 953898146663996856881551 := by
  unfold tailWord_2786565
  simp only [CollatzResearch.WordTrace]
  refine ⟨101634375149758387258185149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67756250099838924838790099 101634375149758387258185149)
  ·
    refine ⟨38112890681159395221819431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101634375149758387258185149 38112890681159395221819431)
    ·
      refine ⟨57169336021739092832729147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38112890681159395221819431 57169336021739092832729147)
      ·
        refine ⟨85754004032608639249093721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57169336021739092832729147 85754004032608639249093721)
        ·
          refine ⟨64315503024456479436820291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85754004032608639249093721 64315503024456479436820291)
          ·
            refine ⟨96473254536684719155230437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64315503024456479436820291 96473254536684719155230437)
            ·
              refine ⟨18088735225628384841605707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96473254536684719155230437 18088735225628384841605707)
              ·
                refine ⟨27133102838442577262408561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18088735225628384841605707 27133102838442577262408561)
                ·
                  refine ⟨20349827128831932946806421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27133102838442577262408561 20349827128831932946806421)
                  ·
                    refine ⟨953898146663996856881551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20349827128831932946806421 953898146663996856881551)
                    ·
                      rfl

theorem cell22_2786565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_2786565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786565 prefixEnd_2786565 := by exact prefixLift 2786565
  have htrace : WordTrace (prefixWord ++ tailWord_2786565) baseStart_2786565 baseEnd_2786565 := by
    simpa [prefixWord, tailWord_2786565, baseEnd_2786565] using wordTrace_append hprefix tailTrace_2786565
  have hstable : (prefixWord ++ tailWord_2786565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786565).length < 2 ^ (prefixWord ++ tailWord_2786565).sum := by decide
  have hdescent : baseEnd_2786565 < baseStart_2786565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786644 : List Nat := [2, 4, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_2786644 : Nat := 118140960795 + 2786644 * 2 ^ 59
def prefixEnd_2786644 : Nat := 4983230072969 + 3 ^ 40 * 2786644 * 2
def baseEnd_2786644 : Nat := 953925189978466984156309

theorem tailTrace_2786644 : CollatzResearch.WordTrace tailWord_2786644 prefixEnd_2786644 953925189978466984156309 := by
  unfold tailWord_2786644
  simp only [CollatzResearch.WordTrace]
  refine ⟨50818628258236091875155493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67758171010981455833540657 50818628258236091875155493)
  ·
    refine ⟨9528492798419267226591655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50818628258236091875155493 9528492798419267226591655)
    ·
      refine ⟨14292739197628900839887483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9528492798419267226591655 14292739197628900839887483)
      ·
        refine ⟨21439108796443351259831225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14292739197628900839887483 21439108796443351259831225)
        ·
          refine ⟨16079331597332513444873419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21439108796443351259831225 16079331597332513444873419)
          ·
            refine ⟨24118997395998770167310129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16079331597332513444873419 24118997395998770167310129)
            ·
              refine ⟨18089248046999077625482597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24118997395998770167310129 18089248046999077625482597)
              ·
                refine ⟨3391734008812327054777987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18089248046999077625482597 3391734008812327054777987)
                ·
                  refine ⟨5087601013218490582166981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391734008812327054777987 5087601013218490582166981)
                  ·
                    refine ⟨953925189978466984156309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5087601013218490582166981 953925189978466984156309)
                    ·
                      rfl

theorem cell22_2786644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_2786644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786644 prefixEnd_2786644 := by exact prefixLift 2786644
  have htrace : WordTrace (prefixWord ++ tailWord_2786644) baseStart_2786644 baseEnd_2786644 := by
    simpa [prefixWord, tailWord_2786644, baseEnd_2786644] using wordTrace_append hprefix tailTrace_2786644
  have hstable : (prefixWord ++ tailWord_2786644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786644).length < 2 ^ (prefixWord ++ tailWord_2786644).sum := by decide
  have hdescent : baseEnd_2786644 < baseStart_2786644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786659 : List Nat := [1, 1, 1, 5, 2, 2, 1, 5, 4]
def baseStart_2786659 : Nat := 118140960795 + 2786659 * 2 ^ 59
def prefixEnd_2786659 : Nat := 4983230072969 + 3 ^ 40 * 2786659 * 2
def baseEnd_2786659 : Nat := 317976774928337315010421

theorem tailTrace_2786659 : CollatzResearch.WordTrace tailWord_2786659 prefixEnd_2786659 317976774928337315010421 := by
  unfold tailWord_2786659
  simp only [CollatzResearch.WordTrace]
  refine ⟨101637803611417841312107031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67758535740945227541404687 101637803611417841312107031)
  ·
    refine ⟨152456705417126761968160547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101637803611417841312107031 152456705417126761968160547)
    ·
      refine ⟨228685058125690142952240821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152456705417126761968160547 228685058125690142952240821)
      ·
        refine ⟨21439224199283450901772577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228685058125690142952240821 21439224199283450901772577)
        ·
          refine ⟨16079418149462588176329433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21439224199283450901772577 16079418149462588176329433)
          ·
            refine ⟨12059563612096941132247075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16079418149462588176329433 12059563612096941132247075)
            ·
              refine ⟨18089345418145411698370613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12059563612096941132247075 18089345418145411698370613)
              ·
                refine ⟨1695876132951132346722245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18089345418145411698370613 1695876132951132346722245)
                ·
                  refine ⟨317976774928337315010421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1695876132951132346722245 317976774928337315010421)
                  ·
                    rfl

theorem cell22_2786659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 4].length) (baseStart_2786659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786659 prefixEnd_2786659 := by exact prefixLift 2786659
  have htrace : WordTrace (prefixWord ++ tailWord_2786659) baseStart_2786659 baseEnd_2786659 := by
    simpa [prefixWord, tailWord_2786659, baseEnd_2786659] using wordTrace_append hprefix tailTrace_2786659
  have hstable : (prefixWord ++ tailWord_2786659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786659).length < 2 ^ (prefixWord ++ tailWord_2786659).sum := by decide
  have hdescent : baseEnd_2786659 < baseStart_2786659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786672 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 4, 4]
def baseStart_2786672 : Nat := 118140960795 + 2786672 * 2 ^ 59
def prefixEnd_2786672 : Nat := 4983230072969 + 3 ^ 40 * 2786672 * 2
def baseEnd_2786672 : Nat := 953934774950684244456223

theorem tailTrace_2786672 : CollatzResearch.WordTrace tailWord_2786672 prefixEnd_2786672 953934774950684244456223 := by
  unfold tailWord_2786672
  simp only [CollatzResearch.WordTrace]
  refine ⟨50819138880185372266165135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67758851840247163021553513 50819138880185372266165135)
  ·
    refine ⟨76228708320278058399247703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50819138880185372266165135 76228708320278058399247703)
    ·
      refine ⟨114343062480417087598871555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76228708320278058399247703 114343062480417087598871555)
      ·
        refine ⟨171514593720625631398307333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114343062480417087598871555 171514593720625631398307333)
        ·
          refine ⟨32158986322617305887182625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171514593720625631398307333 32158986322617305887182625)
          ·
            refine ⟨24119239741962979415386969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32158986322617305887182625 24119239741962979415386969)
            ·
              refine ⟨18089429806472234561540227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24119239741962979415386969 18089429806472234561540227)
              ·
                refine ⟨27134144709708351842310341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18089429806472234561540227 27134144709708351842310341)
                ·
                  refine ⟨5087652133070315970433189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27134144709708351842310341 5087652133070315970433189)
                  ·
                    refine ⟨953934774950684244456223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5087652133070315970433189 953934774950684244456223)
                    ·
                      rfl

theorem cell22_2786672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_2786672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786672 prefixEnd_2786672 := by exact prefixLift 2786672
  have htrace : WordTrace (prefixWord ++ tailWord_2786672) baseStart_2786672 baseEnd_2786672 := by
    simpa [prefixWord, tailWord_2786672, baseEnd_2786672] using wordTrace_append hprefix tailTrace_2786672
  have hstable : (prefixWord ++ tailWord_2786672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786672).length < 2 ^ (prefixWord ++ tailWord_2786672).sum := by decide
  have hdescent : baseEnd_2786672 < baseStart_2786672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786674 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_2786674 : Nat := 118140960795 + 2786674 * 2 ^ 59
def prefixEnd_2786674 : Nat := 4983230072969 + 3 ^ 40 * 2786674 * 2
def baseEnd_2786674 : Nat := 953935459591556905906217

theorem tailTrace_2786674 : CollatzResearch.WordTrace tailWord_2786674 prefixEnd_2786674 953935459591556905906217 := by
  unfold tailWord_2786674
  simp only [CollatzResearch.WordTrace]
  refine ⟨25409587676590874718475769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67758900470908999249268717 25409587676590874718475769)
  ·
    refine ⟨19057190757443156038856827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25409587676590874718475769 19057190757443156038856827)
    ·
      refine ⟨28585786136164734058285241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19057190757443156038856827 28585786136164734058285241)
      ·
        refine ⟨21439339602123550543713931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28585786136164734058285241 21439339602123550543713931)
        ·
          refine ⟨32159009403185325815570897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21439339602123550543713931 32159009403185325815570897)
          ·
            refine ⟨24119257052388994361678173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32159009403185325815570897 24119257052388994361678173)
            ·
              refine ⟨9044721394645872885629315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24119257052388994361678173 9044721394645872885629315)
              ·
                refine ⟨13567082091968809328443973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9044721394645872885629315 13567082091968809328443973)
                ·
                  refine ⟨2543827892244151749083245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13567082091968809328443973 2543827892244151749083245)
                  ·
                    refine ⟨953935459591556905906217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2543827892244151749083245 953935459591556905906217)
                    ·
                      rfl

theorem cell22_2786674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_2786674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786674 prefixEnd_2786674 := by exact prefixLift 2786674
  have htrace : WordTrace (prefixWord ++ tailWord_2786674) baseStart_2786674 baseEnd_2786674 := by
    simpa [prefixWord, tailWord_2786674, baseEnd_2786674] using wordTrace_append hprefix tailTrace_2786674
  have hstable : (prefixWord ++ tailWord_2786674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786674).length < 2 ^ (prefixWord ++ tailWord_2786674).sum := by decide
  have hdescent : baseEnd_2786674 < baseStart_2786674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786732 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 7]
def baseStart_2786732 : Nat := 118140960795 + 2786732 * 2 ^ 59
def prefixEnd_2786732 : Nat := 4983230072969 + 3 ^ 40 * 2786732 * 2
def baseEnd_2786732 : Nat := 317985104725621362652013

theorem tailTrace_2786732 : CollatzResearch.WordTrace tailWord_2786732 prefixEnd_2786732 317985104725621362652013 := by
  unfold tailWord_2786732
  simp only [CollatzResearch.WordTrace]
  refine ⟨50820233070076687389757225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67760310760102249853009633 50820233070076687389757225)
  ·
    refine ⟨38115174802557515542317919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50820233070076687389757225 38115174802557515542317919)
    ·
      refine ⟨57172762203836273313476879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38115174802557515542317919 57172762203836273313476879)
      ·
        refine ⟨85759143305754409970215319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57172762203836273313476879 85759143305754409970215319)
        ·
          refine ⟨128638714958631614955322979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85759143305754409970215319 128638714958631614955322979)
          ·
            refine ⟨192958072437947422432984469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128638714958631614955322979 192958072437947422432984469)
            ·
              refine ⟨9044909645528785426546147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 192958072437947422432984469 9044909645528785426546147)
              ·
                refine ⟨13567364468293178139819221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9044909645528785426546147 13567364468293178139819221)
                ·
                  refine ⟨317985104725621362652013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13567364468293178139819221 317985104725621362652013)
                  ·
                    rfl

theorem cell22_2786732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_2786732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786732 prefixEnd_2786732 := by exact prefixLift 2786732
  have htrace : WordTrace (prefixWord ++ tailWord_2786732) baseStart_2786732 baseEnd_2786732 := by
    simpa [prefixWord, tailWord_2786732, baseEnd_2786732] using wordTrace_append hprefix tailTrace_2786732
  have hstable : (prefixWord ++ tailWord_2786732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786732).length < 2 ^ (prefixWord ++ tailWord_2786732).sum := by decide
  have hdescent : baseEnd_2786732 < baseStart_2786732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786749 : List Nat := [1, 4, 1, 2, 2, 1, 3, 3, 5]
def baseStart_2786749 : Nat := 118140960795 + 2786749 * 2 ^ 59
def prefixEnd_2786749 : Nat := 4983230072969 + 3 ^ 40 * 2786749 * 2
def baseEnd_2786749 : Nat := 317987044541427236760329

theorem tailTrace_2786749 : CollatzResearch.WordTrace tailWord_2786749 prefixEnd_2786749 317987044541427236760329 := by
  unfold tailWord_2786749
  simp only [CollatzResearch.WordTrace]
  refine ⟨101641086181091786682883301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67760724120727857788588867 101641086181091786682883301)
  ·
    refine ⟨19057703658954710003040619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101641086181091786682883301 19057703658954710003040619)
    ·
      refine ⟨28586555488432065004560929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19057703658954710003040619 28586555488432065004560929)
      ·
        refine ⟨21439916616324048753420697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28586555488432065004560929 21439916616324048753420697)
        ·
          refine ⟨16079937462243036565065523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21439916616324048753420697 16079937462243036565065523)
          ·
            refine ⟨24119906193364554847598285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16079937462243036565065523 24119906193364554847598285)
            ·
              refine ⟨9044964822511708067849357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24119906193364554847598285 9044964822511708067849357)
              ·
                refine ⟨3391861808441890525443509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9044964822511708067849357 3391861808441890525443509)
                ·
                  refine ⟨317987044541427236760329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3391861808441890525443509 317987044541427236760329)
                  ·
                    rfl

theorem cell22_2786749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_2786749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786749 prefixEnd_2786749 := by exact prefixLift 2786749
  have htrace : WordTrace (prefixWord ++ tailWord_2786749) baseStart_2786749 baseEnd_2786749 := by
    simpa [prefixWord, tailWord_2786749, baseEnd_2786749] using wordTrace_append hprefix tailTrace_2786749
  have hstable : (prefixWord ++ tailWord_2786749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786749).length < 2 ^ (prefixWord ++ tailWord_2786749).sum := by decide
  have hdescent : baseEnd_2786749 < baseStart_2786749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786809 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 6, 3]
def baseStart_2786809 : Nat := 118140960795 + 2786809 * 2 ^ 59
def prefixEnd_2786809 : Nat := 4983230072969 + 3 ^ 40 * 2786809 * 2
def baseEnd_2786809 : Nat := 953981672850461553780803

theorem tailTrace_2786809 : CollatzResearch.WordTrace tailWord_2786809 prefixEnd_2786809 953981672850461553780803 := by
  unfold tailWord_2786809
  simp only [CollatzResearch.WordTrace]
  refine ⟨101643274560874416930067481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67762183040582944620044987 101643274560874416930067481)
  ·
    refine ⟨76232455920655812697550611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101643274560874416930067481 76232455920655812697550611)
    ·
      refine ⟨114348683880983719046325917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76232455920655812697550611 114348683880983719046325917)
      ·
        refine ⟨42880756455368894642372219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114348683880983719046325917 42880756455368894642372219)
        ·
          refine ⟨64321134683053341963558329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42880756455368894642372219 64321134683053341963558329)
          ·
            refine ⟨48240851012290006472668747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64321134683053341963558329 48240851012290006472668747)
            ·
              refine ⟨72361276518435009709003121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48240851012290006472668747 72361276518435009709003121)
              ·
                refine ⟨54270957388826257281752341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72361276518435009709003121 54270957388826257281752341)
                ·
                  refine ⟨2543951127601230810082141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54270957388826257281752341 2543951127601230810082141)
                  ·
                    refine ⟨953981672850461553780803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2543951127601230810082141 953981672850461553780803)
                    ·
                      rfl

theorem cell22_2786809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 3].length) (baseStart_2786809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786809 prefixEnd_2786809 := by exact prefixLift 2786809
  have htrace : WordTrace (prefixWord ++ tailWord_2786809) baseStart_2786809 baseEnd_2786809 := by
    simpa [prefixWord, tailWord_2786809, baseEnd_2786809] using wordTrace_append hprefix tailTrace_2786809
  have hstable : (prefixWord ++ tailWord_2786809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786809).length < 2 ^ (prefixWord ++ tailWord_2786809).sum := by decide
  have hdescent : baseEnd_2786809 < baseStart_2786809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786828 : List Nat := [2, 2, 1, 2, 5, 1, 2, 3, 4]
def baseStart_2786828 : Nat := 118140960795 + 2786828 * 2 ^ 59
def prefixEnd_2786828 : Nat := 4983230072969 + 3 ^ 40 * 2786828 * 2
def baseEnd_2786828 : Nat := 317996058979583945851915

theorem tailTrace_2786828 : CollatzResearch.WordTrace tailWord_2786828 prefixEnd_2786828 317996058979583945851915 := by
  unfold tailWord_2786828
  simp only [CollatzResearch.WordTrace]
  refine ⟨50821983773902791587504569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67762645031870388783339425 50821983773902791587504569)
  ·
    refine ⟨38116487830427093690628427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50821983773902791587504569 38116487830427093690628427)
    ·
      refine ⟨57174731745640640535942641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38116487830427093690628427 57174731745640640535942641)
      ·
        refine ⟨42881048809230480401956981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57174731745640640535942641 42881048809230480401956981)
        ·
          refine ⟨4020098325865357537683467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42881048809230480401956981 4020098325865357537683467)
          ·
            refine ⟨6030147488798036306525201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020098325865357537683467 6030147488798036306525201)
            ·
              refine ⟨4522610616598527229893901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6030147488798036306525201 4522610616598527229893901)
              ·
                refine ⟨1695978981224447711210213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4522610616598527229893901 1695978981224447711210213)
                ·
                  refine ⟨317996058979583945851915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1695978981224447711210213 317996058979583945851915)
                  ·
                    rfl

theorem cell22_2786828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_2786828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786828 prefixEnd_2786828 := by exact prefixLift 2786828
  have htrace : WordTrace (prefixWord ++ tailWord_2786828) baseStart_2786828 baseEnd_2786828 := by
    simpa [prefixWord, tailWord_2786828, baseEnd_2786828] using wordTrace_append hprefix tailTrace_2786828
  have hstable : (prefixWord ++ tailWord_2786828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786828).length < 2 ^ (prefixWord ++ tailWord_2786828).sum := by decide
  have hdescent : baseEnd_2786828 < baseStart_2786828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786830 : List Nat := [4, 1, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_2786830 : Nat := 118140960795 + 2786830 * 2 ^ 59
def prefixEnd_2786830 : Nat := 4983230072969 + 3 ^ 40 * 2786830 * 2
def baseEnd_2786830 : Nat := 953988861579624499005739

theorem tailTrace_2786830 : CollatzResearch.WordTrace tailWord_2786830 prefixEnd_2786830 953988861579624499005739 := by
  unfold tailWord_2786830
  simp only [CollatzResearch.WordTrace]
  refine ⟨12705505061724792189572743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67762693662532225011054629 12705505061724792189572743)
  ·
    refine ⟨19058257592587188284359115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12705505061724792189572743 19058257592587188284359115)
    ·
      refine ⟨28587386388880782426538673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19058257592587188284359115 28587386388880782426538673)
      ·
        refine ⟨21440539791660586819904005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28587386388880782426538673 21440539791660586819904005)
        ·
          refine ⟨4020101210936360028732001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21440539791660586819904005 4020101210936360028732001)
          ·
            refine ⟨3015075908202270021549001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4020101210936360028732001 3015075908202270021549001)
            ·
              refine ⟨2261306931151702516161751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3015075908202270021549001 2261306931151702516161751)
              ·
                refine ⟨3391960396727553774242627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261306931151702516161751 3391960396727553774242627)
                ·
                  refine ⟨5087940595091330661363941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391960396727553774242627 5087940595091330661363941)
                  ·
                    refine ⟨953988861579624499005739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5087940595091330661363941 953988861579624499005739)
                    ·
                      rfl

theorem cell22_2786830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_2786830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786830 prefixEnd_2786830 := by exact prefixLift 2786830
  have htrace : WordTrace (prefixWord ++ tailWord_2786830) baseStart_2786830 baseEnd_2786830 := by
    simpa [prefixWord, tailWord_2786830, baseEnd_2786830] using wordTrace_append hprefix tailTrace_2786830
  have hstable : (prefixWord ++ tailWord_2786830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786830).length < 2 ^ (prefixWord ++ tailWord_2786830).sum := by decide
  have hdescent : baseEnd_2786830 < baseStart_2786830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786871 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 3, 3]
def baseStart_2786871 : Nat := 118140960795 + 2786871 * 2 ^ 59
def prefixEnd_2786871 : Nat := 4983230072969 + 3 ^ 40 * 2786871 * 2
def baseEnd_2786871 : Nat := 954002896717514058730613

theorem tailTrace_2786871 : CollatzResearch.WordTrace tailWord_2786871 prefixEnd_2786871 954002896717514058730613 := by
  unfold tailWord_2786871
  simp only [CollatzResearch.WordTrace]
  refine ⟨101645535886649801518824467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67763690591099867679216311 101645535886649801518824467)
  ·
    refine ⟨152468303829974702278236701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101645535886649801518824467 152468303829974702278236701)
    ·
      refine ⟨57175613936240513354338763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152468303829974702278236701 57175613936240513354338763)
      ·
        refine ⟨85763420904360770031508145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57175613936240513354338763 85763420904360770031508145)
        ·
          refine ⟨64322565678270577523631109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85763420904360770031508145 64322565678270577523631109)
          ·
            refine ⟨12060481064675733285680833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64322565678270577523631109 12060481064675733285680833)
            ·
              refine ⟨9045360798506799964260625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12060481064675733285680833 9045360798506799964260625)
              ·
                refine ⟨6784020598880099973195469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9045360798506799964260625 6784020598880099973195469)
                ·
                  refine ⟨2544007724580037489948301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6784020598880099973195469 2544007724580037489948301)
                  ·
                    refine ⟨954002896717514058730613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2544007724580037489948301 954002896717514058730613)
                    ·
                      rfl

theorem cell22_2786871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_2786871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786871 prefixEnd_2786871 := by exact prefixLift 2786871
  have htrace : WordTrace (prefixWord ++ tailWord_2786871) baseStart_2786871 baseEnd_2786871 := by
    simpa [prefixWord, tailWord_2786871, baseEnd_2786871] using wordTrace_append hprefix tailTrace_2786871
  have hstable : (prefixWord ++ tailWord_2786871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786871).length < 2 ^ (prefixWord ++ tailWord_2786871).sum := by decide
  have hdescent : baseEnd_2786871 < baseStart_2786871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786929 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 6]
def baseStart_2786929 : Nat := 118140960795 + 2786929 * 2 ^ 59
def prefixEnd_2786929 : Nat := 4983230072969 + 3 ^ 40 * 2786929 * 2
def baseEnd_2786929 : Nat := 318007583767607080260145

theorem tailTrace_2786929 : CollatzResearch.WordTrace tailWord_2786929 prefixEnd_2786929 318007583767607080260145 := by
  unfold tailWord_2786929
  simp only [CollatzResearch.WordTrace]
  refine ⟨101647651320439677424435841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67765100880293118282957227 101647651320439677424435841)
  ·
    refine ⟨76235738490329758068326881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101647651320439677424435841 76235738490329758068326881)
    ·
      refine ⟨57176803867747318551245161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76235738490329758068326881 57176803867747318551245161)
      ·
        refine ⟨42882602900810488913433871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57176803867747318551245161 42882602900810488913433871)
        ·
          refine ⟨64323904351215733370150807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42882602900810488913433871 64323904351215733370150807)
          ·
            refine ⟨96485856526823600055226211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64323904351215733370150807 96485856526823600055226211)
            ·
              refine ⟨144728784790235400082839317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96485856526823600055226211 144728784790235400082839317)
              ·
                refine ⟨6784161787042284378883093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144728784790235400082839317 6784161787042284378883093)
                ·
                  refine ⟨318007583767607080260145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6784161787042284378883093 318007583767607080260145)
                  ·
                    rfl

theorem cell22_2786929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_2786929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786929 prefixEnd_2786929 := by exact prefixLift 2786929
  have htrace : WordTrace (prefixWord ++ tailWord_2786929) baseStart_2786929 baseEnd_2786929 := by
    simpa [prefixWord, tailWord_2786929, baseEnd_2786929] using wordTrace_append hprefix tailTrace_2786929
  have hstable : (prefixWord ++ tailWord_2786929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786929).length < 2 ^ (prefixWord ++ tailWord_2786929).sum := by decide
  have hdescent : baseEnd_2786929 < baseStart_2786929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786991 : List Nat := [1, 1, 2, 1, 2, 4, 5, 6]
def baseStart_2786991 : Nat := 118140960795 + 2786991 * 2 ^ 59
def prefixEnd_2786991 : Nat := 4983230072969 + 3 ^ 40 * 2786991 * 2
def baseEnd_2786991 : Nat := 106004886129985971747805

theorem tailTrace_2786991 : CollatzResearch.WordTrace tailWord_2786991 prefixEnd_2786991 106004886129985971747805 := by
  unfold tailWord_2786991
  simp only [CollatzResearch.WordTrace]
  refine ⟨101649912646215062013192827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67766608430810041342128551 101649912646215062013192827)
  ·
    refine ⟨152474868969322593019789241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101649912646215062013192827 152474868969322593019789241)
    ·
      refine ⟨114356151726991944764841931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152474868969322593019789241 114356151726991944764841931)
      ·
        refine ⟨171534227590487917147262897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114356151726991944764841931 171534227590487917147262897)
        ·
          refine ⟨128650670692865937860447173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171534227590487917147262897 128650670692865937860447173)
          ·
            refine ⟨24122000754912363348833845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128650670692865937860447173 24122000754912363348833845)
            ·
              refine ⟨2261437570773034063953173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24122000754912363348833845 2261437570773034063953173)
              ·
                refine ⟨106004886129985971747805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2261437570773034063953173 106004886129985971747805)
                ·
                  rfl

theorem cell22_2786991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 6].length) (baseStart_2786991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2786991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2786991 prefixEnd_2786991 := by exact prefixLift 2786991
  have htrace : WordTrace (prefixWord ++ tailWord_2786991) baseStart_2786991 baseEnd_2786991 := by
    simpa [prefixWord, tailWord_2786991, baseEnd_2786991] using wordTrace_append hprefix tailTrace_2786991
  have hstable : (prefixWord ++ tailWord_2786991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786991).length < 2 ^ (prefixWord ++ tailWord_2786991).sum := by decide
  have hdescent : baseEnd_2786991 < baseStart_2786991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787057 : List Nat := [1, 2, 2, 2, 2, 5, 1, 3, 1, 3]
def baseStart_2787057 : Nat := 118140960795 + 2787057 * 2 ^ 59
def prefixEnd_2787057 : Nat := 4983230072969 + 3 ^ 40 * 2787057 * 2
def baseEnd_2787057 : Nat := 954066568318671573580043

theorem tailTrace_2787057 : CollatzResearch.WordTrace tailWord_2787057 prefixEnd_2787057 954066568318671573580043 := by
  unfold tailWord_2787057
  simp only [CollatzResearch.WordTrace]
  refine ⟨101652319863975955285095425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67768213242650636856730283 101652319863975955285095425)
  ·
    refine ⟨76239239897981966463821569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101652319863975955285095425 76239239897981966463821569)
    ·
      refine ⟨57179429923486474847866177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76239239897981966463821569 57179429923486474847866177)
      ·
        refine ⟨42884572442614856135899633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57179429923486474847866177 42884572442614856135899633)
        ·
          refine ⟨32163429331961142101924725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42884572442614856135899633 32163429331961142101924725)
          ·
            refine ⟨3015321499871357072055443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32163429331961142101924725 3015321499871357072055443)
            ·
              refine ⟨4522982249807035608083165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015321499871357072055443 4522982249807035608083165)
              ·
                refine ⟨1696118343677638353031187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4522982249807035608083165 1696118343677638353031187)
                ·
                  refine ⟨2544177515516457529546781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696118343677638353031187 2544177515516457529546781)
                  ·
                    refine ⟨954066568318671573580043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2544177515516457529546781 954066568318671573580043)
                    ·
                      rfl

theorem cell22_2787057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_2787057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787057 prefixEnd_2787057 := by exact prefixLift 2787057
  have htrace : WordTrace (prefixWord ++ tailWord_2787057) baseStart_2787057 baseEnd_2787057 := by
    simpa [prefixWord, tailWord_2787057, baseEnd_2787057] using wordTrace_append hprefix tailTrace_2787057
  have hstable : (prefixWord ++ tailWord_2787057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787057).length < 2 ^ (prefixWord ++ tailWord_2787057).sum := by decide
  have hdescent : baseEnd_2787057 < baseStart_2787057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787066 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_2787066 : Nat := 118140960795 + 2787066 * 2 ^ 59
def prefixEnd_2787066 : Nat := 4983230072969 + 3 ^ 40 * 2787066 * 2
def baseEnd_2787066 : Nat := 954069649202598550105015

theorem tailTrace_2787066 : CollatzResearch.WordTrace tailWord_2787066 prefixEnd_2787066 954069649202598550105015 := by
  unfold tailWord_2787066
  simp only [CollatzResearch.WordTrace]
  refine ⟨25413162030235837455543263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67768432080628899881448701 25413162030235837455543263)
  ·
    refine ⟨38119743045353756183314895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25413162030235837455543263 38119743045353756183314895)
    ·
      refine ⟨57179614568030634274972343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38119743045353756183314895 57179614568030634274972343)
      ·
        refine ⟨85769421852045951412458515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57179614568030634274972343 85769421852045951412458515)
        ·
          refine ⟨128654132778068927118687773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85769421852045951412458515 128654132778068927118687773)
          ·
            refine ⟨48245299791775847669507915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128654132778068927118687773 48245299791775847669507915)
            ·
              refine ⟨72367949687663771504261873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48245299791775847669507915 72367949687663771504261873)
              ·
                refine ⟨54275962265747828628196405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72367949687663771504261873 54275962265747828628196405)
                ·
                  refine ⟨5088371462413858933893413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54275962265747828628196405 5088371462413858933893413)
                  ·
                    refine ⟨954069649202598550105015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5088371462413858933893413 954069649202598550105015)
                    ·
                      rfl

theorem cell22_2787066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_2787066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787066 prefixEnd_2787066 := by exact prefixLift 2787066
  have htrace : WordTrace (prefixWord ++ tailWord_2787066) baseStart_2787066 baseEnd_2787066 := by
    simpa [prefixWord, tailWord_2787066, baseEnd_2787066] using wordTrace_append hprefix tailTrace_2787066
  have hstable : (prefixWord ++ tailWord_2787066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787066).length < 2 ^ (prefixWord ++ tailWord_2787066).sum := by decide
  have hdescent : baseEnd_2787066 < baseStart_2787066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787074 : List Nat := [3, 4, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_2787074 : Nat := 118140960795 + 2787074 * 2 ^ 59
def prefixEnd_2787074 : Nat := 4983230072969 + 3 ^ 40 * 2787074 * 2
def baseEnd_2787074 : Nat := 954072387766089195904991

theorem tailTrace_2787074 : CollatzResearch.WordTrace tailWord_2787074 prefixEnd_2787074 954072387766089195904991 := by
  unfold tailWord_2787074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25413234976228591797116069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67768626603276244792309517 25413234976228591797116069)
  ·
    refine ⟨4764981558042860961959263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25413234976228591797116069 4764981558042860961959263)
    ·
      refine ⟨7147472337064291442938895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4764981558042860961959263 7147472337064291442938895)
      ·
        refine ⟨10721208505596437164408343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7147472337064291442938895 10721208505596437164408343)
        ·
          refine ⟨16081812758394655746612515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10721208505596437164408343 16081812758394655746612515)
          ·
            refine ⟨24122719137591983619918773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16081812758394655746612515 24122719137591983619918773)
            ·
              refine ⟨2261504919149248464367385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24122719137591983619918773 2261504919149248464367385)
              ·
                refine ⟨1696128689361936348275539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2261504919149248464367385 1696128689361936348275539)
                ·
                  refine ⟨2544193034042904522413309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696128689361936348275539 2544193034042904522413309)
                  ·
                    refine ⟨954072387766089195904991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2544193034042904522413309 954072387766089195904991)
                    ·
                      rfl

theorem cell22_2787074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_2787074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787074 prefixEnd_2787074 := by exact prefixLift 2787074
  have htrace : WordTrace (prefixWord ++ tailWord_2787074) baseStart_2787074 baseEnd_2787074 := by
    simpa [prefixWord, tailWord_2787074, baseEnd_2787074] using wordTrace_append hprefix tailTrace_2787074
  have hstable : (prefixWord ++ tailWord_2787074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787074).length < 2 ^ (prefixWord ++ tailWord_2787074).sum := by decide
  have hdescent : baseEnd_2787074 < baseStart_2787074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787128 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 2, 4]
def baseStart_2787128 : Nat := 118140960795 + 2787128 * 2 ^ 59
def prefixEnd_2787128 : Nat := 4983230072969 + 3 ^ 40 * 2787128 * 2
def baseEnd_2787128 : Nat := 954090873069651055054825

theorem tailTrace_2787128 : CollatzResearch.WordTrace tailWord_2787128 prefixEnd_2787128 954090873069651055054825 := by
  unfold tailWord_2787128
  simp only [CollatzResearch.WordTrace]
  refine ⟨50827454723359367205465019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67769939631145822940620025 50827454723359367205465019)
  ·
    refine ⟨76241182085039050808197529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50827454723359367205465019 76241182085039050808197529)
    ·
      refine ⟨57180886563779288106148147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76241182085039050808197529 57180886563779288106148147)
      ·
        refine ⟨85771329845668932159222221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57180886563779288106148147 85771329845668932159222221)
        ·
          refine ⟨32164248692125849559708333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85771329845668932159222221 32164248692125849559708333)
          ·
            refine ⟨12061593259547193584890625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32164248692125849559708333 12061593259547193584890625)
            ·
              refine ⟨9046194944660395188667969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12061593259547193584890625 9046194944660395188667969)
              ·
                refine ⟨6784646208495296391500977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9046194944660395188667969 6784646208495296391500977)
                ·
                  refine ⟨5088484656371472293625733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6784646208495296391500977 5088484656371472293625733)
                  ·
                    refine ⟨954090873069651055054825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5088484656371472293625733 954090873069651055054825)
                    ·
                      rfl

theorem cell22_2787128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_2787128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787128 prefixEnd_2787128 := by exact prefixLift 2787128
  have htrace : WordTrace (prefixWord ++ tailWord_2787128) baseStart_2787128 baseEnd_2787128 := by
    simpa [prefixWord, tailWord_2787128, baseEnd_2787128] using wordTrace_append hprefix tailTrace_2787128
  have hstable : (prefixWord ++ tailWord_2787128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787128).length < 2 ^ (prefixWord ++ tailWord_2787128).sum := by decide
  have hdescent : baseEnd_2787128 < baseStart_2787128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787130 : List Nat := [3, 1, 1, 1, 5, 1, 1, 4, 2, 3]
def baseStart_2787130 : Nat := 118140960795 + 2787130 * 2 ^ 59
def prefixEnd_2787130 : Nat := 4983230072969 + 3 ^ 40 * 2787130 * 2
def baseEnd_2787130 : Nat := 954091557710523716504819

theorem tailTrace_2787130 : CollatzResearch.WordTrace tailWord_2787130 prefixEnd_2787130 954091557710523716504819 := by
  unfold tailWord_2787130
  simp only [CollatzResearch.WordTrace]
  refine ⟨25413745598177872188125711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67769988261807659168335229 25413745598177872188125711)
  ·
    refine ⟨38120618397266808282188567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25413745598177872188125711 38120618397266808282188567)
    ·
      refine ⟨57180927595900212423282851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38120618397266808282188567 57180927595900212423282851)
      ·
        refine ⟨85771391393850318634924277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57180927595900212423282851 85771391393850318634924277)
        ·
          refine ⟨8041067943173467372024151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85771391393850318634924277 8041067943173467372024151)
          ·
            refine ⟨12061601914760201058036227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8041067943173467372024151 12061601914760201058036227)
            ·
              refine ⟨18092402872140301587054341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12061601914760201058036227 18092402872140301587054341)
              ·
                refine ⟨3392325538526306547572689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18092402872140301587054341 3392325538526306547572689)
                ·
                  refine ⟨2544244153894729910679517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3392325538526306547572689 2544244153894729910679517)
                  ·
                    refine ⟨954091557710523716504819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2544244153894729910679517 954091557710523716504819)
                    ·
                      rfl

theorem cell22_2787130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_2787130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787130 prefixEnd_2787130 := by exact prefixLift 2787130
  have htrace : WordTrace (prefixWord ++ tailWord_2787130) baseStart_2787130 baseEnd_2787130 := by
    simpa [prefixWord, tailWord_2787130, baseEnd_2787130] using wordTrace_append hprefix tailTrace_2787130
  have hstable : (prefixWord ++ tailWord_2787130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787130).length < 2 ^ (prefixWord ++ tailWord_2787130).sum := by decide
  have hdescent : baseEnd_2787130 < baseStart_2787130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787203 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 2, 5]
def baseStart_2787203 : Nat := 118140960795 + 2787203 * 2 ^ 59
def prefixEnd_2787203 : Nat := 4983230072969 + 3 ^ 40 * 2787203 * 2
def baseEnd_2787203 : Nat := 954116547102375859429595

theorem tailTrace_2787203 : CollatzResearch.WordTrace tailWord_2787203 prefixEnd_2787203 954116547102375859429595 := by
  unfold tailWord_2787203
  simp only [CollatzResearch.WordTrace]
  refine ⟨101657644921447022219910263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67771763280964681479940175 101657644921447022219910263)
  ·
    refine ⟨152486467382170533329865395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101657644921447022219910263 152486467382170533329865395)
    ·
      refine ⟨228729701073255799994798093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152486467382170533329865395 228729701073255799994798093)
      ·
        refine ⟨85773637902470924998049285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228729701073255799994798093 85773637902470924998049285)
        ·
          refine ⟨16082557106713298437134241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85773637902470924998049285 16082557106713298437134241)
          ·
            refine ⟨12061917830034973827850681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16082557106713298437134241 12061917830034973827850681)
            ·
              refine ⟨9046438372526230370888011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12061917830034973827850681 9046438372526230370888011)
              ·
                refine ⟨13569657558789345556332017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9046438372526230370888011 13569657558789345556332017)
                ·
                  refine ⟨10177243169092009167249013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13569657558789345556332017 10177243169092009167249013)
                  ·
                    refine ⟨954116547102375859429595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10177243169092009167249013 954116547102375859429595)
                    ·
                      rfl

theorem cell22_2787203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 5].length) (baseStart_2787203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787203 prefixEnd_2787203 := by exact prefixLift 2787203
  have htrace : WordTrace (prefixWord ++ tailWord_2787203) baseStart_2787203 baseEnd_2787203 := by
    simpa [prefixWord, tailWord_2787203, baseEnd_2787203] using wordTrace_append hprefix tailTrace_2787203
  have hstable : (prefixWord ++ tailWord_2787203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787203).length < 2 ^ (prefixWord ++ tailWord_2787203).sum := by decide
  have hdescent : baseEnd_2787203 < baseStart_2787203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787205 : List Nat := [1, 3, 1, 1, 3, 2, 5, 1, 5]
def baseStart_2787205 : Nat := 118140960795 + 2787205 * 2 ^ 59
def prefixEnd_2787205 : Nat := 4983230072969 + 3 ^ 40 * 2787205 * 2
def baseEnd_2787205 : Nat := 318039077247749506959863

theorem tailTrace_2787205 : CollatzResearch.WordTrace tailWord_2787205 prefixEnd_2787205 318039077247749506959863 := by
  unfold tailWord_2787205
  simp only [CollatzResearch.WordTrace]
  refine ⟨101657717867439776561483069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67771811911626517707655379 101657717867439776561483069)
  ·
    refine ⟨38121644200289916210556151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101657717867439776561483069 38121644200289916210556151)
    ·
      refine ⟨57182466300434874315834227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38121644200289916210556151 57182466300434874315834227)
      ·
        refine ⟨85773699450652311473751341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57182466300434874315834227 85773699450652311473751341)
        ·
          refine ⟨32165137293994616802656753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85773699450652311473751341 32165137293994616802656753)
          ·
            refine ⟨24123852970495962601992565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32165137293994616802656753 24123852970495962601992565)
            ·
              refine ⟨2261611215983996493936803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24123852970495962601992565 2261611215983996493936803)
              ·
                refine ⟨3392416823975994740905205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261611215983996493936803 3392416823975994740905205)
                ·
                  refine ⟨318039077247749506959863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3392416823975994740905205 318039077247749506959863)
                  ·
                    rfl

theorem cell22_2787205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_2787205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787205 prefixEnd_2787205 := by exact prefixLift 2787205
  have htrace : WordTrace (prefixWord ++ tailWord_2787205) baseStart_2787205 baseEnd_2787205 := by
    simpa [prefixWord, tailWord_2787205, baseEnd_2787205] using wordTrace_append hprefix tailTrace_2787205
  have hstable : (prefixWord ++ tailWord_2787205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787205).length < 2 ^ (prefixWord ++ tailWord_2787205).sum := by decide
  have hdescent : baseEnd_2787205 < baseStart_2787205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787250 : List Nat := [3, 2, 1, 1, 1, 1, 1, 8, 4]
def baseStart_2787250 : Nat := 118140960795 + 2787250 * 2 ^ 59
def prefixEnd_2787250 : Nat := 4983230072969 + 3 ^ 40 * 2787250 * 2
def baseEnd_2787250 : Nat := 318044212054294467834817

theorem tailTrace_2787250 : CollatzResearch.WordTrace tailWord_2787250 prefixEnd_2787250 318044212054294467834817 := by
  unfold tailWord_2787250
  simp only [CollatzResearch.WordTrace]
  refine ⟨25414839788069187311717801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67772906101517832831247469 25414839788069187311717801)
  ·
    refine ⟨19061129841051890483788351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25414839788069187311717801 19061129841051890483788351)
    ·
      refine ⟨28591694761577835725682527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19061129841051890483788351 28591694761577835725682527)
      ·
        refine ⟨42887542142366753588523791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28591694761577835725682527 42887542142366753588523791)
        ·
          refine ⟨64331313213550130382785687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42887542142366753588523791 64331313213550130382785687)
          ·
            refine ⟨96496969820325195574178531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64331313213550130382785687 96496969820325195574178531)
            ·
              refine ⟨144745454730487793361267797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96496969820325195574178531 144745454730487793361267797)
              ·
                refine ⟨1696235797622903828452357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 144745454730487793361267797 1696235797622903828452357)
                ·
                  refine ⟨318044212054294467834817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1696235797622903828452357 318044212054294467834817)
                  ·
                    rfl

theorem cell22_2787250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_2787250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787250 prefixEnd_2787250 := by exact prefixLift 2787250
  have htrace : WordTrace (prefixWord ++ tailWord_2787250) baseStart_2787250 baseEnd_2787250 := by
    simpa [prefixWord, tailWord_2787250, baseEnd_2787250] using wordTrace_append hprefix tailTrace_2787250
  have hstable : (prefixWord ++ tailWord_2787250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787250).length < 2 ^ (prefixWord ++ tailWord_2787250).sum := by decide
  have hdescent : baseEnd_2787250 < baseStart_2787250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787263 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 4, 4]
def baseStart_2787263 : Nat := 118140960795 + 2787263 * 2 ^ 59
def prefixEnd_2787263 : Nat := 4983230072969 + 3 ^ 40 * 2787263 * 2
def baseEnd_2787263 : Nat := 954137086328555702929411

theorem tailTrace_2787263 : CollatzResearch.WordTrace tailWord_2787263 prefixEnd_2787263 954137086328555702929411 := by
  unfold tailWord_2787263
  simp only [CollatzResearch.WordTrace]
  refine ⟨101659833301229652467094443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67773222200819768311396295 101659833301229652467094443)
  ·
    refine ⟨152489749951844478700641665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101659833301229652467094443 152489749951844478700641665)
    ·
      refine ⟨114367312463883359025481249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152489749951844478700641665 114367312463883359025481249)
      ·
        refine ⟨85775484347912519269110937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114367312463883359025481249 85775484347912519269110937)
        ·
          refine ⟨64331613260934389451833203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85775484347912519269110937 64331613260934389451833203)
          ·
            refine ⟨96497419891401584177749805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64331613260934389451833203 96497419891401584177749805)
            ·
              refine ⟨36186532459275594066656177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96497419891401584177749805 36186532459275594066656177)
              ·
                refine ⟨27139899344456695549992133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36186532459275594066656177 27139899344456695549992133)
                ·
                  refine ⟨5088731127085630415623525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27139899344456695549992133 5088731127085630415623525)
                  ·
                    refine ⟨954137086328555702929411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5088731127085630415623525 954137086328555702929411)
                    ·
                      rfl

theorem cell22_2787263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_2787263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787263 prefixEnd_2787263 := by exact prefixLift 2787263
  have htrace : WordTrace (prefixWord ++ tailWord_2787263) baseStart_2787263 baseEnd_2787263 := by
    simpa [prefixWord, tailWord_2787263, baseEnd_2787263] using wordTrace_append hprefix tailTrace_2787263
  have hstable : (prefixWord ++ tailWord_2787263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787263).length < 2 ^ (prefixWord ++ tailWord_2787263).sum := by decide
  have hdescent : baseEnd_2787263 < baseStart_2787263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787278 : List Nat := [4, 1, 1, 1, 2, 2, 1, 10]
def baseStart_2787278 : Nat := 118140960795 + 2787278 * 2 ^ 59
def prefixEnd_2787278 : Nat := 4983230072969 + 3 ^ 40 * 2787278 * 2
def baseEnd_2787278 : Nat := 106015802348344518200485

theorem tailTrace_2787278 : CollatzResearch.WordTrace tailWord_2787278 prefixEnd_2787278 106015802348344518200485 := by
  unfold tailWord_2787278
  simp only [CollatzResearch.WordTrace]
  refine ⟨12707547549521913753611311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67773586930783540019260325 12707547549521913753611311)
  ·
    refine ⟨19061321324282870630416967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12707547549521913753611311 19061321324282870630416967)
    ·
      refine ⟨28591981986424305945625451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19061321324282870630416967 28591981986424305945625451)
      ·
        refine ⟨42887972979636458918438177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28591981986424305945625451 42887972979636458918438177)
        ·
          refine ⟨32165979734727344188828633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42887972979636458918438177 32165979734727344188828633)
          ·
            refine ⟨24124484801045508141621475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32165979734727344188828633 24124484801045508141621475)
            ·
              refine ⟨36186727201568262212432213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24124484801045508141621475 36186727201568262212432213)
              ·
                refine ⟨106015802348344518200485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36186727201568262212432213 106015802348344518200485)
                ·
                  rfl

theorem cell22_2787278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_2787278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787278 prefixEnd_2787278 := by exact prefixLift 2787278
  have htrace : WordTrace (prefixWord ++ tailWord_2787278) baseStart_2787278 baseEnd_2787278 := by
    simpa [prefixWord, tailWord_2787278, baseEnd_2787278] using wordTrace_append hprefix tailTrace_2787278
  have hstable : (prefixWord ++ tailWord_2787278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787278).length < 2 ^ (prefixWord ++ tailWord_2787278).sum := by decide
  have hdescent : baseEnd_2787278 < baseStart_2787278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787282 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_2787282 : Nat := 118140960795 + 2787282 * 2 ^ 59
def prefixEnd_2787282 : Nat := 4983230072969 + 3 ^ 40 * 2787282 * 2
def baseEnd_2787282 : Nat := 954143590416845986704353

theorem tailTrace_2787282 : CollatzResearch.WordTrace tailWord_2787282 prefixEnd_2787282 954143590416845986704353 := by
  unfold tailWord_2787282
  simp only [CollatzResearch.WordTrace]
  refine ⟨25415131572040204678009025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67773684192107212474690733 25415131572040204678009025)
  ·
    refine ⟨19061348679030153508506769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25415131572040204678009025 19061348679030153508506769)
    ·
      refine ⟨14296011509272615131380077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19061348679030153508506769 14296011509272615131380077)
      ·
        refine ⟨5361004315977230674267529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14296011509272615131380077 5361004315977230674267529)
        ·
          refine ⟨4020753236982923005700647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5361004315977230674267529 4020753236982923005700647)
          ·
            refine ⟨6031129855474384508550971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020753236982923005700647 6031129855474384508550971)
            ·
              refine ⟨9046694783211576762826457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6031129855474384508550971 9046694783211576762826457)
              ·
                refine ⟨6785021087408682572119843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9046694783211576762826457 6785021087408682572119843)
                ·
                  refine ⟨10177531631113023858179765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6785021087408682572119843 10177531631113023858179765)
                  ·
                    refine ⟨954143590416845986704353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10177531631113023858179765 954143590416845986704353)
                    ·
                      rfl

theorem cell22_2787282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_2787282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787282 prefixEnd_2787282 := by exact prefixLift 2787282
  have htrace : WordTrace (prefixWord ++ tailWord_2787282) baseStart_2787282 baseEnd_2787282 := by
    simpa [prefixWord, tailWord_2787282, baseEnd_2787282] using wordTrace_append hprefix tailTrace_2787282
  have hstable : (prefixWord ++ tailWord_2787282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787282).length < 2 ^ (prefixWord ++ tailWord_2787282).sum := by decide
  have hdescent : baseEnd_2787282 < baseStart_2787282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787286 : List Nat := [5, 2, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_2787286 : Nat := 118140960795 + 2787286 * 2 ^ 59
def prefixEnd_2787286 : Nat := 4983230072969 + 3 ^ 40 * 2787286 * 2
def baseEnd_2787286 : Nat := 954144959698591309604341

theorem tailTrace_2787286 : CollatzResearch.WordTrace tailWord_2787286 prefixEnd_2787286 954144959698591309604341 := by
  unfold tailWord_2787286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6353792011259145462198857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67773781453430884930121141 6353792011259145462198857)
  ·
    refine ⟨4765344008444359096649143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6353792011259145462198857 4765344008444359096649143)
    ·
      refine ⟨7148016012666538644973715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4765344008444359096649143 7148016012666538644973715)
      ·
        refine ⟨10722024018999807967460573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7148016012666538644973715 10722024018999807967460573)
        ·
          refine ⟨4020759007124927987797715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10722024018999807967460573 4020759007124927987797715)
          ·
            refine ⟨6031138510687391981696573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020759007124927987797715 6031138510687391981696573)
            ·
              refine ⟨2261676941507771993136215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6031138510687391981696573 2261676941507771993136215)
              ·
                refine ⟨3392515412261657989704323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261676941507771993136215 3392515412261657989704323)
                ·
                  refine ⟨5088773118392486984556485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3392515412261657989704323 5088773118392486984556485)
                  ·
                    refine ⟨954144959698591309604341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5088773118392486984556485 954144959698591309604341)
                    ·
                      rfl

theorem cell22_2787286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_2787286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787286 prefixEnd_2787286 := by exact prefixLift 2787286
  have htrace : WordTrace (prefixWord ++ tailWord_2787286) baseStart_2787286 baseEnd_2787286 := by
    simpa [prefixWord, tailWord_2787286, baseEnd_2787286] using wordTrace_append hprefix tailTrace_2787286
  have hstable : (prefixWord ++ tailWord_2787286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787286).length < 2 ^ (prefixWord ++ tailWord_2787286).sum := by decide
  have hdescent : baseEnd_2787286 < baseStart_2787286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787357 : List Nat := [1, 4, 2, 2, 2, 1, 3, 2, 5]
def baseStart_2787357 : Nat := 118140960795 + 2787357 * 2 ^ 59
def prefixEnd_2787357 : Nat := 4983230072969 + 3 ^ 40 * 2787357 * 2
def baseEnd_2787357 : Nat := 318056421483190263693041

theorem tailTrace_2787357 : CollatzResearch.WordTrace tailWord_2787357 prefixEnd_2787357 318056421483190263693041 := by
  unfold tailWord_2787357
  simp only [CollatzResearch.WordTrace]
  refine ⟨101663261762889106521016325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67775507841926071014010883 101663261762889106521016325)
  ·
    refine ⟨19061861580541707472690561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101663261762889106521016325 19061861580541707472690561)
    ·
      refine ⟨14296396185406280604517921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19061861580541707472690561 14296396185406280604517921)
      ·
        refine ⟨10722297139054710453388441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14296396185406280604517921 10722297139054710453388441)
        ·
          refine ⟨8041722854291032840041331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10722297139054710453388441 8041722854291032840041331)
          ·
            refine ⟨12062584281436549260061997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8041722854291032840041331 12062584281436549260061997)
            ·
              refine ⟨4523469105538705972523249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12062584281436549260061997 4523469105538705972523249)
              ·
                refine ⟨3392601829154029479392437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4523469105538705972523249 3392601829154029479392437)
                ·
                  refine ⟨318056421483190263693041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3392601829154029479392437 318056421483190263693041)
                  ·
                    rfl

theorem cell22_2787357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_2787357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787357 prefixEnd_2787357 := by exact prefixLift 2787357
  have htrace : WordTrace (prefixWord ++ tailWord_2787357) baseStart_2787357 baseEnd_2787357 := by
    simpa [prefixWord, tailWord_2787357, baseEnd_2787357] using wordTrace_append hprefix tailTrace_2787357
  have hstable : (prefixWord ++ tailWord_2787357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787357).length < 2 ^ (prefixWord ++ tailWord_2787357).sum := by decide
  have hdescent : baseEnd_2787357 < baseStart_2787357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787374 : List Nat := [4, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_2787374 : Nat := 118140960795 + 2787374 * 2 ^ 59
def prefixEnd_2787374 : Nat := 4983230072969 + 3 ^ 40 * 2787374 * 2
def baseEnd_2787374 : Nat := 318058361298996137801357

theorem tailTrace_2787374 : CollatzResearch.WordTrace tailWord_2787374 prefixEnd_2787374 318058361298996137801357 := by
  unfold tailWord_2787374
  simp only [CollatzResearch.WordTrace]
  refine ⟨12707985225478439803048147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67775921202551678949590117 12707985225478439803048147)
  ·
    refine ⟨19061977838217659704572221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12707985225478439803048147 19061977838217659704572221)
    ·
      refine ⟨7148241689331622389214583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19061977838217659704572221 7148241689331622389214583)
      ·
        refine ⟨10722362533997433583821875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7148241689331622389214583 10722362533997433583821875)
        ·
          refine ⟨16083543800996150375732813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10722362533997433583821875 16083543800996150375732813)
          ·
            refine ⟨6031328925373556390899805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16083543800996150375732813 6031328925373556390899805)
            ·
              refine ⟨2261748347015083646587427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6031328925373556390899805 2261748347015083646587427)
              ·
                refine ⟨3392622520522625469881141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261748347015083646587427 3392622520522625469881141)
                ·
                  refine ⟨318058361298996137801357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3392622520522625469881141 318058361298996137801357)
                  ·
                    rfl

theorem cell22_2787374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_2787374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787374 prefixEnd_2787374 := by exact prefixLift 2787374
  have htrace : WordTrace (prefixWord ++ tailWord_2787374) baseStart_2787374 baseEnd_2787374 := by
    simpa [prefixWord, tailWord_2787374, baseEnd_2787374] using wordTrace_append hprefix tailTrace_2787374
  have hstable : (prefixWord ++ tailWord_2787374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787374).length < 2 ^ (prefixWord ++ tailWord_2787374).sum := by decide
  have hdescent : baseEnd_2787374 < baseStart_2787374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787415 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 4, 4]
def baseStart_2787415 : Nat := 118140960795 + 2787415 * 2 ^ 59
def prefixEnd_2787415 : Nat := 4983230072969 + 3 ^ 40 * 2787415 * 2
def baseEnd_2787415 : Nat := 954189119034877973128945

theorem tailTrace_2787415 : CollatzResearch.WordTrace tailWord_2787415 prefixEnd_2787415 954189119034877973128945 := by
  unfold tailWord_2787415
  simp only [CollatzResearch.WordTrace]
  refine ⟨101665377196678982426627699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67776918131119321617751799 101665377196678982426627699)
  ·
    refine ⟨152498065795018473639941549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101665377196678982426627699 152498065795018473639941549)
    ·
      refine ⟨57186774673131927614978081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152498065795018473639941549 57186774673131927614978081)
      ·
        refine ⟨42890081004848945711233561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57186774673131927614978081 42890081004848945711233561)
        ·
          refine ⟨32167560753636709283425171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42890081004848945711233561 32167560753636709283425171)
          ·
            refine ⟨48251341130455063925137757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32167560753636709283425171 48251341130455063925137757)
            ·
              refine ⟨18094252923920648971926659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48251341130455063925137757 18094252923920648971926659)
              ·
                refine ⟨27141379385880973457889989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18094252923920648971926659 27141379385880973457889989)
                ·
                  refine ⟨5089008634852682523354373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27141379385880973457889989 5089008634852682523354373)
                  ·
                    refine ⟨954189119034877973128945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5089008634852682523354373 954189119034877973128945)
                    ·
                      rfl

theorem cell22_2787415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_2787415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787415 prefixEnd_2787415 := by exact prefixLift 2787415
  have htrace : WordTrace (prefixWord ++ tailWord_2787415) baseStart_2787415 baseEnd_2787415 := by
    simpa [prefixWord, tailWord_2787415, baseEnd_2787415] using wordTrace_append hprefix tailTrace_2787415
  have hstable : (prefixWord ++ tailWord_2787415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787415).length < 2 ^ (prefixWord ++ tailWord_2787415).sum := by decide
  have hdescent : baseEnd_2787415 < baseStart_2787415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787417 : List Nat := [1, 2, 1, 2, 2, 1, 4, 4, 2, 3]
def baseStart_2787417 : Nat := 118140960795 + 2787417 * 2 ^ 59
def prefixEnd_2787417 : Nat := 4983230072969 + 3 ^ 40 * 2787417 * 2
def baseEnd_2787417 : Nat := 954189803675750634578939

theorem tailTrace_2787417 : CollatzResearch.WordTrace tailWord_2787417 prefixEnd_2787417 954189803675750634578939 := by
  unfold tailWord_2787417
  simp only [CollatzResearch.WordTrace]
  refine ⟨101665450142671736768200505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67776966761781157845467003 101665450142671736768200505)
  ·
    refine ⟨76249087607003802576150379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101665450142671736768200505 76249087607003802576150379)
    ·
      refine ⟨114373631410505703864225569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76249087607003802576150379 114373631410505703864225569)
      ·
        refine ⟨85780223557879277898169177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114373631410505703864225569 85780223557879277898169177)
        ·
          refine ⟨64335167668409458423626883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85780223557879277898169177 64335167668409458423626883)
          ·
            refine ⟨96502751502614187635440325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64335167668409458423626883 96502751502614187635440325)
            ·
              refine ⟨18094265906740160181645061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96502751502614187635440325 18094265906740160181645061)
              ·
                refine ⟨3392674857513780034058449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18094265906740160181645061 3392674857513780034058449)
                ·
                  refine ⟨2544506143135335025543837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3392674857513780034058449 2544506143135335025543837)
                  ·
                    refine ⟨954189803675750634578939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2544506143135335025543837 954189803675750634578939)
                    ·
                      rfl

theorem cell22_2787417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 3].length) (baseStart_2787417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787417 prefixEnd_2787417 := by exact prefixLift 2787417
  have htrace : WordTrace (prefixWord ++ tailWord_2787417) baseStart_2787417 baseEnd_2787417 := by
    simpa [prefixWord, tailWord_2787417, baseEnd_2787417] using wordTrace_append hprefix tailTrace_2787417
  have hstable : (prefixWord ++ tailWord_2787417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787417).length < 2 ^ (prefixWord ++ tailWord_2787417).sum := by decide
  have hdescent : baseEnd_2787417 < baseStart_2787417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787567 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 1, 6]
def baseStart_2787567 : Nat := 118140960795 + 2787567 * 2 ^ 59
def prefixEnd_2787567 : Nat := 4983230072969 + 3 ^ 40 * 2787567 * 2
def baseEnd_2787567 : Nat := 954241151741200243328479

theorem tailTrace_2787567 : CollatzResearch.WordTrace tailWord_2787567 prefixEnd_2787567 954241151741200243328479 := by
  unfold tailWord_2787567
  simp only [CollatzResearch.WordTrace]
  refine ⟨101670921092128312386160955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67780614061418874924107303 101670921092128312386160955)
  ·
    refine ⟨152506381638192468579241433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101670921092128312386160955 152506381638192468579241433)
    ·
      refine ⟨114379786228644351434431075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152506381638192468579241433 114379786228644351434431075)
      ·
        refine ⟨171569679342966527151646613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114379786228644351434431075 171569679342966527151646613)
        ·
          refine ⟨8042328719201555960233435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171569679342966527151646613 8042328719201555960233435)
          ·
            refine ⟨12063493078802333940350153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8042328719201555960233435 12063493078802333940350153)
            ·
              refine ⟨9047619809101750455262615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12063493078802333940350153 9047619809101750455262615)
              ·
                refine ⟨13571429713652625682893923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9047619809101750455262615 13571429713652625682893923)
                ·
                  refine ⟨20357144570478938524340885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13571429713652625682893923 20357144570478938524340885)
                  ·
                    refine ⟨954241151741200243328479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20357144570478938524340885 954241151741200243328479)
                    ·
                      rfl

theorem cell22_2787567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_2787567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787567 prefixEnd_2787567 := by exact prefixLift 2787567
  have htrace : WordTrace (prefixWord ++ tailWord_2787567) baseStart_2787567 baseEnd_2787567 := by
    simpa [prefixWord, tailWord_2787567, baseEnd_2787567] using wordTrace_append hprefix tailTrace_2787567
  have hstable : (prefixWord ++ tailWord_2787567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787567).length < 2 ^ (prefixWord ++ tailWord_2787567).sum := by decide
  have hdescent : baseEnd_2787567 < baseStart_2787567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787586 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_2787586 : Nat := 118140960795 + 2787586 * 2 ^ 59
def prefixEnd_2787586 : Nat := 4983230072969 + 3 ^ 40 * 2787586 * 2
def baseEnd_2787586 : Nat := 954247655829490527103421

theorem tailTrace_2787586 : CollatzResearch.WordTrace tailWord_2787586 prefixEnd_2787586 954247655829490527103421 := by
  unfold tailWord_2787586
  simp only [CollatzResearch.WordTrace]
  refine ⟨25417903519764869657775653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67781076052706319087401741 25417903519764869657775653)
  ·
    refine ⟨4765856909955913060832935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25417903519764869657775653 4765856909955913060832935)
    ·
      refine ⟨7148785364933869591249403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4765856909955913060832935 7148785364933869591249403)
      ·
        refine ⟨10723178047400804386874105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7148785364933869591249403 10723178047400804386874105)
        ·
          refine ⟨8042383535550603290155579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10723178047400804386874105 8042383535550603290155579)
          ·
            refine ⟨12063575303325904935233369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8042383535550603290155579 12063575303325904935233369)
            ·
              refine ⟨9047681477494428701425027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12063575303325904935233369 9047681477494428701425027)
              ·
                refine ⟨13571522216241643052137541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9047681477494428701425027 13571522216241643052137541)
                ·
                  refine ⟨2544660415545308072275789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13571522216241643052137541 2544660415545308072275789)
                  ·
                    refine ⟨954247655829490527103421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2544660415545308072275789 954247655829490527103421)
                    ·
                      rfl

theorem cell22_2787586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_2787586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787586 prefixEnd_2787586 := by exact prefixLift 2787586
  have htrace : WordTrace (prefixWord ++ tailWord_2787586) baseStart_2787586 baseEnd_2787586 := by
    simpa [prefixWord, tailWord_2787586, baseEnd_2787586] using wordTrace_append hprefix tailTrace_2787586
  have hstable : (prefixWord ++ tailWord_2787586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787586).length < 2 ^ (prefixWord ++ tailWord_2787586).sum := by decide
  have hdescent : baseEnd_2787586 < baseStart_2787586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787588 : List Nat := [2, 3, 2, 2, 3, 1, 3, 2, 4]
def baseStart_2787588 : Nat := 118140960795 + 2787588 * 2 ^ 59
def prefixEnd_2787588 : Nat := 4983230072969 + 3 ^ 40 * 2787588 * 2
def baseEnd_2787588 : Nat := 318082780156787729517805

theorem tailTrace_2787588 : CollatzResearch.WordTrace tailWord_2787588 prefixEnd_2787588 318082780156787729517805 := by
  unfold tailWord_2787588
  simp only [CollatzResearch.WordTrace]
  refine ⟨50835843512526116486337709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67781124683368155315116945 50835843512526116486337709)
  ·
    refine ⟨19063441317197293682376641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50835843512526116486337709 19063441317197293682376641)
    ·
      refine ⟨14297580987897970261782481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19063441317197293682376641 14297580987897970261782481)
      ·
        refine ⟨10723185740923477696336861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14297580987897970261782481 10723185740923477696336861)
        ·
          refine ⟨4021194652846304136126323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10723185740923477696336861 4021194652846304136126323)
          ·
            refine ⟨6031791979269456204189485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021194652846304136126323 6031791979269456204189485)
            ·
              refine ⟨2261921992226046076571057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6031791979269456204189485 2261921992226046076571057)
              ·
                refine ⟨1696441494169534557428293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2261921992226046076571057 1696441494169534557428293)
                ·
                  refine ⟨318082780156787729517805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1696441494169534557428293 318082780156787729517805)
                  ·
                    rfl

theorem cell22_2787588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_2787588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787588 prefixEnd_2787588 := by exact prefixLift 2787588
  have htrace : WordTrace (prefixWord ++ tailWord_2787588) baseStart_2787588 baseEnd_2787588 := by
    simpa [prefixWord, tailWord_2787588, baseEnd_2787588] using wordTrace_append hprefix tailTrace_2787588
  have hstable : (prefixWord ++ tailWord_2787588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787588).length < 2 ^ (prefixWord ++ tailWord_2787588).sum := by decide
  have hdescent : baseEnd_2787588 < baseStart_2787588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787644 : List Nat := [2, 2, 2, 2, 1, 2, 4, 2, 5]
def baseStart_2787644 : Nat := 118140960795 + 2787644 * 2 ^ 59
def prefixEnd_2787644 : Nat := 4983230072969 + 3 ^ 40 * 2787644 * 2
def baseEnd_2787644 : Nat := 318089170138265903051081

theorem tailTrace_2787644 : CollatzResearch.WordTrace tailWord_2787644 prefixEnd_2787644 318089170138265903051081 := by
  unfold tailWord_2787644
  simp only [CollatzResearch.WordTrace]
  refine ⟨50836864756424677268356993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67782486341899569691142657 50836864756424677268356993)
  ·
    refine ⟨38127648567318507951267745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50836864756424677268356993 38127648567318507951267745)
    ·
      refine ⟨28595736425488880963450809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38127648567318507951267745 28595736425488880963450809)
      ·
        refine ⟨21446802319116660722588107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28595736425488880963450809 21446802319116660722588107)
        ·
          refine ⟨32170203478674991083882161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21446802319116660722588107 32170203478674991083882161)
          ·
            refine ⟨24127652609006243312911621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32170203478674991083882161 24127652609006243312911621)
            ·
              refine ⟨4523934864188670621170929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24127652609006243312911621 4523934864188670621170929)
              ·
                refine ⟨3392951148141502965878197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4523934864188670621170929 3392951148141502965878197)
                ·
                  refine ⟨318089170138265903051081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3392951148141502965878197 318089170138265903051081)
                  ·
                    rfl

theorem cell22_2787644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_2787644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787644 prefixEnd_2787644 := by exact prefixLift 2787644
  have htrace : WordTrace (prefixWord ++ tailWord_2787644) baseStart_2787644 baseEnd_2787644 := by
    simpa [prefixWord, tailWord_2787644, baseEnd_2787644] using wordTrace_append hprefix tailTrace_2787644
  have hstable : (prefixWord ++ tailWord_2787644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787644).length < 2 ^ (prefixWord ++ tailWord_2787644).sum := by decide
  have hdescent : baseEnd_2787644 < baseStart_2787644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787674 : List Nat := [3, 1, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_2787674 : Nat := 118140960795 + 2787674 * 2 ^ 59
def prefixEnd_2787674 : Nat := 4983230072969 + 3 ^ 40 * 2787674 * 2
def baseEnd_2787674 : Nat := 954277780027887630903151

theorem tailTrace_2787674 : CollatzResearch.WordTrace tailWord_2787674 prefixEnd_2787674 954277780027887630903151 := by
  unfold tailWord_2787674
  simp only [CollatzResearch.WordTrace]
  refine ⟨25418705925685167415076519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67783215801827113106870717 25418705925685167415076519)
  ·
    refine ⟨38128058888527751122614779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25418705925685167415076519 38128058888527751122614779)
    ·
      refine ⟨57192088332791626683922169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38128058888527751122614779 57192088332791626683922169)
      ·
        refine ⟨42894066249593720012941627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57192088332791626683922169 42894066249593720012941627)
        ·
          refine ⟨64341099374390580019412441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42894066249593720012941627 64341099374390580019412441)
          ·
            refine ⟨48255824530792935014559331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64341099374390580019412441 48255824530792935014559331)
            ·
              refine ⟨72383736796189402521838997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48255824530792935014559331 72383736796189402521838997)
              ·
                refine ⟨3392987662321378243211203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72383736796189402521838997 3392987662321378243211203)
                ·
                  refine ⟨5089481493482067364816805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3392987662321378243211203 5089481493482067364816805)
                  ·
                    refine ⟨954277780027887630903151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5089481493482067364816805 954277780027887630903151)
                    ·
                      rfl

theorem cell22_2787674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_2787674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787674 prefixEnd_2787674 := by exact prefixLift 2787674
  have htrace : WordTrace (prefixWord ++ tailWord_2787674) baseStart_2787674 baseEnd_2787674 := by
    simpa [prefixWord, tailWord_2787674, baseEnd_2787674] using wordTrace_append hprefix tailTrace_2787674
  have hstable : (prefixWord ++ tailWord_2787674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787674).length < 2 ^ (prefixWord ++ tailWord_2787674).sum := by decide
  have hdescent : baseEnd_2787674 < baseStart_2787674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787717 : List Nat := [1, 3, 1, 1, 3, 1, 1, 11]
def baseStart_2787717 : Nat := 118140960795 + 2787717 * 2 ^ 59
def prefixEnd_2787717 : Nat := 4983230072969 + 3 ^ 40 * 2787717 * 2
def baseEnd_2787717 : Nat := 106032499978516650230891

theorem tailTrace_2787717 : CollatzResearch.WordTrace tailWord_2787717 prefixEnd_2787717 106032499978516650230891 := by
  unfold tailWord_2787717
  simp only [CollatzResearch.WordTrace]
  refine ⟨101676392041584888004121405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67784261361056592002747603 101676392041584888004121405)
  ·
    refine ⟨38128647015594333001545527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101676392041584888004121405 38128647015594333001545527)
    ·
      refine ⟨57192970523391499502318291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38128647015594333001545527 57192970523391499502318291)
      ·
        refine ⟨85789455785087249253477437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57192970523391499502318291 85789455785087249253477437)
        ·
          refine ⟨32171045919407718470054039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85789455785087249253477437 32171045919407718470054039)
          ·
            refine ⟨48256568879111577705081059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32171045919407718470054039 48256568879111577705081059)
            ·
              refine ⟨72384853318667366557621589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48256568879111577705081059 72384853318667366557621589)
              ·
                refine ⟨106032499978516650230891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 72384853318667366557621589 106032499978516650230891)
                ·
                  rfl

theorem cell22_2787717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 11].length) (baseStart_2787717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787717 prefixEnd_2787717 := by exact prefixLift 2787717
  have htrace : WordTrace (prefixWord ++ tailWord_2787717) baseStart_2787717 baseEnd_2787717 := by
    simpa [prefixWord, tailWord_2787717, baseEnd_2787717] using wordTrace_append hprefix tailTrace_2787717
  have hstable : (prefixWord ++ tailWord_2787717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787717).length < 2 ^ (prefixWord ++ tailWord_2787717).sum := by decide
  have hdescent : baseEnd_2787717 < baseStart_2787717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787721 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 1, 5]
def baseStart_2787721 : Nat := 118140960795 + 2787721 * 2 ^ 59
def prefixEnd_2787721 : Nat := 4983230072969 + 3 ^ 40 * 2787721 * 2
def baseEnd_2787721 : Nat := 954293869088395174978007

theorem tailTrace_2787721 : CollatzResearch.WordTrace tailWord_2787721 prefixEnd_2787721 954293869088395174978007 := by
  unfold tailWord_2787721
  simp only [CollatzResearch.WordTrace]
  refine ⟨101676537933570396687267017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67784358622380264458178011 101676537933570396687267017)
  ·
    refine ⟨76257403450177797515450263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101676537933570396687267017 76257403450177797515450263)
    ·
      refine ⟨114386105175266696273175395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76257403450177797515450263 114386105175266696273175395)
      ·
        refine ⟨171579157762900044409763093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114386105175266696273175395 171579157762900044409763093)
        ·
          refine ⟨8042773020135939581707645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171579157762900044409763093 8042773020135939581707645)
          ·
            refine ⟨3016039882550977343140367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8042773020135939581707645 3016039882550977343140367)
            ·
              refine ⟨4524059823826466014710551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016039882550977343140367 4524059823826466014710551)
              ·
                refine ⟨6786089735739699022065827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524059823826466014710551 6786089735739699022065827)
                ·
                  refine ⟨10179134603609548533098741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6786089735739699022065827 10179134603609548533098741)
                  ·
                    refine ⟨954293869088395174978007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10179134603609548533098741 954293869088395174978007)
                    ·
                      rfl

theorem cell22_2787721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 5].length) (baseStart_2787721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787721 prefixEnd_2787721 := by exact prefixLift 2787721
  have htrace : WordTrace (prefixWord ++ tailWord_2787721) baseStart_2787721 baseEnd_2787721 := by
    simpa [prefixWord, tailWord_2787721, baseEnd_2787721] using wordTrace_append hprefix tailTrace_2787721
  have hstable : (prefixWord ++ tailWord_2787721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787721).length < 2 ^ (prefixWord ++ tailWord_2787721).sum := by decide
  have hdescent : baseEnd_2787721 < baseStart_2787721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787813 : List Nat := [1, 3, 1, 5, 2, 1, 2, 2, 5]
def baseStart_2787813 : Nat := 118140960795 + 2787813 * 2 ^ 59
def prefixEnd_2787813 : Nat := 4983230072969 + 3 ^ 40 * 2787813 * 2
def baseEnd_2787813 : Nat := 318108454189512533892575

theorem tailTrace_2787813 : CollatzResearch.WordTrace tailWord_2787813 prefixEnd_2787813 318108454189512533892575 := by
  unfold tailWord_2787813
  simp only [CollatzResearch.WordTrace]
  refine ⟨101679893449237096399616093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67786595632824730933077395 101679893449237096399616093)
  ·
    refine ⟨38129960043463911149856035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101679893449237096399616093 38129960043463911149856035)
    ·
      refine ⟨57194940065195866724784053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38129960043463911149856035 57194940065195866724784053)
      ·
        refine ⟨5362025631112112505448505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57194940065195866724784053 5362025631112112505448505)
        ·
          refine ⟨4021519223334084379086379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5362025631112112505448505 4021519223334084379086379)
          ·
            refine ⟨6032278835001126568629569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021519223334084379086379 6032278835001126568629569)
            ·
              refine ⟨4524209126250844926472177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6032278835001126568629569 4524209126250844926472177)
              ·
                refine ⟨3393156844688133694854133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4524209126250844926472177 3393156844688133694854133)
                ·
                  refine ⟨318108454189512533892575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3393156844688133694854133 318108454189512533892575)
                  ·
                    rfl

theorem cell22_2787813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_2787813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787813 prefixEnd_2787813 := by exact prefixLift 2787813
  have htrace : WordTrace (prefixWord ++ tailWord_2787813) baseStart_2787813 baseEnd_2787813 := by
    simpa [prefixWord, tailWord_2787813, baseEnd_2787813] using wordTrace_append hprefix tailTrace_2787813
  have hstable : (prefixWord ++ tailWord_2787813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787813).length < 2 ^ (prefixWord ++ tailWord_2787813).sum := by decide
  have hdescent : baseEnd_2787813 < baseStart_2787813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787824 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 6]
def baseStart_2787824 : Nat := 118140960795 + 2787824 * 2 ^ 59
def prefixEnd_2787824 : Nat := 4983230072969 + 3 ^ 40 * 2787824 * 2
def baseEnd_2787824 : Nat := 318109709364445746550897

theorem tailTrace_2787824 : CollatzResearch.WordTrace tailWord_2787824 prefixEnd_2787824 318109709364445746550897 := by
  unfold tailWord_2787824
  simp only [CollatzResearch.WordTrace]
  refine ⟨50840147326098622639133263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67786863101464830185511017 50840147326098622639133263)
  ·
    refine ⟨76260220989147933958699895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50840147326098622639133263 76260220989147933958699895)
    ·
      refine ⟨114390331483721900938049843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76260220989147933958699895 114390331483721900938049843)
      ·
        refine ⟨171585497225582851407074765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114390331483721900938049843 171585497225582851407074765)
        ·
          refine ⟨64344561459593569277653037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171585497225582851407074765 64344561459593569277653037)
          ·
            refine ⟨24129210547347588479119889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64344561459593569277653037 24129210547347588479119889)
            ·
              refine ⟨18096907910510691359339917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24129210547347588479119889 18096907910510691359339917)
              ·
                refine ⟨6786340466441509259752469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18096907910510691359339917 6786340466441509259752469)
                ·
                  refine ⟨318109709364445746550897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6786340466441509259752469 318109709364445746550897)
                  ·
                    rfl

theorem cell22_2787824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_2787824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787824 prefixEnd_2787824 := by exact prefixLift 2787824
  have htrace : WordTrace (prefixWord ++ tailWord_2787824) baseStart_2787824 baseEnd_2787824 := by
    simpa [prefixWord, tailWord_2787824, baseEnd_2787824] using wordTrace_append hprefix tailTrace_2787824
  have hstable : (prefixWord ++ tailWord_2787824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787824).length < 2 ^ (prefixWord ++ tailWord_2787824).sum := by decide
  have hdescent : baseEnd_2787824 < baseStart_2787824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787841 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 6]
def baseStart_2787841 : Nat := 118140960795 + 2787841 * 2 ^ 59
def prefixEnd_2787841 : Nat := 4983230072969 + 3 ^ 40 * 2787841 * 2
def baseEnd_2787841 : Nat := 318111649180251620659213

theorem tailTrace_2787841 : CollatzResearch.WordTrace tailWord_2787841 prefixEnd_2787841 318111649180251620659213 := by
  unfold tailWord_2787841
  simp only [CollatzResearch.WordTrace]
  refine ⟨101680914693135657181635377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67787276462090438121090251 101680914693135657181635377)
  ·
    refine ⟨76260686019851742886226533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101680914693135657181635377 76260686019851742886226533)
    ·
      refine ⟨14298878628722201791167475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76260686019851742886226533 14298878628722201791167475)
      ·
        refine ⟨21448317943083302686751213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14298878628722201791167475 21448317943083302686751213)
        ·
          refine ⟨8043119228656238507531705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21448317943083302686751213 8043119228656238507531705)
          ·
            refine ⟨6032339421492178880648779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8043119228656238507531705 6032339421492178880648779)
            ·
              refine ⟨9048509132238268320973169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032339421492178880648779 9048509132238268320973169)
              ·
                refine ⟨6786381849178701240729877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9048509132238268320973169 6786381849178701240729877)
                ·
                  refine ⟨318111649180251620659213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6786381849178701240729877 318111649180251620659213)
                  ·
                    rfl

theorem cell22_2787841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_2787841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787841 prefixEnd_2787841 := by exact prefixLift 2787841
  have htrace : WordTrace (prefixWord ++ tailWord_2787841) baseStart_2787841 baseEnd_2787841 := by
    simpa [prefixWord, tailWord_2787841, baseEnd_2787841] using wordTrace_append hprefix tailTrace_2787841
  have hstable : (prefixWord ++ tailWord_2787841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787841).length < 2 ^ (prefixWord ++ tailWord_2787841).sum := by decide
  have hdescent : baseEnd_2787841 < baseStart_2787841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787860 : List Nat := [2, 4, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2787860 : Nat := 118140960795 + 2787860 * 2 ^ 59
def prefixEnd_2787860 : Nat := 4983230072969 + 3 ^ 40 * 2787860 * 2
def baseEnd_2787860 : Nat := 954341451629045145752581

theorem tailTrace_2787860 : CollatzResearch.WordTrace tailWord_2787860 prefixEnd_2787860 954341451629045145752581 := by
  unfold tailWord_2787860
  simp only [CollatzResearch.WordTrace]
  refine ⟨50840803840033411713288517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67787738453377882284384689 50840803840033411713288517)
  ·
    refine ⟨9532650720006264696241597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50840803840033411713288517 9532650720006264696241597)
    ·
      refine ⟨3574744020002349261090599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9532650720006264696241597 3574744020002349261090599)
      ·
        refine ⟨5362116030003523891635899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3574744020002349261090599 5362116030003523891635899)
        ·
          refine ⟨8043174045005285837453849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5362116030003523891635899 8043174045005285837453849)
          ·
            refine ⟨6032380533753964378090387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8043174045005285837453849 6032380533753964378090387)
            ·
              refine ⟨9048570800630946567135581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032380533753964378090387 9048570800630946567135581)
              ·
                refine ⟨3393214050236604962675843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9048570800630946567135581 3393214050236604962675843)
                ·
                  refine ⟨5089821075354907444013765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393214050236604962675843 5089821075354907444013765)
                  ·
                    refine ⟨954341451629045145752581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5089821075354907444013765 954341451629045145752581)
                    ·
                      rfl

theorem cell22_2787860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2787860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787860 prefixEnd_2787860 := by exact prefixLift 2787860
  have htrace : WordTrace (prefixWord ++ tailWord_2787860) baseStart_2787860 baseEnd_2787860 := by
    simpa [prefixWord, tailWord_2787860, baseEnd_2787860] using wordTrace_append hprefix tailTrace_2787860
  have hstable : (prefixWord ++ tailWord_2787860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787860).length < 2 ^ (prefixWord ++ tailWord_2787860).sum := by decide
  have hdescent : baseEnd_2787860 < baseStart_2787860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787946 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_2787946 : Nat := 118140960795 + 2787946 * 2 ^ 59
def prefixEnd_2787946 : Nat := 4983230072969 + 3 ^ 40 * 2787946 * 2
def baseEnd_2787946 : Nat := 954370891186569588102317

theorem tailTrace_2787946 : CollatzResearch.WordTrace tailWord_2787946 prefixEnd_2787946 954370891186569588102317 := by
  unfold tailWord_2787946
  simp only [CollatzResearch.WordTrace]
  refine ⟨25421186089438815028551923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67789829571836840076138461 25421186089438815028551923)
  ·
    refine ⟨38131779134158222542827885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25421186089438815028551923 38131779134158222542827885)
    ·
      refine ⟨14299417175309333453560457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38131779134158222542827885 14299417175309333453560457)
      ·
        refine ⟨10724562881482000090170343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14299417175309333453560457 10724562881482000090170343)
        ·
          refine ⟨16086844322223000135255515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10724562881482000090170343 16086844322223000135255515)
          ·
            refine ⟨24130266483334500202883273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16086844322223000135255515 24130266483334500202883273)
            ·
              refine ⟨18097699862500875152162455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24130266483334500202883273 18097699862500875152162455)
              ·
                refine ⟨27146549793751312728243683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18097699862500875152162455 27146549793751312728243683)
                ·
                  refine ⟨40719824690626969092365525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27146549793751312728243683 40719824690626969092365525)
                  ·
                    refine ⟨954370891186569588102317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40719824690626969092365525 954370891186569588102317)
                    ·
                      rfl

theorem cell22_2787946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_2787946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787946 prefixEnd_2787946 := by exact prefixLift 2787946
  have htrace : WordTrace (prefixWord ++ tailWord_2787946) baseStart_2787946 baseEnd_2787946 := by
    simpa [prefixWord, tailWord_2787946, baseEnd_2787946] using wordTrace_append hprefix tailTrace_2787946
  have hstable : (prefixWord ++ tailWord_2787946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787946).length < 2 ^ (prefixWord ++ tailWord_2787946).sum := by decide
  have hdescent : baseEnd_2787946 < baseStart_2787946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787948 : List Nat := [2, 2, 1, 1, 3, 1, 6, 1, 5]
def baseStart_2787948 : Nat := 118140960795 + 2787948 * 2 ^ 59
def prefixEnd_2787948 : Nat := 4983230072969 + 3 ^ 40 * 2787948 * 2
def baseEnd_2787948 : Nat := 318123858609147416517437

theorem tailTrace_2787948 : CollatzResearch.WordTrace tailWord_2787948 prefixEnd_2787948 318123858609147416517437 := by
  unfold tailWord_2787948
  simp only [CollatzResearch.WordTrace]
  refine ⟨50842408651874007227890249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67789878202498676303853665 50842408651874007227890249)
  ·
    refine ⟨38131806488905505420917687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50842408651874007227890249 38131806488905505420917687)
    ·
      refine ⟨57197709733358258131376531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38131806488905505420917687 57197709733358258131376531)
      ·
        refine ⟨85796564600037387197064797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57197709733358258131376531 85796564600037387197064797)
        ·
          refine ⟨32173711725014020198899299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85796564600037387197064797 32173711725014020198899299)
          ·
            refine ⟨48260567587521030298348949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32173711725014020198899299 48260567587521030298348949)
            ·
              refine ⟨2262214105665048295235107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48260567587521030298348949 2262214105665048295235107)
              ·
                refine ⟨3393321158497572442852661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262214105665048295235107 3393321158497572442852661)
                ·
                  refine ⟨318123858609147416517437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3393321158497572442852661 318123858609147416517437)
                  ·
                    rfl

theorem cell22_2787948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_2787948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787948 prefixEnd_2787948 := by exact prefixLift 2787948
  have htrace : WordTrace (prefixWord ++ tailWord_2787948) baseStart_2787948 baseEnd_2787948 := by
    simpa [prefixWord, tailWord_2787948, baseEnd_2787948] using wordTrace_append hprefix tailTrace_2787948
  have hstable : (prefixWord ++ tailWord_2787948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787948).length < 2 ^ (prefixWord ++ tailWord_2787948).sum := by decide
  have hdescent : baseEnd_2787948 < baseStart_2787948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787991 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 3, 5]
def baseStart_2787991 : Nat := 118140960795 + 2787991 * 2 ^ 59
def prefixEnd_2787991 : Nat := 4983230072969 + 3 ^ 40 * 2787991 * 2
def baseEnd_2787991 : Nat := 954386295606204470727179

theorem tailTrace_2787991 : CollatzResearch.WordTrace tailWord_2787991 prefixEnd_2787991 954386295606204470727179 := by
  unfold tailWord_2787991
  simp only [CollatzResearch.WordTrace]
  refine ⟨101686385642592232799595827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67790923761728155199730551 101686385642592232799595827)
  ·
    refine ⟨152529578463888349199393741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101686385642592232799595827 152529578463888349199393741)
    ·
      refine ⟨57198591923958130949772653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152529578463888349199393741 57198591923958130949772653)
      ·
        refine ⟨21449471971484299106164745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57198591923958130949772653 21449471971484299106164745)
        ·
          refine ⟨16087103978613224329623559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21449471971484299106164745 16087103978613224329623559)
          ·
            refine ⟨24130655967919836494435339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16087103978613224329623559 24130655967919836494435339)
            ·
              refine ⟨36195983951879754741653009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24130655967919836494435339 36195983951879754741653009)
              ·
                refine ⟨27146987963909816056239757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36195983951879754741653009 27146987963909816056239757)
                ·
                  refine ⟨10180120486466181021089909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27146987963909816056239757 10180120486466181021089909)
                  ·
                    refine ⟨954386295606204470727179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10180120486466181021089909 954386295606204470727179)
                    ·
                      rfl

theorem cell22_2787991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_2787991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787991 prefixEnd_2787991 := by exact prefixLift 2787991
  have htrace : WordTrace (prefixWord ++ tailWord_2787991) baseStart_2787991 baseEnd_2787991 := by
    simpa [prefixWord, tailWord_2787991, baseEnd_2787991] using wordTrace_append hprefix tailTrace_2787991
  have hstable : (prefixWord ++ tailWord_2787991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787991).length < 2 ^ (prefixWord ++ tailWord_2787991).sum := by decide
  have hdescent : baseEnd_2787991 < baseStart_2787991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787993 : List Nat := [1, 2, 1, 2, 1, 2, 5, 4, 4]
def baseStart_2787993 : Nat := 118140960795 + 2787993 * 2 ^ 59
def prefixEnd_2787993 : Nat := 4983230072969 + 3 ^ 40 * 2787993 * 2
def baseEnd_2787993 : Nat := 318128993415692377392391

theorem tailTrace_2787993 : CollatzResearch.WordTrace tailWord_2787993 prefixEnd_2787993 318128993415692377392391 := by
  unfold tailWord_2787993
  simp only [CollatzResearch.WordTrace]
  refine ⟨101686458588584987141168633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67790972392389991427445755 101686458588584987141168633)
  ·
    refine ⟨76264843941438740355876475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101686458588584987141168633 76264843941438740355876475)
    ·
      refine ⟨114397265912158110533814713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76264843941438740355876475 114397265912158110533814713)
      ·
        refine ⟨85797949434118582900361035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114397265912158110533814713 85797949434118582900361035)
        ·
          refine ⟨128696924151177874350541553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85797949434118582900361035 128696924151177874350541553)
          ·
            refine ⟨96522693113383405762906165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128696924151177874350541553 96522693113383405762906165)
            ·
              refine ⟨9049002479379694290272453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96522693113383405762906165 9049002479379694290272453)
              ·
                refine ⟨1696687964883692679426085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9049002479379694290272453 1696687964883692679426085)
                ·
                  refine ⟨318128993415692377392391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1696687964883692679426085 318128993415692377392391)
                  ·
                    rfl

theorem cell22_2787993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 4].length) (baseStart_2787993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2787993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2787993 prefixEnd_2787993 := by exact prefixLift 2787993
  have htrace : WordTrace (prefixWord ++ tailWord_2787993) baseStart_2787993 baseEnd_2787993 := by
    simpa [prefixWord, tailWord_2787993, baseEnd_2787993] using wordTrace_append hprefix tailTrace_2787993
  have hstable : (prefixWord ++ tailWord_2787993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787993).length < 2 ^ (prefixWord ++ tailWord_2787993).sum := by decide
  have hdescent : baseEnd_2787993 < baseStart_2787993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788023 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 1, 6]
def baseStart_2788023 : Nat := 118140960795 + 2788023 * 2 ^ 59
def prefixEnd_2788023 : Nat := 4983230072969 + 3 ^ 40 * 2788023 * 2
def baseEnd_2788023 : Nat := 954397249860167053927081

theorem tailTrace_2788023 : CollatzResearch.WordTrace tailWord_2788023 prefixEnd_2788023 954397249860167053927081 := by
  unfold tailWord_2788023
  simp only [CollatzResearch.WordTrace]
  refine ⟨101687552778476302264760723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67791701852317534843173815 101687552778476302264760723)
  ·
    refine ⟨152531329167714453397141085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101687552778476302264760723 152531329167714453397141085)
    ·
      refine ⟨57199248437892920023927907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152531329167714453397141085 57199248437892920023927907)
      ·
        refine ⟨85798872656839380035891861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57199248437892920023927907 85798872656839380035891861)
        ·
          refine ⟨4021822155789345939182431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85798872656839380035891861 4021822155789345939182431)
          ·
            refine ⟨6032733233684018908773647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021822155789345939182431 6032733233684018908773647)
            ·
              refine ⟨9049099850526028363160471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032733233684018908773647 9049099850526028363160471)
              ·
                refine ⟨13573649775789042544740707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9049099850526028363160471 13573649775789042544740707)
                ·
                  refine ⟨20360474663683563817111061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13573649775789042544740707 20360474663683563817111061)
                  ·
                    refine ⟨954397249860167053927081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20360474663683563817111061 954397249860167053927081)
                    ·
                      rfl

theorem cell22_2788023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_2788023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788023 prefixEnd_2788023 := by exact prefixLift 2788023
  have htrace : WordTrace (prefixWord ++ tailWord_2788023) baseStart_2788023 baseEnd_2788023 := by
    simpa [prefixWord, tailWord_2788023, baseEnd_2788023] using wordTrace_append hprefix tailTrace_2788023
  have hstable : (prefixWord ++ tailWord_2788023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788023).length < 2 ^ (prefixWord ++ tailWord_2788023).sum := by decide
  have hdescent : baseEnd_2788023 < baseStart_2788023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788042 : List Nat := [3, 1, 2, 1, 4, 3, 1, 2, 2, 3]
def baseStart_2788042 : Nat := 118140960795 + 2788042 * 2 ^ 59
def prefixEnd_2788042 : Nat := 4983230072969 + 3 ^ 40 * 2788042 * 2
def baseEnd_2788042 : Nat := 954403753948457337702023

theorem tailTrace_2788042 : CollatzResearch.WordTrace tailWord_2788042 prefixEnd_2788042 954403753948457337702023 := by
  unfold tailWord_2788042
  simp only [CollatzResearch.WordTrace]
  refine ⟨25422061441351867127425595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67792163843604979006468253 25422061441351867127425595)
  ·
    refine ⟨38133092162027800691138393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25422061441351867127425595 38133092162027800691138393)
    ·
      refine ⟨28599819121520850518353795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38133092162027800691138393 28599819121520850518353795)
      ·
        refine ⟨42899728682281275777530693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28599819121520850518353795 42899728682281275777530693)
        ·
          refine ⟨8043699127927739208287005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42899728682281275777530693 8043699127927739208287005)
          ·
            refine ⟨3016387172972902203107627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8043699127927739208287005 3016387172972902203107627)
            ·
              refine ⟨4524580759459353304661441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016387172972902203107627 4524580759459353304661441)
              ·
                refine ⟨3393435569594514978496081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4524580759459353304661441 3393435569594514978496081)
                ·
                  refine ⟨2545076677195886233872061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3393435569594514978496081 2545076677195886233872061)
                  ·
                    refine ⟨954403753948457337702023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2545076677195886233872061 954403753948457337702023)
                    ·
                      rfl

theorem cell22_2788042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_2788042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788042 prefixEnd_2788042 := by exact prefixLift 2788042
  have htrace : WordTrace (prefixWord ++ tailWord_2788042) baseStart_2788042 baseEnd_2788042 := by
    simpa [prefixWord, tailWord_2788042, baseEnd_2788042] using wordTrace_append hprefix tailTrace_2788042
  have hstable : (prefixWord ++ tailWord_2788042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788042).length < 2 ^ (prefixWord ++ tailWord_2788042).sum := by decide
  have hdescent : baseEnd_2788042 < baseStart_2788042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788072 : List Nat := [2, 1, 4, 1, 5, 1, 2, 6]
def baseStart_2788072 : Nat := 118140960795 + 2788072 * 2 ^ 59
def prefixEnd_2788072 : Nat := 4983230072969 + 3 ^ 40 * 2788072 * 2
def baseEnd_2788072 : Nat := 106046002617949695494659

theorem tailTrace_2788072 : CollatzResearch.WordTrace tailWord_2788072 prefixEnd_2788072 106046002617949695494659 := by
  unfold tailWord_2788072
  simp only [CollatzResearch.WordTrace]
  refine ⟨50844669977649391816647235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67792893303532522422196313 50844669977649391816647235)
  ·
    refine ⟨76267004966474087724970853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50844669977649391816647235 76267004966474087724970853)
    ·
      refine ⟨14300063431213891448432035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76267004966474087724970853 14300063431213891448432035)
      ·
        refine ⟨21450095146820837172648053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14300063431213891448432035 21450095146820837172648053)
        ·
          refine ⟨2010946420014453484935755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21450095146820837172648053 2010946420014453484935755)
          ·
            refine ⟨3016419630021680227403633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010946420014453484935755 3016419630021680227403633)
            ·
              refine ⟨2262314722516260170552725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3016419630021680227403633 2262314722516260170552725)
              ·
                refine ⟨106046002617949695494659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2262314722516260170552725 106046002617949695494659)
                ·
                  rfl

theorem cell22_2788072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 6].length) (baseStart_2788072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788072 prefixEnd_2788072 := by exact prefixLift 2788072
  have htrace : WordTrace (prefixWord ++ tailWord_2788072) baseStart_2788072 baseEnd_2788072 := by
    simpa [prefixWord, tailWord_2788072, baseEnd_2788072] using wordTrace_append hprefix tailTrace_2788072
  have hstable : (prefixWord ++ tailWord_2788072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788072).length < 2 ^ (prefixWord ++ tailWord_2788072).sum := by decide
  have hdescent : baseEnd_2788072 < baseStart_2788072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788104 : List Nat := [2, 1, 3, 2, 2, 3, 3, 2, 1, 3]
def baseStart_2788104 : Nat := 118140960795 + 2788104 * 2 ^ 59
def prefixEnd_2788104 : Nat := 4983230072969 + 3 ^ 40 * 2788104 * 2
def baseEnd_2788104 : Nat := 954424977815509842651833

theorem tailTrace_2788104 : CollatzResearch.WordTrace tailWord_2788104 prefixEnd_2788104 954424977815509842651833 := by
  unfold tailWord_2788104
  simp only [CollatzResearch.WordTrace]
  refine ⟨50845253545591426549229683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67793671394121902065639577 50845253545591426549229683)
  ·
    refine ⟨76267880318387139823844525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50845253545591426549229683 76267880318387139823844525)
    ·
      refine ⟨28600455119395177433941697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76267880318387139823844525 28600455119395177433941697)
      ·
        refine ⟨21450341339546383075456273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28600455119395177433941697 21450341339546383075456273)
        ·
          refine ⟨16087756004659787306592205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21450341339546383075456273 16087756004659787306592205)
          ·
            refine ⟨6032908501747420239972077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16087756004659787306592205 6032908501747420239972077)
            ·
              refine ⟨2262340688155282589989529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6032908501747420239972077 2262340688155282589989529)
              ·
                refine ⟨1696755516116461942492147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2262340688155282589989529 1696755516116461942492147)
                ·
                  refine ⟨2545133274174692913738221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696755516116461942492147 2545133274174692913738221)
                  ·
                    refine ⟨954424977815509842651833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2545133274174692913738221 954424977815509842651833)
                    ·
                      rfl

theorem cell22_2788104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_2788104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788104 prefixEnd_2788104 := by exact prefixLift 2788104
  have htrace : WordTrace (prefixWord ++ tailWord_2788104) baseStart_2788104 baseEnd_2788104 := by
    simpa [prefixWord, tailWord_2788104, baseEnd_2788104] using wordTrace_append hprefix tailTrace_2788104
  have hstable : (prefixWord ++ tailWord_2788104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788104).length < 2 ^ (prefixWord ++ tailWord_2788104).sum := by decide
  have hdescent : baseEnd_2788104 < baseStart_2788104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788130 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2788130 : Nat := 118140960795 + 2788130 * 2 ^ 59
def prefixEnd_2788130 : Nat := 4983230072969 + 3 ^ 40 * 2788130 * 2
def baseEnd_2788130 : Nat := 954433878146854441501753

theorem tailTrace_2788130 : CollatzResearch.WordTrace tailWord_2788130 prefixEnd_2788130 954433878146854441501753 := by
  unfold tailWord_2788130
  simp only [CollatzResearch.WordTrace]
  refine ⟨25422863847272164884726461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67794303592725773025937229 25422863847272164884726461)
  ·
    refine ⟨9533573942727061831772423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25422863847272164884726461 9533573942727061831772423)
    ·
      refine ⟨14300360914090592747658635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9533573942727061831772423 14300360914090592747658635)
      ·
        refine ⟨21450541371135889121487953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14300360914090592747658635 21450541371135889121487953)
        ·
          refine ⟨16087906028351916841115965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21450541371135889121487953 16087906028351916841115965)
          ·
            refine ⟨6032964760631968815418487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16087906028351916841115965 6032964760631968815418487)
            ·
              refine ⟨9049447140947953223127731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032964760631968815418487 9049447140947953223127731)
              ·
                refine ⟨13574170711421929834691597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9049447140947953223127731 13574170711421929834691597)
                ·
                  refine ⟨5090314016783223688009349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13574170711421929834691597 5090314016783223688009349)
                  ·
                    refine ⟨954433878146854441501753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5090314016783223688009349 954433878146854441501753)
                    ·
                      rfl

theorem cell22_2788130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2788130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788130 prefixEnd_2788130 := by exact prefixLift 2788130
  have htrace : WordTrace (prefixWord ++ tailWord_2788130) baseStart_2788130 baseEnd_2788130 := by
    simpa [prefixWord, tailWord_2788130, baseEnd_2788130] using wordTrace_append hprefix tailTrace_2788130
  have hstable : (prefixWord ++ tailWord_2788130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788130).length < 2 ^ (prefixWord ++ tailWord_2788130).sum := by decide
  have hdescent : baseEnd_2788130 < baseStart_2788130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788145 : List Nat := [1, 2, 2, 3, 2, 1, 2, 5, 4]
def baseStart_2788145 : Nat := 118140960795 + 2788145 * 2 ^ 59
def prefixEnd_2788145 : Nat := 4983230072969 + 3 ^ 40 * 2788145 * 2
def baseEnd_2788145 : Nat := 318146337651133134125569

theorem tailTrace_2788145 : CollatzResearch.WordTrace tailWord_2788145 prefixEnd_2788145 318146337651133134125569 := by
  unfold tailWord_2788145
  simp only [CollatzResearch.WordTrace]
  refine ⟨101692002484034317100701889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67794668322689544733801259 101692002484034317100701889)
  ·
    refine ⟨76269001863025737825526417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101692002484034317100701889 76269001863025737825526417)
    ·
      refine ⟨57201751397269303369144813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76269001863025737825526417 57201751397269303369144813)
      ·
        refine ⟨21450656773975988763429305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57201751397269303369144813 21450656773975988763429305)
        ·
          refine ⟨16087992580481991572571979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21450656773975988763429305 16087992580481991572571979)
          ·
            refine ⟨24131988870722987358857969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16087992580481991572571979 24131988870722987358857969)
            ·
              refine ⟨18098991653042240519143477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24131988870722987358857969 18098991653042240519143477)
              ·
                refine ⟨1696780467472710048669701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18098991653042240519143477 1696780467472710048669701)
                ·
                  refine ⟨318146337651133134125569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1696780467472710048669701 318146337651133134125569)
                  ·
                    rfl

theorem cell22_2788145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 4].length) (baseStart_2788145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788145 prefixEnd_2788145 := by exact prefixLift 2788145
  have htrace : WordTrace (prefixWord ++ tailWord_2788145) baseStart_2788145 baseEnd_2788145 := by
    simpa [prefixWord, tailWord_2788145, baseEnd_2788145] using wordTrace_append hprefix tailTrace_2788145
  have hstable : (prefixWord ++ tailWord_2788145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788145).length < 2 ^ (prefixWord ++ tailWord_2788145).sum := by decide
  have hdescent : baseEnd_2788145 < baseStart_2788145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788147 : List Nat := [1, 1, 1, 2, 6, 2, 3, 1, 1, 4]
def baseStart_2788147 : Nat := 118140960795 + 2788147 * 2 ^ 59
def prefixEnd_2788147 : Nat := 4983230072969 + 3 ^ 40 * 2788147 * 2
def baseEnd_2788147 : Nat := 954439697594272063826701

theorem tailTrace_2788147 : CollatzResearch.WordTrace tailWord_2788147 prefixEnd_2788147 954439697594272063826701 := by
  unfold tailWord_2788147
  simp only [CollatzResearch.WordTrace]
  refine ⟨101692075430027071442274695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67794716953351380961516463 101692075430027071442274695)
  ·
    refine ⟨152538113145040607163412043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101692075430027071442274695 152538113145040607163412043)
    ·
      refine ⟨228807169717560910745118065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152538113145040607163412043 228807169717560910745118065)
      ·
        refine ⟨171605377288170683058838549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228807169717560910745118065 171605377288170683058838549)
        ·
          refine ⟨8044002060383000768383057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171605377288170683058838549 8044002060383000768383057)
          ·
            refine ⟨6033001545287250576287293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8044002060383000768383057 6033001545287250576287293)
            ·
              refine ⟨2262375579482718966107735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6033001545287250576287293 2262375579482718966107735)
              ·
                refine ⟨3393563369224078449161603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262375579482718966107735 3393563369224078449161603)
                ·
                  refine ⟨5090345053836117673742405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393563369224078449161603 5090345053836117673742405)
                  ·
                    refine ⟨954439697594272063826701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5090345053836117673742405 954439697594272063826701)
                    ·
                      rfl

theorem cell22_2788147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 1, 4].length) (baseStart_2788147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788147 prefixEnd_2788147 := by exact prefixLift 2788147
  have htrace : WordTrace (prefixWord ++ tailWord_2788147) baseStart_2788147 baseEnd_2788147 := by
    simpa [prefixWord, tailWord_2788147, baseEnd_2788147] using wordTrace_append hprefix tailTrace_2788147
  have hstable : (prefixWord ++ tailWord_2788147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788147).length < 2 ^ (prefixWord ++ tailWord_2788147).sum := by decide
  have hdescent : baseEnd_2788147 < baseStart_2788147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788205 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_2788205 : Nat := 118140960795 + 2788205 * 2 ^ 59
def prefixEnd_2788205 : Nat := 4983230072969 + 3 ^ 40 * 2788205 * 2
def baseEnd_2788205 : Nat := 954459552179579245876523

theorem tailTrace_2788205 : CollatzResearch.WordTrace tailWord_2788205 prefixEnd_2788205 954459552179579245876523 := by
  unfold tailWord_2788205
  simp only [CollatzResearch.WordTrace]
  refine ⟨101694190863816947347886069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67796127242544631565257379 101694190863816947347886069)
  ·
    refine ⟨9533830393482838813864319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101694190863816947347886069 9533830393482838813864319)
    ·
      refine ⟨14300745590224258220796479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9533830393482838813864319 14300745590224258220796479)
      ·
        refine ⟨21451118385336387331194719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14300745590224258220796479 21451118385336387331194719)
        ·
          refine ⟨32176677578004580996792079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21451118385336387331194719 32176677578004580996792079)
          ·
            refine ⟨48265016367006871495188119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32176677578004580996792079 48265016367006871495188119)
            ·
              refine ⟨72397524550510307242782179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48265016367006871495188119 72397524550510307242782179)
              ·
                refine ⟨108596286825765460864173269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72397524550510307242782179 108596286825765460864173269)
                ·
                  refine ⟨2545225472478877989004061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 108596286825765460864173269 2545225472478877989004061)
                  ·
                    refine ⟨954459552179579245876523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2545225472478877989004061 954459552179579245876523)
                    ·
                      rfl

theorem cell22_2788205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_2788205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788205 prefixEnd_2788205 := by exact prefixLift 2788205
  have htrace : WordTrace (prefixWord ++ tailWord_2788205) baseStart_2788205 baseEnd_2788205 := by
    simpa [prefixWord, tailWord_2788205, baseEnd_2788205] using wordTrace_append hprefix tailTrace_2788205
  have hstable : (prefixWord ++ tailWord_2788205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788205).length < 2 ^ (prefixWord ++ tailWord_2788205).sum := by decide
  have hdescent : baseEnd_2788205 < baseStart_2788205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788265 : List Nat := [1, 2, 1, 1, 1, 1, 5, 5, 1, 4]
def baseStart_2788265 : Nat := 118140960795 + 2788265 * 2 ^ 59
def prefixEnd_2788265 : Nat := 4983230072969 + 3 ^ 40 * 2788265 * 2
def baseEnd_2788265 : Nat := 954480091405759089376339

theorem tailTrace_2788265 : CollatzResearch.WordTrace tailWord_2788265 prefixEnd_2788265 954480091405759089376339 := by
  unfold tailWord_2788265
  simp only [CollatzResearch.WordTrace]
  refine ⟨101696379243599577595070249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67797586162399718396713499 101696379243599577595070249)
  ·
    refine ⟨76272284432699683196302687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101696379243599577595070249 76272284432699683196302687)
    ·
      refine ⟨114408426649049524794454031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76272284432699683196302687 114408426649049524794454031)
      ·
        refine ⟨171612639973574287191681047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114408426649049524794454031 171612639973574287191681047)
        ·
          refine ⟨257418959960361430787521571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171612639973574287191681047 257418959960361430787521571)
          ·
            refine ⟨386128439940542146181282357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257418959960361430787521571 386128439940542146181282357)
            ·
              refine ⟨36199541244425826204495221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 386128439940542146181282357 36199541244425826204495221)
              ·
                refine ⟨3393706991664921206671427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36199541244425826204495221 3393706991664921206671427)
                ·
                  refine ⟨5090560487497381810007141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393706991664921206671427 5090560487497381810007141)
                  ·
                    refine ⟨954480091405759089376339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5090560487497381810007141 954480091405759089376339)
                    ·
                      rfl

theorem cell22_2788265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_2788265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788265 prefixEnd_2788265 := by exact prefixLift 2788265
  have htrace : WordTrace (prefixWord ++ tailWord_2788265) baseStart_2788265 baseEnd_2788265 := by
    simpa [prefixWord, tailWord_2788265, baseEnd_2788265] using wordTrace_append hprefix tailTrace_2788265
  have hstable : (prefixWord ++ tailWord_2788265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788265).length < 2 ^ (prefixWord ++ tailWord_2788265).sum := by decide
  have hdescent : baseEnd_2788265 < baseStart_2788265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788280 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 6]
def baseStart_2788280 : Nat := 118140960795 + 2788280 * 2 ^ 59
def prefixEnd_2788280 : Nat := 4983230072969 + 3 ^ 40 * 2788280 * 2
def baseEnd_2788280 : Nat := 318161742070768016750431

theorem tailTrace_2788280 : CollatzResearch.WordTrace tailWord_2788280 prefixEnd_2788280 318161742070768016750431 := by
  unfold tailWord_2788280
  simp only [CollatzResearch.WordTrace]
  refine ⟨50848463169272617578433147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67797950892363490104577529 50848463169272617578433147)
  ·
    refine ⟨76272694753908926367649721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50848463169272617578433147 76272694753908926367649721)
    ·
      refine ⟨57204521065431694775737291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76272694753908926367649721 57204521065431694775737291)
      ·
        refine ⟨85806781598147542163605937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57204521065431694775737291 85806781598147542163605937)
        ·
          refine ⟨64355086198610656622704453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85806781598147542163605937 64355086198610656622704453)
          ·
            refine ⟨12066578662239498116757085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64355086198610656622704453 12066578662239498116757085)
            ·
              refine ⟨4524966998339811793783907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12066578662239498116757085 4524966998339811793783907)
              ·
                refine ⟨6787450497509717690675861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524966998339811793783907 6787450497509717690675861)
                ·
                  refine ⟨318161742070768016750431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6787450497509717690675861 318161742070768016750431)
                  ·
                    rfl

theorem cell22_2788280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_2788280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788280 prefixEnd_2788280 := by exact prefixLift 2788280
  have htrace : WordTrace (prefixWord ++ tailWord_2788280) baseStart_2788280 baseEnd_2788280 := by
    simpa [prefixWord, tailWord_2788280, baseEnd_2788280] using wordTrace_append hprefix tailTrace_2788280
  have hstable : (prefixWord ++ tailWord_2788280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788280).length < 2 ^ (prefixWord ++ tailWord_2788280).sum := by decide
  have hdescent : baseEnd_2788280 < baseStart_2788280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788325 : List Nat := [1, 3, 1, 6, 11]
def baseStart_2788325 : Nat := 118140960795 + 2788325 * 2 ^ 59
def prefixEnd_2788325 : Nat := 4983230072969 + 3 ^ 40 * 2788325 * 2
def baseEnd_2788325 : Nat := 3927986134287814538585

theorem tailTrace_2788325 : CollatzResearch.WordTrace tailWord_2788325 prefixEnd_2788325 3927986134287814538585 := by
  unfold tailWord_2788325
  simp only [CollatzResearch.WordTrace]
  refine ⟨101698567623382207842254429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67799045082254805228169619 101698567623382207842254429)
  ·
    refine ⟨38136962858768327940845411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101698567623382207842254429 38136962858768327940845411)
    ·
      refine ⟨57205444288152491911268117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38136962858768327940845411 57205444288152491911268117)
      ·
        refine ⟨2681505201007148058340693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57205444288152491911268117 2681505201007148058340693)
        ·
          refine ⟨3927986134287814538585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2681505201007148058340693 3927986134287814538585)
          ·
            rfl

theorem cell22_2788325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 11].length) (baseStart_2788325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788325 prefixEnd_2788325 := by exact prefixLift 2788325
  have htrace : WordTrace (prefixWord ++ tailWord_2788325) baseStart_2788325 baseEnd_2788325 := by
    simpa [prefixWord, tailWord_2788325, baseEnd_2788325] using wordTrace_append hprefix tailTrace_2788325
  have hstable : (prefixWord ++ tailWord_2788325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788325).length < 2 ^ (prefixWord ++ tailWord_2788325).sum := by decide
  have hdescent : baseEnd_2788325 < baseStart_2788325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788327 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2788327 : Nat := 118140960795 + 2788327 * 2 ^ 59
def prefixEnd_2788327 : Nat := 4983230072969 + 3 ^ 40 * 2788327 * 2
def baseEnd_2788327 : Nat := 954501315272811594326149

theorem tailTrace_2788327 : CollatzResearch.WordTrace tailWord_2788327 prefixEnd_2788327 954501315272811594326149 := by
  unfold tailWord_2788327
  simp only [CollatzResearch.WordTrace]
  refine ⟨101698640569374962183827235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67799093712916641455884823 101698640569374962183827235)
  ·
    refine ⟨152547960854062443275740853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101698640569374962183827235 152547960854062443275740853)
    ·
      refine ⟨14301371330068354057100705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152547960854062443275740853 14301371330068354057100705)
      ·
        refine ⟨10726028497551265542825529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14301371330068354057100705 10726028497551265542825529)
        ·
          refine ⟨8044521373163449157119147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10726028497551265542825529 8044521373163449157119147)
          ·
            refine ⟨12066782059745173735678721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044521373163449157119147 12066782059745173735678721)
            ·
              refine ⟨9050086544808880301759041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12066782059745173735678721 9050086544808880301759041)
              ·
                refine ⟨6787564908606660226319281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9050086544808880301759041 6787564908606660226319281)
                ·
                  refine ⟨5090673681454995169739461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6787564908606660226319281 5090673681454995169739461)
                  ·
                    refine ⟨954501315272811594326149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5090673681454995169739461 954501315272811594326149)
                    ·
                      rfl

theorem cell22_2788327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2788327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788327 prefixEnd_2788327 := by exact prefixLift 2788327
  have htrace : WordTrace (prefixWord ++ tailWord_2788327) baseStart_2788327 baseEnd_2788327 := by
    simpa [prefixWord, tailWord_2788327, baseEnd_2788327] using wordTrace_append hprefix tailTrace_2788327
  have hstable : (prefixWord ++ tailWord_2788327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788327).length < 2 ^ (prefixWord ++ tailWord_2788327).sum := by decide
  have hdescent : baseEnd_2788327 < baseStart_2788327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788342 : List Nat := [5, 1, 1, 1, 3, 1, 3, 7]
def baseStart_2788342 : Nat := 118140960795 + 2788342 * 2 ^ 59
def prefixEnd_2788342 : Nat := 4983230072969 + 3 ^ 40 * 2788342 * 2
def baseEnd_2788342 : Nat := 106056272231039617244567

theorem tailTrace_2788342 : CollatzResearch.WordTrace tailWord_2788342 prefixEnd_2788342 106056272231039617244567 := by
  unfold tailWord_2788342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6356199229020038734101455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67799458442880413163748853 6356199229020038734101455)
  ·
    refine ⟨9534298843530058101152183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6356199229020038734101455 9534298843530058101152183)
    ·
      refine ⟨14301448265295087151728275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9534298843530058101152183 14301448265295087151728275)
      ·
        refine ⟨21452172397942630727592413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14301448265295087151728275 21452172397942630727592413)
        ·
          refine ⟨8044564649228486522847155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21452172397942630727592413 8044564649228486522847155)
          ·
            refine ⟨12066846973842729784270733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044564649228486522847155 12066846973842729784270733)
            ·
              refine ⟨4525067615191023669101525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12066846973842729784270733 4525067615191023669101525)
              ·
                refine ⟨106056272231039617244567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4525067615191023669101525 106056272231039617244567)
                ·
                  rfl

theorem cell22_2788342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_2788342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788342 prefixEnd_2788342 := by exact prefixLift 2788342
  have htrace : WordTrace (prefixWord ++ tailWord_2788342) baseStart_2788342 baseEnd_2788342 := by
    simpa [prefixWord, tailWord_2788342, baseEnd_2788342] using wordTrace_append hprefix tailTrace_2788342
  have hstable : (prefixWord ++ tailWord_2788342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788342).length < 2 ^ (prefixWord ++ tailWord_2788342).sum := by decide
  have hdescent : baseEnd_2788342 < baseStart_2788342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788357 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 3, 3]
def baseStart_2788357 : Nat := 118140960795 + 2788357 * 2 ^ 59
def prefixEnd_2788357 : Nat := 4983230072969 + 3 ^ 40 * 2788357 * 2
def baseEnd_2788357 : Nat := 954511584885901516076057

theorem tailTrace_2788357 : CollatzResearch.WordTrace tailWord_2788357 prefixEnd_2788357 954511584885901516076057 := by
  unfold tailWord_2788357
  simp only [CollatzResearch.WordTrace]
  refine ⟨101699734759266277307419325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67799823172844184871612883 101699734759266277307419325)
  ·
    refine ⟨38137400534724853990282247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101699734759266277307419325 38137400534724853990282247)
    ·
      refine ⟨57206100802087280985423371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38137400534724853990282247 57206100802087280985423371)
      ·
        refine ⟨85809151203130921478135057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57206100802087280985423371 85809151203130921478135057)
        ·
          refine ⟨64356863402348191108601293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85809151203130921478135057 64356863402348191108601293)
          ·
            refine ⟨24133823775880571665725485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64356863402348191108601293 24133823775880571665725485)
            ·
              refine ⟨9050183915955214374647057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24133823775880571665725485 9050183915955214374647057)
              ·
                refine ⟨6787637936966410780985293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9050183915955214374647057 6787637936966410780985293)
                ·
                  refine ⟨2545364226362404042869485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6787637936966410780985293 2545364226362404042869485)
                  ·
                    refine ⟨954511584885901516076057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2545364226362404042869485 954511584885901516076057)
                    ·
                      rfl

theorem cell22_2788357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_2788357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788357 prefixEnd_2788357 := by exact prefixLift 2788357
  have htrace : WordTrace (prefixWord ++ tailWord_2788357) baseStart_2788357 baseEnd_2788357 := by
    simpa [prefixWord, tailWord_2788357, baseEnd_2788357] using wordTrace_append hprefix tailTrace_2788357
  have hstable : (prefixWord ++ tailWord_2788357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788357).length < 2 ^ (prefixWord ++ tailWord_2788357).sum := by decide
  have hdescent : baseEnd_2788357 < baseStart_2788357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788387 : List Nat := [1, 1, 1, 4, 3, 2, 3, 2, 5]
def baseStart_2788387 : Nat := 118140960795 + 2788387 * 2 ^ 59
def prefixEnd_2788387 : Nat := 4983230072969 + 3 ^ 40 * 2788387 * 2
def baseEnd_2788387 : Nat := 318173951499663812608655

theorem tailTrace_2788387 : CollatzResearch.WordTrace tailWord_2788387 prefixEnd_2788387 318173951499663812608655 := by
  unfold tailWord_2788387
  simp only [CollatzResearch.WordTrace]
  refine ⟨101700828949157592431011415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67800552632771728287340943 101700828949157592431011415)
  ·
    refine ⟨152551243423736388646517123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101700828949157592431011415 152551243423736388646517123)
    ·
      refine ⟨228826865135604582969775685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152551243423736388646517123 228826865135604582969775685)
      ·
        refine ⟨42905037212925859306832941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228826865135604582969775685 42905037212925859306832941)
        ·
          refine ⟨16089388954847197240062353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42905037212925859306832941 16089388954847197240062353)
          ·
            refine ⟨12067041716135397930046765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16089388954847197240062353 12067041716135397930046765)
            ·
              refine ⟨4525140643550774223767537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12067041716135397930046765 4525140643550774223767537)
              ·
                refine ⟨3393855482663080667825653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4525140643550774223767537 3393855482663080667825653)
                ·
                  refine ⟨318173951499663812608655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3393855482663080667825653 318173951499663812608655)
                  ·
                    rfl

theorem cell22_2788387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 5].length) (baseStart_2788387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788387 prefixEnd_2788387 := by exact prefixLift 2788387
  have htrace : WordTrace (prefixWord ++ tailWord_2788387) baseStart_2788387 baseEnd_2788387 := by
    simpa [prefixWord, tailWord_2788387, baseEnd_2788387] using wordTrace_append hprefix tailTrace_2788387
  have hstable : (prefixWord ++ tailWord_2788387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788387).length < 2 ^ (prefixWord ++ tailWord_2788387).sum := by decide
  have hdescent : baseEnd_2788387 < baseStart_2788387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788391 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2788391 : Nat := 118140960795 + 2788391 * 2 ^ 59
def prefixEnd_2788391 : Nat := 4983230072969 + 3 ^ 40 * 2788391 * 2
def baseEnd_2788391 : Nat := 954523223780736760725953

theorem tailTrace_2788391 : CollatzResearch.WordTrace tailWord_2788391 prefixEnd_2788391 954523223780736760725953 := by
  unfold tailWord_2788391
  simp only [CollatzResearch.WordTrace]
  refine ⟨101700974841143101114157027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67800649894095400742771351 101700974841143101114157027)
  ·
    refine ⟨152551462261714651671235541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101700974841143101114157027 152551462261714651671235541)
    ·
      refine ⟨3575424896758937148544583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 152551462261714651671235541 3575424896758937148544583)
      ·
        refine ⟨5363137345138405722816875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575424896758937148544583 5363137345138405722816875)
        ·
          refine ⟨8044706017707608584225313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5363137345138405722816875 8044706017707608584225313)
          ·
            refine ⟨6033529513280706438168985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8044706017707608584225313 6033529513280706438168985)
            ·
              refine ⟨4525147134960529828626739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6033529513280706438168985 4525147134960529828626739)
              ·
                refine ⟨6787720702440794742940109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525147134960529828626739 6787720702440794742940109)
                ·
                  refine ⟨2545395263415298028602541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6787720702440794742940109 2545395263415298028602541)
                  ·
                    refine ⟨954523223780736760725953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2545395263415298028602541 954523223780736760725953)
                    ·
                      rfl

theorem cell22_2788391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2788391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788391 prefixEnd_2788391 := by exact prefixLift 2788391
  have htrace : WordTrace (prefixWord ++ tailWord_2788391) baseStart_2788391 baseEnd_2788391 := by
    simpa [prefixWord, tailWord_2788391, baseEnd_2788391] using wordTrace_append hprefix tailTrace_2788391
  have hstable : (prefixWord ++ tailWord_2788391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788391).length < 2 ^ (prefixWord ++ tailWord_2788391).sum := by decide
  have hdescent : baseEnd_2788391 < baseStart_2788391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788434 : List Nat := [3, 2, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_2788434 : Nat := 118140960795 + 2788434 * 2 ^ 59
def prefixEnd_2788434 : Nat := 4983230072969 + 3 ^ 40 * 2788434 * 2
def baseEnd_2788434 : Nat := 954537943559498981900821

theorem tailTrace_2788434 : CollatzResearch.WordTrace tailWord_2788434 prefixEnd_2788434 954537943559498981900821 := by
  unfold tailWord_2788434
  simp only [CollatzResearch.WordTrace]
  refine ⟨25425635794996829864493089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67801695453324879638648237 25425635794996829864493089)
  ·
    refine ⟨19069226846247622398369817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25425635794996829864493089 19069226846247622398369817)
    ·
      refine ⟨14301920134685716798777363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19069226846247622398369817 14301920134685716798777363)
      ·
        refine ⟨21452880202028575198166045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14301920134685716798777363 21452880202028575198166045)
        ·
          refine ⟨8044830075760715699312267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21452880202028575198166045 8044830075760715699312267)
          ·
            refine ⟨12067245113641073548968401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044830075760715699312267 12067245113641073548968401)
            ·
              refine ⟨9050433835230805161726301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12067245113641073548968401 9050433835230805161726301)
              ·
                refine ⟨3393912688211551935647363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9050433835230805161726301 3393912688211551935647363)
                ·
                  refine ⟨5090869032317327903471045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393912688211551935647363 5090869032317327903471045)
                  ·
                    refine ⟨954537943559498981900821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5090869032317327903471045 954537943559498981900821)
                    ·
                      rfl

theorem cell22_2788434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_2788434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788434 prefixEnd_2788434 := by exact prefixLift 2788434
  have htrace : WordTrace (prefixWord ++ tailWord_2788434) baseStart_2788434 baseEnd_2788434 := by
    simpa [prefixWord, tailWord_2788434, baseEnd_2788434] using wordTrace_append hprefix tailTrace_2788434
  have hstable : (prefixWord ++ tailWord_2788434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788434).length < 2 ^ (prefixWord ++ tailWord_2788434).sum := by decide
  have hdescent : baseEnd_2788434 < baseStart_2788434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788447 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 4, 3]
def baseStart_2788447 : Nat := 118140960795 + 2788447 * 2 ^ 59
def prefixEnd_2788447 : Nat := 4983230072969 + 3 ^ 40 * 2788447 * 2
def baseEnd_2788447 : Nat := 954542393725171281325781

theorem tailTrace_2788447 : CollatzResearch.WordTrace tailWord_2788447 prefixEnd_2788447 954542393725171281325781 := by
  unfold tailWord_2788447
  simp only [CollatzResearch.WordTrace]
  refine ⟨101703017328940222678195595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67802011552626815118797063 101703017328940222678195595)
  ·
    refine ⟨152554525993410334017293393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101703017328940222678195595 152554525993410334017293393)
    ·
      refine ⟨114415894495057750512970045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152554525993410334017293393 114415894495057750512970045)
      ·
        refine ⟨42905960435646656442363767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114415894495057750512970045 42905960435646656442363767)
        ·
          refine ⟨64358940653469984663545651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42905960435646656442363767 64358940653469984663545651)
          ·
            refine ⟨96538410980204976995318477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64358940653469984663545651 96538410980204976995318477)
            ·
              refine ⟨36201904117576866373244429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96538410980204976995318477 36201904117576866373244429)
              ·
                refine ⟨13575714044091324889966661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36201904117576866373244429 13575714044091324889966661)
                ·
                  refine ⟨2545446383267123416868749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13575714044091324889966661 2545446383267123416868749)
                  ·
                    refine ⟨954542393725171281325781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2545446383267123416868749 954542393725171281325781)
                    ·
                      rfl

theorem cell22_2788447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 3].length) (baseStart_2788447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788447 prefixEnd_2788447 := by exact prefixLift 2788447
  have htrace : WordTrace (prefixWord ++ tailWord_2788447) baseStart_2788447 baseEnd_2788447 := by
    simpa [prefixWord, tailWord_2788447, baseEnd_2788447] using wordTrace_append hprefix tailTrace_2788447
  have hstable : (prefixWord ++ tailWord_2788447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788447).length < 2 ^ (prefixWord ++ tailWord_2788447).sum := by decide
  have hdescent : baseEnd_2788447 < baseStart_2788447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788464 : List Nat := [2, 1, 1, 1, 5, 1, 3, 3, 2, 3]
def baseStart_2788464 : Nat := 118140960795 + 2788464 * 2 ^ 59
def prefixEnd_2788464 : Nat := 4983230072969 + 3 ^ 40 * 2788464 * 2
def baseEnd_2788464 : Nat := 954548213172588903650729

theorem tailTrace_2788464 : CollatzResearch.WordTrace tailWord_2788464 prefixEnd_2788464 954548213172588903650729 := by
  unfold tailWord_2788464
  simp only [CollatzResearch.WordTrace]
  refine ⟨50851818684939317290782223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67802424913252423054376297 50851818684939317290782223)
  ·
    refine ⟨76277728027408975936173335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50851818684939317290782223 76277728027408975936173335)
    ·
      refine ⟨114416592041113463904260003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76277728027408975936173335 114416592041113463904260003)
      ·
        refine ⟨171624888061670195856390005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114416592041113463904260003 171624888061670195856390005)
        ·
          refine ⟨16089833255781580861536563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171624888061670195856390005 16089833255781580861536563)
          ·
            refine ⟨24134749883672371292304845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16089833255781580861536563 24134749883672371292304845)
            ·
              refine ⟨9050531206377139234614317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24134749883672371292304845 9050531206377139234614317)
              ·
                refine ⟨3393949202391427212980369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9050531206377139234614317 3393949202391427212980369)
                ·
                  refine ⟨2545461901793570409735277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3393949202391427212980369 2545461901793570409735277)
                  ·
                    refine ⟨954548213172588903650729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2545461901793570409735277 954548213172588903650729)
                    ·
                      rfl

theorem cell22_2788464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 2, 3].length) (baseStart_2788464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788464 prefixEnd_2788464 := by exact prefixLift 2788464
  have htrace : WordTrace (prefixWord ++ tailWord_2788464) baseStart_2788464 baseEnd_2788464 := by
    simpa [prefixWord, tailWord_2788464, baseEnd_2788464] using wordTrace_append hprefix tailTrace_2788464
  have hstable : (prefixWord ++ tailWord_2788464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788464).length < 2 ^ (prefixWord ++ tailWord_2788464).sum := by decide
  have hdescent : baseEnd_2788464 < baseStart_2788464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788475 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 2, 7]
def baseStart_2788475 : Nat := 118140960795 + 2788475 * 2 ^ 59
def prefixEnd_2788475 : Nat := 4983230072969 + 3 ^ 40 * 2788475 * 2
def baseEnd_2788475 : Nat := 954551978697388541625695

theorem tailTrace_2788475 : CollatzResearch.WordTrace tailWord_2788475 prefixEnd_2788475 954551978697388541625695 := by
  unfold tailWord_2788475
  simp only [CollatzResearch.WordTrace]
  refine ⟨101704038572838783460214879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67802692381892522306809919 101704038572838783460214879)
  ·
    refine ⟨152556057859258175190322319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101704038572838783460214879 152556057859258175190322319)
    ·
      refine ⟨228834086788887262785483479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152556057859258175190322319 228834086788887262785483479)
      ·
        refine ⟨343251130183330894178225219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228834086788887262785483479 343251130183330894178225219)
        ·
          refine ⟨514876695274996341267337829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343251130183330894178225219 514876695274996341267337829)
          ·
            refine ⟨96539380364061813987625843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 514876695274996341267337829 96539380364061813987625843)
            ·
              refine ⟨144809070546092720981438765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96539380364061813987625843 144809070546092720981438765)
              ·
                refine ⟨54303401454784770368039537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144809070546092720981438765 54303401454784770368039537)
                ·
                  refine ⟨40727551091088577776029653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54303401454784770368039537 40727551091088577776029653)
                  ·
                    refine ⟨954551978697388541625695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40727551091088577776029653 954551978697388541625695)
                    ·
                      rfl

theorem cell22_2788475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_2788475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788475 prefixEnd_2788475 := by exact prefixLift 2788475
  have htrace : WordTrace (prefixWord ++ tailWord_2788475) baseStart_2788475 baseEnd_2788475 := by
    simpa [prefixWord, tailWord_2788475, baseEnd_2788475] using wordTrace_append hprefix tailTrace_2788475
  have hstable : (prefixWord ++ tailWord_2788475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788475).length < 2 ^ (prefixWord ++ tailWord_2788475).sum := by decide
  have hdescent : baseEnd_2788475 < baseStart_2788475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788509 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2788509 : Nat := 118140960795 + 2788509 * 2 ^ 59
def prefixEnd_2788509 : Nat := 4983230072969 + 3 ^ 40 * 2788509 * 2
def baseEnd_2788509 : Nat := 954563617592223786275591

theorem tailTrace_2788509 : CollatzResearch.WordTrace tailWord_2788509 prefixEnd_2788509 954563617592223786275591 := by
  unfold tailWord_2788509
  simp only [CollatzResearch.WordTrace]
  refine ⟨101705278654715607266952581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67803519103143738177968387 101705278654715607266952581)
  ·
    refine ⟨19069739747759176362553609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101705278654715607266952581 19069739747759176362553609)
    ·
      refine ⟨14302304810819382271915207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19069739747759176362553609 14302304810819382271915207)
      ·
        refine ⟨21453457216229073407872811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14302304810819382271915207 21453457216229073407872811)
        ·
          refine ⟨32180185824343610111809217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21453457216229073407872811 32180185824343610111809217)
          ·
            refine ⟨24135139368257707583856913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32180185824343610111809217 24135139368257707583856913)
            ·
              refine ⟨18101354526193280687892685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24135139368257707583856913 18101354526193280687892685)
              ·
                refine ⟨6788007947322480257959757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18101354526193280687892685 6788007947322480257959757)
                ·
                  refine ⟨2545502980245930096734909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6788007947322480257959757 2545502980245930096734909)
                  ·
                    refine ⟨954563617592223786275591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2545502980245930096734909 954563617592223786275591)
                    ·
                      rfl

theorem cell22_2788509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2788509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788509 prefixEnd_2788509 := by exact prefixLift 2788509
  have htrace : WordTrace (prefixWord ++ tailWord_2788509) baseStart_2788509 baseEnd_2788509 := by
    simpa [prefixWord, tailWord_2788509, baseEnd_2788509] using wordTrace_append hprefix tailTrace_2788509
  have hstable : (prefixWord ++ tailWord_2788509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788509).length < 2 ^ (prefixWord ++ tailWord_2788509).sum := by decide
  have hdescent : baseEnd_2788509 < baseStart_2788509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788511 : List Nat := [1, 1, 2, 6, 3, 1, 1, 7]
def baseStart_2788511 : Nat := 118140960795 + 2788511 * 2 ^ 59
def prefixEnd_2788511 : Nat := 4983230072969 + 3 ^ 40 * 2788511 * 2
def baseEnd_2788511 : Nat := 106062700248121827525065

theorem tailTrace_2788511 : CollatzResearch.WordTrace tailWord_2788511 prefixEnd_2788511 106062700248121827525065 := by
  unfold tailWord_2788511
  simp only [CollatzResearch.WordTrace]
  refine ⟨101705351600708361608525387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67803567733805574405683591 101705351600708361608525387)
  ·
    refine ⟨152558027401062542412788081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101705351600708361608525387 152558027401062542412788081)
    ·
      refine ⟨114418520550796906809591061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152558027401062542412788081 114418520550796906809591061)
      ·
        refine ⟨5363368150818605006699581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114418520550796906809591061 5363368150818605006699581)
        ·
          refine ⟨2011263056556976877512343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5363368150818605006699581 2011263056556976877512343)
          ·
            refine ⟨3016894584835465316268515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011263056556976877512343 3016894584835465316268515)
            ·
              refine ⟨4525341877253197974402773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016894584835465316268515 4525341877253197974402773)
              ·
                refine ⟨106062700248121827525065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4525341877253197974402773 106062700248121827525065)
                ·
                  rfl

theorem cell22_2788511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 7].length) (baseStart_2788511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788511 prefixEnd_2788511 := by exact prefixLift 2788511
  have htrace : WordTrace (prefixWord ++ tailWord_2788511) baseStart_2788511 baseEnd_2788511 := by
    simpa [prefixWord, tailWord_2788511, baseEnd_2788511] using wordTrace_append hprefix tailTrace_2788511
  have hstable : (prefixWord ++ tailWord_2788511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788511).length < 2 ^ (prefixWord ++ tailWord_2788511).sum := by decide
  have hdescent : baseEnd_2788511 < baseStart_2788511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788567 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 6]
def baseStart_2788567 : Nat := 118140960795 + 2788567 * 2 ^ 59
def prefixEnd_2788567 : Nat := 4983230072969 + 3 ^ 40 * 2788567 * 2
def baseEnd_2788567 : Nat := 318194490725843656108471

theorem tailTrace_2788567 : CollatzResearch.WordTrace tailWord_2788567 prefixEnd_2788567 318194490725843656108471 := by
  unfold tailWord_2788567
  simp only [CollatzResearch.WordTrace]
  refine ⟨101707394088505483172563955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67804929392336988781709303 101707394088505483172563955)
  ·
    refine ⟨152561091132758224758845933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101707394088505483172563955 152561091132758224758845933)
    ·
      refine ⟨57210409174784334284567225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152561091132758224758845933 57210409174784334284567225)
      ·
        refine ⟨42907806881088250713425419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57210409174784334284567225 42907806881088250713425419)
        ·
          refine ⟨64361710321632376070138129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42907806881088250713425419 64361710321632376070138129)
          ·
            refine ⟨48271282741224282052603597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64361710321632376070138129 48271282741224282052603597)
            ·
              refine ⟨18101731027959105769726349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48271282741224282052603597 18101731027959105769726349)
              ·
                refine ⟨6788149135484664663647381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18101731027959105769726349 6788149135484664663647381)
                ·
                  refine ⟨318194490725843656108471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6788149135484664663647381 318194490725843656108471)
                  ·
                    rfl

theorem cell22_2788567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 6].length) (baseStart_2788567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788567 prefixEnd_2788567 := by exact prefixLift 2788567
  have htrace : WordTrace (prefixWord ++ tailWord_2788567) baseStart_2788567 baseEnd_2788567 := by
    simpa [prefixWord, tailWord_2788567, baseEnd_2788567] using wordTrace_append hprefix tailTrace_2788567
  have hstable : (prefixWord ++ tailWord_2788567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788567).length < 2 ^ (prefixWord ++ tailWord_2788567).sum := by decide
  have hdescent : baseEnd_2788567 < baseStart_2788567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788573 : List Nat := [1, 4, 3, 2, 2, 1, 3, 1, 5]
def baseStart_2788573 : Nat := 118140960795 + 2788573 * 2 ^ 59
def prefixEnd_2788573 : Nat := 4983230072969 + 3 ^ 40 * 2788573 * 2
def baseEnd_2788573 : Nat := 318195175366716317558465

theorem tailTrace_2788573 : CollatzResearch.WordTrace tailWord_2788573 prefixEnd_2788573 318195175366716317558465 := by
  unfold tailWord_2788573
  simp only [CollatzResearch.WordTrace]
  refine ⟨101707612926483746197282373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67805075284322497464854915 101707612926483746197282373)
  ·
    refine ⟨19070177423715702411990445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101707612926483746197282373 19070177423715702411990445)
    ·
      refine ⟨7151316533893388404496417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19070177423715702411990445 7151316533893388404496417)
      ·
        refine ⟨5363487400420041303372313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7151316533893388404496417 5363487400420041303372313)
        ·
          refine ⟨4022615550315030977529235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5363487400420041303372313 4022615550315030977529235)
          ·
            refine ⟨6033923325472546466293853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4022615550315030977529235 6033923325472546466293853)
            ·
              refine ⟨2262721247052204924860195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6033923325472546466293853 2262721247052204924860195)
              ·
                refine ⟨3394081870578307387290293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262721247052204924860195 3394081870578307387290293)
                ·
                  refine ⟨318195175366716317558465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3394081870578307387290293 318195175366716317558465)
                  ·
                    rfl

theorem cell22_2788573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_2788573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788573 prefixEnd_2788573 := by exact prefixLift 2788573
  have htrace : WordTrace (prefixWord ++ tailWord_2788573) baseStart_2788573 baseEnd_2788573 := by
    simpa [prefixWord, tailWord_2788573, baseEnd_2788573] using wordTrace_append hprefix tailTrace_2788573
  have hstable : (prefixWord ++ tailWord_2788573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788573).length < 2 ^ (prefixWord ++ tailWord_2788573).sum := by decide
  have hdescent : baseEnd_2788573 < baseStart_2788573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788586 : List Nat := [3, 1, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_2788586 : Nat := 118140960795 + 2788586 * 2 ^ 59
def prefixEnd_2788586 : Nat := 4983230072969 + 3 ^ 40 * 2788586 * 2
def baseEnd_2788586 : Nat := 954589976265821252100355

theorem tailTrace_2788586 : CollatzResearch.WordTrace tailWord_2788586 prefixEnd_2788586 954589976265821252100355 := by
  unfold tailWord_2788586
  simp only [CollatzResearch.WordTrace]
  refine ⟨25427021768859162354376403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67805391383624432945003741 25427021768859162354376403)
  ·
    refine ⟨38140532653288743531564605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25427021768859162354376403 38140532653288743531564605)
    ·
      refine ⟨14302699744983278824336727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38140532653288743531564605 14302699744983278824336727)
      ·
        refine ⟨21454049617474918236505091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14302699744983278824336727 21454049617474918236505091)
        ·
          refine ⟨32181074426212377354757637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21454049617474918236505091 32181074426212377354757637)
          ·
            refine ⟨6033951454914820754017057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32181074426212377354757637 6033951454914820754017057)
            ·
              refine ⟨4525463591186115565512793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6033951454914820754017057 4525463591186115565512793)
              ·
                refine ⟨3394097693389586674134595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4525463591186115565512793 3394097693389586674134595)
                ·
                  refine ⟨5091146540084380011201893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3394097693389586674134595 5091146540084380011201893)
                  ·
                    refine ⟨954589976265821252100355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5091146540084380011201893 954589976265821252100355)
                    ·
                      rfl

theorem cell22_2788586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_2788586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788586 prefixEnd_2788586 := by exact prefixLift 2788586
  have htrace : WordTrace (prefixWord ++ tailWord_2788586) baseStart_2788586 baseEnd_2788586 := by
    simpa [prefixWord, tailWord_2788586, baseEnd_2788586] using wordTrace_append hprefix tailTrace_2788586
  have hstable : (prefixWord ++ tailWord_2788586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788586).length < 2 ^ (prefixWord ++ tailWord_2788586).sum := by decide
  have hdescent : baseEnd_2788586 < baseStart_2788586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788676 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2788676 : Nat := 118140960795 + 2788676 * 2 ^ 59
def prefixEnd_2788676 : Nat := 4983230072969 + 3 ^ 40 * 2788676 * 2
def baseEnd_2788676 : Nat := 954620785105091017350079

theorem tailTrace_2788676 : CollatzResearch.WordTrace tailWord_2788676 prefixEnd_2788676 954620785105091017350079 := by
  unfold tailWord_2788676
  simp only [CollatzResearch.WordTrace]
  refine ⟨50855684822555297394140941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67807579763407063192187921 50855684822555297394140941)
  ·
    refine ⟨19070881808458236522802853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50855684822555297394140941 19070881808458236522802853)
    ·
      refine ⟨3575790339085919348025535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19070881808458236522802853 3575790339085919348025535)
      ·
        refine ⟨5363685508628879022038303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575790339085919348025535 5363685508628879022038303)
        ·
          refine ⟨8045528262943318533057455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5363685508628879022038303 8045528262943318533057455)
          ·
            refine ⟨12068292394414977799586183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8045528262943318533057455 12068292394414977799586183)
            ·
              refine ⟨18102438591622466699379275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12068292394414977799586183 18102438591622466699379275)
              ·
                refine ⟨27153657887433700049068913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18102438591622466699379275 27153657887433700049068913)
                ·
                  refine ⟨20365243415575275036801685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27153657887433700049068913 20365243415575275036801685)
                  ·
                    refine ⟨954620785105091017350079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20365243415575275036801685 954620785105091017350079)
                    ·
                      rfl

theorem cell22_2788676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2788676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788676 prefixEnd_2788676 := by exact prefixLift 2788676
  have htrace : WordTrace (prefixWord ++ tailWord_2788676) baseStart_2788676 baseEnd_2788676 := by
    simpa [prefixWord, tailWord_2788676, baseEnd_2788676] using wordTrace_append hprefix tailTrace_2788676
  have hstable : (prefixWord ++ tailWord_2788676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788676).length < 2 ^ (prefixWord ++ tailWord_2788676).sum := by decide
  have hdescent : baseEnd_2788676 < baseStart_2788676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788689 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 2, 5]
def baseStart_2788689 : Nat := 118140960795 + 2788689 * 2 ^ 59
def prefixEnd_2788689 : Nat := 4983230072969 + 3 ^ 40 * 2788689 * 2
def baseEnd_2788689 : Nat := 954625235270763316775039

theorem tailTrace_2788689 : CollatzResearch.WordTrace tailWord_2788689 prefixEnd_2788689 954625235270763316775039 := by
  unfold tailWord_2788689
  simp only [CollatzResearch.WordTrace]
  refine ⟨101711843794063498008505121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67807895862708998672336747 101711843794063498008505121)
  ·
    refine ⟨76283882845547623506378841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101711843794063498008505121 76283882845547623506378841)
    ·
      refine ⟨57212912134160717629784131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76283882845547623506378841 57212912134160717629784131)
      ·
        refine ⟨85819368201241076444676197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57212912134160717629784131 85819368201241076444676197)
        ·
          refine ⟨16091131537732701833376787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85819368201241076444676197 16091131537732701833376787)
          ·
            refine ⟨24136697306599052750065181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16091131537732701833376787 24136697306599052750065181)
            ·
              refine ⟨9051261489974644781274443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24136697306599052750065181 9051261489974644781274443)
              ·
                refine ⟨13576892234961967171911665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9051261489974644781274443 13576892234961967171911665)
                ·
                  refine ⟨10182669176221475378933749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13576892234961967171911665 10182669176221475378933749)
                  ·
                    refine ⟨954625235270763316775039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10182669176221475378933749 954625235270763316775039)
                    ·
                      rfl

theorem cell22_2788689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_2788689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788689 prefixEnd_2788689 := by exact prefixLift 2788689
  have htrace : WordTrace (prefixWord ++ tailWord_2788689) baseStart_2788689 baseEnd_2788689 := by
    simpa [prefixWord, tailWord_2788689, baseEnd_2788689] using wordTrace_append hprefix tailTrace_2788689
  have hstable : (prefixWord ++ tailWord_2788689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788689).length < 2 ^ (prefixWord ++ tailWord_2788689).sum := by decide
  have hdescent : baseEnd_2788689 < baseStart_2788689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788725 : List Nat := [1, 3, 4, 1, 4, 1, 1, 2, 5]
def baseStart_2788725 : Nat := 118140960795 + 2788725 * 2 ^ 59
def prefixEnd_2788725 : Nat := 4983230072969 + 3 ^ 40 * 2788725 * 2
def baseEnd_2788725 : Nat := 318212519602157074291643

theorem tailTrace_2788725 : CollatzResearch.WordTrace tailWord_2788725 prefixEnd_2788725 318212519602157074291643 := by
  unfold tailWord_2788725
  simp only [CollatzResearch.WordTrace]
  refine ⟨101713156821933076156815629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67808771214622050771210419 101713156821933076156815629)
  ·
    refine ⟨38142433808224903558805861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101713156821933076156815629 38142433808224903558805861)
    ·
      refine ⟨7151706339042169417276099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38142433808224903558805861 7151706339042169417276099)
      ·
        refine ⟨10727559508563254125914149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7151706339042169417276099 10727559508563254125914149)
        ·
          refine ⟨2011417407855610148608903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10727559508563254125914149 2011417407855610148608903)
          ·
            refine ⟨3017126111783415222913355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011417407855610148608903 3017126111783415222913355)
            ·
              refine ⟨4525689167675122834370033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3017126111783415222913355 4525689167675122834370033)
              ·
                refine ⟨3394266875756342125777525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4525689167675122834370033 3394266875756342125777525)
                ·
                  refine ⟨318212519602157074291643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3394266875756342125777525 318212519602157074291643)
                  ·
                    rfl

theorem cell22_2788725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_2788725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788725 prefixEnd_2788725 := by exact prefixLift 2788725
  have htrace : WordTrace (prefixWord ++ tailWord_2788725) baseStart_2788725 baseEnd_2788725 := by
    simpa [prefixWord, tailWord_2788725, baseEnd_2788725] using wordTrace_append hprefix tailTrace_2788725
  have hstable : (prefixWord ++ tailWord_2788725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788725).length < 2 ^ (prefixWord ++ tailWord_2788725).sum := by decide
  have hdescent : baseEnd_2788725 < baseStart_2788725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788770 : List Nat := [3, 3, 1, 2, 1, 4, 1, 3, 4]
def baseStart_2788770 : Nat := 118140960795 + 2788770 * 2 ^ 59
def prefixEnd_2788770 : Nat := 4983230072969 + 3 ^ 40 * 2788770 * 2
def baseEnd_2788770 : Nat := 318217654408702035166597

theorem tailTrace_2788770 : CollatzResearch.WordTrace tailWord_2788770 prefixEnd_2788770 318217654408702035166597 := by
  unfold tailWord_2788770
  simp only [CollatzResearch.WordTrace]
  refine ⟨25428699526692512210550941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67809865404513365894802509 25428699526692512210550941)
  ·
    refine ⟨9535762322509692078956603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25428699526692512210550941 9535762322509692078956603)
    ·
      refine ⟨14303643483764538118434905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9535762322509692078956603 14303643483764538118434905)
      ·
        refine ⟨10727732612823403588826179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14303643483764538118434905 10727732612823403588826179)
        ·
          refine ⟨16091598919235105383239269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10727732612823403588826179 16091598919235105383239269)
          ·
            refine ⟨3017174797356582259357363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16091598919235105383239269 3017174797356582259357363)
            ·
              refine ⟨4525762196034873389036045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3017174797356582259357363 4525762196034873389036045)
              ·
                refine ⟨1697160823513077520888517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4525762196034873389036045 1697160823513077520888517)
                ·
                  refine ⟨318217654408702035166597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1697160823513077520888517 318217654408702035166597)
                  ·
                    rfl

theorem cell22_2788770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_2788770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788770 prefixEnd_2788770 := by exact prefixLift 2788770
  have htrace : WordTrace (prefixWord ++ tailWord_2788770) baseStart_2788770 baseEnd_2788770 := by
    simpa [prefixWord, tailWord_2788770, baseEnd_2788770] using wordTrace_append hprefix tailTrace_2788770
  have hstable : (prefixWord ++ tailWord_2788770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788770).length < 2 ^ (prefixWord ++ tailWord_2788770).sum := by decide
  have hdescent : baseEnd_2788770 < baseStart_2788770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788781 : List Nat := [1, 5, 2, 2, 1, 1, 10]
def baseStart_2788781 : Nat := 118140960795 + 2788781 * 2 ^ 59
def prefixEnd_2788781 : Nat := 4983230072969 + 3 ^ 40 * 2788781 * 2
def baseEnd_2788781 : Nat := 35357656620403916424991

theorem tailTrace_2788781 : CollatzResearch.WordTrace tailWord_2788781 prefixEnd_2788781 35357656620403916424991 := by
  unfold tailWord_2788781
  simp only [CollatzResearch.WordTrace]
  refine ⟨101715199309730197720854197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67810132873153465147236131 101715199309730197720854197)
  ·
    refine ⟨9535799935287206036330081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101715199309730197720854197 9535799935287206036330081)
    ·
      refine ⟨7151849951465404527247561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9535799935287206036330081 7151849951465404527247561)
      ·
        refine ⟨5363887463599053395435671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7151849951465404527247561 5363887463599053395435671)
        ·
          refine ⟨8045831195398580093153507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5363887463599053395435671 8045831195398580093153507)
          ·
            refine ⟨12068746793097870139730261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8045831195398580093153507 12068746793097870139730261)
            ·
              refine ⟨35357656620403916424991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12068746793097870139730261 35357656620403916424991)
              ·
                rfl

theorem cell22_2788781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 10].length) (baseStart_2788781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788781 prefixEnd_2788781 := by exact prefixLift 2788781
  have htrace : WordTrace (prefixWord ++ tailWord_2788781) baseStart_2788781 baseEnd_2788781 := by
    simpa [prefixWord, tailWord_2788781, baseEnd_2788781] using wordTrace_append hprefix tailTrace_2788781
  have hstable : (prefixWord ++ tailWord_2788781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788781).length < 2 ^ (prefixWord ++ tailWord_2788781).sum := by decide
  have hdescent : baseEnd_2788781 < baseStart_2788781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788856 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 3, 4]
def baseStart_2788856 : Nat := 118140960795 + 2788856 * 2 ^ 59
def prefixEnd_2788856 : Nat := 4983230072969 + 3 ^ 40 * 2788856 * 2
def baseEnd_2788856 : Nat := 954682402783630547849527

theorem tailTrace_2788856 : CollatzResearch.WordTrace tailWord_2788856 prefixEnd_2788856 954682402783630547849527 := by
  unfold tailWord_2788856
  simp only [CollatzResearch.WordTrace]
  refine ⟨50858967392229242764917211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67811956522972323686556281 50858967392229242764917211)
  ·
    refine ⟨76288451088343864147375817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50858967392229242764917211 76288451088343864147375817)
    ·
      refine ⟨57216338316257898110531863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76288451088343864147375817 57216338316257898110531863)
      ·
        refine ⟨85824507474386847165797795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57216338316257898110531863 85824507474386847165797795)
        ·
          refine ⟨128736761211580270748696693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85824507474386847165797795 128736761211580270748696693)
          ·
            refine ⟨12069071363585650382690315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128736761211580270748696693 12069071363585650382690315)
            ·
              refine ⟨18103607045378475574035473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12069071363585650382690315 18103607045378475574035473)
              ·
                refine ⟨13577705284033856680526605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18103607045378475574035473 13577705284033856680526605)
                ·
                  refine ⟨5091639481512696255197477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13577705284033856680526605 5091639481512696255197477)
                  ·
                    refine ⟨954682402783630547849527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5091639481512696255197477 954682402783630547849527)
                    ·
                      rfl

theorem cell22_2788856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_2788856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788856 prefixEnd_2788856 := by exact prefixLift 2788856
  have htrace : WordTrace (prefixWord ++ tailWord_2788856) baseStart_2788856 baseEnd_2788856 := by
    simpa [prefixWord, tailWord_2788856, baseEnd_2788856] using wordTrace_append hprefix tailTrace_2788856
  have hstable : (prefixWord ++ tailWord_2788856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788856).length < 2 ^ (prefixWord ++ tailWord_2788856).sum := by decide
  have hdescent : baseEnd_2788856 < baseStart_2788856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788871 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 8]
def baseStart_2788871 : Nat := 118140960795 + 2788871 * 2 ^ 59
def prefixEnd_2788871 : Nat := 4983230072969 + 3 ^ 40 * 2788871 * 2
def baseEnd_2788871 : Nat := 318229179196725169574827

theorem tailTrace_2788871 : CollatzResearch.WordTrace tailWord_2788871 prefixEnd_2788871 318229179196725169574827 := by
  unfold tailWord_2788871
  simp only [CollatzResearch.WordTrace]
  refine ⟨101718481879404143091630467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67812321252936095394420311 101718481879404143091630467)
  ·
    refine ⟨152577722819106214637445701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101718481879404143091630467 152577722819106214637445701)
    ·
      refine ⟨28608323028582415244521069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152577722819106214637445701 28608323028582415244521069)
      ·
        refine ⟨10728121135718405716695401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28608323028582415244521069 10728121135718405716695401)
        ·
          refine ⟨8046090851788804287521551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10728121135718405716695401 8046090851788804287521551)
          ·
            refine ⟨12069136277683206431282327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8046090851788804287521551 12069136277683206431282327)
            ·
              refine ⟨18103704416524809646923491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12069136277683206431282327 18103704416524809646923491)
              ·
                refine ⟨27155556624787214470385237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18103704416524809646923491 27155556624787214470385237)
                ·
                  refine ⟨318229179196725169574827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27155556624787214470385237 318229179196725169574827)
                  ·
                    rfl

theorem cell22_2788871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 8].length) (baseStart_2788871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788871 prefixEnd_2788871 := by exact prefixLift 2788871
  have htrace : WordTrace (prefixWord ++ tailWord_2788871) baseStart_2788871 baseEnd_2788871 := by
    simpa [prefixWord, tailWord_2788871, baseEnd_2788871] using wordTrace_append hprefix tailTrace_2788871
  have hstable : (prefixWord ++ tailWord_2788871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788871).length < 2 ^ (prefixWord ++ tailWord_2788871).sum := by decide
  have hdescent : baseEnd_2788871 < baseStart_2788871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788901 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_2788901 : Nat := 118140960795 + 2788901 * 2 ^ 59
def prefixEnd_2788901 : Nat := 4983230072969 + 3 ^ 40 * 2788901 * 2
def baseEnd_2788901 : Nat := 954697807203265430474389

theorem tailTrace_2788901 : CollatzResearch.WordTrace tailWord_2788901 prefixEnd_2788901 954697807203265430474389 := by
  unfold tailWord_2788901
  simp only [CollatzResearch.WordTrace]
  refine ⟨101719576069295458215222557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67813050712863638810148371 101719576069295458215222557)
  ·
    refine ⟨38144841025985796830708459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101719576069295458215222557 38144841025985796830708459)
    ·
      refine ⟨57217261538978695246062689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38144841025985796830708459 57217261538978695246062689)
      ·
        refine ⟨42912946154234021434547017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57217261538978695246062689 42912946154234021434547017)
        ·
          refine ⟨32184709615675516075910263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42912946154234021434547017 32184709615675516075910263)
          ·
            refine ⟨48277064423513274113865395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32184709615675516075910263 48277064423513274113865395)
            ·
              refine ⟨72415596635269911170798093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48277064423513274113865395 72415596635269911170798093)
              ·
                refine ⟨27155848738226216689049285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72415596635269911170798093 27155848738226216689049285)
                ·
                  refine ⟨5091721638417415629196741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27155848738226216689049285 5091721638417415629196741)
                  ·
                    refine ⟨954697807203265430474389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5091721638417415629196741 954697807203265430474389)
                    ·
                      rfl

theorem cell22_2788901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_2788901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788901 prefixEnd_2788901 := by exact prefixLift 2788901
  have htrace : WordTrace (prefixWord ++ tailWord_2788901) baseStart_2788901 baseEnd_2788901 := by
    simpa [prefixWord, tailWord_2788901, baseEnd_2788901] using wordTrace_append hprefix tailTrace_2788901
  have hstable : (prefixWord ++ tailWord_2788901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788901).length < 2 ^ (prefixWord ++ tailWord_2788901).sum := by decide
  have hdescent : baseEnd_2788901 < baseStart_2788901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788961 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 7]
def baseStart_2788961 : Nat := 118140960795 + 2788961 * 2 ^ 59
def prefixEnd_2788961 : Nat := 4983230072969 + 3 ^ 40 * 2788961 * 2
def baseEnd_2788961 : Nat := 318239448809815091324735

theorem tailTrace_2788961 : CollatzResearch.WordTrace tailWord_2788961 prefixEnd_2788961 318239448809815091324735 := by
  unfold tailWord_2788961
  simp only [CollatzResearch.WordTrace]
  refine ⟨101721764449078088462406737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67814509632718725641604491 101721764449078088462406737)
  ·
    refine ⟨76291323336808566346805053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101721764449078088462406737 76291323336808566346805053)
    ·
      refine ⟨28609246251303212380051895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76291323336808566346805053 28609246251303212380051895)
      ·
        refine ⟨42913869376954818570077843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28609246251303212380051895 42913869376954818570077843)
        ·
          refine ⟨64370804065432227855116765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42913869376954818570077843 64370804065432227855116765)
          ·
            refine ⟨24139051524537085445668787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64370804065432227855116765 24139051524537085445668787)
            ·
              refine ⟨36208577286805628168503181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24139051524537085445668787 36208577286805628168503181)
              ·
                refine ⟨13578216482552110563188693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36208577286805628168503181 13578216482552110563188693)
                ·
                  refine ⟨318239448809815091324735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13578216482552110563188693 318239448809815091324735)
                  ·
                    rfl

theorem cell22_2788961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_2788961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788961 prefixEnd_2788961 := by exact prefixLift 2788961
  have htrace : WordTrace (prefixWord ++ tailWord_2788961) baseStart_2788961 baseEnd_2788961 := by
    simpa [prefixWord, tailWord_2788961, baseEnd_2788961] using wordTrace_append hprefix tailTrace_2788961
  have hstable : (prefixWord ++ tailWord_2788961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788961).length < 2 ^ (prefixWord ++ tailWord_2788961).sum := by decide
  have hdescent : baseEnd_2788961 < baseStart_2788961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788965 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 3, 3]
def baseStart_2788965 : Nat := 118140960795 + 2788965 * 2 ^ 59
def prefixEnd_2788965 : Nat := 4983230072969 + 3 ^ 40 * 2788965 * 2
def baseEnd_2788965 : Nat := 954719715711190596874193

theorem tailTrace_2788965 : CollatzResearch.WordTrace tailWord_2788965 prefixEnd_2788965 954719715711190596874193 := by
  unfold tailWord_2788965
  simp only [CollatzResearch.WordTrace]
  refine ⟨101721910341063597145552349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67814606894042398097034899 101721910341063597145552349)
  ·
    refine ⟨38145716377898848929582131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101721910341063597145552349 38145716377898848929582131)
    ·
      refine ⟨57218574566848273394373197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38145716377898848929582131 57218574566848273394373197)
      ·
        refine ⟨21456965462568102522889949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57218574566848273394373197 21456965462568102522889949)
        ·
          refine ⟨8046362048463038446083731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21456965462568102522889949 8046362048463038446083731)
          ·
            refine ⟨12069543072694557669125597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8046362048463038446083731 12069543072694557669125597)
            ·
              refine ⟨4526078652260459125922099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12069543072694557669125597 4526078652260459125922099)
              ·
                refine ⟨6789117978390688688883149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4526078652260459125922099 6789117978390688688883149)
                ·
                  refine ⟨2545919241896508258331181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6789117978390688688883149 2545919241896508258331181)
                  ·
                    refine ⟨954719715711190596874193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2545919241896508258331181 954719715711190596874193)
                    ·
                      rfl

theorem cell22_2788965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_2788965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2788965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2788965 prefixEnd_2788965 := by exact prefixLift 2788965
  have htrace : WordTrace (prefixWord ++ tailWord_2788965) baseStart_2788965 baseEnd_2788965 := by
    simpa [prefixWord, tailWord_2788965, baseEnd_2788965] using wordTrace_append hprefix tailTrace_2788965
  have hstable : (prefixWord ++ tailWord_2788965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788965).length < 2 ^ (prefixWord ++ tailWord_2788965).sum := by decide
  have hdescent : baseEnd_2788965 < baseStart_2788965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789008 : List Nat := [2, 1, 1, 1, 1, 1, 3, 7, 1, 4]
def baseStart_2789008 : Nat := 118140960795 + 2789008 * 2 ^ 59
def prefixEnd_2789008 : Nat := 4983230072969 + 3 ^ 40 * 2789008 * 2
def baseEnd_2789008 : Nat := 954734435489952818049061

theorem tailTrace_2789008 : CollatzResearch.WordTrace tailWord_2789008 prefixEnd_2789008 954734435489952818049061 := by
  unfold tailWord_2789008
  simp only [CollatzResearch.WordTrace]
  refine ⟨50861739339953907744683839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67815652453271876992911785 50861739339953907744683839)
  ·
    refine ⟨76292609009930861617025759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50861739339953907744683839 76292609009930861617025759)
    ·
      refine ⟨114438913514896292425538639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76292609009930861617025759 114438913514896292425538639)
      ·
        refine ⟨171658370272344438638307959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114438913514896292425538639 171658370272344438638307959)
        ·
          refine ⟨257487555408516657957461939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171658370272344438638307959 257487555408516657957461939)
          ·
            refine ⟨386231333112774986936192909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257487555408516657957461939 386231333112774986936192909)
            ·
              refine ⟨144836749917290620101072341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386231333112774986936192909 144836749917290620101072341)
              ·
                refine ⟨3394611326186498908618883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 144836749917290620101072341 3394611326186498908618883)
                ·
                  refine ⟨5091916989279748362928325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3394611326186498908618883 5091916989279748362928325)
                  ·
                    refine ⟨954734435489952818049061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5091916989279748362928325 954734435489952818049061)
                    ·
                      rfl

theorem cell22_2789008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_2789008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789008 prefixEnd_2789008 := by exact prefixLift 2789008
  have htrace : WordTrace (prefixWord ++ tailWord_2789008) baseStart_2789008 baseEnd_2789008 := by
    simpa [prefixWord, tailWord_2789008, baseEnd_2789008] using wordTrace_append hprefix tailTrace_2789008
  have hstable : (prefixWord ++ tailWord_2789008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789008).length < 2 ^ (prefixWord ++ tailWord_2789008).sum := by decide
  have hdescent : baseEnd_2789008 < baseStart_2789008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789012 : List Nat := [2, 4, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2789012 : Nat := 118140960795 + 2789012 * 2 ^ 59
def prefixEnd_2789012 : Nat := 4983230072969 + 3 ^ 40 * 2789012 * 2
def baseEnd_2789012 : Nat := 318245268257232713649683

theorem tailTrace_2789012 : CollatzResearch.WordTrace tailWord_2789012 prefixEnd_2789012 318245268257232713649683 := by
  unfold tailWord_2789012
  simp only [CollatzResearch.WordTrace]
  refine ⟨50861812285946662086256645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67815749714595549448342193 50861812285946662086256645)
  ·
    refine ⟨9536589803614999141173121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50861812285946662086256645 9536589803614999141173121)
    ·
      refine ⟨7152442352711249355879841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9536589803614999141173121 7152442352711249355879841)
      ·
        refine ⟨5364331764533437016909881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7152442352711249355879841 5364331764533437016909881)
        ·
          refine ⟨4023248823400077762682411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5364331764533437016909881 4023248823400077762682411)
          ·
            refine ⟨6034873235100116644023617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023248823400077762682411 6034873235100116644023617)
            ·
              refine ⟨4526154926325087483017713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6034873235100116644023617 4526154926325087483017713)
              ·
                refine ⟨3394616194743815612263285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4526154926325087483017713 3394616194743815612263285)
                ·
                  refine ⟨318245268257232713649683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3394616194743815612263285 318245268257232713649683)
                  ·
                    rfl

theorem cell22_2789012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2789012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789012 prefixEnd_2789012 := by exact prefixLift 2789012
  have htrace : WordTrace (prefixWord ++ tailWord_2789012) baseStart_2789012 baseEnd_2789012 := by
    simpa [prefixWord, tailWord_2789012, baseEnd_2789012] using wordTrace_append hprefix tailTrace_2789012
  have hstable : (prefixWord ++ tailWord_2789012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789012).length < 2 ^ (prefixWord ++ tailWord_2789012).sum := by decide
  have hdescent : baseEnd_2789012 < baseStart_2789012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789051 : List Nat := [1, 1, 1, 1, 1, 2, 3, 12]
def baseStart_2789051 : Nat := 118140960795 + 2789051 * 2 ^ 59
def prefixEnd_2789051 : Nat := 4983230072969 + 3 ^ 40 * 2789051 * 2
def baseEnd_2789051 : Nat := 106083239474301671024881

theorem tailTrace_2789051 : CollatzResearch.WordTrace tailWord_2789051 prefixEnd_2789051 106083239474301671024881 := by
  unfold tailWord_2789051
  simp only [CollatzResearch.WordTrace]
  refine ⟨101725047018752033833183007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67816698012501355888788671 101725047018752033833183007)
  ·
    refine ⟨152587570528128050749774511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101725047018752033833183007 152587570528128050749774511)
    ·
      refine ⟨228881355792192076124661767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152587570528128050749774511 228881355792192076124661767)
      ·
        refine ⟨343322033688288114186992651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228881355792192076124661767 343322033688288114186992651)
        ·
          refine ⟨514983050532432171280488977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343322033688288114186992651 514983050532432171280488977)
          ·
            refine ⟨386237287899324128460366733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514983050532432171280488977 386237287899324128460366733)
            ·
              refine ⟨144838982962246548172637525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386237287899324128460366733 144838982962246548172637525)
              ·
                refine ⟨106083239474301671024881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 144838982962246548172637525 106083239474301671024881)
                ·
                  rfl

theorem cell22_2789051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 12].length) (baseStart_2789051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789051 prefixEnd_2789051 := by exact prefixLift 2789051
  have htrace : WordTrace (prefixWord ++ tailWord_2789051) baseStart_2789051 baseEnd_2789051 := by
    simpa [prefixWord, tailWord_2789051, baseEnd_2789051] using wordTrace_append hprefix tailTrace_2789051
  have hstable : (prefixWord ++ tailWord_2789051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789051).length < 2 ^ (prefixWord ++ tailWord_2789051).sum := by decide
  have hdescent : baseEnd_2789051 < baseStart_2789051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789053 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_2789053 : Nat := 118140960795 + 2789053 * 2 ^ 59
def prefixEnd_2789053 : Nat := 4983230072969 + 3 ^ 40 * 2789053 * 2
def baseEnd_2789053 : Nat := 954749839909587700673923

theorem tailTrace_2789053 : CollatzResearch.WordTrace tailWord_2789053 prefixEnd_2789053 954749839909587700673923 := by
  unfold tailWord_2789053
  simp only [CollatzResearch.WordTrace]
  refine ⟨101725119964744788174755813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67816746643163192116503875 101725119964744788174755813)
  ·
    refine ⟨19073459993389647782766715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101725119964744788174755813 19073459993389647782766715)
    ·
      refine ⟨28610189990084471674150073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19073459993389647782766715 28610189990084471674150073)
      ·
        refine ⟨21457642492563353755612555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28610189990084471674150073 21457642492563353755612555)
        ·
          refine ⟨32186463738845030633418833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21457642492563353755612555 32186463738845030633418833)
          ·
            refine ⟨24139847804133772975064125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32186463738845030633418833 24139847804133772975064125)
            ·
              refine ⟨9052442926550164865649047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24139847804133772975064125 9052442926550164865649047)
              ·
                refine ⟨13578664389825247298473571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9052442926550164865649047 13578664389825247298473571)
                ·
                  refine ⟨20367996584737870947710357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13578664389825247298473571 20367996584737870947710357)
                  ·
                    refine ⟨954749839909587700673923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20367996584737870947710357 954749839909587700673923)
                    ·
                      rfl

theorem cell22_2789053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_2789053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789053 prefixEnd_2789053 := by exact prefixLift 2789053
  have htrace : WordTrace (prefixWord ++ tailWord_2789053) baseStart_2789053 baseEnd_2789053 := by
    simpa [prefixWord, tailWord_2789053, baseEnd_2789053] using wordTrace_append hprefix tailTrace_2789053
  have hstable : (prefixWord ++ tailWord_2789053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789053).length < 2 ^ (prefixWord ++ tailWord_2789053).sum := by decide
  have hdescent : baseEnd_2789053 < baseStart_2789053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789089 : List Nat := [1, 2, 3, 1, 5, 1, 3, 1, 2, 3]
def baseStart_2789089 : Nat := 118140960795 + 2789089 * 2 ^ 59
def prefixEnd_2789089 : Nat := 4983230072969 + 3 ^ 40 * 2789089 * 2
def baseEnd_2789089 : Nat := 954762163445295606773813

theorem tailTrace_2789089 : CollatzResearch.WordTrace tailWord_2789089 prefixEnd_2789089 954762163445295606773813 := by
  unfold tailWord_2789089
  simp only [CollatzResearch.WordTrace]
  refine ⟨101726432992614366323066321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67817621995076244215377547 101726432992614366323066321)
  ·
    refine ⟨76294824744460774742299741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101726432992614366323066321 76294824744460774742299741)
    ·
      refine ⟨28610559279172790528362403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76294824744460774742299741 28610559279172790528362403)
      ·
        refine ⟨42915838918759185792543605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28610559279172790528362403 42915838918759185792543605)
        ·
          refine ⟨4023359898633673668050963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42915838918759185792543605 4023359898633673668050963)
          ·
            refine ⟨6035039847950510502076445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023359898633673668050963 6035039847950510502076445)
            ·
              refine ⟨2263139942981441438278667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6035039847950510502076445 2263139942981441438278667)
              ·
                refine ⟨3394709914472162157418001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2263139942981441438278667 3394709914472162157418001)
                ·
                  refine ⟨2546032435854121618063501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3394709914472162157418001 2546032435854121618063501)
                  ·
                    refine ⟨954762163445295606773813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546032435854121618063501 954762163445295606773813)
                    ·
                      rfl

theorem cell22_2789089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_2789089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789089 prefixEnd_2789089 := by exact prefixLift 2789089
  have htrace : WordTrace (prefixWord ++ tailWord_2789089) baseStart_2789089 baseEnd_2789089 := by
    simpa [prefixWord, tailWord_2789089, baseEnd_2789089] using wordTrace_append hprefix tailTrace_2789089
  have hstable : (prefixWord ++ tailWord_2789089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789089).length < 2 ^ (prefixWord ++ tailWord_2789089).sum := by decide
  have hdescent : baseEnd_2789089 < baseStart_2789089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789098 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_2789098 : Nat := 118140960795 + 2789098 * 2 ^ 59
def prefixEnd_2789098 : Nat := 4983230072969 + 3 ^ 40 * 2789098 * 2
def baseEnd_2789098 : Nat := 954765244329222583298785

theorem tailTrace_2789098 : CollatzResearch.WordTrace tailWord_2789098 prefixEnd_2789098 954765244329222583298785 := by
  unfold tailWord_2789098
  simp only [CollatzResearch.WordTrace]
  refine ⟨25431690312395440215035987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67817840833054507240095965 25431690312395440215035987)
  ·
    refine ⟨38147535468593160322553981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25431690312395440215035987 38147535468593160322553981)
    ·
      refine ⟨14305325800722435120957743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38147535468593160322553981 14305325800722435120957743)
      ·
        refine ⟨21457988701083652681436615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14305325800722435120957743 21457988701083652681436615)
        ·
          refine ⟨32186983051625479022154923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21457988701083652681436615 32186983051625479022154923)
          ·
            refine ⟨48280474577438218533232385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32186983051625479022154923 48280474577438218533232385)
            ·
              refine ⟨36210355933078663899924289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48280474577438218533232385 36210355933078663899924289)
              ·
                refine ⟨27157766949808997924943217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36210355933078663899924289 27157766949808997924943217)
                ·
                  refine ⟨20368325212356748443707413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27157766949808997924943217 20368325212356748443707413)
                  ·
                    refine ⟨954765244329222583298785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20368325212356748443707413 954765244329222583298785)
                    ·
                      rfl

theorem cell22_2789098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_2789098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789098 prefixEnd_2789098 := by exact prefixLift 2789098
  have htrace : WordTrace (prefixWord ++ tailWord_2789098) baseStart_2789098 baseEnd_2789098 := by
    simpa [prefixWord, tailWord_2789098, baseEnd_2789098] using wordTrace_append hprefix tailTrace_2789098
  have hstable : (prefixWord ++ tailWord_2789098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789098).length < 2 ^ (prefixWord ++ tailWord_2789098).sum := by decide
  have hdescent : baseEnd_2789098 < baseStart_2789098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789100 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 3, 3]
def baseStart_2789100 : Nat := 118140960795 + 2789100 * 2 ^ 59
def prefixEnd_2789100 : Nat := 4983230072969 + 3 ^ 40 * 2789100 * 2
def baseEnd_2789100 : Nat := 954765928970095244748779

theorem tailTrace_2789100 : CollatzResearch.WordTrace tailWord_2789100 prefixEnd_2789100 954765928970095244748779 := by
  unfold tailWord_2789100
  simp only [CollatzResearch.WordTrace]
  refine ⟨50863417097787257600858377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67817889463716343467811169 50863417097787257600858377)
  ·
    refine ⟨38147562823340443200643783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50863417097787257600858377 38147562823340443200643783)
    ·
      refine ⟨57221344235010664800965675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38147562823340443200643783 57221344235010664800965675)
      ·
        refine ⟨85832016352515997201448513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57221344235010664800965675 85832016352515997201448513)
        ·
          refine ⟨64374012264386997901086385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85832016352515997201448513 64374012264386997901086385)
          ·
            refine ⟨48280509198290248425814789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64374012264386997901086385 48280509198290248425814789)
            ·
              refine ⟨9052595474679421579840273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48280509198290248425814789 9052595474679421579840273)
              ·
                refine ⟨6789446606009566184880205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9052595474679421579840273 6789446606009566184880205)
                ·
                  refine ⟨2546042477253587319330077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6789446606009566184880205 2546042477253587319330077)
                  ·
                    refine ⟨954765928970095244748779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546042477253587319330077 954765928970095244748779)
                    ·
                      rfl

theorem cell22_2789100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_2789100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789100 prefixEnd_2789100 := by exact prefixLift 2789100
  have htrace : WordTrace (prefixWord ++ tailWord_2789100) baseStart_2789100 baseEnd_2789100 := by
    simpa [prefixWord, tailWord_2789100, baseEnd_2789100] using wordTrace_append hprefix tailTrace_2789100
  have hstable : (prefixWord ++ tailWord_2789100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789100).length < 2 ^ (prefixWord ++ tailWord_2789100).sum := by decide
  have hdescent : baseEnd_2789100 < baseStart_2789100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789117 : List Nat := [1, 4, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_2789117 : Nat := 118140960795 + 2789117 * 2 ^ 59
def prefixEnd_2789117 : Nat := 4983230072969 + 3 ^ 40 * 2789117 * 2
def baseEnd_2789117 : Nat := 954771748417512867073727

theorem tailTrace_2789117 : CollatzResearch.WordTrace tailWord_2789117 prefixEnd_2789117 954771748417512867073727 := by
  unfold tailWord_2789117
  simp only [CollatzResearch.WordTrace]
  refine ⟨101727454236512927105085605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67818302824341951403390403 101727454236512927105085605)
  ·
    refine ⟨19073897669346173832203551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101727454236512927105085605 19073897669346173832203551)
    ·
      refine ⟨28610846504019260748305327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19073897669346173832203551 28610846504019260748305327)
      ·
        refine ⟨42916269756028891122457991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28610846504019260748305327 42916269756028891122457991)
        ·
          refine ⟨64374404634043336683686987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42916269756028891122457991 64374404634043336683686987)
          ·
            refine ⟨96561606951065005025530481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64374404634043336683686987 96561606951065005025530481)
            ·
              refine ⟨72421205213298753769147861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96561606951065005025530481 72421205213298753769147861)
              ·
                refine ⟨1697371997186689541464403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72421205213298753769147861 1697371997186689541464403)
                ·
                  refine ⟨2546057995780034312196605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697371997186689541464403 2546057995780034312196605)
                  ·
                    refine ⟨954771748417512867073727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546057995780034312196605 954771748417512867073727)
                    ·
                      rfl

theorem cell22_2789117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_2789117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789117 prefixEnd_2789117 := by exact prefixLift 2789117
  have htrace : WordTrace (prefixWord ++ tailWord_2789117) baseStart_2789117 baseEnd_2789117 := by
    simpa [prefixWord, tailWord_2789117, baseEnd_2789117] using wordTrace_append hprefix tailTrace_2789117
  have hstable : (prefixWord ++ tailWord_2789117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789117).length < 2 ^ (prefixWord ++ tailWord_2789117).sum := by decide
  have hdescent : baseEnd_2789117 < baseStart_2789117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789140 : List Nat := [2, 4, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2789140 : Nat := 118140960795 + 2789140 * 2 ^ 59
def prefixEnd_2789140 : Nat := 4983230072969 + 3 ^ 40 * 2789140 * 2
def baseEnd_2789140 : Nat := 954779621787548473748657

theorem tailTrace_2789140 : CollatzResearch.WordTrace tailWord_2789140 prefixEnd_2789140 954779621787548473748657 := by
  unfold tailWord_2789140
  simp only [CollatzResearch.WordTrace]
  refine ⟨50864146557714801016586437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67818862076953068022115249 50864146557714801016586437)
  ·
    refine ⟨9537027479571525190609957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50864146557714801016586437 9537027479571525190609957)
    ·
      refine ⟨1788192652419660973239367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9537027479571525190609957 1788192652419660973239367)
      ·
        refine ⟨2682288978629491459859051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1788192652419660973239367 2682288978629491459859051)
        ·
          refine ⟨4023433467944237189788577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682288978629491459859051 4023433467944237189788577)
          ·
            refine ⟨3017575100958177892341433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4023433467944237189788577 3017575100958177892341433)
            ·
              refine ⟨2263181325718633419256075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3017575100958177892341433 2263181325718633419256075)
              ·
                refine ⟨3394771988577950128884113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2263181325718633419256075 3394771988577950128884113)
                ·
                  refine ⟨2546078991433462596663085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3394771988577950128884113 2546078991433462596663085)
                  ·
                    refine ⟨954779621787548473748657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546078991433462596663085 954779621787548473748657)
                    ·
                      rfl

theorem cell22_2789140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2789140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789140 prefixEnd_2789140 := by exact prefixLift 2789140
  have htrace : WordTrace (prefixWord ++ tailWord_2789140) baseStart_2789140 baseEnd_2789140 := by
    simpa [prefixWord, tailWord_2789140, baseEnd_2789140] using wordTrace_append hprefix tailTrace_2789140
  have hstable : (prefixWord ++ tailWord_2789140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789140).length < 2 ^ (prefixWord ++ tailWord_2789140).sum := by decide
  have hdescent : baseEnd_2789140 < baseStart_2789140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789192 : List Nat := [2, 1, 3, 1, 1, 5, 1, 4, 4]
def baseStart_2789192 : Nat := 118140960795 + 2789192 * 2 ^ 59
def prefixEnd_2789192 : Nat := 4983230072969 + 3 ^ 40 * 2789192 * 2
def baseEnd_2789192 : Nat := 318265807483412557149499

theorem tailTrace_2789192 : CollatzResearch.WordTrace tailWord_2789192 prefixEnd_2789192 318265807483412557149499 := by
  unfold tailWord_2789192
  simp only [CollatzResearch.WordTrace]
  refine ⟨50865094855620607457032915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67820126474160809942710553 50865094855620607457032915)
  ·
    refine ⟨76297642283430911185549373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50865094855620607457032915 76297642283430911185549373)
    ·
      refine ⟨28611615856286591694581015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76297642283430911185549373 28611615856286591694581015)
      ·
        refine ⟨42917423784429887541871523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28611615856286591694581015 42917423784429887541871523)
        ·
          refine ⟨64376135676644831312807285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42917423784429887541871523 64376135676644831312807285)
          ·
            refine ⟨6035262719685452935575683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64376135676644831312807285 6035262719685452935575683)
            ·
              refine ⟨9052894079528179403363525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6035262719685452935575683 9052894079528179403363525)
              ·
                refine ⟨1697417639911533638130661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9052894079528179403363525 1697417639911533638130661)
                ·
                  refine ⟨318265807483412557149499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1697417639911533638130661 318265807483412557149499)
                  ·
                    rfl

theorem cell22_2789192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 4].length) (baseStart_2789192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789192 prefixEnd_2789192 := by exact prefixLift 2789192
  have htrace : WordTrace (prefixWord ++ tailWord_2789192) baseStart_2789192 baseEnd_2789192 := by
    simpa [prefixWord, tailWord_2789192, baseEnd_2789192] using wordTrace_append hprefix tailTrace_2789192
  have hstable : (prefixWord ++ tailWord_2789192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789192).length < 2 ^ (prefixWord ++ tailWord_2789192).sum := by decide
  have hdescent : baseEnd_2789192 < baseStart_2789192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789207 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 1, 5]
def baseStart_2789207 : Nat := 118140960795 + 2789207 * 2 ^ 59
def prefixEnd_2789207 : Nat := 4983230072969 + 3 ^ 40 * 2789207 * 2
def baseEnd_2789207 : Nat := 954802557256782632323451

theorem tailTrace_2789207 : CollatzResearch.WordTrace tailWord_2789207 prefixEnd_2789207 954802557256782632323451 := by
  unfold tailWord_2789207
  simp only [CollatzResearch.WordTrace]
  refine ⟨101730736806186872475861875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67820491204124581650574583 101730736806186872475861875)
  ·
    refine ⟨152596105209280308713792813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101730736806186872475861875 152596105209280308713792813)
    ·
      refine ⟨57223539453480115767672305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152596105209280308713792813 57223539453480115767672305)
      ·
        refine ⟨42917654590110086825754229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57223539453480115767672305 42917654590110086825754229)
        ·
          refine ⟨4023530117822820639914459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42917654590110086825754229 4023530117822820639914459)
          ·
            refine ⟨6035295176734230959871689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023530117822820639914459 6035295176734230959871689)
            ·
              refine ⟨4526471382550673219903767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6035295176734230959871689 4526471382550673219903767)
              ·
                refine ⟨6789707073826009829855651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4526471382550673219903767 6789707073826009829855651)
                ·
                  refine ⟨10184560610739014744783477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6789707073826009829855651 10184560610739014744783477)
                  ·
                    refine ⟨954802557256782632323451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10184560610739014744783477 954802557256782632323451)
                    ·
                      rfl

theorem cell22_2789207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_2789207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789207 prefixEnd_2789207 := by exact prefixLift 2789207
  have htrace : WordTrace (prefixWord ++ tailWord_2789207) baseStart_2789207 baseEnd_2789207 := by
    simpa [prefixWord, tailWord_2789207, baseEnd_2789207] using wordTrace_append hprefix tailTrace_2789207
  have hstable : (prefixWord ++ tailWord_2789207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789207).length < 2 ^ (prefixWord ++ tailWord_2789207).sum := by decide
  have hdescent : baseEnd_2789207 < baseStart_2789207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789226 : List Nat := [3, 1, 3, 4, 1, 1, 2, 3, 4]
def baseStart_2789226 : Nat := 118140960795 + 2789226 * 2 ^ 59
def prefixEnd_2789226 : Nat := 4983230072969 + 3 ^ 40 * 2789226 * 2
def baseEnd_2789226 : Nat := 318269687115024305366131

theorem tailTrace_2789226 : CollatzResearch.WordTrace tailWord_2789226 prefixEnd_2789226 318269687115024305366131 := by
  unfold tailWord_2789226
  simp only [CollatzResearch.WordTrace]
  refine ⟨25432857448279509680200883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67820953195412025813869021 25432857448279509680200883)
  ·
    refine ⟨38149286172419264520301325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25432857448279509680200883 38149286172419264520301325)
    ·
      refine ⟨14305982314657224195112997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38149286172419264520301325 14305982314657224195112997)
      ·
        refine ⟨2682371683998229536583687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14305982314657224195112997 2682371683998229536583687)
        ·
          refine ⟨4023557525997344304875531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682371683998229536583687 4023557525997344304875531)
          ·
            refine ⟨6035336288996016457313297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023557525997344304875531 6035336288996016457313297)
            ·
              refine ⟨4526502216747012342984973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6035336288996016457313297 4526502216747012342984973)
              ·
                refine ⟨1697438331280129628619365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4526502216747012342984973 1697438331280129628619365)
                ·
                  refine ⟨318269687115024305366131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1697438331280129628619365 318269687115024305366131)
                  ·
                    rfl

theorem cell22_2789226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_2789226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789226 prefixEnd_2789226 := by exact prefixLift 2789226
  have htrace : WordTrace (prefixWord ++ tailWord_2789226) baseStart_2789226 baseEnd_2789226 := by
    simpa [prefixWord, tailWord_2789226, baseEnd_2789226] using wordTrace_append hprefix tailTrace_2789226
  have hstable : (prefixWord ++ tailWord_2789226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789226).length < 2 ^ (prefixWord ++ tailWord_2789226).sum := by decide
  have hdescent : baseEnd_2789226 < baseStart_2789226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789235 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 7, 3]
def baseStart_2789235 : Nat := 118140960795 + 2789235 * 2 ^ 59
def prefixEnd_2789235 : Nat := 4983230072969 + 3 ^ 40 * 2789235 * 2
def baseEnd_2789235 : Nat := 954812142228999892623365

theorem tailTrace_2789235 : CollatzResearch.WordTrace tailWord_2789235 prefixEnd_2789235 954812142228999892623365 := by
  unfold tailWord_2789235
  simp only [CollatzResearch.WordTrace]
  refine ⟨101731758050085433257881159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67821172033390288838587439 101731758050085433257881159)
  ·
    refine ⟨152597637075128149886821739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101731758050085433257881159 152597637075128149886821739)
    ·
      refine ⟨228896455612692224830232609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152597637075128149886821739 228896455612692224830232609)
      ·
        refine ⟨171672341709519168622674457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228896455612692224830232609 171672341709519168622674457)
        ·
          refine ⟨128754256282139376467005843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171672341709519168622674457 128754256282139376467005843)
          ·
            refine ⟨193131384423209064700508765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128754256282139376467005843 193131384423209064700508765)
            ·
              refine ⟨72424269158703399262690787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193131384423209064700508765 72424269158703399262690787)
              ·
                refine ⟨108636403738055098894036181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72424269158703399262690787 108636403738055098894036181)
                ·
                  refine ⟨2546165712610666380328973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 108636403738055098894036181 2546165712610666380328973)
                  ·
                    refine ⟨954812142228999892623365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546165712610666380328973 954812142228999892623365)
                    ·
                      rfl

theorem cell22_2789235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 3].length) (baseStart_2789235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789235 prefixEnd_2789235 := by exact prefixLift 2789235
  have htrace : WordTrace (prefixWord ++ tailWord_2789235) baseStart_2789235 baseEnd_2789235 := by
    simpa [prefixWord, tailWord_2789235, baseEnd_2789235] using wordTrace_append hprefix tailTrace_2789235
  have hstable : (prefixWord ++ tailWord_2789235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789235).length < 2 ^ (prefixWord ++ tailWord_2789235).sum := by decide
  have hdescent : baseEnd_2789235 < baseStart_2789235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789252 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_2789252 : Nat := 118140960795 + 2789252 * 2 ^ 59
def prefixEnd_2789252 : Nat := 4983230072969 + 3 ^ 40 * 2789252 * 2
def baseEnd_2789252 : Nat := 954817961676417514948313

theorem tailTrace_2789252 : CollatzResearch.WordTrace tailWord_2789252 prefixEnd_2789252 954817961676417514948313 := by
  unfold tailWord_2789252
  simp only [CollatzResearch.WordTrace]
  refine ⟨50866189045511922580625005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67821585394015896774166673 50866189045511922580625005)
  ·
    refine ⟨19074820892066970967734377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50866189045511922580625005 19074820892066970967734377)
    ·
      refine ⟨14306115669050228225800783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19074820892066970967734377 14306115669050228225800783)
      ·
        refine ⟨21459173503575342338701175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14306115669050228225800783 21459173503575342338701175)
        ·
          refine ⟨32188760255363013508051763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21459173503575342338701175 32188760255363013508051763)
          ·
            refine ⟨48283140383044520262077645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32188760255363013508051763 48283140383044520262077645)
            ·
              refine ⟨18106177643641695098279117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48283140383044520262077645 18106177643641695098279117)
              ·
                refine ⟨6789816616365635661854669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18106177643641695098279117 6789816616365635661854669)
                ·
                  refine ⟨2546181231137113373195501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6789816616365635661854669 2546181231137113373195501)
                  ·
                    refine ⟨954817961676417514948313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546181231137113373195501 954817961676417514948313)
                    ·
                      rfl

theorem cell22_2789252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_2789252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789252 prefixEnd_2789252 := by exact prefixLift 2789252
  have htrace : WordTrace (prefixWord ++ tailWord_2789252) baseStart_2789252 baseEnd_2789252 := by
    simpa [prefixWord, tailWord_2789252, baseEnd_2789252] using wordTrace_append hprefix tailTrace_2789252
  have hstable : (prefixWord ++ tailWord_2789252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789252).length < 2 ^ (prefixWord ++ tailWord_2789252).sum := by decide
  have hdescent : baseEnd_2789252 < baseStart_2789252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789265 : List Nat := [1, 2, 2, 1, 1, 1, 4, 5, 5]
def baseStart_2789265 : Nat := 118140960795 + 2789265 * 2 ^ 59
def prefixEnd_2789265 : Nat := 4983230072969 + 3 ^ 40 * 2789265 * 2
def baseEnd_2789265 : Nat := 318274137280696604791091

theorem tailTrace_2789265 : CollatzResearch.WordTrace tailWord_2789265 prefixEnd_2789265 318274137280696604791091 := by
  unfold tailWord_2789265
  simp only [CollatzResearch.WordTrace]
  refine ⟨101732852239976748381473249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67821901493317832254315499 101732852239976748381473249)
  ·
    refine ⟨76299639179982561286104937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101732852239976748381473249 76299639179982561286104937)
    ·
      refine ⟨57224729384986920964578703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76299639179982561286104937 57224729384986920964578703)
      ·
        refine ⟨85837094077480381446868055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57224729384986920964578703 85837094077480381446868055)
        ·
          refine ⟨128755641116220572170302083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85837094077480381446868055 128755641116220572170302083)
          ·
            refine ⟨193133461674330858255453125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128755641116220572170302083 193133461674330858255453125)
            ·
              refine ⟨36212524063937035922897461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193133461674330858255453125 36212524063937035922897461)
              ·
                refine ⟨3394924130994097117771637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36212524063937035922897461 3394924130994097117771637)
                ·
                  refine ⟨318274137280696604791091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3394924130994097117771637 318274137280696604791091)
                  ·
                    rfl

theorem cell22_2789265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_2789265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789265 prefixEnd_2789265 := by exact prefixLift 2789265
  have htrace : WordTrace (prefixWord ++ tailWord_2789265) baseStart_2789265 baseEnd_2789265 := by
    simpa [prefixWord, tailWord_2789265, baseEnd_2789265] using wordTrace_append hprefix tailTrace_2789265
  have hstable : (prefixWord ++ tailWord_2789265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789265).length < 2 ^ (prefixWord ++ tailWord_2789265).sum := by decide
  have hdescent : baseEnd_2789265 < baseStart_2789265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789359 : List Nat := [1, 1, 2, 1, 4, 2, 4, 2, 2, 3]
def baseStart_2789359 : Nat := 118140960795 + 2789359 * 2 ^ 59
def prefixEnd_2789359 : Nat := 4983230072969 + 3 ^ 40 * 2789359 * 2
def baseEnd_2789359 : Nat := 954854589963104902522985

theorem tailTrace_2789359 : CollatzResearch.WordTrace tailWord_2789359 prefixEnd_2789359 954854589963104902522985 := by
  unfold tailWord_2789359
  simp only [CollatzResearch.WordTrace]
  refine ⟨101736280701636202435395131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67824187134424134956930087 101736280701636202435395131)
  ·
    refine ⟨152604421052454303653092697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101736280701636202435395131 152604421052454303653092697)
    ·
      refine ⟨114453315789340727739819523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152604421052454303653092697 114453315789340727739819523)
      ·
        refine ⟨171679973684011091609729285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114453315789340727739819523 171679973684011091609729285)
        ·
          refine ⟨32189995065752079676824241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171679973684011091609729285 32189995065752079676824241)
          ·
            refine ⟨24142496299314059757618181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32189995065752079676824241 24142496299314059757618181)
            ·
              refine ⟨4526718056121386204553409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24142496299314059757618181 4526718056121386204553409)
              ·
                refine ⟨3395038542091039653415057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4526718056121386204553409 3395038542091039653415057)
                ·
                  refine ⟨2546278906568279740061293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3395038542091039653415057 2546278906568279740061293)
                  ·
                    refine ⟨954854589963104902522985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546278906568279740061293 954854589963104902522985)
                    ·
                      rfl

theorem cell22_2789359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 3].length) (baseStart_2789359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789359 prefixEnd_2789359 := by exact prefixLift 2789359
  have htrace : WordTrace (prefixWord ++ tailWord_2789359) baseStart_2789359 baseEnd_2789359 := by
    simpa [prefixWord, tailWord_2789359, baseEnd_2789359] using wordTrace_append hprefix tailTrace_2789359
  have hstable : (prefixWord ++ tailWord_2789359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789359).length < 2 ^ (prefixWord ++ tailWord_2789359).sum := by decide
  have hdescent : baseEnd_2789359 < baseStart_2789359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789370 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_2789370 : Nat := 118140960795 + 2789370 * 2 ^ 59
def prefixEnd_2789370 : Nat := 4983230072969 + 3 ^ 40 * 2789370 * 2
def baseEnd_2789370 : Nat := 954858355487904540497951

theorem tailTrace_2789370 : CollatzResearch.WordTrace tailWord_2789370 prefixEnd_2789370 954858355487904540497951 := by
  unfold tailWord_2789370
  simp only [CollatzResearch.WordTrace]
  refine ⟨25434170476149087828511391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67824454603064234209363709 25434170476149087828511391)
  ·
    refine ⟨38151255714223631742767087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25434170476149087828511391 38151255714223631742767087)
    ·
      refine ⟨57226883571335447614150631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38151255714223631742767087 57226883571335447614150631)
      ·
        refine ⟨85840325357003171421225947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57226883571335447614150631 85840325357003171421225947)
        ·
          refine ⟨128760488035504757131838921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85840325357003171421225947 128760488035504757131838921)
          ·
            refine ⟨96570366026628567848879191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128760488035504757131838921 96570366026628567848879191)
            ·
              refine ⟨144855549039942851773318787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96570366026628567848879191 144855549039942851773318787)
              ·
                refine ⟨217283323559914277659978181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144855549039942851773318787 217283323559914277659978181)
                ·
                  refine ⟨40740623167483927061245909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217283323559914277659978181 40740623167483927061245909)
                  ·
                    refine ⟨954858355487904540497951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40740623167483927061245909 954858355487904540497951)
                    ·
                      rfl

theorem cell22_2789370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_2789370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789370 prefixEnd_2789370 := by exact prefixLift 2789370
  have htrace : WordTrace (prefixWord ++ tailWord_2789370) baseStart_2789370 baseEnd_2789370 := by
    simpa [prefixWord, tailWord_2789370, baseEnd_2789370] using wordTrace_append hprefix tailTrace_2789370
  have hstable : (prefixWord ++ tailWord_2789370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789370).length < 2 ^ (prefixWord ++ tailWord_2789370).sum := by decide
  have hdescent : baseEnd_2789370 < baseStart_2789370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789464 : List Nat := [2, 1, 2, 2, 1, 4, 2, 3, 1, 4]
def baseStart_2789464 : Nat := 118140960795 + 2789464 * 2 ^ 59
def prefixEnd_2789464 : Nat := 4983230072969 + 3 ^ 40 * 2789464 * 2
def baseEnd_2789464 : Nat := 954890533608919628647663

theorem tailTrace_2789464 : CollatzResearch.WordTrace tailWord_2789464 prefixEnd_2789464 954890533608919628647663 := by
  unfold tailWord_2789464
  simp only [CollatzResearch.WordTrace]
  refine ⟨50870055183127902683983723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67826740244170536911978297 50870055183127902683983723)
  ·
    refine ⟨76305082774691854025975585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50870055183127902683983723 76305082774691854025975585)
    ·
      refine ⟨57228812081018890519481689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76305082774691854025975585 57228812081018890519481689)
      ·
        refine ⟨42921609060764167889611267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57228812081018890519481689 42921609060764167889611267)
        ·
          refine ⟨64382413591146251834416901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42921609060764167889611267 64382413591146251834416901)
          ·
            refine ⟨12071702548339922218953169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64382413591146251834416901 12071702548339922218953169)
            ·
              refine ⟨9053776911254941664214877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12071702548339922218953169 9053776911254941664214877)
              ·
                refine ⟨3395166341720603124080579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9053776911254941664214877 3395166341720603124080579)
                ·
                  refine ⟨5092749512580904686120869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3395166341720603124080579 5092749512580904686120869)
                  ·
                    refine ⟨954890533608919628647663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5092749512580904686120869 954890533608919628647663)
                    ·
                      rfl

theorem cell22_2789464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_2789464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789464 prefixEnd_2789464 := by exact prefixLift 2789464
  have htrace : WordTrace (prefixWord ++ tailWord_2789464) baseStart_2789464 baseEnd_2789464 := by
    simpa [prefixWord, tailWord_2789464, baseEnd_2789464] using wordTrace_append hprefix tailTrace_2789464
  have hstable : (prefixWord ++ tailWord_2789464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789464).length < 2 ^ (prefixWord ++ tailWord_2789464).sum := by decide
  have hdescent : baseEnd_2789464 < baseStart_2789464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789507 : List Nat := [1, 1, 1, 3, 3, 3, 2, 8]
def baseStart_2789507 : Nat := 118140960795 + 2789507 * 2 ^ 59
def prefixEnd_2789507 : Nat := 4983230072969 + 3 ^ 40 * 2789507 * 2
def baseEnd_2789507 : Nat := 106100583709742427758059

theorem tailTrace_2789507 : CollatzResearch.WordTrace tailWord_2789507 prefixEnd_2789507 106100583709742427758059 := by
  unfold tailWord_2789507
  simp only [CollatzResearch.WordTrace]
  refine ⟨101741678705100023711782775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67827785803400015807855183 101741678705100023711782775)
  ·
    refine ⟨152612518057650035567674163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101741678705100023711782775 152612518057650035567674163)
    ·
      refine ⟨228918777086475053351511245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152612518057650035567674163 228918777086475053351511245)
      ·
        refine ⟨85844541407428145006816717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228918777086475053351511245 85844541407428145006816717)
        ·
          refine ⟨32191703027785554377556269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85844541407428145006816717 32191703027785554377556269)
          ·
            refine ⟨12071888635419582891583601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32191703027785554377556269 12071888635419582891583601)
            ·
              refine ⟨9053916476564687168687701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12071888635419582891583601 9053916476564687168687701)
              ·
                refine ⟨106100583709742427758059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9053916476564687168687701 106100583709742427758059)
                ·
                  rfl

theorem cell22_2789507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 8].length) (baseStart_2789507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789507 prefixEnd_2789507 := by exact prefixLift 2789507
  have htrace : WordTrace (prefixWord ++ tailWord_2789507) baseStart_2789507 baseEnd_2789507 := by
    simpa [prefixWord, tailWord_2789507, baseEnd_2789507] using wordTrace_append hprefix tailTrace_2789507
  have hstable : (prefixWord ++ tailWord_2789507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789507).length < 2 ^ (prefixWord ++ tailWord_2789507).sum := by decide
  have hdescent : baseEnd_2789507 < baseStart_2789507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789509 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_2789509 : Nat := 118140960795 + 2789509 * 2 ^ 59
def prefixEnd_2789509 : Nat := 4983230072969 + 3 ^ 40 * 2789509 * 2
def baseEnd_2789509 : Nat := 954905938028554511272525

theorem tailTrace_2789509 : CollatzResearch.WordTrace tailWord_2789509 prefixEnd_2789509 954905938028554511272525 := by
  unfold tailWord_2789509
  simp only [CollatzResearch.WordTrace]
  refine ⟨101741751651092778053355581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67827834434061852035570387 101741751651092778053355581)
  ·
    refine ⟨38153156869159791770008343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101741751651092778053355581 38153156869159791770008343)
    ·
      refine ⟨57229735303739687655012515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38153156869159791770008343 57229735303739687655012515)
      ·
        refine ⟨85844602955609531482518773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57229735303739687655012515 85844602955609531482518773)
        ·
          refine ⟨8047931527088393576486135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85844602955609531482518773 8047931527088393576486135)
          ·
            refine ⟨12071897290632590364729203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8047931527088393576486135 12071897290632590364729203)
            ·
              refine ⟨18107845935948885547093805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12071897290632590364729203 18107845935948885547093805)
              ·
                refine ⟨6790442225980832080160177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18107845935948885547093805 6790442225980832080160177)
                ·
                  refine ⟨5092831669485624060120133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6790442225980832080160177 5092831669485624060120133)
                  ·
                    refine ⟨954905938028554511272525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5092831669485624060120133 954905938028554511272525)
                    ·
                      rfl

theorem cell22_2789509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_2789509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789509 prefixEnd_2789509 := by exact prefixLift 2789509
  have htrace : WordTrace (prefixWord ++ tailWord_2789509) baseStart_2789509 baseEnd_2789509 := by
    simpa [prefixWord, tailWord_2789509, baseEnd_2789509] using wordTrace_append hprefix tailTrace_2789509
  have hstable : (prefixWord ++ tailWord_2789509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789509).length < 2 ^ (prefixWord ++ tailWord_2789509).sum := by decide
  have hdescent : baseEnd_2789509 < baseStart_2789509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789524 : List Nat := [2, 4, 2, 3, 11]
def baseStart_2789524 : Nat := 118140960795 + 2789524 * 2 ^ 59
def prefixEnd_2789524 : Nat := 4983230072969 + 3 ^ 40 * 2789524 * 2
def baseEnd_2789524 : Nat := 3929675196852261202253

theorem tailTrace_2789524 : CollatzResearch.WordTrace tailWord_2789524 prefixEnd_2789524 3929675196852261202253 := by
  unfold tailWord_2789524
  simp only [CollatzResearch.WordTrace]
  refine ⟨50871149373019217807575813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67828199164025623743434417 50871149373019217807575813)
  ·
    refine ⟨9538340507441103338920465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50871149373019217807575813 9538340507441103338920465)
    ·
      refine ⟨7153755380580827504190349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9538340507441103338920465 7153755380580827504190349)
      ·
        refine ⟨2682658267717810314071381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7153755380580827504190349 2682658267717810314071381)
        ·
          refine ⟨3929675196852261202253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2682658267717810314071381 3929675196852261202253)
          ·
            rfl

theorem cell22_2789524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 11].length) (baseStart_2789524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789524 prefixEnd_2789524 := by exact prefixLift 2789524
  have htrace : WordTrace (prefixWord ++ tailWord_2789524) baseStart_2789524 baseEnd_2789524 := by
    simpa [prefixWord, tailWord_2789524, baseEnd_2789524] using wordTrace_append hprefix tailTrace_2789524
  have hstable : (prefixWord ++ tailWord_2789524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789524).length < 2 ^ (prefixWord ++ tailWord_2789524).sum := by decide
  have hdescent : baseEnd_2789524 < baseStart_2789524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789528 : List Nat := [2, 1, 2, 4, 3, 1, 2, 2, 2, 3]
def baseStart_2789528 : Nat := 118140960795 + 2789528 * 2 ^ 59
def prefixEnd_2789528 : Nat := 4983230072969 + 3 ^ 40 * 2789528 * 2
def baseEnd_2789528 : Nat := 954912442116844795047467

theorem tailTrace_2789528 : CollatzResearch.WordTrace tailWord_2789528 prefixEnd_2789528 954912442116844795047467 := by
  unfold tailWord_2789528
  simp only [CollatzResearch.WordTrace]
  refine ⟨50871222319011972149148619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67828296425349296198864825 50871222319011972149148619)
  ·
    refine ⟨76306833478517958223722929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50871222319011972149148619 76306833478517958223722929)
    ·
      refine ⟨57230125108888468667792197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76306833478517958223722929 57230125108888468667792197)
      ·
        refine ⟨10730648457916587875211037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57230125108888468667792197 10730648457916587875211037)
        ·
          refine ⟨4023993171718720453204139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10730648457916587875211037 4023993171718720453204139)
          ·
            refine ⟨6035989757578080679806209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023993171718720453204139 6035989757578080679806209)
            ·
              refine ⟨4526992318183560509854657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6035989757578080679806209 4526992318183560509854657)
              ·
                refine ⟨3395244238637670382390993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4526992318183560509854657 3395244238637670382390993)
                ·
                  refine ⟨2546433178978252786793245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3395244238637670382390993 2546433178978252786793245)
                  ·
                    refine ⟨954912442116844795047467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546433178978252786793245 954912442116844795047467)
                    ·
                      rfl

theorem cell22_2789528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_2789528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789528 prefixEnd_2789528 := by exact prefixLift 2789528
  have htrace : WordTrace (prefixWord ++ tailWord_2789528) baseStart_2789528 baseEnd_2789528 := by
    simpa [prefixWord, tailWord_2789528, baseEnd_2789528] using wordTrace_append hprefix tailTrace_2789528
  have hstable : (prefixWord ++ tailWord_2789528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789528).length < 2 ^ (prefixWord ++ tailWord_2789528).sum := by decide
  have hdescent : baseEnd_2789528 < baseStart_2789528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789530 : List Nat := [3, 1, 1, 5, 2, 2, 2, 2, 4]
def baseStart_2789530 : Nat := 118140960795 + 2789530 * 2 ^ 59
def prefixEnd_2789530 : Nat := 4983230072969 + 3 ^ 40 * 2789530 * 2
def baseEnd_2789530 : Nat := 318304375585905818832487

theorem tailTrace_2789530 : CollatzResearch.WordTrace tailWord_2789530 prefixEnd_2789530 318304375585905818832487 := by
  unfold tailWord_2789530
  simp only [CollatzResearch.WordTrace]
  refine ⟨25435629396004174659967511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67828345056011132426580029 25435629396004174659967511)
  ·
    refine ⟨38153444094006261989951267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25435629396004174659967511 38153444094006261989951267)
    ·
      refine ⟨57230166141009392984926901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38153444094006261989951267 57230166141009392984926901)
      ·
        refine ⟨5365328075719630592336897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57230166141009392984926901 5365328075719630592336897)
        ·
          refine ⟨4023996056789722944252673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5365328075719630592336897 4023996056789722944252673)
          ·
            refine ⟨3017997042592292208189505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4023996056789722944252673 3017997042592292208189505)
            ·
              refine ⟨2263497781944219156142129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3017997042592292208189505 2263497781944219156142129)
              ·
                refine ⟨1697623336458164367106597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2263497781944219156142129 1697623336458164367106597)
                ·
                  refine ⟨318304375585905818832487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1697623336458164367106597 318304375585905818832487)
                  ·
                    rfl

theorem cell22_2789530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_2789530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789530 prefixEnd_2789530 := by exact prefixLift 2789530
  have htrace : WordTrace (prefixWord ++ tailWord_2789530) baseStart_2789530 baseEnd_2789530 := by
    simpa [prefixWord, tailWord_2789530, baseEnd_2789530] using wordTrace_append hprefix tailTrace_2789530
  have hstable : (prefixWord ++ tailWord_2789530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789530).length < 2 ^ (prefixWord ++ tailWord_2789530).sum := by decide
  have hdescent : baseEnd_2789530 < baseStart_2789530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789567 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 3, 7]
def baseStart_2789567 : Nat := 118140960795 + 2789567 * 2 ^ 59
def prefixEnd_2789567 : Nat := 4983230072969 + 3 ^ 40 * 2789567 * 2
def baseEnd_2789567 : Nat := 954925792613861693322347

theorem tailTrace_2789567 : CollatzResearch.WordTrace tailWord_2789567 prefixEnd_2789567 954925792613861693322347 := by
  unfold tailWord_2789567
  simp only [CollatzResearch.WordTrace]
  refine ⟨101743867084882653958966955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67829244723255102639311303 101743867084882653958966955)
  ·
    refine ⟨152615800627323980938450433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101743867084882653958966955 152615800627323980938450433)
    ·
      refine ⟨114461850470492985703837825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152615800627323980938450433 114461850470492985703837825)
      ·
        refine ⟨85846387852869739277878369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114461850470492985703837825 85846387852869739277878369)
        ·
          refine ⟨64384790889652304458408777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85846387852869739277878369 64384790889652304458408777)
          ·
            refine ⟨48288593167239228343806583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64384790889652304458408777 48288593167239228343806583)
            ·
              refine ⟨72432889750858842515709875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48288593167239228343806583 72432889750858842515709875)
              ·
                refine ⟨108649334626288263773564813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72432889750858842515709875 108649334626288263773564813)
                ·
                  refine ⟨40743500484858098915086805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108649334626288263773564813 40743500484858098915086805)
                  ·
                    refine ⟨954925792613861693322347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40743500484858098915086805 954925792613861693322347)
                    ·
                      rfl

theorem cell22_2789567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_2789567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789567 prefixEnd_2789567 := by exact prefixLift 2789567
  have htrace : WordTrace (prefixWord ++ tailWord_2789567) baseStart_2789567 baseEnd_2789567 := by
    simpa [prefixWord, tailWord_2789567, baseEnd_2789567] using wordTrace_append hprefix tailTrace_2789567
  have hstable : (prefixWord ++ tailWord_2789567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789567).length < 2 ^ (prefixWord ++ tailWord_2789567).sum := by decide
  have hdescent : baseEnd_2789567 < baseStart_2789567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789586 : List Nat := [3, 2, 2, 2, 1, 2, 3, 2, 5]
def baseStart_2789586 : Nat := 118140960795 + 2789586 * 2 ^ 59
def prefixEnd_2789586 : Nat := 4983230072969 + 3 ^ 40 * 2789586 * 2
def baseEnd_2789586 : Nat := 318310765567383992365763

theorem tailTrace_2789586 : CollatzResearch.WordTrace tailWord_2789586 prefixEnd_2789586 318310765567383992365763 := by
  unfold tailWord_2789586
  simp only [CollatzResearch.WordTrace]
  refine ⟨25436140017953455050977153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67829706714542546802605741 25436140017953455050977153)
  ·
    refine ⟨19077105013465091288232865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25436140017953455050977153 19077105013465091288232865)
    ·
      refine ⟨14307828760098818466174649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19077105013465091288232865 14307828760098818466174649)
      ·
        refine ⟨10730871570074113849630987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14307828760098818466174649 10730871570074113849630987)
        ·
          refine ⟨16096307355111170774446481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10730871570074113849630987 16096307355111170774446481)
          ·
            refine ⟨12072230516333378080834861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16096307355111170774446481 12072230516333378080834861)
            ·
              refine ⟨4527086443625016780313073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12072230516333378080834861 4527086443625016780313073)
              ·
                refine ⟨3395314832718762585234805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4527086443625016780313073 3395314832718762585234805)
                ·
                  refine ⟨318310765567383992365763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3395314832718762585234805 318310765567383992365763)
                  ·
                    rfl

theorem cell22_2789586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_2789586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789586 prefixEnd_2789586 := by exact prefixLift 2789586
  have htrace : WordTrace (prefixWord ++ tailWord_2789586) baseStart_2789586 baseEnd_2789586 := by
    simpa [prefixWord, tailWord_2789586, baseEnd_2789586] using wordTrace_append hprefix tailTrace_2789586
  have hstable : (prefixWord ++ tailWord_2789586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789586).length < 2 ^ (prefixWord ++ tailWord_2789586).sum := by decide
  have hdescent : baseEnd_2789586 < baseStart_2789586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789590 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_2789590 : Nat := 118140960795 + 2789590 * 2 ^ 59
def prefixEnd_2789590 : Nat := 4983230072969 + 3 ^ 40 * 2789590 * 2
def baseEnd_2789590 : Nat := 954933665983897299997277

theorem tailTrace_2789590 : CollatzResearch.WordTrace tailWord_2789590 prefixEnd_2789590 954933665983897299997277 := by
  unfold tailWord_2789590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6359044122737458055440889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67829803975866219258036149 6359044122737458055440889)
  ·
    refine ⟨4769283092053093541580667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6359044122737458055440889 4769283092053093541580667)
    ·
      refine ⟨7153924638079640312371001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4769283092053093541580667 7153924638079640312371001)
      ·
        refine ⟨5365443478559730234278251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7153924638079640312371001 5365443478559730234278251)
        ·
          refine ⟨8048165217839595351417377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365443478559730234278251 8048165217839595351417377)
          ·
            refine ⟨6036123913379696513563033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8048165217839595351417377 6036123913379696513563033)
            ·
              refine ⟨4527092935034772385172275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6036123913379696513563033 4527092935034772385172275)
              ·
                refine ⟨6790639402552158577758413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4527092935034772385172275 6790639402552158577758413)
                ·
                  refine ⟨2546489775957059466659405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6790639402552158577758413 2546489775957059466659405)
                  ·
                    refine ⟨954933665983897299997277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546489775957059466659405 954933665983897299997277)
                    ·
                      rfl

theorem cell22_2789590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_2789590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789590 prefixEnd_2789590 := by exact prefixLift 2789590
  have htrace : WordTrace (prefixWord ++ tailWord_2789590) baseStart_2789590 baseEnd_2789590 := by
    simpa [prefixWord, tailWord_2789590, baseEnd_2789590] using wordTrace_append hprefix tailTrace_2789590
  have hstable : (prefixWord ++ tailWord_2789590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789590).length < 2 ^ (prefixWord ++ tailWord_2789590).sum := by decide
  have hdescent : baseEnd_2789590 < baseStart_2789590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789629 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_2789629 : Nat := 118140960795 + 2789629 * 2 ^ 59
def prefixEnd_2789629 : Nat := 4983230072969 + 3 ^ 40 * 2789629 * 2
def baseEnd_2789629 : Nat := 954947016480914198272157

theorem tailTrace_2789629 : CollatzResearch.WordTrace tailWord_2789629 prefixEnd_2789629 954947016480914198272157 := by
  unfold tailWord_2789629
  simp only [CollatzResearch.WordTrace]
  refine ⟨101746128410658038547723941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67830752273772025698482627 101746128410658038547723941)
  ·
    refine ⟨19077399076998382227698239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101746128410658038547723941 19077399076998382227698239)
    ·
      refine ⟨28616098615497573341547359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19077399076998382227698239 28616098615497573341547359)
      ·
        refine ⟨42924147923246360012321039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28616098615497573341547359 42924147923246360012321039)
        ·
          refine ⟨64386221884869540018481559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42924147923246360012321039 64386221884869540018481559)
          ·
            refine ⟨96579332827304310027722339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64386221884869540018481559 96579332827304310027722339)
            ·
              refine ⟨144868999240956465041583509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96579332827304310027722339 144868999240956465041583509)
              ·
                refine ⟨6790734339419834298824227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144868999240956465041583509 6790734339419834298824227)
                ·
                  refine ⟨10186101509129751448236341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6790734339419834298824227 10186101509129751448236341)
                  ·
                    refine ⟨954947016480914198272157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10186101509129751448236341 954947016480914198272157)
                    ·
                      rfl

theorem cell22_2789629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_2789629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789629 prefixEnd_2789629 := by exact prefixLift 2789629
  have htrace : WordTrace (prefixWord ++ tailWord_2789629) baseStart_2789629 baseEnd_2789629 := by
    simpa [prefixWord, tailWord_2789629, baseEnd_2789629] using wordTrace_append hprefix tailTrace_2789629
  have hstable : (prefixWord ++ tailWord_2789629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789629).length < 2 ^ (prefixWord ++ tailWord_2789629).sum := by decide
  have hdescent : baseEnd_2789629 < baseStart_2789629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789646 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_2789646 : Nat := 118140960795 + 2789646 * 2 ^ 59
def prefixEnd_2789646 : Nat := 4983230072969 + 3 ^ 40 * 2789646 * 2
def baseEnd_2789646 : Nat := 954952835928331820597105

theorem tailTrace_2789646 : CollatzResearch.WordTrace tailWord_2789646 prefixEnd_2789646 954952835928331820597105 := by
  unfold tailWord_2789646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12718343556449556306386599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67831165634397633634061861 12718343556449556306386599)
  ·
    refine ⟨19077515334674334459579899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12718343556449556306386599 19077515334674334459579899)
    ·
      refine ⟨28616273002011501689369849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19077515334674334459579899 28616273002011501689369849)
      ·
        refine ⟨21462204751508626267027387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28616273002011501689369849 21462204751508626267027387)
        ·
          refine ⟨32193307127262939400541081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21462204751508626267027387 32193307127262939400541081)
          ·
            refine ⟨24144980345447204550405811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32193307127262939400541081 24144980345447204550405811)
            ·
              refine ⟨36217470518170806825608717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24144980345447204550405811 36217470518170806825608717)
              ·
                refine ⟨13581551444314052559603269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36217470518170806825608717 13581551444314052559603269)
                ·
                  refine ⟨2546540895808884854925613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13581551444314052559603269 2546540895808884854925613)
                  ·
                    refine ⟨954952835928331820597105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546540895808884854925613 954952835928331820597105)
                    ·
                      rfl

theorem cell22_2789646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_2789646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789646 prefixEnd_2789646 := by exact prefixLift 2789646
  have htrace : WordTrace (prefixWord ++ tailWord_2789646) baseStart_2789646 baseEnd_2789646 := by
    simpa [prefixWord, tailWord_2789646, baseEnd_2789646] using wordTrace_append hprefix tailTrace_2789646
  have hstable : (prefixWord ++ tailWord_2789646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789646).length < 2 ^ (prefixWord ++ tailWord_2789646).sum := by decide
  have hdescent : baseEnd_2789646 < baseStart_2789646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789663 : List Nat := [1, 1, 2, 4, 3, 2, 1, 3, 2, 3]
def baseStart_2789663 : Nat := 118140960795 + 2789663 * 2 ^ 59
def prefixEnd_2789663 : Nat := 4983230072969 + 3 ^ 40 * 2789663 * 2
def baseEnd_2789663 : Nat := 954958655375749442922053

theorem tailTrace_2789663 : CollatzResearch.WordTrace tailWord_2789663 prefixEnd_2789663 954958655375749442922053 := by
  unfold tailWord_2789663
  simp only [CollatzResearch.WordTrace]
  refine ⟨101747368492534862354461643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67831578995023241569641095 101747368492534862354461643)
  ·
    refine ⟨152621052738802293531692465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101747368492534862354461643 152621052738802293531692465)
    ·
      refine ⟨114465789554101720148769349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152621052738802293531692465 114465789554101720148769349)
      ·
        refine ⟨21462335541394072527894253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114465789554101720148769349 21462335541394072527894253)
        ·
          refine ⟨8048375828022777197960345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21462335541394072527894253 8048375828022777197960345)
          ·
            refine ⟨6036281871017082898470259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8048375828022777197960345 6036281871017082898470259)
            ·
              refine ⟨9054422806525624347705389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6036281871017082898470259 9054422806525624347705389)
              ·
                refine ⟨3395408552447109130389521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9054422806525624347705389 3395408552447109130389521)
                ·
                  refine ⟨2546556414335331847792141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3395408552447109130389521 2546556414335331847792141)
                  ·
                    refine ⟨954958655375749442922053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546556414335331847792141 954958655375749442922053)
                    ·
                      rfl

theorem cell22_2789663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 3].length) (baseStart_2789663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789663 prefixEnd_2789663 := by exact prefixLift 2789663
  have htrace : WordTrace (prefixWord ++ tailWord_2789663) baseStart_2789663 baseEnd_2789663 := by
    simpa [prefixWord, tailWord_2789663, baseEnd_2789663] using wordTrace_append hprefix tailTrace_2789663
  have hstable : (prefixWord ++ tailWord_2789663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789663).length < 2 ^ (prefixWord ++ tailWord_2789663).sum := by decide
  have hdescent : baseEnd_2789663 < baseStart_2789663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789704 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 7]
def baseStart_2789704 : Nat := 118140960795 + 2789704 * 2 ^ 59
def prefixEnd_2789704 : Nat := 4983230072969 + 3 ^ 40 * 2789704 * 2
def baseEnd_2789704 : Nat := 318324230171213000882309

theorem tailTrace_2789704 : CollatzResearch.WordTrace tailWord_2789704 prefixEnd_2789704 318324230171213000882309 := by
  unfold tailWord_2789704
  simp only [CollatzResearch.WordTrace]
  refine ⟨50874431942693163178352083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67832575923590884237802777 50874431942693163178352083)
  ·
    refine ⟨76311647914039744767528125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50874431942693163178352083 76311647914039744767528125)
    ·
      refine ⟨28616867967764904287823047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76311647914039744767528125 28616867967764904287823047)
      ·
        refine ⟨42925301951647356431734571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28616867967764904287823047 42925301951647356431734571)
        ·
          refine ⟨64387952927471034647601857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42925301951647356431734571 64387952927471034647601857)
          ·
            refine ⟨48290964695603275985701393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64387952927471034647601857 48290964695603275985701393)
            ·
              refine ⟨36218223521702456989276045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48290964695603275985701393 36218223521702456989276045)
              ·
                refine ⟨13581833820638421370978517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36218223521702456989276045 13581833820638421370978517)
                ·
                  refine ⟨318324230171213000882309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13581833820638421370978517 318324230171213000882309)
                  ·
                    rfl

theorem cell22_2789704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_2789704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789704 prefixEnd_2789704 := by exact prefixLift 2789704
  have htrace : WordTrace (prefixWord ++ tailWord_2789704) baseStart_2789704 baseEnd_2789704 := by
    simpa [prefixWord, tailWord_2789704, baseEnd_2789704] using wordTrace_append hprefix tailTrace_2789704
  have hstable : (prefixWord ++ tailWord_2789704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789704).length < 2 ^ (prefixWord ++ tailWord_2789704).sum := by decide
  have hdescent : baseEnd_2789704 < baseStart_2789704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789796 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_2789796 : Nat := 118140960795 + 2789796 * 2 ^ 59
def prefixEnd_2789796 : Nat := 4983230072969 + 3 ^ 40 * 2789796 * 2
def baseEnd_2789796 : Nat := 955004183993781429346645

theorem tailTrace_2789796 : CollatzResearch.WordTrace tailWord_2789796 prefixEnd_2789796 955004183993781429346645 := by
  unfold tailWord_2789796
  simp only [CollatzResearch.WordTrace]
  refine ⟨50876109700526513034526621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67834812934035350712702161 50876109700526513034526621)
  ·
    refine ⟨19078541137697442387947483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50876109700526513034526621 19078541137697442387947483)
    ·
      refine ⟨28617811706546163581921225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19078541137697442387947483 28617811706546163581921225)
      ·
        refine ⟨21463358779909622686440919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28617811706546163581921225 21463358779909622686440919)
        ·
          refine ⟨32195038169864434029661379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21463358779909622686440919 32195038169864434029661379)
          ·
            refine ⟨48292557254796651044492069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32195038169864434029661379 48292557254796651044492069)
            ·
              refine ⟨9054854485274372070842263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48292557254796651044492069 9054854485274372070842263)
              ·
                refine ⟨13582281727911558106263395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9054854485274372070842263 13582281727911558106263395)
                ·
                  refine ⟨20373422591867337159395093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13582281727911558106263395 20373422591867337159395093)
                  ·
                    refine ⟨955004183993781429346645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20373422591867337159395093 955004183993781429346645)
                    ·
                      rfl

theorem cell22_2789796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_2789796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789796 prefixEnd_2789796 := by exact prefixLift 2789796
  have htrace : WordTrace (prefixWord ++ tailWord_2789796) baseStart_2789796 baseEnd_2789796 := by
    simpa [prefixWord, tailWord_2789796, baseEnd_2789796] using wordTrace_append hprefix tailTrace_2789796
  have hstable : (prefixWord ++ tailWord_2789796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789796).length < 2 ^ (prefixWord ++ tailWord_2789796).sum := by decide
  have hdescent : baseEnd_2789796 < baseStart_2789796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789832 : List Nat := [2, 1, 3, 1, 3, 4, 2, 1, 2, 3]
def baseStart_2789832 : Nat := 118140960795 + 2789832 * 2 ^ 59
def prefixEnd_2789832 : Nat := 4983230072969 + 3 ^ 40 * 2789832 * 2
def baseEnd_2789832 : Nat := 955016507529489335446535

theorem tailTrace_2789832 : CollatzResearch.WordTrace tailWord_2789832 prefixEnd_2789832 955016507529489335446535 := by
  unfold tailWord_2789832
  simp only [CollatzResearch.WordTrace]
  refine ⟨50876766214461302108681875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67835688285948402811575833 50876766214461302108681875)
  ·
    refine ⟨76315149321691953163022813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50876766214461302108681875 76315149321691953163022813)
    ·
      refine ⟨28618180995634482436133555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76315149321691953163022813 28618180995634482436133555)
      ·
        refine ⟨42927271493451723654200333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28618180995634482436133555 42927271493451723654200333)
        ·
          refine ⟨16097726810044396370325125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42927271493451723654200333 16097726810044396370325125)
          ·
            refine ⟨3018323776883324319435961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16097726810044396370325125 3018323776883324319435961)
            ·
              refine ⟨2263742832662493239576971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3018323776883324319435961 2263742832662493239576971)
              ·
                refine ⟨3395614248993739859365457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2263742832662493239576971 3395614248993739859365457)
                ·
                  refine ⟨2546710686745304894524093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3395614248993739859365457 2546710686745304894524093)
                  ·
                    refine ⟨955016507529489335446535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546710686745304894524093 955016507529489335446535)
                    ·
                      rfl

theorem cell22_2789832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_2789832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789832 prefixEnd_2789832 := by exact prefixLift 2789832
  have htrace : WordTrace (prefixWord ++ tailWord_2789832) baseStart_2789832 baseEnd_2789832 := by
    simpa [prefixWord, tailWord_2789832, baseEnd_2789832] using wordTrace_append hprefix tailTrace_2789832
  have hstable : (prefixWord ++ tailWord_2789832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789832).length < 2 ^ (prefixWord ++ tailWord_2789832).sum := by decide
  have hdescent : baseEnd_2789832 < baseStart_2789832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789871 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 2, 5]
def baseStart_2789871 : Nat := 118140960795 + 2789871 * 2 ^ 59
def prefixEnd_2789871 : Nat := 4983230072969 + 3 ^ 40 * 2789871 * 2
def baseEnd_2789871 : Nat := 955029858026506233721415

theorem tailTrace_2789871 : CollatzResearch.WordTrace tailWord_2789871 prefixEnd_2789871 955029858026506233721415 := by
  unfold tailWord_2789871
  simp only [CollatzResearch.WordTrace]
  refine ⟨101754954875781313878033467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67836636583854209252022311 101754954875781313878033467)
  ·
    refine ⟨152632432313671970817050201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101754954875781313878033467 152632432313671970817050201)
    ·
      refine ⟨114474324235253978112787651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152632432313671970817050201 114474324235253978112787651)
      ·
        refine ⟨171711486352880967169181477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114474324235253978112787651 171711486352880967169181477)
        ·
          refine ⟨32195903691165181344221527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171711486352880967169181477 32195903691165181344221527)
          ·
            refine ⟨48293855536747772016332291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32195903691165181344221527 48293855536747772016332291)
            ·
              refine ⟨72440783305121658024498437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48293855536747772016332291 72440783305121658024498437)
              ·
                refine ⟨13582646869710310879593457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72440783305121658024498437 13582646869710310879593457)
                ·
                  refine ⟨10186985152282733159695093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13582646869710310879593457 10186985152282733159695093)
                  ·
                    refine ⟨955029858026506233721415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10186985152282733159695093 955029858026506233721415)
                    ·
                      rfl

theorem cell22_2789871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_2789871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789871 prefixEnd_2789871 := by exact prefixLift 2789871
  have htrace : WordTrace (prefixWord ++ tailWord_2789871) baseStart_2789871 baseEnd_2789871 := by
    simpa [prefixWord, tailWord_2789871, baseEnd_2789871] using wordTrace_append hprefix tailTrace_2789871
  have hstable : (prefixWord ++ tailWord_2789871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789871).length < 2 ^ (prefixWord ++ tailWord_2789871).sum := by decide
  have hdescent : baseEnd_2789871 < baseStart_2789871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789873 : List Nat := [1, 2, 2, 2, 3, 1, 4, 2, 5]
def baseStart_2789873 : Nat := 118140960795 + 2789873 * 2 ^ 59
def prefixEnd_2789873 : Nat := 4983230072969 + 3 ^ 40 * 2789873 * 2
def baseEnd_2789873 : Nat := 318343514222459631723803

theorem tailTrace_2789873 : CollatzResearch.WordTrace tailWord_2789873 prefixEnd_2789873 318343514222459631723803 := by
  unfold tailWord_2789873
  simp only [CollatzResearch.WordTrace]
  refine ⟨101755027821774068219606273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67836685214516045479737515 101755027821774068219606273)
  ·
    refine ⟨76316270866330551164704705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101755027821774068219606273 76316270866330551164704705)
    ·
      refine ⟨57237203149747913373528529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76316270866330551164704705 57237203149747913373528529)
      ·
        refine ⟨42927902362310935030146397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57237203149747913373528529 42927902362310935030146397)
        ·
          refine ⟨16097963385866600636304899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42927902362310935030146397 16097963385866600636304899)
          ·
            refine ⟨24146945078799900954457349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16097963385866600636304899 24146945078799900954457349)
            ·
              refine ⟨4527552202274981428960753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24146945078799900954457349 4527552202274981428960753)
              ·
                refine ⟨3395664151706236071720565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4527552202274981428960753 3395664151706236071720565)
                ·
                  refine ⟨318343514222459631723803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3395664151706236071720565 318343514222459631723803)
                  ·
                    rfl

theorem cell22_2789873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_2789873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789873 prefixEnd_2789873 := by exact prefixLift 2789873
  have htrace : WordTrace (prefixWord ++ tailWord_2789873) baseStart_2789873 baseEnd_2789873 := by
    simpa [prefixWord, tailWord_2789873, baseEnd_2789873] using wordTrace_append hprefix tailTrace_2789873
  have hstable : (prefixWord ++ tailWord_2789873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789873).length < 2 ^ (prefixWord ++ tailWord_2789873).sum := by decide
  have hdescent : baseEnd_2789873 < baseStart_2789873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789894 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2789894 : Nat := 118140960795 + 2789894 * 2 ^ 59
def prefixEnd_2789894 : Nat := 4983230072969 + 3 ^ 40 * 2789894 * 2
def baseEnd_2789894 : Nat := 955037731396541840396345

theorem tailTrace_2789894 : CollatzResearch.WordTrace tailWord_2789894 prefixEnd_2789894 955037731396541840396345 := by
  unfold tailWord_2789894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179868554834312150191273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67837195836465325870747157 3179868554834312150191273)
  ·
    refine ⟨2384901416125734112643455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3179868554834312150191273 2384901416125734112643455)
    ·
      refine ⟨3577352124188601168965183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2384901416125734112643455 3577352124188601168965183)
      ·
        refine ⟨5366028186282901753447775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3577352124188601168965183 5366028186282901753447775)
        ·
          refine ⟨8049042279424352630171663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5366028186282901753447775 8049042279424352630171663)
          ·
            refine ⟨12073563419136528945257495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8049042279424352630171663 12073563419136528945257495)
            ·
              refine ⟨18110345128704793417886243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12073563419136528945257495 18110345128704793417886243)
              ·
                refine ⟨27165517693057190126829365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18110345128704793417886243 27165517693057190126829365)
                ·
                  refine ⟨2546767283724111574390253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27165517693057190126829365 2546767283724111574390253)
                  ·
                    refine ⟨955037731396541840396345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546767283724111574390253 955037731396541840396345)
                    ·
                      rfl

theorem cell22_2789894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2789894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789894 prefixEnd_2789894 := by exact prefixLift 2789894
  have htrace : WordTrace (prefixWord ++ tailWord_2789894) baseStart_2789894 baseEnd_2789894 := by
    simpa [prefixWord, tailWord_2789894, baseEnd_2789894] using wordTrace_append hprefix tailTrace_2789894
  have hstable : (prefixWord ++ tailWord_2789894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789894).length < 2 ^ (prefixWord ++ tailWord_2789894).sum := by decide
  have hdescent : baseEnd_2789894 < baseStart_2789894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789924 : List Nat := [2, 3, 1, 5, 2, 1, 1, 2, 5]
def baseStart_2789924 : Nat := 118140960795 + 2789924 * 2 ^ 59
def prefixEnd_2789924 : Nat := 4983230072969 + 3 ^ 40 * 2789924 * 2
def baseEnd_2789924 : Nat := 318349333669877254048751

theorem tailTrace_2789924 : CollatzResearch.WordTrace tailWord_2789924 prefixEnd_2789924 318349333669877254048751 := by
  unfold tailWord_2789924
  simp only [CollatzResearch.WordTrace]
  refine ⟨50878443972294651964856413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67837925296392869286475217 50878443972294651964856413)
  ·
    refine ⟨19079416489610494486821155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50878443972294651964856413 19079416489610494486821155)
    ·
      refine ⟨28619124734415741730231733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19079416489610494486821155 28619124734415741730231733)
      ·
        refine ⟨2683042943851475787209225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28619124734415741730231733 2683042943851475787209225)
        ·
          refine ⟨2012282207888606840406919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2683042943851475787209225 2012282207888606840406919)
          ·
            refine ⟨3018423311832910260610379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012282207888606840406919 3018423311832910260610379)
            ·
              refine ⟨4527634967749365390915569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018423311832910260610379 4527634967749365390915569)
              ·
                refine ⟨3395726225812024043186677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4527634967749365390915569 3395726225812024043186677)
                ·
                  refine ⟨318349333669877254048751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3395726225812024043186677 318349333669877254048751)
                  ·
                    rfl

theorem cell22_2789924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_2789924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789924 prefixEnd_2789924 := by exact prefixLift 2789924
  have htrace : WordTrace (prefixWord ++ tailWord_2789924) baseStart_2789924 baseEnd_2789924 := by
    simpa [prefixWord, tailWord_2789924, baseEnd_2789924] using wordTrace_append hprefix tailTrace_2789924
  have hstable : (prefixWord ++ tailWord_2789924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789924).length < 2 ^ (prefixWord ++ tailWord_2789924).sum := by decide
  have hdescent : baseEnd_2789924 < baseStart_2789924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789948 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_2789948 : Nat := 118140960795 + 2789948 * 2 ^ 59
def prefixEnd_2789948 : Nat := 4983230072969 + 3 ^ 40 * 2789948 * 2
def baseEnd_2789948 : Nat := 955056216700103699546179

theorem tailTrace_2789948 : CollatzResearch.WordTrace tailWord_2789948 prefixEnd_2789948 955056216700103699546179 := by
  unfold tailWord_2789948
  simp only [CollatzResearch.WordTrace]
  refine ⟨50878881648251178014293249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67838508864334904019057665 50878881648251178014293249)
  ·
    refine ⟨38159161236188383510719937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50878881648251178014293249 38159161236188383510719937)
    ·
      refine ⟨28619370927141287633039953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38159161236188383510719937 28619370927141287633039953)
      ·
        refine ⟨21464528195355965724779965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28619370927141287633039953 21464528195355965724779965)
        ·
          refine ⟨8049198073258487146792487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21464528195355965724779965 8049198073258487146792487)
          ·
            refine ⟨12073797109887730720188731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8049198073258487146792487 12073797109887730720188731)
            ·
              refine ⟨18110695664831596080283097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12073797109887730720188731 18110695664831596080283097)
              ·
                refine ⟨13583021748623697060212323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18110695664831596080283097 13583021748623697060212323)
                ·
                  refine ⟨20374532622935545590318485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13583021748623697060212323 20374532622935545590318485)
                  ·
                    refine ⟨955056216700103699546179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20374532622935545590318485 955056216700103699546179)
                    ·
                      rfl

theorem cell22_2789948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_2789948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789948 prefixEnd_2789948 := by exact prefixLift 2789948
  have htrace : WordTrace (prefixWord ++ tailWord_2789948) baseStart_2789948 baseEnd_2789948 := by
    simpa [prefixWord, tailWord_2789948, baseEnd_2789948] using wordTrace_append hprefix tailTrace_2789948
  have hstable : (prefixWord ++ tailWord_2789948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789948).length < 2 ^ (prefixWord ++ tailWord_2789948).sum := by decide
  have hdescent : baseEnd_2789948 < baseStart_2789948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789963 : List Nat := [1, 1, 1, 1, 3, 1, 8, 6]
def baseStart_2789963 : Nat := 118140960795 + 2789963 * 2 ^ 59
def prefixEnd_2789963 : Nat := 4983230072969 + 3 ^ 40 * 2789963 * 2
def baseEnd_2789963 : Nat := 106117927945183184491237

theorem tailTrace_2789963 : CollatzResearch.WordTrace tailWord_2789963 prefixEnd_2789963 106117927945183184491237 := by
  unfold tailWord_2789963
  simp only [CollatzResearch.WordTrace]
  refine ⟨101758310391448013590382543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67838873594298675726921695 101758310391448013590382543)
  ·
    refine ⟨152637465587172020385573815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101758310391448013590382543 152637465587172020385573815)
    ·
      refine ⟨228956198380758030578360723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152637465587172020385573815 228956198380758030578360723)
      ·
        refine ⟨343434297571137045867541085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228956198380758030578360723 343434297571137045867541085)
        ·
          refine ⟨128787861589176392200327907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343434297571137045867541085 128787861589176392200327907)
          ·
            refine ⟨193181792383764588300491861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128787861589176392200327907 193181792383764588300491861)
            ·
              refine ⟨2263849129497241269146389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 193181792383764588300491861 2263849129497241269146389)
              ·
                refine ⟨106117927945183184491237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2263849129497241269146389 106117927945183184491237)
                ·
                  rfl

theorem cell22_2789963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 6].length) (baseStart_2789963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789963 prefixEnd_2789963 := by exact prefixLift 2789963
  have htrace : WordTrace (prefixWord ++ tailWord_2789963) baseStart_2789963 baseEnd_2789963 := by
    simpa [prefixWord, tailWord_2789963, baseEnd_2789963] using wordTrace_append hprefix tailTrace_2789963
  have hstable : (prefixWord ++ tailWord_2789963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789963).length < 2 ^ (prefixWord ++ tailWord_2789963).sum := by decide
  have hdescent : baseEnd_2789963 < baseStart_2789963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789965 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2789965 : Nat := 118140960795 + 2789965 * 2 ^ 59
def prefixEnd_2789965 : Nat := 4983230072969 + 3 ^ 40 * 2789965 * 2
def baseEnd_2789965 : Nat := 955062036147521321871127

theorem tailTrace_2789965 : CollatzResearch.WordTrace tailWord_2789965 prefixEnd_2789965 955062036147521321871127 := by
  unfold tailWord_2789965
  simp only [CollatzResearch.WordTrace]
  refine ⟨101758383337440767931955349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67838922224960511954636899 101758383337440767931955349)
  ·
    refine ⟨4769924218942535996810407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101758383337440767931955349 4769924218942535996810407)
    ·
      refine ⟨7154886328413803995215611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4769924218942535996810407 7154886328413803995215611)
      ·
        refine ⟨10732329492620705992823417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7154886328413803995215611 10732329492620705992823417)
        ·
          refine ⟨8049247119465529494617563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10732329492620705992823417 8049247119465529494617563)
          ·
            refine ⟨12073870679198294241926345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8049247119465529494617563 12073870679198294241926345)
            ·
              refine ⟨9055403009398720681444759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12073870679198294241926345 9055403009398720681444759)
              ·
                refine ⟨13583104514098081022167139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9055403009398720681444759 13583104514098081022167139)
                ·
                  refine ⟨20374656771147121533250709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13583104514098081022167139 20374656771147121533250709)
                  ·
                    refine ⟨955062036147521321871127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20374656771147121533250709 955062036147521321871127)
                    ·
                      rfl

theorem cell22_2789965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2789965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789965 prefixEnd_2789965 := by exact prefixLift 2789965
  have htrace : WordTrace (prefixWord ++ tailWord_2789965) baseStart_2789965 baseEnd_2789965 := by
    simpa [prefixWord, tailWord_2789965, baseEnd_2789965] using wordTrace_append hprefix tailTrace_2789965
  have hstable : (prefixWord ++ tailWord_2789965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789965).length < 2 ^ (prefixWord ++ tailWord_2789965).sum := by decide
  have hdescent : baseEnd_2789965 < baseStart_2789965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789980 : List Nat := [2, 2, 4, 1, 3, 2, 8]
def baseStart_2789980 : Nat := 118140960795 + 2789980 * 2 ^ 59
def prefixEnd_2789980 : Nat := 4983230072969 + 3 ^ 40 * 2789980 * 2
def baseEnd_2789980 : Nat := 35372858183483936398003

theorem tailTrace_2789980 : CollatzResearch.WordTrace tailWord_2789980 prefixEnd_2789980 35372858183483936398003 := by
  unfold tailWord_2789980
  simp only [CollatzResearch.WordTrace]
  refine ⟨50879465216193212746875697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67839286954924283662500929 50879465216193212746875697)
  ·
    refine ⟨38159598912144909560156773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50879465216193212746875697 38159598912144909560156773)
    ·
      refine ⟨7154924796027170542529395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38159598912144909560156773 7154924796027170542529395)
      ·
        refine ⟨10732387194040755813794093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7154924796027170542529395 10732387194040755813794093)
        ·
          refine ⟨4024645197765283430172785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10732387194040755813794093 4024645197765283430172785)
          ·
            refine ⟨3018483898323962572629589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4024645197765283430172785 3018483898323962572629589)
            ·
              refine ⟨35372858183483936398003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3018483898323962572629589 35372858183483936398003)
              ·
                rfl

theorem cell22_2789980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 8].length) (baseStart_2789980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789980 prefixEnd_2789980 := by exact prefixLift 2789980
  have htrace : WordTrace (prefixWord ++ tailWord_2789980) baseStart_2789980 baseEnd_2789980 := by
    simpa [prefixWord, tailWord_2789980, baseEnd_2789980] using wordTrace_append hprefix tailTrace_2789980
  have hstable : (prefixWord ++ tailWord_2789980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789980).length < 2 ^ (prefixWord ++ tailWord_2789980).sum := by decide
  have hdescent : baseEnd_2789980 < baseStart_2789980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789986 : List Nat := [3, 3, 2, 3, 1, 1, 3, 2, 4]
def baseStart_2789986 : Nat := 118140960795 + 2789986 * 2 ^ 59
def prefixEnd_2789986 : Nat := 4983230072969 + 3 ^ 40 * 2789986 * 2
def baseEnd_2789986 : Nat := 318356408292228089032021

theorem tailTrace_2789986 : CollatzResearch.WordTrace tailWord_2789986 prefixEnd_2789986 318356408292228089032021 := by
  unfold tailWord_2789986
  simp only [CollatzResearch.WordTrace]
  refine ⟨25439787317591172129617453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67839432846909792345646541 25439787317591172129617453)
  ·
    refine ⟨9539920244096689548606545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25439787317591172129617453 9539920244096689548606545)
    ·
      refine ⟨7154940183072517161454909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9539920244096689548606545 7154940183072517161454909)
      ·
        refine ⟨2683102568652193935545591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7154940183072517161454909 2683102568652193935545591)
        ·
          refine ⟨4024653852978290903318387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683102568652193935545591 4024653852978290903318387)
          ·
            refine ⟨6036980779467436354977581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4024653852978290903318387 6036980779467436354977581)
            ·
              refine ⟨2263867792300288633116593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6036980779467436354977581 2263867792300288633116593)
              ·
                refine ⟨1697900844225216474837445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2263867792300288633116593 1697900844225216474837445)
                ·
                  refine ⟨318356408292228089032021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1697900844225216474837445 318356408292228089032021)
                  ·
                    rfl

theorem cell22_2789986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_2789986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2789986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2789986 prefixEnd_2789986 := by exact prefixLift 2789986
  have htrace : WordTrace (prefixWord ++ tailWord_2789986) baseStart_2789986 baseEnd_2789986 := by
    simpa [prefixWord, tailWord_2789986, baseEnd_2789986] using wordTrace_append hprefix tailTrace_2789986
  have hstable : (prefixWord ++ tailWord_2789986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789986).length < 2 ^ (prefixWord ++ tailWord_2789986).sum := by decide
  have hdescent : baseEnd_2789986 < baseStart_2789986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790008 : List Nat := [2, 1, 2, 1, 1, 1, 2, 7, 5]
def baseStart_2790008 : Nat := 118140960795 + 2790008 * 2 ^ 59
def prefixEnd_2790008 : Nat := 4983230072969 + 3 ^ 40 * 2790008 * 2
def baseEnd_2790008 : Nat := 318358918642094514348665

theorem tailTrace_2790008 : CollatzResearch.WordTrace tailWord_2790008 prefixEnd_2790008 318358918642094514348665 := by
  unfold tailWord_2790008
  simp only [CollatzResearch.WordTrace]
  refine ⟨50879975838142493137885339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67839967784189990850513785 50879975838142493137885339)
  ·
    refine ⟨76319963757213739706828009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50879975838142493137885339 76319963757213739706828009)
    ·
      refine ⟨57239972817910304780121007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76319963757213739706828009 57239972817910304780121007)
      ·
        refine ⟨85859959226865457170181511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57239972817910304780121007 85859959226865457170181511)
        ·
          refine ⟨128789938840298185755272267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85859959226865457170181511 128789938840298185755272267)
          ·
            refine ⟨193184908260447278632908401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128789938840298185755272267 193184908260447278632908401)
            ·
              refine ⟨144888681195335458974681301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193184908260447278632908401 144888681195335458974681301)
              ·
                refine ⟨3395828465515674819719093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 144888681195335458974681301 3395828465515674819719093)
                ·
                  refine ⟨318358918642094514348665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3395828465515674819719093 318358918642094514348665)
                  ·
                    rfl

theorem cell22_2790008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_2790008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790008 prefixEnd_2790008 := by exact prefixLift 2790008
  have htrace : WordTrace (prefixWord ++ tailWord_2790008) baseStart_2790008 baseEnd_2790008 := by
    simpa [prefixWord, tailWord_2790008, baseEnd_2790008] using wordTrace_append hprefix tailTrace_2790008
  have hstable : (prefixWord ++ tailWord_2790008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790008).length < 2 ^ (prefixWord ++ tailWord_2790008).sum := by decide
  have hdescent : baseEnd_2790008 < baseStart_2790008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790053 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 6]
def baseStart_2790053 : Nat := 118140960795 + 2790053 * 2 ^ 59
def prefixEnd_2790053 : Nat := 4983230072969 + 3 ^ 40 * 2790053 * 2
def baseEnd_2790053 : Nat := 318364053448639475223619

theorem tailTrace_2790053 : CollatzResearch.WordTrace tailWord_2790053 prefixEnd_2790053 318364053448639475223619 := by
  unfold tailWord_2790053
  simp only [CollatzResearch.WordTrace]
  refine ⟨101761592961121958961158813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67841061974081305974105875 101761592961121958961158813)
  ·
    refine ⟨38160597360420734610434555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101761592961121958961158813 38160597360420734610434555)
    ·
      refine ⟨57240896040631101915651833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38160597360420734610434555 57240896040631101915651833)
      ·
        refine ⟨42930672030473326436738875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57240896040631101915651833 42930672030473326436738875)
        ·
          refine ⟨64396008045709989655108313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42930672030473326436738875 64396008045709989655108313)
          ·
            refine ⟨48297006034282492241331235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64396008045709989655108313 48297006034282492241331235)
            ·
              refine ⟨72445509051423738361996853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48297006034282492241331235 72445509051423738361996853)
              ·
                refine ⟨6791766473570975471437205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72445509051423738361996853 6791766473570975471437205)
                ·
                  refine ⟨318364053448639475223619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6791766473570975471437205 318364053448639475223619)
                  ·
                    rfl

theorem cell22_2790053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_2790053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790053 prefixEnd_2790053 := by exact prefixLift 2790053
  have htrace : WordTrace (prefixWord ++ tailWord_2790053) baseStart_2790053 baseEnd_2790053 := by
    simpa [prefixWord, tailWord_2790053, baseEnd_2790053] using wordTrace_append hprefix tailTrace_2790053
  have hstable : (prefixWord ++ tailWord_2790053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790053).length < 2 ^ (prefixWord ++ tailWord_2790053).sum := by decide
  have hdescent : baseEnd_2790053 < baseStart_2790053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790333 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_2790333 : Nat := 118140960795 + 2790333 * 2 ^ 59
def prefixEnd_2790333 : Nat := 4983230072969 + 3 ^ 40 * 2790333 * 2
def baseEnd_2790333 : Nat := 955188010068091028669999

theorem tailTrace_2790333 : CollatzResearch.WordTrace tailWord_2790333 prefixEnd_2790333 955188010068091028669999 := by
  unfold tailWord_2790333
  simp only [CollatzResearch.WordTrace]
  refine ⟨101771805400107566781351653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67847870266738377854234435 101771805400107566781351653)
  ·
    refine ⟨19082213512520168771503435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101771805400107566781351653 19082213512520168771503435)
    ·
      refine ⟨28623320268780253157255153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19082213512520168771503435 28623320268780253157255153)
      ·
        refine ⟨21467490201585189867941365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28623320268780253157255153 21467490201585189867941365)
        ·
          refine ⟨2012577206398611550119503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21467490201585189867941365 2012577206398611550119503)
          ·
            refine ⟨3018865809597917325179255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012577206398611550119503 3018865809597917325179255)
            ·
              refine ⟨4528298714396875987768883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018865809597917325179255 4528298714396875987768883)
              ·
                refine ⟨6792448071595313981653325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528298714396875987768883 6792448071595313981653325)
                ·
                  refine ⟨2547168026848242743119997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6792448071595313981653325 2547168026848242743119997)
                  ·
                    refine ⟨955188010068091028669999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2547168026848242743119997 955188010068091028669999)
                    ·
                      rfl

theorem cell22_2790333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_2790333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790333 prefixEnd_2790333 := by exact prefixLift 2790333
  have htrace : WordTrace (prefixWord ++ tailWord_2790333) baseStart_2790333 baseEnd_2790333 := by
    simpa [prefixWord, tailWord_2790333, baseEnd_2790333] using wordTrace_append hprefix tailTrace_2790333
  have hstable : (prefixWord ++ tailWord_2790333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790333).length < 2 ^ (prefixWord ++ tailWord_2790333).sum := by decide
  have hdescent : baseEnd_2790333 < baseStart_2790333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790421 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 2, 4]
def baseStart_2790421 : Nat := 118140960795 + 2790421 * 2 ^ 59
def prefixEnd_2790421 : Nat := 4983230072969 + 3 ^ 40 * 2790421 * 2
def baseEnd_2790421 : Nat := 955218134266488132469729

theorem tailTrace_2790421 : CollatzResearch.WordTrace tailWord_2790421 prefixEnd_2790421 955218134266488132469729 := by
  unfold tailWord_2790421
  simp only [CollatzResearch.WordTrace]
  refine ⟨101775015023788757810555117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67850010015859171873703411 101775015023788757810555117)
  ·
    refine ⟨38165630633920784178958169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101775015023788757810555117 38165630633920784178958169)
    ·
      refine ⟨28624222975440588134218627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38165630633920784178958169 28624222975440588134218627)
      ·
        refine ⟨42936334463160882201327941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28624222975440588134218627 42936334463160882201327941)
        ·
          refine ⟨8050562711842665412748989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42936334463160882201327941 8050562711842665412748989)
          ·
            refine ⟨3018961016940999529780871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8050562711842665412748989 3018961016940999529780871)
            ·
              refine ⟨4528441525411499294671307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018961016940999529780871 4528441525411499294671307)
              ·
                refine ⟨6792662288117248942006961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528441525411499294671307 6792662288117248942006961)
                ·
                  refine ⟨5094496716087936706505221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6792662288117248942006961 5094496716087936706505221)
                  ·
                    refine ⟨955218134266488132469729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5094496716087936706505221 955218134266488132469729)
                    ·
                      rfl

theorem cell22_2790421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_2790421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790421 prefixEnd_2790421 := by exact prefixLift 2790421
  have htrace : WordTrace (prefixWord ++ tailWord_2790421) baseStart_2790421 baseEnd_2790421 := by
    simpa [prefixWord, tailWord_2790421, baseEnd_2790421] using wordTrace_append hprefix tailTrace_2790421
  have hstable : (prefixWord ++ tailWord_2790421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790421).length < 2 ^ (prefixWord ++ tailWord_2790421).sum := by decide
  have hdescent : baseEnd_2790421 < baseStart_2790421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790524 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_2790524 : Nat := 118140960795 + 2790524 * 2 ^ 59
def prefixEnd_2790524 : Nat := 4983230072969 + 3 ^ 40 * 2790524 * 2
def baseEnd_2790524 : Nat := 955253393271430197144413

theorem tailTrace_2790524 : CollatzResearch.WordTrace tailWord_2790524 prefixEnd_2790524 955253393271430197144413 := by
  unfold tailWord_2790524
  simp only [CollatzResearch.WordTrace]
  refine ⟨50889385871207803200777313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67852514494943737601036417 50889385871207803200777313)
  ·
    refine ⟨38167039403405852400582985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50889385871207803200777313 38167039403405852400582985)
    ·
      refine ⟨28625279552554389300437239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38167039403405852400582985 28625279552554389300437239)
      ·
        refine ⟨42937919328831583950655859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28625279552554389300437239 42937919328831583950655859)
        ·
          refine ⟨64406878993247375925983789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42937919328831583950655859 64406878993247375925983789)
          ·
            refine ⟨24152579622467765972243921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64406878993247375925983789 24152579622467765972243921)
            ·
              refine ⟨18114434716850824479182941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24152579622467765972243921 18114434716850824479182941)
              ·
                refine ⟨6792913018819059179693603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18114434716850824479182941 6792913018819059179693603)
                ·
                  refine ⟨10189369528228588769540405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6792913018819059179693603 10189369528228588769540405)
                  ·
                    refine ⟨955253393271430197144413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10189369528228588769540405 955253393271430197144413)
                    ·
                      rfl

theorem cell22_2790524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_2790524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790524 prefixEnd_2790524 := by exact prefixLift 2790524
  have htrace : WordTrace (prefixWord ++ tailWord_2790524) baseStart_2790524 baseEnd_2790524 := by
    simpa [prefixWord, tailWord_2790524, baseEnd_2790524] using wordTrace_append hprefix tailTrace_2790524
  have hstable : (prefixWord ++ tailWord_2790524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790524).length < 2 ^ (prefixWord ++ tailWord_2790524).sum := by decide
  have hdescent : baseEnd_2790524 < baseStart_2790524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790554 : List Nat := [3, 1, 1, 5, 1, 11]
def baseStart_2790554 : Nat := 118140960795 + 2790554 * 2 ^ 59
def prefixEnd_2790554 : Nat := 4983230072969 + 3 ^ 40 * 2790554 * 2
def baseEnd_2790554 : Nat := 11793378554129878011041

theorem tailTrace_2790554 : CollatzResearch.WordTrace tailWord_2790554 prefixEnd_2790554 11793378554129878011041 := by
  unfold tailWord_2790554
  simp only [CollatzResearch.WordTrace]
  refine ⟨25444966483076730381286679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67853243954871281016764477 25444966483076730381286679)
  ·
    refine ⟨38167449724615095571930019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25444966483076730381286679 38167449724615095571930019)
    ·
      refine ⟨57251174586922643357895029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38167449724615095571930019 57251174586922643357895029)
      ·
        refine ⟨5367297617523997814802659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57251174586922643357895029 5367297617523997814802659)
        ·
          refine ⟨8050946426285996722203989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5367297617523997814802659 8050946426285996722203989)
          ·
            refine ⟨11793378554129878011041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8050946426285996722203989 11793378554129878011041)
            ·
              rfl

theorem cell22_2790554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 11].length) (baseStart_2790554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790554 prefixEnd_2790554 := by exact prefixLift 2790554
  have htrace : WordTrace (prefixWord ++ tailWord_2790554) baseStart_2790554 baseEnd_2790554 := by
    simpa [prefixWord, tailWord_2790554, baseEnd_2790554] using wordTrace_append hprefix tailTrace_2790554
  have hstable : (prefixWord ++ tailWord_2790554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790554).length < 2 ^ (prefixWord ++ tailWord_2790554).sum := by decide
  have hdescent : baseEnd_2790554 < baseStart_2790554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790556 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_2790556 : Nat := 118140960795 + 2790556 * 2 ^ 59
def prefixEnd_2790556 : Nat := 4983230072969 + 3 ^ 40 * 2790556 * 2
def baseEnd_2790556 : Nat := 955264347525392780344315

theorem tailTrace_2790556 : CollatzResearch.WordTrace tailWord_2790556 prefixEnd_2790556 955264347525392780344315 := by
  unfold tailWord_2790556
  simp only [CollatzResearch.WordTrace]
  refine ⟨50889969439149837933359761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67853292585533117244479681 50889969439149837933359761)
  ·
    refine ⟨38167477079362378450019821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50889969439149837933359761 38167477079362378450019821)
    ·
      refine ⟨14312803904760891918757433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38167477079362378450019821 14312803904760891918757433)
      ·
        refine ⟨10734602928570668939068075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14312803904760891918757433 10734602928570668939068075)
        ·
          refine ⟨16101904392856003408602113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10734602928570668939068075 16101904392856003408602113)
          ·
            refine ⟨12076428294642002556451585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16101904392856003408602113 12076428294642002556451585)
            ·
              refine ⟨9057321220981501917338689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12076428294642002556451585 9057321220981501917338689)
              ·
                refine ⟨6792990915736126438004017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9057321220981501917338689 6792990915736126438004017)
                ·
                  refine ⟨5094743186802094828503013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6792990915736126438004017 5094743186802094828503013)
                  ·
                    refine ⟨955264347525392780344315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5094743186802094828503013 955264347525392780344315)
                    ·
                      rfl

theorem cell22_2790556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_2790556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790556 prefixEnd_2790556 := by exact prefixLift 2790556
  have htrace : WordTrace (prefixWord ++ tailWord_2790556) baseStart_2790556 baseEnd_2790556 := by
    simpa [prefixWord, tailWord_2790556, baseEnd_2790556] using wordTrace_append hprefix tailTrace_2790556
  have hstable : (prefixWord ++ tailWord_2790556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790556).length < 2 ^ (prefixWord ++ tailWord_2790556).sum := by decide
  have hdescent : baseEnd_2790556 < baseStart_2790556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790616 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 7]
def baseStart_2790616 : Nat := 118140960795 + 2790616 * 2 ^ 59
def prefixEnd_2790616 : Nat := 4983230072969 + 3 ^ 40 * 2790616 * 2
def baseEnd_2790616 : Nat := 318428295583857541281377

theorem tailTrace_2790616 : CollatzResearch.WordTrace tailWord_2790616 prefixEnd_2790616 318428295583857541281377 := by
  unfold tailWord_2790616
  simp only [CollatzResearch.WordTrace]
  refine ⟨50891063629041153056951851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67854751505388204075935801 50891063629041153056951851)
  ·
    refine ⟨76336595443561729585427777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50891063629041153056951851 76336595443561729585427777)
    ·
      refine ⟨57252446582671297189070833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76336595443561729585427777 57252446582671297189070833)
      ·
        refine ⟨42939334937003472891803125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57252446582671297189070833 42939334937003472891803125)
        ·
          refine ⟨4025562650344075583606543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42939334937003472891803125 4025562650344075583606543)
          ·
            refine ⟨6038343975516113375409815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025562650344075583606543 6038343975516113375409815)
            ·
              refine ⟨9057515963274170063114723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6038343975516113375409815 9057515963274170063114723)
              ·
                refine ⟨13586273944911255094672085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9057515963274170063114723 13586273944911255094672085)
                ·
                  refine ⟨318428295583857541281377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13586273944911255094672085 318428295583857541281377)
                  ·
                    rfl

theorem cell22_2790616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_2790616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790616 prefixEnd_2790616 := by exact prefixLift 2790616
  have htrace : WordTrace (prefixWord ++ tailWord_2790616) baseStart_2790616 baseEnd_2790616 := by
    simpa [prefixWord, tailWord_2790616, baseEnd_2790616] using wordTrace_append hprefix tailTrace_2790616
  have hstable : (prefixWord ++ tailWord_2790616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790616).length < 2 ^ (prefixWord ++ tailWord_2790616).sum := by decide
  have hdescent : baseEnd_2790616 < baseStart_2790616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790706 : List Nat := [3, 2, 1, 1, 4, 1, 2, 8]
def baseStart_2790706 : Nat := 118140960795 + 2790706 * 2 ^ 59
def prefixEnd_2790706 : Nat := 4983230072969 + 3 ^ 40 * 2790706 * 2
def baseEnd_2790706 : Nat := 106146188398982487677095

theorem tailTrace_2790706 : CollatzResearch.WordTrace tailWord_2790706 prefixEnd_2790706 106146188398982487677095 := by
  unfold tailWord_2790706
  simp only [CollatzResearch.WordTrace]
  refine ⟨25446352456939062871169993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67856939885170834323119981 25446352456939062871169993)
  ·
    refine ⟨19084764342704297153377495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25446352456939062871169993 19084764342704297153377495)
    ·
      refine ⟨28627146514056445730066243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19084764342704297153377495 28627146514056445730066243)
      ·
        refine ⟨42940719771084668595099365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28627146514056445730066243 42940719771084668595099365)
        ·
          refine ⟨8051384957078375361581131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42940719771084668595099365 8051384957078375361581131)
          ·
            refine ⟨12077077435617563042371697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8051384957078375361581131 12077077435617563042371697)
            ·
              refine ⟨9057808076713172281778773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12077077435617563042371697 9057808076713172281778773)
              ·
                refine ⟨106146188398982487677095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9057808076713172281778773 106146188398982487677095)
                ·
                  rfl

theorem cell22_2790706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_2790706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790706 prefixEnd_2790706 := by exact prefixLift 2790706
  have htrace : WordTrace (prefixWord ++ tailWord_2790706) baseStart_2790706 baseEnd_2790706 := by
    simpa [prefixWord, tailWord_2790706, baseEnd_2790706] using wordTrace_append hprefix tailTrace_2790706
  have hstable : (prefixWord ++ tailWord_2790706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790706).length < 2 ^ (prefixWord ++ tailWord_2790706).sum := by decide
  have hdescent : baseEnd_2790706 < baseStart_2790706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790738 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_2790738 : Nat := 118140960795 + 2790738 * 2 ^ 59
def prefixEnd_2790738 : Nat := 4983230072969 + 3 ^ 40 * 2790738 * 2
def baseEnd_2790738 : Nat := 955326649844804972293757

theorem tailTrace_2790738 : CollatzResearch.WordTrace tailWord_2790738 prefixEnd_2790738 955326649844804972293757 := by
  unfold tailWord_2790738
  simp only [CollatzResearch.WordTrace]
  refine ⟨25446644240910080237461217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67857717975760213966563245 25446644240910080237461217)
  ·
    refine ⟨19084983180682560178095913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25446644240910080237461217 19084983180682560178095913)
    ·
      refine ⟨14313737385511920133571935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19084983180682560178095913 14313737385511920133571935)
      ·
        refine ⟨21470606078267880200357903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14313737385511920133571935 21470606078267880200357903)
        ·
          refine ⟨32205909117401820300536855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21470606078267880200357903 32205909117401820300536855)
          ·
            refine ⟨48308863676102730450805283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32205909117401820300536855 48308863676102730450805283)
            ·
              refine ⟨72463295514154095676207925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48308863676102730450805283 72463295514154095676207925)
              ·
                refine ⟨6793433954451946469644493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72463295514154095676207925 6793433954451946469644493)
                ·
                  refine ⟨2547537732919479926116685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6793433954451946469644493 2547537732919479926116685)
                  ·
                    refine ⟨955326649844804972293757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2547537732919479926116685 955326649844804972293757)
                    ·
                      rfl

theorem cell22_2790738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_2790738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790738 prefixEnd_2790738 := by exact prefixLift 2790738
  have htrace : WordTrace (prefixWord ++ tailWord_2790738) baseStart_2790738 baseEnd_2790738 := by
    simpa [prefixWord, tailWord_2790738, baseEnd_2790738] using wordTrace_append hprefix tailTrace_2790738
  have hstable : (prefixWord ++ tailWord_2790738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790738).length < 2 ^ (prefixWord ++ tailWord_2790738).sum := by decide
  have hdescent : baseEnd_2790738 < baseStart_2790738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790813 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 6]
def baseStart_2790813 : Nat := 118140960795 + 2790813 * 2 ^ 59
def prefixEnd_2790813 : Nat := 4983230072969 + 3 ^ 40 * 2790813 * 2
def baseEnd_2790813 : Nat := 318450774625843258889509

theorem tailTrace_2790813 : CollatzResearch.WordTrace tailWord_2790813 prefixEnd_2790813 318450774625843258889509 := by
  unfold tailWord_2790813
  simp only [CollatzResearch.WordTrace]
  refine ⟨101789312438368608758825093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67859541625579072505883395 101789312438368608758825093)
  ·
    refine ⟨19085496082194114142279705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101789312438368608758825093 19085496082194114142279705)
    ·
      refine ⟨14314122061645585606709779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19085496082194114142279705 14314122061645585606709779)
      ·
        refine ⟨21471183092468378410064669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14314122061645585606709779 21471183092468378410064669)
        ·
          refine ⟨8051693659675641903774251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21471183092468378410064669 8051693659675641903774251)
          ·
            refine ⟨12077540489513462855661377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8051693659675641903774251 12077540489513462855661377)
            ·
              refine ⟨9058155367135097141746033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12077540489513462855661377 9058155367135097141746033)
              ·
                refine ⟨6793616525351322856309525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9058155367135097141746033 6793616525351322856309525)
                ·
                  refine ⟨318450774625843258889509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6793616525351322856309525 318450774625843258889509)
                  ·
                    rfl

theorem cell22_2790813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_2790813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790813 prefixEnd_2790813 := by exact prefixLift 2790813
  have htrace : WordTrace (prefixWord ++ tailWord_2790813) baseStart_2790813 baseEnd_2790813 := by
    simpa [prefixWord, tailWord_2790813, baseEnd_2790813] using wordTrace_append hprefix tailTrace_2790813
  have hstable : (prefixWord ++ tailWord_2790813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790813).length < 2 ^ (prefixWord ++ tailWord_2790813).sum := by decide
  have hdescent : baseEnd_2790813 < baseStart_2790813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790815 : List Nat := [1, 1, 2, 5, 1, 3, 2, 2, 1, 4]
def baseStart_2790815 : Nat := 118140960795 + 2790815 * 2 ^ 59
def prefixEnd_2790815 : Nat := 4983230072969 + 3 ^ 40 * 2790815 * 2
def baseEnd_2790815 : Nat := 955353008518402438118521

theorem tailTrace_2790815 : CollatzResearch.WordTrace tailWord_2790815 prefixEnd_2790815 955353008518402438118521 := by
  unfold tailWord_2790815
  simp only [CollatzResearch.WordTrace]
  refine ⟨101789385384361363100397899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67859590256240908733598599 101789385384361363100397899)
  ·
    refine ⟨152684078076542044650596849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101789385384361363100397899 152684078076542044650596849)
    ·
      refine ⟨114513058557406533487947637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152684078076542044650596849 114513058557406533487947637)
      ·
        refine ⟨10735599239756862514495091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114513058557406533487947637 10735599239756862514495091)
        ·
          refine ⟨16103398859635293771742637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10735599239756862514495091 16103398859635293771742637)
          ·
            refine ⟨6038774572363235164403489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16103398859635293771742637 6038774572363235164403489)
            ·
              refine ⟨4529080929272426373302617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6038774572363235164403489 4529080929272426373302617)
              ·
                refine ⟨3396810696954319779976963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4529080929272426373302617 3396810696954319779976963)
                ·
                  refine ⟨5095216045431479669965445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396810696954319779976963 5095216045431479669965445)
                  ·
                    refine ⟨955353008518402438118521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5095216045431479669965445 955353008518402438118521)
                    ·
                      rfl

theorem cell22_2790815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_2790815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790815 prefixEnd_2790815 := by exact prefixLift 2790815
  have htrace : WordTrace (prefixWord ++ tailWord_2790815) baseStart_2790815 baseEnd_2790815 := by
    simpa [prefixWord, tailWord_2790815, baseEnd_2790815] using wordTrace_append hprefix tailTrace_2790815
  have hstable : (prefixWord ++ tailWord_2790815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790815).length < 2 ^ (prefixWord ++ tailWord_2790815).sum := by decide
  have hdescent : baseEnd_2790815 < baseStart_2790815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790828 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 4, 3]
def baseStart_2790828 : Nat := 118140960795 + 2790828 * 2 ^ 59
def prefixEnd_2790828 : Nat := 4983230072969 + 3 ^ 40 * 2790828 * 2
def baseEnd_2790828 : Nat := 955357458684074737543481

theorem tailTrace_2790828 : CollatzResearch.WordTrace tailWord_2790828 prefixEnd_2790828 955357458684074737543481 := by
  unfold tailWord_2790828
  simp only [CollatzResearch.WordTrace]
  refine ⟨50894929766657133160310569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67859906355542844213747425 50894929766657133160310569)
  ·
    refine ⟨38171197324992849870232927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50894929766657133160310569 38171197324992849870232927)
    ·
      refine ⟨57256795987489274805349391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38171197324992849870232927 57256795987489274805349391)
      ·
        refine ⟨85885193981233912208024087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57256795987489274805349391 85885193981233912208024087)
        ·
          refine ⟨128827790971850868312036131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85885193981233912208024087 128827790971850868312036131)
          ·
            refine ⟨193241686457776302468054197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128827790971850868312036131 193241686457776302468054197)
            ·
              refine ⟨18116408105416528356380081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193241686457776302468054197 18116408105416528356380081)
              ·
                refine ⟨13587306079062396267285061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18116408105416528356380081 13587306079062396267285061)
                ·
                  refine ⟨2547619889824199300115949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13587306079062396267285061 2547619889824199300115949)
                  ·
                    refine ⟨955357458684074737543481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2547619889824199300115949 955357458684074737543481)
                    ·
                      rfl

theorem cell22_2790828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_2790828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790828 prefixEnd_2790828 := by exact prefixLift 2790828
  have htrace : WordTrace (prefixWord ++ tailWord_2790828) baseStart_2790828 baseEnd_2790828 := by
    simpa [prefixWord, tailWord_2790828, baseEnd_2790828] using wordTrace_append hprefix tailTrace_2790828
  have hstable : (prefixWord ++ tailWord_2790828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790828).length < 2 ^ (prefixWord ++ tailWord_2790828).sum := by decide
  have hdescent : baseEnd_2790828 < baseStart_2790828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790845 : List Nat := [1, 4, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_2790845 : Nat := 118140960795 + 2790845 * 2 ^ 59
def prefixEnd_2790845 : Nat := 4983230072969 + 3 ^ 40 * 2790845 * 2
def baseEnd_2790845 : Nat := 955363278131492359868429

theorem tailTrace_2790845 : CollatzResearch.WordTrace tailWord_2790845 prefixEnd_2790845 955363278131492359868429 := by
  unfold tailWord_2790845
  simp only [CollatzResearch.WordTrace]
  refine ⟨101790479574252678223989989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67860319716168452149326659 101790479574252678223989989)
  ·
    refine ⟨19085714920172377166998123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101790479574252678223989989 19085714920172377166998123)
    ·
      refine ⟨28628572380258565750497185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19085714920172377166998123 28628572380258565750497185)
      ·
        refine ⟨21471429285193924312872889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28628572380258565750497185 21471429285193924312872889)
        ·
          refine ⟨16103571963895443234654667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21471429285193924312872889 16103571963895443234654667)
          ·
            refine ⟨24155357945843164851982001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16103571963895443234654667 24155357945843164851982001)
            ·
              refine ⟨18116518459382373638986501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24155357945843164851982001 18116518459382373638986501)
              ·
                refine ⟨3396847211134195057309969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18116518459382373638986501 3396847211134195057309969)
                ·
                  refine ⟨2547635408350646292982477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3396847211134195057309969 2547635408350646292982477)
                  ·
                    refine ⟨955363278131492359868429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2547635408350646292982477 955363278131492359868429)
                    ·
                      rfl

theorem cell22_2790845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_2790845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790845 prefixEnd_2790845 := by exact prefixLift 2790845
  have htrace : WordTrace (prefixWord ++ tailWord_2790845) baseStart_2790845 baseEnd_2790845 := by
    simpa [prefixWord, tailWord_2790845, baseEnd_2790845] using wordTrace_append hprefix tailTrace_2790845
  have hstable : (prefixWord ++ tailWord_2790845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790845).length < 2 ^ (prefixWord ++ tailWord_2790845).sum := by decide
  have hdescent : baseEnd_2790845 < baseStart_2790845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790858 : List Nat := [3, 1, 2, 1, 2, 4, 2, 7]
def baseStart_2790858 : Nat := 118140960795 + 2790858 * 2 ^ 59
def prefixEnd_2790858 : Nat := 4983230072969 + 3 ^ 40 * 2790858 * 2
def baseEnd_2790858 : Nat := 106151969810796073254821

theorem tailTrace_2790858 : CollatzResearch.WordTrace tailWord_2790858 prefixEnd_2790858 106151969810796073254821 := by
  unfold tailWord_2790858
  simp only [CollatzResearch.WordTrace]
  refine ⟨25447738430801395361053307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67860635815470387629475485 25447738430801395361053307)
  ·
    refine ⟨38171607646202093041579961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25447738430801395361053307 38171607646202093041579961)
    ·
      refine ⟨28628705734651569781184971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38171607646202093041579961 28628705734651569781184971)
      ·
        refine ⟨42943058601977354671777457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28628705734651569781184971 42943058601977354671777457)
        ·
          refine ⟨32207293951483016003833093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42943058601977354671777457 32207293951483016003833093)
          ·
            refine ⟨6038867615903065500718705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32207293951483016003833093 6038867615903065500718705)
            ·
              refine ⟨4529150711927299125539029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6038867615903065500718705 4529150711927299125539029)
              ·
                refine ⟨106151969810796073254821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4529150711927299125539029 106151969810796073254821)
                ·
                  rfl

theorem cell22_2790858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_2790858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790858 prefixEnd_2790858 := by exact prefixLift 2790858
  have htrace : WordTrace (prefixWord ++ tailWord_2790858) baseStart_2790858 baseEnd_2790858 := by
    simpa [prefixWord, tailWord_2790858, baseEnd_2790858] using wordTrace_append hprefix tailTrace_2790858
  have hstable : (prefixWord ++ tailWord_2790858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790858).length < 2 ^ (prefixWord ++ tailWord_2790858).sum := by decide
  have hdescent : baseEnd_2790858 < baseStart_2790858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790862 : List Nat := [4, 1, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_2790862 : Nat := 118140960795 + 2790862 * 2 ^ 59
def prefixEnd_2790862 : Nat := 4983230072969 + 3 ^ 40 * 2790862 * 2
def baseEnd_2790862 : Nat := 955369097578909982193377

theorem tailTrace_2790862 : CollatzResearch.WordTrace tailWord_2790862 prefixEnd_2790862 955369097578909982193377 := by
  unfold tailWord_2790862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12723887451898886265919855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67860733076794060084905893 12723887451898886265919855)
  ·
    refine ⟨19085831177848329398879783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12723887451898886265919855 19085831177848329398879783)
    ·
      refine ⟨28628746766772494098319675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19085831177848329398879783 28628746766772494098319675)
      ·
        refine ⟨42943120150158741147479513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28628746766772494098319675 42943120150158741147479513)
        ·
          refine ⟨32207340112619055860609635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42943120150158741147479513 32207340112619055860609635)
          ·
            refine ⟨48311010168928583790914453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32207340112619055860609635 48311010168928583790914453)
            ·
              refine ⟨2264578601668527365199115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48311010168928583790914453 2264578601668527365199115)
              ·
                refine ⟨3396867902502791047798673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2264578601668527365199115 3396867902502791047798673)
                ·
                  refine ⟨2547650926877093285849005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3396867902502791047798673 2547650926877093285849005)
                  ·
                    refine ⟨955369097578909982193377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2547650926877093285849005 955369097578909982193377)
                    ·
                      rfl

theorem cell22_2790862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_2790862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790862 prefixEnd_2790862 := by exact prefixLift 2790862
  have htrace : WordTrace (prefixWord ++ tailWord_2790862) baseStart_2790862 baseEnd_2790862 := by
    simpa [prefixWord, tailWord_2790862, baseEnd_2790862] using wordTrace_append hprefix tailTrace_2790862
  have hstable : (prefixWord ++ tailWord_2790862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790862).length < 2 ^ (prefixWord ++ tailWord_2790862).sum := by decide
  have hdescent : baseEnd_2790862 < baseStart_2790862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790965 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 6]
def baseStart_2790965 : Nat := 118140960795 + 2790965 * 2 ^ 59
def prefixEnd_2790965 : Nat := 4983230072969 + 3 ^ 40 * 2790965 * 2
def baseEnd_2790965 : Nat := 318468118861284015622687

theorem tailTrace_2790965 : CollatzResearch.WordTrace tailWord_2790965 prefixEnd_2790965 318468118861284015622687 := by
  unfold tailWord_2790965
  simp only [CollatzResearch.WordTrace]
  refine ⟨101794856333817938718358349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67863237555878625812238899 101794856333817938718358349)
  ·
    refine ⟨38173071125181727019384381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101794856333817938718358349 38173071125181727019384381)
    ·
      refine ⟨14314901671943147632269143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38173071125181727019384381 14314901671943147632269143)
      ·
        refine ⟨21472352507914721448403715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14314901671943147632269143 21472352507914721448403715)
        ·
          refine ⟨32208528761872082172605573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21472352507914721448403715 32208528761872082172605573)
          ·
            refine ⟨6039099142851015407363545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32208528761872082172605573 6039099142851015407363545)
            ·
              refine ⟨4529324357138261555522659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6039099142851015407363545 4529324357138261555522659)
              ·
                refine ⟨6793986535707392333283989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4529324357138261555522659 6793986535707392333283989)
                ·
                  refine ⟨318468118861284015622687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6793986535707392333283989 318468118861284015622687)
                  ·
                    rfl

theorem cell22_2790965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_2790965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790965 prefixEnd_2790965 := by exact prefixLift 2790965
  have htrace : WordTrace (prefixWord ++ tailWord_2790965) baseStart_2790965 baseEnd_2790965 := by
    simpa [prefixWord, tailWord_2790965, baseEnd_2790965] using wordTrace_append hprefix tailTrace_2790965
  have hstable : (prefixWord ++ tailWord_2790965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790965).length < 2 ^ (prefixWord ++ tailWord_2790965).sum := by decide
  have hdescent : baseEnd_2790965 < baseStart_2790965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790993 : List Nat := [1, 2, 2, 1, 3, 2, 3, 8]
def baseStart_2790993 : Nat := 118140960795 + 2790993 * 2 ^ 59
def prefixEnd_2790993 : Nat := 4983230072969 + 3 ^ 40 * 2790993 * 2
def baseEnd_2790993 : Nat := 106157104617341034129775

theorem tailTrace_2790993 : CollatzResearch.WordTrace tailWord_2790993 prefixEnd_2790993 106157104617341034129775 := by
  unfold tailWord_2790993
  simp only [CollatzResearch.WordTrace]
  refine ⟨101795877577716499500377633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67863918385144333000251755 101795877577716499500377633)
  ·
    refine ⟨76346908183287374625283225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101795877577716499500377633 76346908183287374625283225)
    ·
      refine ⟨57260181137465530968962419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76346908183287374625283225 57260181137465530968962419)
      ·
        refine ⟨85890271706198296453443629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57260181137465530968962419 85890271706198296453443629)
        ·
          refine ⟨32208851889824361170041361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85890271706198296453443629 32208851889824361170041361)
          ·
            refine ⟨24156638917368270877531021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32208851889824361170041361 24156638917368270877531021)
            ·
              refine ⟨9058739594013101579074133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24156638917368270877531021 9058739594013101579074133)
              ·
                refine ⟨106157104617341034129775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9058739594013101579074133 106157104617341034129775)
                ·
                  rfl

theorem cell22_2790993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 8].length) (baseStart_2790993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2790993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2790993 prefixEnd_2790993 := by exact prefixLift 2790993
  have htrace : WordTrace (prefixWord ++ tailWord_2790993) baseStart_2790993 baseEnd_2790993 := by
    simpa [prefixWord, tailWord_2790993, baseEnd_2790993] using wordTrace_append hprefix tailTrace_2790993
  have hstable : (prefixWord ++ tailWord_2790993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790993).length < 2 ^ (prefixWord ++ tailWord_2790993).sum := by decide
  have hdescent : baseEnd_2790993 < baseStart_2790993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791023 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 2, 6]
def baseStart_2791023 : Nat := 118140960795 + 2791023 * 2 ^ 59
def prefixEnd_2791023 : Nat := 4983230072969 + 3 ^ 40 * 2791023 * 2
def baseEnd_2791023 : Nat := 955424211169159228917883

theorem tailTrace_2791023 : CollatzResearch.WordTrace tailWord_2791023 prefixEnd_2791023 955424211169159228917883 := by
  unfold tailWord_2791023
  simp only [CollatzResearch.WordTrace]
  refine ⟨101796971767607814623969723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67864647845071876415979815 101796971767607814623969723)
  ·
    refine ⟨152695457651411721935954585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101796971767607814623969723 152695457651411721935954585)
    ·
      refine ⟨114521593238558791451965939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152695457651411721935954585 114521593238558791451965939)
      ·
        refine ⟨171782389857838187177948909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114521593238558791451965939 171782389857838187177948909)
        ·
          refine ⟨64418396196689320191730841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171782389857838187177948909 64418396196689320191730841)
          ·
            refine ⟨48313797147516990143798131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64418396196689320191730841 48313797147516990143798131)
            ·
              refine ⟨72470695721275485215697197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48313797147516990143798131 72470695721275485215697197)
              ·
                refine ⟨27176510895478306955886449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72470695721275485215697197 27176510895478306955886449)
                ·
                  refine ⟨20382383171608730216914837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27176510895478306955886449 20382383171608730216914837)
                  ·
                    refine ⟨955424211169159228917883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20382383171608730216914837 955424211169159228917883)
                    ·
                      rfl

theorem cell22_2791023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_2791023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791023 prefixEnd_2791023 := by exact prefixLift 2791023
  have htrace : WordTrace (prefixWord ++ tailWord_2791023) baseStart_2791023 baseEnd_2791023 := by
    simpa [prefixWord, tailWord_2791023, baseEnd_2791023] using wordTrace_append hprefix tailTrace_2791023
  have hstable : (prefixWord ++ tailWord_2791023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791023).length < 2 ^ (prefixWord ++ tailWord_2791023).sum := by decide
  have hdescent : baseEnd_2791023 < baseStart_2791023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791072 : List Nat := [2, 1, 1, 4, 3, 2, 2, 2, 5]
def baseStart_2791072 : Nat := 118140960795 + 2791072 * 2 ^ 59
def prefixEnd_2791072 : Nat := 4983230072969 + 3 ^ 40 * 2791072 * 2
def baseEnd_2791072 : Nat := 318480328290179811480911

theorem tailTrace_2791072 : CollatzResearch.WordTrace tailWord_2791072 prefixEnd_2791072 318480328290179811480911 := by
  unfold tailWord_2791072
  simp only [CollatzResearch.WordTrace]
  refine ⟨50899379472215147996251735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67865839296286863995002313 50899379472215147996251735)
  ·
    refine ⟨76349069208322721994377603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50899379472215147996251735 76349069208322721994377603)
    ·
      refine ⟨114523603812484082991566405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76349069208322721994377603 114523603812484082991566405)
      ·
        refine ⟨21473175714840765560918701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114523603812484082991566405 21473175714840765560918701)
        ·
          refine ⟨8052440893065287085344513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21473175714840765560918701 8052440893065287085344513)
          ·
            refine ⟨6039330669798965314008385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8052440893065287085344513 6039330669798965314008385)
            ·
              refine ⟨4529498002349223985506289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6039330669798965314008385 4529498002349223985506289)
              ·
                refine ⟨3397123501761917989129717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4529498002349223985506289 3397123501761917989129717)
                ·
                  refine ⟨318480328290179811480911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3397123501761917989129717 318480328290179811480911)
                  ·
                    rfl

theorem cell22_2791072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_2791072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791072 prefixEnd_2791072 := by exact prefixLift 2791072
  have htrace : WordTrace (prefixWord ++ tailWord_2791072) baseStart_2791072 baseEnd_2791072 := by
    simpa [prefixWord, tailWord_2791072, baseEnd_2791072] using wordTrace_append hprefix tailTrace_2791072
  have hstable : (prefixWord ++ tailWord_2791072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791072).length < 2 ^ (prefixWord ++ tailWord_2791072).sum := by decide
  have hdescent : baseEnd_2791072 < baseStart_2791072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791076 : List Nat := [2, 3, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_2791076 : Nat := 118140960795 + 2791076 * 2 ^ 59
def prefixEnd_2791076 : Nat := 4983230072969 + 3 ^ 40 * 2791076 * 2
def baseEnd_2791076 : Nat := 955442354152284757342721

theorem tailTrace_2791076 : CollatzResearch.WordTrace tailWord_2791076 prefixEnd_2791076 955442354152284757342721 := by
  unfold tailWord_2791076
  simp only [CollatzResearch.WordTrace]
  refine ⟨50899452418207902337824541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67865936557610536450432721 50899452418207902337824541)
  ·
    refine ⟨19087294656827963376684203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50899452418207902337824541 19087294656827963376684203)
    ·
      refine ⟨28630941985241945065026305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19087294656827963376684203 28630941985241945065026305)
      ·
        refine ⟨21473206488931458798769729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28630941985241945065026305 21473206488931458798769729)
        ·
          refine ⟨16104904866698594099077297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21473206488931458798769729 16104904866698594099077297)
          ·
            refine ⟨12078678650023945574307973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16104904866698594099077297 12078678650023945574307973)
            ·
              refine ⟨2264752246879489795182745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12078678650023945574307973 2264752246879489795182745)
              ·
                refine ⟨1698564185159617346387059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2264752246879489795182745 1698564185159617346387059)
                ·
                  refine ⟨2547846277739426019580589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698564185159617346387059 2547846277739426019580589)
                  ·
                    refine ⟨955442354152284757342721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2547846277739426019580589 955442354152284757342721)
                    ·
                      rfl

theorem cell22_2791076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_2791076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791076 prefixEnd_2791076 := by exact prefixLift 2791076
  have htrace : WordTrace (prefixWord ++ tailWord_2791076) baseStart_2791076 baseEnd_2791076 := by
    simpa [prefixWord, tailWord_2791076, baseEnd_2791076] using wordTrace_append hprefix tailTrace_2791076
  have hstable : (prefixWord ++ tailWord_2791076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791076).length < 2 ^ (prefixWord ++ tailWord_2791076).sum := by decide
  have hdescent : baseEnd_2791076 < baseStart_2791076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791100 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 8]
def baseStart_2791100 : Nat := 118140960795 + 2791100 * 2 ^ 59
def prefixEnd_2791100 : Nat := 4983230072969 + 3 ^ 40 * 2791100 * 2
def baseEnd_2791100 : Nat := 318483523280918898247549

theorem tailTrace_2791100 : CollatzResearch.WordTrace tailWord_2791100 prefixEnd_2791100 318483523280918898247549 := by
  unfold tailWord_2791100
  simp only [CollatzResearch.WordTrace]
  refine ⟨50899890094164428387261377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67866520125552571183015169 50899890094164428387261377)
  ·
    refine ⟨38174917570623321290446033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50899890094164428387261377 38174917570623321290446033)
    ·
      refine ⟨28631188177967490967834525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38174917570623321290446033 28631188177967490967834525)
      ·
        refine ⟨10736695566737809112937947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28631188177967490967834525 10736695566737809112937947)
        ·
          refine ⟨16105043350106713669406921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10736695566737809112937947 16105043350106713669406921)
          ·
            refine ⟨12078782512580035252055191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16105043350106713669406921 12078782512580035252055191)
            ·
              refine ⟨18118173768870052878082787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12078782512580035252055191 18118173768870052878082787)
              ·
                refine ⟨27177260653305079317124181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18118173768870052878082787 27177260653305079317124181)
                ·
                  refine ⟨318483523280918898247549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27177260653305079317124181 318483523280918898247549)
                  ·
                    rfl

theorem cell22_2791100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_2791100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791100 prefixEnd_2791100 := by exact prefixLift 2791100
  have htrace : WordTrace (prefixWord ++ tailWord_2791100) baseStart_2791100 baseEnd_2791100 := by
    simpa [prefixWord, tailWord_2791100, baseEnd_2791100] using wordTrace_append hprefix tailTrace_2791100
  have hstable : (prefixWord ++ tailWord_2791100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791100).length < 2 ^ (prefixWord ++ tailWord_2791100).sum := by decide
  have hdescent : baseEnd_2791100 < baseStart_2791100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791102 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_2791102 : Nat := 118140960795 + 2791102 * 2 ^ 59
def prefixEnd_2791102 : Nat := 4983230072969 + 3 ^ 40 * 2791102 * 2
def baseEnd_2791102 : Nat := 955451254483629356192641

theorem tailTrace_2791102 : CollatzResearch.WordTrace tailWord_2791102 prefixEnd_2791102 955451254483629356192641 := by
  unfold tailWord_2791102
  simp only [CollatzResearch.WordTrace]
  refine ⟨12724981641790201389511945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67866568756214407410730373 12724981641790201389511945)
  ·
    refine ⟨9543736231342651042133959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12724981641790201389511945 9543736231342651042133959)
    ·
      refine ⟨14315604347013976563200939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9543736231342651042133959 14315604347013976563200939)
      ·
        refine ⟨21473406520520964844801409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14315604347013976563200939 21473406520520964844801409)
        ·
          refine ⟨16105054890390723633601057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21473406520520964844801409 16105054890390723633601057)
          ·
            refine ⟨12078791167793042725200793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16105054890390723633601057 12078791167793042725200793)
            ·
              refine ⟨9059093375844782043900595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12078791167793042725200793 9059093375844782043900595)
              ·
                refine ⟨13588640063767173065850893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9059093375844782043900595 13588640063767173065850893)
                ·
                  refine ⟨5095740023912689899694085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13588640063767173065850893 5095740023912689899694085)
                  ·
                    refine ⟨955451254483629356192641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5095740023912689899694085 955451254483629356192641)
                    ·
                      rfl

theorem cell22_2791102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_2791102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791102 prefixEnd_2791102 := by exact prefixLift 2791102
  have htrace : WordTrace (prefixWord ++ tailWord_2791102) baseStart_2791102 baseEnd_2791102 := by
    simpa [prefixWord, tailWord_2791102, baseEnd_2791102] using wordTrace_append hprefix tailTrace_2791102
  have hstable : (prefixWord ++ tailWord_2791102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791102).length < 2 ^ (prefixWord ++ tailWord_2791102).sum := by decide
  have hdescent : baseEnd_2791102 < baseStart_2791102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791110 : List Nat := [6, 1, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2791110 : Nat := 118140960795 + 2791110 * 2 ^ 59
def prefixEnd_2791110 : Nat := 4983230072969 + 3 ^ 40 * 2791110 * 2
def baseEnd_2791110 : Nat := 955453993047120001992617

theorem tailTrace_2791110 : CollatzResearch.WordTrace tailWord_2791110 prefixEnd_2791110 955453993047120001992617 := by
  unfold tailWord_2791110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3181254528696644640074587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67866763278861752321591189 3181254528696644640074587)
  ·
    refine ⟨4771881793044966960111881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3181254528696644640074587 4771881793044966960111881)
    ·
      refine ⟨3578911344783725220083911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4771881793044966960111881 3578911344783725220083911)
      ·
        refine ⟨5368367017175587830125867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3578911344783725220083911 5368367017175587830125867)
        ·
          refine ⟨8052550525763381745188801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5368367017175587830125867 8052550525763381745188801)
          ·
            refine ⟨6039412894322536308891601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8052550525763381745188801 6039412894322536308891601)
            ·
              refine ⟨4529559670741902231668701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6039412894322536308891601 4529559670741902231668701)
              ·
                refine ⟨1698584876528213336875763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4529559670741902231668701 1698584876528213336875763)
                ·
                  refine ⟨2547877314792320005313645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698584876528213336875763 2547877314792320005313645)
                  ·
                    refine ⟨955453993047120001992617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2547877314792320005313645 955453993047120001992617)
                    ·
                      rfl

theorem cell22_2791110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2791110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791110 prefixEnd_2791110 := by exact prefixLift 2791110
  have htrace : WordTrace (prefixWord ++ tailWord_2791110) baseStart_2791110 baseEnd_2791110 := by
    simpa [prefixWord, tailWord_2791110, baseEnd_2791110] using wordTrace_append hprefix tailTrace_2791110
  have hstable : (prefixWord ++ tailWord_2791110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791110).length < 2 ^ (prefixWord ++ tailWord_2791110).sum := by decide
  have hdescent : baseEnd_2791110 < baseStart_2791110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791149 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_2791149 : Nat := 118140960795 + 2791149 * 2 ^ 59
def prefixEnd_2791149 : Nat := 4983230072969 + 3 ^ 40 * 2791149 * 2
def baseEnd_2791149 : Nat := 955467343544136900267497

theorem tailTrace_2791149 : CollatzResearch.WordTrace tailWord_2791149 prefixEnd_2791149 955467343544136900267497 := by
  unfold tailWord_2791149
  simp only [CollatzResearch.WordTrace]
  refine ⟨101801567365151338143056501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67867711576767558762037667 101801567365151338143056501)
  ·
    refine ⟨9543896940482937950911547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101801567365151338143056501 9543896940482937950911547)
    ·
      refine ⟨14315845410724406926367321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9543896940482937950911547 14315845410724406926367321)
      ·
        refine ⟨10736884058043305194775491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14315845410724406926367321 10736884058043305194775491)
        ·
          refine ⟨16105326087064957792163237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10736884058043305194775491 16105326087064957792163237)
          ·
            refine ⟨3019748641324679586030607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16105326087064957792163237 3019748641324679586030607)
            ·
              refine ⟨4529622961987019379045911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3019748641324679586030607 4529622961987019379045911)
              ·
                refine ⟨6794434442980529068568867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4529622961987019379045911 6794434442980529068568867)
                ·
                  refine ⟨10191651664470793602853301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6794434442980529068568867 10191651664470793602853301)
                  ·
                    refine ⟨955467343544136900267497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10191651664470793602853301 955467343544136900267497)
                    ·
                      rfl

theorem cell22_2791149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_2791149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791149 prefixEnd_2791149 := by exact prefixLift 2791149
  have htrace : WordTrace (prefixWord ++ tailWord_2791149) baseStart_2791149 baseEnd_2791149 := by
    simpa [prefixWord, tailWord_2791149, baseEnd_2791149] using wordTrace_append hprefix tailTrace_2791149
  have hstable : (prefixWord ++ tailWord_2791149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791149).length < 2 ^ (prefixWord ++ tailWord_2791149).sum := by decide
  have hdescent : baseEnd_2791149 < baseStart_2791149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791194 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 3, 3]
def baseStart_2791194 : Nat := 118140960795 + 2791194 * 2 ^ 59
def prefixEnd_2791194 : Nat := 4983230072969 + 3 ^ 40 * 2791194 * 2
def baseEnd_2791194 : Nat := 955482747963771782892359

theorem tailTrace_2791194 : CollatzResearch.WordTrace tailWord_2791194 prefixEnd_2791194 955482747963771782892359 := by
  unfold tailWord_2791194
  simp only [CollatzResearch.WordTrace]
  refine ⟨25450802162497077707111159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67868805766658873885629757 25450802162497077707111159)
  ·
    refine ⟨38176203243745616560666739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25450802162497077707111159 38176203243745616560666739)
    ·
      refine ⟨57264304865618424841000109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38176203243745616560666739 57264304865618424841000109)
      ·
        refine ⟨21474114324606909315375041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57264304865618424841000109 21474114324606909315375041)
        ·
          refine ⟨16105585743455181986531281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21474114324606909315375041 16105585743455181986531281)
          ·
            refine ⟨12079189307591386489898461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16105585743455181986531281 12079189307591386489898461)
            ·
              refine ⟨4529695990346769933711923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12079189307591386489898461 4529695990346769933711923)
              ·
                refine ⟨6794543985520154900567885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4529695990346769933711923 6794543985520154900567885)
                ·
                  refine ⟨2547953994570058087712957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6794543985520154900567885 2547953994570058087712957)
                  ·
                    refine ⟨955482747963771782892359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2547953994570058087712957 955482747963771782892359)
                    ·
                      rfl

theorem cell22_2791194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_2791194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791194 prefixEnd_2791194 := by exact prefixLift 2791194
  have htrace : WordTrace (prefixWord ++ tailWord_2791194) baseStart_2791194 baseEnd_2791194 := by
    simpa [prefixWord, tailWord_2791194, baseEnd_2791194] using wordTrace_append hprefix tailTrace_2791194
  have hstable : (prefixWord ++ tailWord_2791194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791194).length < 2 ^ (prefixWord ++ tailWord_2791194).sum := by decide
  have hdescent : baseEnd_2791194 < baseStart_2791194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791245 : List Nat := [1, 6, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_2791245 : Nat := 118140960795 + 2791245 * 2 ^ 59
def prefixEnd_2791245 : Nat := 4983230072969 + 3 ^ 40 * 2791245 * 2
def baseEnd_2791245 : Nat := 955500206306024649867203

theorem tailTrace_2791245 : CollatzResearch.WordTrace tailWord_2791245 prefixEnd_2791245 955500206306024649867203 := by
  unfold tailWord_2791245
  simp only [CollatzResearch.WordTrace]
  refine ⟨101805068772803546538551189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67870045848535697692367459 101805068772803546538551189)
  ·
    refine ⟨4772112598725166243994587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101805068772803546538551189 4772112598725166243994587)
    ·
      refine ⟨7158168898087749365991881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4772112598725166243994587 7158168898087749365991881)
      ·
        refine ⟨5368626673565812024493911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7158168898087749365991881 5368626673565812024493911)
        ·
          refine ⟨8052940010348718036740867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5368626673565812024493911 8052940010348718036740867)
          ·
            refine ⟨12079410015523077055111301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8052940010348718036740867 12079410015523077055111301)
            ·
              refine ⟨2264889377910576947833369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12079410015523077055111301 2264889377910576947833369)
              ·
                refine ⟨1698667033432932710875027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2264889377910576947833369 1698667033432932710875027)
                ·
                  refine ⟨2548000550149399066312541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698667033432932710875027 2548000550149399066312541)
                  ·
                    refine ⟨955500206306024649867203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2548000550149399066312541 955500206306024649867203)
                    ·
                      rfl

theorem cell22_2791245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_2791245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791245 prefixEnd_2791245 := by exact prefixLift 2791245
  have htrace : WordTrace (prefixWord ++ tailWord_2791245) baseStart_2791245 baseEnd_2791245 := by
    simpa [prefixWord, tailWord_2791245, baseEnd_2791245] using wordTrace_append hprefix tailTrace_2791245
  have hstable : (prefixWord ++ tailWord_2791245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791245).length < 2 ^ (prefixWord ++ tailWord_2791245).sum := by decide
  have hdescent : baseEnd_2791245 < baseStart_2791245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791348 : List Nat := [2, 5, 2, 1, 3, 1, 8]
def baseStart_2791348 : Nat := 118140960795 + 2791348 * 2 ^ 59
def prefixEnd_2791348 : Nat := 4983230072969 + 3 ^ 40 * 2791348 * 2
def baseEnd_2791348 : Nat := 35390202418924693131181

theorem tailTrace_2791348 : CollatzResearch.WordTrace tailWord_2791348 prefixEnd_2791348 35390202418924693131181 := by
  unfold tailWord_2791348
  simp only [CollatzResearch.WordTrace]
  refine ⟨50904412745715197564775349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67872550327620263419700465 50904412745715197564775349)
  ·
    refine ⟨4772288694910799771697689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50904412745715197564775349 4772288694910799771697689)
    ·
      refine ⟨3579216521183099828773267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4772288694910799771697689 3579216521183099828773267)
      ·
        refine ⟨5368824781774649743159901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3579216521183099828773267 5368824781774649743159901)
        ·
          refine ⟨2013309293165493653684963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5368824781774649743159901 2013309293165493653684963)
          ·
            refine ⟨3019963939748240480527445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013309293165493653684963 3019963939748240480527445)
            ·
              refine ⟨35390202418924693131181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3019963939748240480527445 35390202418924693131181)
              ·
                rfl

theorem cell22_2791348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 8].length) (baseStart_2791348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791348 prefixEnd_2791348 := by exact prefixLift 2791348
  have htrace : WordTrace (prefixWord ++ tailWord_2791348) baseStart_2791348 baseEnd_2791348 := by
    simpa [prefixWord, tailWord_2791348, baseEnd_2791348] using wordTrace_append hprefix tailTrace_2791348
  have hstable : (prefixWord ++ tailWord_2791348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791348).length < 2 ^ (prefixWord ++ tailWord_2791348).sum := by decide
  have hdescent : baseEnd_2791348 < baseStart_2791348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791414 : List Nat := [5, 1, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_2791414 : Nat := 118140960795 + 2791414 * 2 ^ 59
def prefixEnd_2791414 : Nat := 4983230072969 + 3 ^ 40 * 2791414 * 2
def baseEnd_2791414 : Nat := 955558058459764542391685

theorem tailTrace_2791414 : CollatzResearch.WordTrace tailWord_2791414 prefixEnd_2791414 955558058459764542391685 := by
  unfold tailWord_2791414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6363202044324455525090831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67874155139460858934302197 6363202044324455525090831)
  ·
    refine ⟨9544803066486683287636247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6363202044324455525090831 9544803066486683287636247)
    ·
      refine ⟨14317204599730024931454371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9544803066486683287636247 14317204599730024931454371)
      ·
        refine ⟨21475806899595037397181557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14317204599730024931454371 21475806899595037397181557)
        ·
          refine ⟨2013356896837034755985771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21475806899595037397181557 2013356896837034755985771)
          ·
            refine ⟨3020035345255552133978657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013356896837034755985771 3020035345255552133978657)
            ·
              refine ⟨2265026508941664100483993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3020035345255552133978657 2265026508941664100483993)
              ·
                refine ⟨1698769881706248075362995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2265026508941664100483993 1698769881706248075362995)
                ·
                  refine ⟨2548154822559372113044493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698769881706248075362995 2548154822559372113044493)
                  ·
                    refine ⟨955558058459764542391685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2548154822559372113044493 955558058459764542391685)
                    ·
                      rfl

theorem cell22_2791414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_2791414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791414 prefixEnd_2791414 := by exact prefixLift 2791414
  have htrace : WordTrace (prefixWord ++ tailWord_2791414) baseStart_2791414 baseEnd_2791414 := by
    simpa [prefixWord, tailWord_2791414, baseEnd_2791414] using wordTrace_append hprefix tailTrace_2791414
  have hstable : (prefixWord ++ tailWord_2791414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791414).length < 2 ^ (prefixWord ++ tailWord_2791414).sum := by decide
  have hdescent : baseEnd_2791414 < baseStart_2791414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791419 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 4, 3]
def baseStart_2791419 : Nat := 118140960795 + 2791419 * 2 ^ 59
def prefixEnd_2791419 : Nat := 4983230072969 + 3 ^ 40 * 2791419 * 2
def baseEnd_2791419 : Nat := 955559770061946196016669

theorem tailTrace_2791419 : CollatzResearch.WordTrace tailWord_2791419 prefixEnd_2791419 955559770061946196016669 := by
  unfold tailWord_2791419
  simp only [CollatzResearch.WordTrace]
  refine ⟨101811415074173174255385311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67874276716115449503590207 101811415074173174255385311)
  ·
    refine ⟨152717122611259761383077967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101811415074173174255385311 152717122611259761383077967)
    ·
      refine ⟨229075683916889642074616951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152717122611259761383077967 229075683916889642074616951)
      ·
        refine ⟨343613525875334463111925427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229075683916889642074616951 343613525875334463111925427)
        ·
          refine ⟨515420288813001694667888141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343613525875334463111925427 515420288813001694667888141)
          ·
            refine ⟨193282608304875635500458053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 515420288813001694667888141 193282608304875635500458053)
            ·
              refine ⟨36240489057164181656335885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193282608304875635500458053 36240489057164181656335885)
              ·
                refine ⟨13590183396436568121125957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36240489057164181656335885 13590183396436568121125957)
                ·
                  refine ⟨2548159386831856522711117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13590183396436568121125957 2548159386831856522711117)
                  ·
                    refine ⟨955559770061946196016669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2548159386831856522711117 955559770061946196016669)
                    ·
                      rfl

theorem cell22_2791419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 3].length) (baseStart_2791419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791419 prefixEnd_2791419 := by exact prefixLift 2791419
  have htrace : WordTrace (prefixWord ++ tailWord_2791419) baseStart_2791419 baseEnd_2791419 := by
    simpa [prefixWord, tailWord_2791419, baseEnd_2791419] using wordTrace_append hprefix tailTrace_2791419
  have hstable : (prefixWord ++ tailWord_2791419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791419).length < 2 ^ (prefixWord ++ tailWord_2791419).sum := by decide
  have hdescent : baseEnd_2791419 < baseStart_2791419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791436 : List Nat := [2, 2, 1, 2, 3, 1, 1, 5, 2, 3]
def baseStart_2791436 : Nat := 118140960795 + 2791436 * 2 ^ 59
def prefixEnd_2791436 : Nat := 4983230072969 + 3 ^ 40 * 2791436 * 2
def baseEnd_2791436 : Nat := 955565589509363818341617

theorem tailTrace_2791436 : CollatzResearch.WordTrace tailWord_2791436 prefixEnd_2791436 955565589509363818341617 := by
  unfold tailWord_2791436
  simp only [CollatzResearch.WordTrace]
  refine ⟨50906017557555793079377081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67874690076741057439169441 50906017557555793079377081)
  ·
    refine ⟨38179513168166844809532811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50906017557555793079377081 38179513168166844809532811)
    ·
      refine ⟨57269269752250267214299217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38179513168166844809532811 57269269752250267214299217)
      ·
        refine ⟨42951952314187700410724413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57269269752250267214299217 42951952314187700410724413)
        ·
          refine ⟨16106982117820387654021655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42951952314187700410724413 16106982117820387654021655)
          ·
            refine ⟨24160473176730581481032483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16106982117820387654021655 24160473176730581481032483)
            ·
              refine ⟨36240709765095872221548725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24160473176730581481032483 36240709765095872221548725)
              ·
                refine ⟨3397566540477738020770193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36240709765095872221548725 3397566540477738020770193)
                ·
                  refine ⟨2548174905358303515577645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3397566540477738020770193 2548174905358303515577645)
                  ·
                    refine ⟨955565589509363818341617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2548174905358303515577645 955565589509363818341617)
                    ·
                      rfl

theorem cell22_2791436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_2791436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791436 prefixEnd_2791436 := by exact prefixLift 2791436
  have htrace : WordTrace (prefixWord ++ tailWord_2791436) baseStart_2791436 baseEnd_2791436 := by
    simpa [prefixWord, tailWord_2791436, baseEnd_2791436] using wordTrace_append hprefix tailTrace_2791436
  have hstable : (prefixWord ++ tailWord_2791436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791436).length < 2 ^ (prefixWord ++ tailWord_2791436).sum := by decide
  have hdescent : baseEnd_2791436 < baseStart_2791436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791470 : List Nat := [4, 1, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_2791470 : Nat := 118140960795 + 2791470 * 2 ^ 59
def prefixEnd_2791470 : Nat := 4983230072969 + 3 ^ 40 * 2791470 * 2
def baseEnd_2791470 : Nat := 955577228404199062991513

theorem tailTrace_2791470 : CollatzResearch.WordTrace tailWord_2791470 prefixEnd_2791470 955577228404199062991513 := by
  unfold tailWord_2791470
  simp only [CollatzResearch.WordTrace]
  refine ⟨12726659399623551245686483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67875516797992273310327909 12726659399623551245686483)
  ·
    refine ⟨19089989099435326868529725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12726659399623551245686483 19089989099435326868529725)
    ·
      refine ⟨7158745912288247575698647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19089989099435326868529725 7158745912288247575698647)
      ·
        refine ⟨10738118868432371363547971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7158745912288247575698647 10738118868432371363547971)
        ·
          refine ⟨16107178302648557045321957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10738118868432371363547971 16107178302648557045321957)
          ·
            refine ⟨3020095931746604445997867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16107178302648557045321957 3020095931746604445997867)
            ·
              refine ⟨4530143897619906668996801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020095931746604445997867 4530143897619906668996801)
              ·
                refine ⟨3397607923214930001747601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4530143897619906668996801 3397607923214930001747601)
                ·
                  refine ⟨2548205942411197501310701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3397607923214930001747601 2548205942411197501310701)
                  ·
                    refine ⟨955577228404199062991513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2548205942411197501310701 955577228404199062991513)
                    ·
                      rfl

theorem cell22_2791470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_2791470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791470 prefixEnd_2791470 := by exact prefixLift 2791470
  have htrace : WordTrace (prefixWord ++ tailWord_2791470) baseStart_2791470 baseEnd_2791470 := by
    simpa [prefixWord, tailWord_2791470, baseEnd_2791470] using wordTrace_append hprefix tailTrace_2791470
  have hstable : (prefixWord ++ tailWord_2791470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791470).length < 2 ^ (prefixWord ++ tailWord_2791470).sum := by decide
  have hdescent : baseEnd_2791470 < baseStart_2791470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791575 : List Nat := [1, 1, 3, 3, 4, 1, 3, 1, 1, 4]
def baseStart_2791575 : Nat := 118140960795 + 2791575 * 2 ^ 59
def prefixEnd_2791575 : Nat := 4983230072969 + 3 ^ 40 * 2791575 * 2
def baseEnd_2791575 : Nat := 955613172050013789116191

theorem tailTrace_2791575 : CollatzResearch.WordTrace tailWord_2791575 prefixEnd_2791575 955613172050013789116191 := by
  unfold tailWord_2791575
  simp only [CollatzResearch.WordTrace]
  refine ⟨101817104861608012898064179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67878069907738675265376119 101817104861608012898064179)
  ·
    refine ⟨152725657292412019347096269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101817104861608012898064179 152725657292412019347096269)
    ·
      refine ⟨57272121484654507255161101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152725657292412019347096269 57272121484654507255161101)
      ·
        refine ⟨21477045556745440220685413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57272121484654507255161101 21477045556745440220685413)
        ·
          refine ⟨4026946041889770041378515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21477045556745440220685413 4026946041889770041378515)
          ·
            refine ⟨6040419062834655062067773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026946041889770041378515 6040419062834655062067773)
            ·
              refine ⟨2265157148562995648275415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6040419062834655062067773 2265157148562995648275415)
              ·
                refine ⟨3397735722844493472413123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265157148562995648275415 3397735722844493472413123)
                ·
                  refine ⟨5096603584266740208619685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397735722844493472413123 5096603584266740208619685)
                  ·
                    refine ⟨955613172050013789116191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5096603584266740208619685 955613172050013789116191)
                    ·
                      rfl

theorem cell22_2791575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_2791575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791575 prefixEnd_2791575 := by exact prefixLift 2791575
  have htrace : WordTrace (prefixWord ++ tailWord_2791575) baseStart_2791575 baseEnd_2791575 := by
    simpa [prefixWord, tailWord_2791575, baseEnd_2791575] using wordTrace_append hprefix tailTrace_2791575
  have hstable : (prefixWord ++ tailWord_2791575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791575).length < 2 ^ (prefixWord ++ tailWord_2791575).sum := by decide
  have hdescent : baseEnd_2791575 < baseStart_2791575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791584 : List Nat := [2, 1, 1, 4, 2, 12]
def baseStart_2791584 : Nat := 118140960795 + 2791584 * 2 ^ 59
def prefixEnd_2791584 : Nat := 4983230072969 + 3 ^ 40 * 2791584 * 2
def baseEnd_2791584 : Nat := 11797731517702972415323

theorem tailTrace_2791584 : CollatzResearch.WordTrace tailWord_2791584 prefixEnd_2791584 11797731517702972415323 := by
  unfold tailWord_2791584
  simp only [CollatzResearch.WordTrace]
  refine ⟨50908716559287703717570903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67878288745716938290094537 50908716559287703717570903)
  ·
    refine ⟨76363074838931555576356355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50908716559287703717570903 76363074838931555576356355)
    ·
      refine ⟨114544612258397333364534533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76363074838931555576356355 114544612258397333364534533)
      ·
        refine ⟨21477114798449500005850225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114544612258397333364534533 21477114798449500005850225)
        ·
          refine ⟨16107836098837125004387669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21477114798449500005850225 16107836098837125004387669)
          ·
            refine ⟨11797731517702972415323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16107836098837125004387669 11797731517702972415323)
            ·
              rfl

theorem cell22_2791584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 12].length) (baseStart_2791584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791584 prefixEnd_2791584 := by exact prefixLift 2791584
  have htrace : WordTrace (prefixWord ++ tailWord_2791584) baseStart_2791584 baseEnd_2791584 := by
    simpa [prefixWord, tailWord_2791584, baseEnd_2791584] using wordTrace_append hprefix tailTrace_2791584
  have hstable : (prefixWord ++ tailWord_2791584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791584).length < 2 ^ (prefixWord ++ tailWord_2791584).sum := by decide
  have hdescent : baseEnd_2791584 < baseStart_2791584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791599 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 2, 7]
def baseStart_2791599 : Nat := 118140960795 + 2791599 * 2 ^ 59
def prefixEnd_2791599 : Nat := 4983230072969 + 3 ^ 40 * 2791599 * 2
def baseEnd_2791599 : Nat := 955621387740485726516117

theorem tailTrace_2791599 : CollatzResearch.WordTrace tailWord_2791599 prefixEnd_2791599 955621387740485726516117 := by
  unfold tailWord_2791599
  simp only [CollatzResearch.WordTrace]
  refine ⟨101817980213521064996937851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67878653475680709997958567 101817980213521064996937851)
  ·
    refine ⟨152726970320281597495406777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101817980213521064996937851 152726970320281597495406777)
    ·
      refine ⟨114545227740211198121555083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152726970320281597495406777 114545227740211198121555083)
      ·
        refine ⟨171817841610316797182332625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114545227740211198121555083 171817841610316797182332625)
        ·
          refine ⟨128863381207737597886749469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171817841610316797182332625 128863381207737597886749469)
          ·
            refine ⟨48323767952901599207531051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128863381207737597886749469 48323767952901599207531051)
            ·
              refine ⟨72485651929352398811296577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48323767952901599207531051 72485651929352398811296577)
              ·
                refine ⟨54364238947014299108472433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72485651929352398811296577 54364238947014299108472433)
                ·
                  refine ⟨40773179210260724331354325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54364238947014299108472433 40773179210260724331354325)
                  ·
                    refine ⟨955621387740485726516117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40773179210260724331354325 955621387740485726516117)
                    ·
                      rfl

theorem cell22_2791599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_2791599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791599 prefixEnd_2791599 := by exact prefixLift 2791599
  have htrace : WordTrace (prefixWord ++ tailWord_2791599) baseStart_2791599 baseEnd_2791599 := by
    simpa [prefixWord, tailWord_2791599, baseEnd_2791599] using wordTrace_append hprefix tailTrace_2791599
  have hstable : (prefixWord ++ tailWord_2791599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791599).length < 2 ^ (prefixWord ++ tailWord_2791599).sum := by decide
  have hdescent : baseEnd_2791599 < baseStart_2791599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791605 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 1, 5]
def baseStart_2791605 : Nat := 118140960795 + 2791605 * 2 ^ 59
def prefixEnd_2791605 : Nat := 4983230072969 + 3 ^ 40 * 2791605 * 2
def baseEnd_2791605 : Nat := 955623441663103710866099

theorem tailTrace_2791605 : CollatzResearch.WordTrace tailWord_2791605 prefixEnd_2791605 955623441663103710866099 := by
  unfold tailWord_2791605
  simp only [CollatzResearch.WordTrace]
  refine ⟨101818199051499328021656269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67878799367666218681104179 101818199051499328021656269)
  ·
    refine ⟨38181824644312248008121101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101818199051499328021656269 38181824644312248008121101)
    ·
      refine ⟨14318184241617093003045413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38181824644312248008121101 14318184241617093003045413)
      ·
        refine ⟨2684659545303204938071015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14318184241617093003045413 2684659545303204938071015)
        ·
          refine ⟨4026989317954807407106523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2684659545303204938071015 4026989317954807407106523)
          ·
            refine ⟨6040483976932211110659785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026989317954807407106523 6040483976932211110659785)
            ·
              refine ⟨4530362982699158332994839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6040483976932211110659785 4530362982699158332994839)
              ·
                refine ⟨6795544474048737499492259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4530362982699158332994839 6795544474048737499492259)
                ·
                  refine ⟨10193316711073106249238389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6795544474048737499492259 10193316711073106249238389)
                  ·
                    refine ⟨955623441663103710866099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10193316711073106249238389 955623441663103710866099)
                    ·
                      rfl

theorem cell22_2791605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_2791605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791605 prefixEnd_2791605 := by exact prefixLift 2791605
  have htrace : WordTrace (prefixWord ++ tailWord_2791605) baseStart_2791605 baseEnd_2791605 := by
    simpa [prefixWord, tailWord_2791605, baseEnd_2791605] using wordTrace_append hprefix tailTrace_2791605
  have hstable : (prefixWord ++ tailWord_2791605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791605).length < 2 ^ (prefixWord ++ tailWord_2791605).sum := by decide
  have hdescent : baseEnd_2791605 < baseStart_2791605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791620 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_2791620 : Nat := 118140960795 + 2791620 * 2 ^ 59
def prefixEnd_2791620 : Nat := 4983230072969 + 3 ^ 40 * 2791620 * 2
def baseEnd_2791620 : Nat := 955628576469648671741053

theorem tailTrace_2791620 : CollatzResearch.WordTrace tailWord_2791620 prefixEnd_2791620 955628576469648671741053 := by
  unfold tailWord_2791620
  simp only [CollatzResearch.WordTrace]
  refine ⟨50909373073222492791726157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67879164097629990388968209 50909373073222492791726157)
  ·
    refine ⟨19091014902458434796897309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50909373073222492791726157 19091014902458434796897309)
    ·
      refine ⟨7159130588421913048836491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19091014902458434796897309 7159130588421913048836491)
      ·
        refine ⟨10738695882632869573254737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7159130588421913048836491 10738695882632869573254737)
        ·
          refine ⟨8054021911974652179941053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10738695882632869573254737 8054021911974652179941053)
          ·
            refine ⟨3020258216990494567477895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8054021911974652179941053 3020258216990494567477895)
            ·
              refine ⟨4530387325485741851216843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020258216990494567477895 4530387325485741851216843)
              ·
                refine ⟨6795580988228612776825265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4530387325485741851216843 6795580988228612776825265)
                ·
                  refine ⟨5096685741171459582618949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6795580988228612776825265 5096685741171459582618949)
                  ·
                    refine ⟨955628576469648671741053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5096685741171459582618949 955628576469648671741053)
                    ·
                      rfl

theorem cell22_2791620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_2791620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791620 prefixEnd_2791620 := by exact prefixLift 2791620
  have htrace : WordTrace (prefixWord ++ tailWord_2791620) baseStart_2791620 baseEnd_2791620 := by
    simpa [prefixWord, tailWord_2791620, baseEnd_2791620] using wordTrace_append hprefix tailTrace_2791620
  have hstable : (prefixWord ++ tailWord_2791620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791620).length < 2 ^ (prefixWord ++ tailWord_2791620).sum := by decide
  have hdescent : baseEnd_2791620 < baseStart_2791620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791684 : List Nat := [2, 3, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_2791684 : Nat := 118140960795 + 2791684 * 2 ^ 59
def prefixEnd_2791684 : Nat := 4983230072969 + 3 ^ 40 * 2791684 * 2
def baseEnd_2791684 : Nat := 955650484977573838140857

theorem tailTrace_2791684 : CollatzResearch.WordTrace tailWord_2791684 prefixEnd_2791684 955650484977573838140857 := by
  unfold tailWord_2791684
  simp only [CollatzResearch.WordTrace]
  refine ⟨50910540209106562256891053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67880720278808749675854737 50910540209106562256891053)
  ·
    refine ⟨19091452578414960846334145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50910540209106562256891053 19091452578414960846334145)
    ·
      refine ⟨14318589433811220634750609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19091452578414960846334145 14318589433811220634750609)
      ·
        refine ⟨10738942075358415476062957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14318589433811220634750609 10738942075358415476062957)
        ·
          refine ⟨4027103278259405803523609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10738942075358415476062957 4027103278259405803523609)
          ·
            refine ⟨3020327458694554352642707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4027103278259405803523609 3020327458694554352642707)
            ·
              refine ⟨4530491188041831528964061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020327458694554352642707 4530491188041831528964061)
              ·
                refine ⟨1698934195515686823361523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4530491188041831528964061 1698934195515686823361523)
                ·
                  refine ⟨2548401293273530235042285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698934195515686823361523 2548401293273530235042285)
                  ·
                    refine ⟨955650484977573838140857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2548401293273530235042285 955650484977573838140857)
                    ·
                      rfl

theorem cell22_2791684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_2791684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791684 prefixEnd_2791684 := by exact prefixLift 2791684
  have htrace : WordTrace (prefixWord ++ tailWord_2791684) baseStart_2791684 baseEnd_2791684 := by
    simpa [prefixWord, tailWord_2791684, baseEnd_2791684] using wordTrace_append hprefix tailTrace_2791684
  have hstable : (prefixWord ++ tailWord_2791684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791684).length < 2 ^ (prefixWord ++ tailWord_2791684).sum := by decide
  have hdescent : baseEnd_2791684 < baseStart_2791684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791736 : List Nat := [2, 1, 2, 1, 3, 1, 4, 8]
def baseStart_2791736 : Nat := 118140960795 + 2791736 * 2 ^ 59
def prefixEnd_2791736 : Nat := 4983230072969 + 3 ^ 40 * 2791736 * 2
def baseEnd_2791736 : Nat := 106185365071140337315633

theorem tailTrace_2791736 : CollatzResearch.WordTrace tailWord_2791736 prefixEnd_2791736 106185365071140337315633 := by
  unfold tailWord_2791736
  simp only [CollatzResearch.WordTrace]
  refine ⟨50911488507012368697337531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67881984676016491596450041 50911488507012368697337531)
  ·
    refine ⟨76367232760518553046006297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50911488507012368697337531 76367232760518553046006297)
    ·
      refine ⟨57275424570388914784504723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76367232760518553046006297 57275424570388914784504723)
      ·
        refine ⟨85913136855583372176757085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57275424570388914784504723 85913136855583372176757085)
        ·
          refine ⟨32217426320843764566283907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85913136855583372176757085 32217426320843764566283907)
          ·
            refine ⟨48326139481265646849425861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32217426320843764566283907 48326139481265646849425861)
            ·
              refine ⟨9061151152737308784267349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48326139481265646849425861 9061151152737308784267349)
              ·
                refine ⟨106185365071140337315633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9061151152737308784267349 106185365071140337315633)
                ·
                  rfl

theorem cell22_2791736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 8].length) (baseStart_2791736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791736 prefixEnd_2791736 := by exact prefixLift 2791736
  have htrace : WordTrace (prefixWord ++ tailWord_2791736) baseStart_2791736 baseEnd_2791736 := by
    simpa [prefixWord, tailWord_2791736, baseEnd_2791736] using wordTrace_append hprefix tailTrace_2791736
  have hstable : (prefixWord ++ tailWord_2791736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791736).length < 2 ^ (prefixWord ++ tailWord_2791736).sum := by decide
  have hdescent : baseEnd_2791736 < baseStart_2791736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
