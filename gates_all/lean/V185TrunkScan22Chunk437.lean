import V185TrunkScan22Chunk436

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3895509 : List Nat := [1, 3, 2, 4, 2, 2, 1, 2, 1, 4]
def baseStart_3895509 : Nat := 118140960795 + 3895509 * 2 ^ 59
def prefixEnd_3895509 : Nat := 4983230072969 + 3 ^ 40 * 3895509 * 2
def baseEnd_3895509 : Nat := 1333512340610336357881591

theorem tailTrace_3895509 : CollatzResearch.WordTrace tailWord_3895509 prefixEnd_3895509 1333512340610336357881591 := by
  unfold tailWord_3895509
  simp only [CollatzResearch.WordTrace]
  refine ⟨142080885644243667815073581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94720590429495778543382387 142080885644243667815073581)
  ·
    refine ⟨53280332116591375430652593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142080885644243667815073581 53280332116591375430652593)
    ·
      refine ⟨39960249087443531572989445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53280332116591375430652593 39960249087443531572989445)
      ·
        refine ⟨7492546703895662169935521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39960249087443531572989445 7492546703895662169935521)
        ·
          refine ⟨5619410027921746627451641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7492546703895662169935521 5619410027921746627451641)
          ·
            refine ⟨4214557520941309970588731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5619410027921746627451641 4214557520941309970588731)
            ·
              refine ⟨6321836281411964955883097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4214557520941309970588731 6321836281411964955883097)
              ·
                refine ⟨4741377211058973716912323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6321836281411964955883097 4741377211058973716912323)
                ·
                  refine ⟨7112065816588460575368485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741377211058973716912323 7112065816588460575368485)
                  ·
                    refine ⟨1333512340610336357881591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7112065816588460575368485 1333512340610336357881591)
                    ·
                      rfl

theorem cell22_3895509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_3895509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895509 prefixEnd_3895509 := by exact prefixLift 3895509
  have htrace : WordTrace (prefixWord ++ tailWord_3895509) baseStart_3895509 baseEnd_3895509 := by
    simpa [prefixWord, tailWord_3895509, baseEnd_3895509] using wordTrace_append hprefix tailTrace_3895509
  have hstable : (prefixWord ++ tailWord_3895509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895509).length < 2 ^ (prefixWord ++ tailWord_3895509).sum := by decide
  have hdescent : baseEnd_3895509 < baseStart_3895509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895520 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 2, 4]
def baseStart_3895520 : Nat := 118140960795 + 3895520 * 2 ^ 59
def prefixEnd_3895520 : Nat := 4983230072969 + 3 ^ 40 * 3895520 * 2
def baseEnd_3895520 : Nat := 1333516106135135995856557

theorem tailTrace_3895520 : CollatzResearch.WordTrace tailWord_3895520 prefixEnd_3895520 1333516106135135995856557 := by
  unfold tailWord_3895520
  simp only [CollatzResearch.WordTrace]
  refine ⟨71040643423601908346862007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94720857898135877795816009 71040643423601908346862007)
  ·
    refine ⟨106560965135402862520293011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71040643423601908346862007 106560965135402862520293011)
    ·
      refine ⟨159841447703104293780439517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106560965135402862520293011 159841447703104293780439517)
      ·
        refine ⟨59940542888664110167664819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159841447703104293780439517 59940542888664110167664819)
        ·
          refine ⟨89910814332996165251497229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59940542888664110167664819 89910814332996165251497229)
          ·
            refine ⟨33716555374873561969311461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89910814332996165251497229 33716555374873561969311461)
            ·
              refine ⟨6321854132788792869245899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33716555374873561969311461 6321854132788792869245899)
              ·
                refine ⟨9482781199183189303868849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321854132788792869245899 9482781199183189303868849)
                ·
                  refine ⟨7112085899387391977901637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9482781199183189303868849 7112085899387391977901637)
                  ·
                    refine ⟨1333516106135135995856557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7112085899387391977901637 1333516106135135995856557)
                    ·
                      rfl

theorem cell22_3895520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_3895520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895520 prefixEnd_3895520 := by exact prefixLift 3895520
  have htrace : WordTrace (prefixWord ++ tailWord_3895520) baseStart_3895520 baseEnd_3895520 := by
    simpa [prefixWord, tailWord_3895520, baseEnd_3895520] using wordTrace_append hprefix tailTrace_3895520
  have hstable : (prefixWord ++ tailWord_3895520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895520).length < 2 ^ (prefixWord ++ tailWord_3895520).sum := by decide
  have hdescent : baseEnd_3895520 < baseStart_3895520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895584 : List Nat := [2, 1, 1, 5, 2, 1, 1, 5, 1, 3]
def baseStart_3895584 : Nat := 118140960795 + 3895584 * 2 ^ 59
def prefixEnd_3895584 : Nat := 4983230072969 + 3 ^ 40 * 3895584 * 2
def baseEnd_3895584 : Nat := 1333538014643061162256361

theorem tailTrace_3895584 : CollatzResearch.WordTrace tailWord_3895584 prefixEnd_3895584 1333538014643061162256361 := by
  unfold tailWord_3895584
  simp only [CollatzResearch.WordTrace]
  refine ⟨71041810559485977812026903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94722414079314637082702537 71041810559485977812026903)
  ·
    refine ⟨106562715839228966718040355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71041810559485977812026903 106562715839228966718040355)
    ·
      refine ⟨159844073758843450077060533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106562715839228966718040355 159844073758843450077060533)
      ·
        refine ⟨14985381914891573444724425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159844073758843450077060533 14985381914891573444724425)
        ·
          refine ⟨11239036436168680083543319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14985381914891573444724425 11239036436168680083543319)
          ·
            refine ⟨16858554654253020125314979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11239036436168680083543319 16858554654253020125314979)
            ·
              refine ⟨25287831981379530187972469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16858554654253020125314979 25287831981379530187972469)
              ·
                refine ⟨2370734248254330955122419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25287831981379530187972469 2370734248254330955122419)
                ·
                  refine ⟨3556101372381496432683629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370734248254330955122419 3556101372381496432683629)
                  ·
                    refine ⟨1333538014643061162256361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3556101372381496432683629 1333538014643061162256361)
                    ·
                      rfl

theorem cell22_3895584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 1, 3].length) (baseStart_3895584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895584 prefixEnd_3895584 := by exact prefixLift 3895584
  have htrace : WordTrace (prefixWord ++ tailWord_3895584) baseStart_3895584 baseEnd_3895584 := by
    simpa [prefixWord, tailWord_3895584, baseEnd_3895584] using wordTrace_append hprefix tailTrace_3895584
  have hstable : (prefixWord ++ tailWord_3895584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895584).length < 2 ^ (prefixWord ++ tailWord_3895584).sum := by decide
  have hdescent : baseEnd_3895584 < baseStart_3895584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895614 : List Nat := [4, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_3895614 : Nat := 118140960795 + 3895614 * 2 ^ 59
def prefixEnd_3895614 : Nat := 4983230072969 + 3 ^ 40 * 3895614 * 2
def baseEnd_3895614 : Nat := 444516094752050361335423

theorem tailTrace_3895614 : CollatzResearch.WordTrace tailWord_3895614 prefixEnd_3895614 444516094752050361335423 := by
  unfold tailWord_3895614
  simp only [CollatzResearch.WordTrace]
  refine ⟨17760589413607908843455737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94723143539242180498430597 17760589413607908843455737)
  ·
    refine ⟨13320442060205931632591803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17760589413607908843455737 13320442060205931632591803)
    ·
      refine ⟨19980663090308897448887705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13320442060205931632591803 19980663090308897448887705)
      ·
        refine ⟨14985497317731673086665779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19980663090308897448887705 14985497317731673086665779)
        ·
          refine ⟨22478245976597509629998669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14985497317731673086665779 22478245976597509629998669)
          ·
            refine ⟨8429342241224066111249501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22478245976597509629998669 8429342241224066111249501)
            ·
              refine ⟨3161003340459024791718563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8429342241224066111249501 3161003340459024791718563)
              ·
                refine ⟨4741505010688537187577845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161003340459024791718563 4741505010688537187577845)
                ·
                  refine ⟨444516094752050361335423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4741505010688537187577845 444516094752050361335423)
                  ·
                    rfl

theorem cell22_3895614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_3895614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895614 prefixEnd_3895614 := by exact prefixLift 3895614
  have htrace : WordTrace (prefixWord ++ tailWord_3895614) baseStart_3895614 baseEnd_3895614 := by
    simpa [prefixWord, tailWord_3895614, baseEnd_3895614] using wordTrace_append hprefix tailTrace_3895614
  have hstable : (prefixWord ++ tailWord_3895614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895614).length < 2 ^ (prefixWord ++ tailWord_3895614).sum := by decide
  have hdescent : baseEnd_3895614 < baseStart_3895614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895657 : List Nat := [1, 2, 1, 1, 1, 3, 4, 4, 2, 3]
def baseStart_3895657 : Nat := 118140960795 + 3895657 * 2 ^ 59
def prefixEnd_3895657 : Nat := 4983230072969 + 3 ^ 40 * 3895657 * 2
def baseEnd_3895657 : Nat := 1333563004034913305181137

theorem tailTrace_3895657 : CollatzResearch.WordTrace tailWord_3895657 prefixEnd_3895657 1333563004034913305181137 := by
  unfold tailWord_3895657
  simp only [CollatzResearch.WordTrace]
  refine ⟨142086283647707489091461225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94724189098471659394307483 142086283647707489091461225)
  ·
    refine ⟨106564712735780616818595919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142086283647707489091461225 106564712735780616818595919)
    ·
      refine ⟨159847069103670925227893879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106564712735780616818595919 159847069103670925227893879)
      ·
        refine ⟨239770603655506387841840819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159847069103670925227893879 239770603655506387841840819)
        ·
          refine ⟨359655905483259581762761229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239770603655506387841840819 359655905483259581762761229)
          ·
            refine ⟨134870964556222343161035461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359655905483259581762761229 134870964556222343161035461)
            ·
              refine ⟨25288305854291689342694149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134870964556222343161035461 25288305854291689342694149)
              ·
                refine ⟨4741557347679691751755153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25288305854291689342694149 4741557347679691751755153)
                ·
                  refine ⟨3556168010759768813816365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4741557347679691751755153 3556168010759768813816365)
                  ·
                    refine ⟨1333563004034913305181137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3556168010759768813816365 1333563004034913305181137)
                    ·
                      rfl

theorem cell22_3895657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 3].length) (baseStart_3895657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895657 prefixEnd_3895657 := by exact prefixLift 3895657
  have htrace : WordTrace (prefixWord ++ tailWord_3895657) baseStart_3895657 baseEnd_3895657 := by
    simpa [prefixWord, tailWord_3895657, baseEnd_3895657] using wordTrace_append hprefix tailTrace_3895657
  have hstable : (prefixWord ++ tailWord_3895657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895657).length < 2 ^ (prefixWord ++ tailWord_3895657).sum := by decide
  have hdescent : baseEnd_3895657 < baseStart_3895657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895777 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 6]
def baseStart_3895777 : Nat := 118140960795 + 3895777 * 2 ^ 59
def prefixEnd_3895777 : Nat := 4983230072969 + 3 ^ 40 * 3895777 * 2
def baseEnd_3895777 : Nat := 444534694162424330726923

theorem tailTrace_3895777 : CollatzResearch.WordTrace tailWord_3895777 prefixEnd_3895777 444534694162424330726923 := by
  unfold tailWord_3895777
  simp only [CollatzResearch.WordTrace]
  refine ⟨142090660407272749585829585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94727106938181833057219723 142090660407272749585829585)
  ·
    refine ⟨106567995305454562189372189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142090660407272749585829585 106567995305454562189372189)
    ·
      refine ⟨39962998239545460821014571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106567995305454562189372189 39962998239545460821014571)
      ·
        refine ⟨59944497359318191231521857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39962998239545460821014571 59944497359318191231521857)
        ·
          refine ⟨44958373019488643423641393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59944497359318191231521857 44958373019488643423641393)
          ·
            refine ⟨33718779764616482567731045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44958373019488643423641393 33718779764616482567731045)
            ·
              refine ⟨6322271205865590481449571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33718779764616482567731045 6322271205865590481449571)
              ·
                refine ⟨9483406808798385722174357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6322271205865590481449571 9483406808798385722174357)
                ·
                  refine ⟨444534694162424330726923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9483406808798385722174357 444534694162424330726923)
                  ·
                    rfl

theorem cell22_3895777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_3895777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895777 prefixEnd_3895777 := by exact prefixLift 3895777
  have htrace : WordTrace (prefixWord ++ tailWord_3895777) baseStart_3895777 baseEnd_3895777 := by
    simpa [prefixWord, tailWord_3895777, baseEnd_3895777] using wordTrace_append hprefix tailTrace_3895777
  have hstable : (prefixWord ++ tailWord_3895777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895777).length < 2 ^ (prefixWord ++ tailWord_3895777).sum := by decide
  have hdescent : baseEnd_3895777 < baseStart_3895777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895807 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 2, 4]
def baseStart_3895807 : Nat := 118140960795 + 3895807 * 2 ^ 59
def prefixEnd_3895807 : Nat := 4983230072969 + 3 ^ 40 * 3895807 * 2
def baseEnd_3895807 : Nat := 1333614352100362913930677

theorem tailTrace_3895807 : CollatzResearch.WordTrace tailWord_3895807 prefixEnd_3895807 1333614352100362913930677 := by
  unfold tailWord_3895807
  simp only [CollatzResearch.WordTrace]
  refine ⟨142091754597164064709421675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94727836398109376472947783 142091754597164064709421675)
  ·
    refine ⟨213137631895746097064132513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142091754597164064709421675 213137631895746097064132513)
    ·
      refine ⟨159853223921809572798099385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213137631895746097064132513 159853223921809572798099385)
      ·
        refine ⟨119889917941357179598574539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159853223921809572798099385 119889917941357179598574539)
        ·
          refine ⟨179834876912035769397861809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119889917941357179598574539 179834876912035769397861809)
          ·
            refine ⟨134876157684026827048396357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179834876912035769397861809 134876157684026827048396357)
            ·
              refine ⟨25289279565755030071574317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134876157684026827048396357 25289279565755030071574317)
              ·
                refine ⟨9483479837158136276840369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25289279565755030071574317 9483479837158136276840369)
                ·
                  refine ⟨7112609877868602207630277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9483479837158136276840369 7112609877868602207630277)
                  ·
                    refine ⟨1333614352100362913930677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7112609877868602207630277 1333614352100362913930677)
                    ·
                      rfl

theorem cell22_3895807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_3895807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895807 prefixEnd_3895807 := by exact prefixLift 3895807
  have htrace : WordTrace (prefixWord ++ tailWord_3895807) baseStart_3895807 baseEnd_3895807 := by
    simpa [prefixWord, tailWord_3895807, baseEnd_3895807] using wordTrace_append hprefix tailTrace_3895807
  have hstable : (prefixWord ++ tailWord_3895807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895807).length < 2 ^ (prefixWord ++ tailWord_3895807).sum := by decide
  have hdescent : baseEnd_3895807 < baseStart_3895807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895809 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 4, 3]
def baseStart_3895809 : Nat := 118140960795 + 3895809 * 2 ^ 59
def prefixEnd_3895809 : Nat := 4983230072969 + 3 ^ 40 * 3895809 * 2
def baseEnd_3895809 : Nat := 1333615036741235575380671

theorem tailTrace_3895809 : CollatzResearch.WordTrace tailWord_3895809 prefixEnd_3895809 1333615036741235575380671 := by
  unfold tailWord_3895809
  simp only [CollatzResearch.WordTrace]
  refine ⟨142091827543156819050994481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94727885028771212700662987 142091827543156819050994481)
  ·
    refine ⟨106568870657367614288245861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142091827543156819050994481 106568870657367614288245861)
    ·
      refine ⟨19981663248256427679046099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106568870657367614288245861 19981663248256427679046099)
      ·
        refine ⟨29972494872384641518569149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19981663248256427679046099 29972494872384641518569149)
        ·
          refine ⟨11239685577144240569463431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29972494872384641518569149 11239685577144240569463431)
          ·
            refine ⟨16859528365716360854195147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11239685577144240569463431 16859528365716360854195147)
            ·
              refine ⟨25289292548574541281292721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16859528365716360854195147 25289292548574541281292721)
              ·
                refine ⟨18966969411430905960969541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25289292548574541281292721 18966969411430905960969541)
                ·
                  refine ⟨3556306764643294867681789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18966969411430905960969541 3556306764643294867681789)
                  ·
                    refine ⟨1333615036741235575380671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3556306764643294867681789 1333615036741235575380671)
                    ·
                      rfl

theorem cell22_3895809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_3895809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895809 prefixEnd_3895809 := by exact prefixLift 3895809
  have htrace : WordTrace (prefixWord ++ tailWord_3895809) baseStart_3895809 baseEnd_3895809 := by
    simpa [prefixWord, tailWord_3895809, baseEnd_3895809] using wordTrace_append hprefix tailTrace_3895809
  have hstable : (prefixWord ++ tailWord_3895809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895809).length < 2 ^ (prefixWord ++ tailWord_3895809).sum := by decide
  have hdescent : baseEnd_3895809 < baseStart_3895809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895822 : List Nat := [4, 1, 1, 2, 3, 1, 10]
def baseStart_3895822 : Nat := 118140960795 + 3895822 * 2 ^ 59
def prefixEnd_3895822 : Nat := 4983230072969 + 3 ^ 40 * 3895822 * 2
def baseEnd_3895822 : Nat := 49393314329885476844653

theorem tailTrace_3895822 : CollatzResearch.WordTrace tailWord_3895822 prefixEnd_3895822 49393314329885476844653 := by
  unfold tailWord_3895822
  simp only [CollatzResearch.WordTrace]
  refine ⟨17761537711513715283902215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94728201128073148180811813 17761537711513715283902215)
  ·
    refine ⟨26642306567270572925853323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17761537711513715283902215 26642306567270572925853323)
    ·
      refine ⟨39963459850905859388779985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26642306567270572925853323 39963459850905859388779985)
      ·
        refine ⟨29972594888179394541584989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39963459850905859388779985 29972594888179394541584989)
        ·
          refine ⟨11239723083067272953094371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29972594888179394541584989 11239723083067272953094371)
          ·
            refine ⟨16859584624600909429641557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11239723083067272953094371 16859584624600909429641557)
            ·
              refine ⟨49393314329885476844653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16859584624600909429641557 49393314329885476844653)
              ·
                rfl

theorem cell22_3895822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 10].length) (baseStart_3895822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895822 prefixEnd_3895822 := by exact prefixLift 3895822
  have htrace : WordTrace (prefixWord ++ tailWord_3895822) baseStart_3895822 baseEnd_3895822 := by
    simpa [prefixWord, tailWord_3895822, baseEnd_3895822] using wordTrace_append hprefix tailTrace_3895822
  have hstable : (prefixWord ++ tailWord_3895822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895822).length < 2 ^ (prefixWord ++ tailWord_3895822).sum := by decide
  have hdescent : baseEnd_3895822 < baseStart_3895822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895843 : List Nat := [1, 1, 1, 4, 4, 3, 2, 1, 2, 3]
def baseStart_3895843 : Nat := 118140960795 + 3895843 * 2 ^ 59
def prefixEnd_3895843 : Nat := 4983230072969 + 3 ^ 40 * 3895843 * 2
def baseEnd_3895843 : Nat := 1333626675636070820030567

theorem tailTrace_3895843 : CollatzResearch.WordTrace tailWord_3895843 prefixEnd_3895843 1333626675636070820030567 := by
  unfold tailWord_3895843
  simp only [CollatzResearch.WordTrace]
  refine ⟨142093067625033642857732183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94728711750022428571821455 142093067625033642857732183)
  ·
    refine ⟨213139601437550464286598275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142093067625033642857732183 213139601437550464286598275)
    ·
      refine ⟨319709402156325696429897413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213139601437550464286598275 319709402156325696429897413)
      ·
        refine ⟨59945512904311068080605765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319709402156325696429897413 59945512904311068080605765)
        ·
          refine ⟨11239783669558325265113581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59945512904311068080605765 11239783669558325265113581)
          ·
            refine ⟨4214918876084371974417593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11239783669558325265113581 4214918876084371974417593)
            ·
              refine ⟨3161189157063278980813195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4214918876084371974417593 3161189157063278980813195)
              ·
                refine ⟨4741783735594918471219793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161189157063278980813195 4741783735594918471219793)
                ·
                  refine ⟨3556337801696188853414845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4741783735594918471219793 3556337801696188853414845)
                  ·
                    refine ⟨1333626675636070820030567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3556337801696188853414845 1333626675636070820030567)
                    ·
                      rfl

theorem cell22_3895843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 2, 3].length) (baseStart_3895843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895843 prefixEnd_3895843 := by exact prefixLift 3895843
  have htrace : WordTrace (prefixWord ++ tailWord_3895843) baseStart_3895843 baseEnd_3895843 := by
    simpa [prefixWord, tailWord_3895843, baseEnd_3895843] using wordTrace_append hprefix tailTrace_3895843
  have hstable : (prefixWord ++ tailWord_3895843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895843).length < 2 ^ (prefixWord ++ tailWord_3895843).sum := by decide
  have hdescent : baseEnd_3895843 < baseStart_3895843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895871 : List Nat := [1, 1, 2, 2, 3, 2, 2, 5, 1, 3]
def baseStart_3895871 : Nat := 118140960795 + 3895871 * 2 ^ 59
def prefixEnd_3895871 : Nat := 4983230072969 + 3 ^ 40 * 3895871 * 2
def baseEnd_3895871 : Nat := 1333636260608288080330481

theorem tailTrace_3895871 : CollatzResearch.WordTrace tailWord_3895871 prefixEnd_3895871 1333636260608288080330481 := by
  unfold tailWord_3895871
  simp only [CollatzResearch.WordTrace]
  refine ⟨142094088868932203639751467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94729392579288135759834311 142094088868932203639751467)
  ·
    refine ⟨213141133303398305459627201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142094088868932203639751467 213141133303398305459627201)
    ·
      refine ⟨159855849977548729094720401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213141133303398305459627201 159855849977548729094720401)
      ·
        refine ⟨119891887483161546821040301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159855849977548729094720401 119891887483161546821040301)
        ·
          refine ⟨44959457806185580057890113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119891887483161546821040301 44959457806185580057890113)
          ·
            refine ⟨33719593354639185043417585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44959457806185580057890113 33719593354639185043417585)
            ·
              refine ⟨25289695015979388782563189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33719593354639185043417585 25289695015979388782563189)
              ·
                refine ⟨2370908907748067698365299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25289695015979388782563189 2370908907748067698365299)
                ·
                  refine ⟨3556363361622101547547949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370908907748067698365299 3556363361622101547547949)
                  ·
                    refine ⟨1333636260608288080330481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3556363361622101547547949 1333636260608288080330481)
                    ·
                      rfl

theorem cell22_3895871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 1, 3].length) (baseStart_3895871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895871 prefixEnd_3895871 := by exact prefixLift 3895871
  have htrace : WordTrace (prefixWord ++ tailWord_3895871) baseStart_3895871 baseEnd_3895871 := by
    simpa [prefixWord, tailWord_3895871, baseEnd_3895871] using wordTrace_append hprefix tailTrace_3895871
  have hstable : (prefixWord ++ tailWord_3895871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895871).length < 2 ^ (prefixWord ++ tailWord_3895871).sum := by decide
  have hdescent : baseEnd_3895871 < baseStart_3895871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895884 : List Nat := [2, 2, 1, 3, 1, 2, 4, 2, 5]
def baseStart_3895884 : Nat := 118140960795 + 3895884 * 2 ^ 59
def prefixEnd_3895884 : Nat := 4983230072969 + 3 ^ 40 * 3895884 * 2
def baseEnd_3895884 : Nat := 444546903591320126585147

theorem tailTrace_3895884 : CollatzResearch.WordTrace tailWord_3895884 prefixEnd_3895884 444546903591320126585147 := by
  unfold tailWord_3895884
  simp only [CollatzResearch.WordTrace]
  refine ⟨71047281508942553429987353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94729708678590071239983137 71047281508942553429987353)
  ·
    refine ⟨53285461131706915072490515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71047281508942553429987353 53285461131706915072490515)
    ·
      refine ⟨79928191697560372608735773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53285461131706915072490515 79928191697560372608735773)
      ·
        refine ⟨29973071886585139728275915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79928191697560372608735773 29973071886585139728275915)
        ·
          refine ⟨44959607829877709592413873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29973071886585139728275915 44959607829877709592413873)
          ·
            refine ⟨33719705872408282194310405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44959607829877709592413873 33719705872408282194310405)
            ·
              refine ⟨6322444851076552911433201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33719705872408282194310405 6322444851076552911433201)
              ·
                refine ⟨4741833638307414683574901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6322444851076552911433201 4741833638307414683574901)
                ·
                  refine ⟨444546903591320126585147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4741833638307414683574901 444546903591320126585147)
                  ·
                    rfl

theorem cell22_3895884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_3895884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895884 prefixEnd_3895884 := by exact prefixLift 3895884
  have htrace : WordTrace (prefixWord ++ tailWord_3895884) baseStart_3895884 baseEnd_3895884 := by
    simpa [prefixWord, tailWord_3895884, baseEnd_3895884] using wordTrace_append hprefix tailTrace_3895884
  have hstable : (prefixWord ++ tailWord_3895884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895884).length < 2 ^ (prefixWord ++ tailWord_3895884).sum := by decide
  have hdescent : baseEnd_3895884 < baseStart_3895884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895914 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_3895914 : Nat := 118140960795 + 3895914 * 2 ^ 59
def prefixEnd_3895914 : Nat := 4983230072969 + 3 ^ 40 * 3895914 * 2
def baseEnd_3895914 : Nat := 1333650980387050301505349

theorem tailTrace_3895914 : CollatzResearch.WordTrace tailWord_3895914 prefixEnd_3895914 1333650980387050301505349 := by
  unfold tailWord_3895914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35523914301944105495891699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94730438138517614655711197 35523914301944105495891699)
  ·
    refine ⟨53285871452916158243837549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35523914301944105495891699 53285871452916158243837549)
    ·
      refine ⟨19982201794843559341439081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53285871452916158243837549 19982201794843559341439081)
      ·
        refine ⟨14986651346132669506079311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19982201794843559341439081 14986651346132669506079311)
        ·
          refine ⟨22479977019199004259118967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14986651346132669506079311 22479977019199004259118967)
          ·
            refine ⟨33719965528798506388678451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22479977019199004259118967 33719965528798506388678451)
            ·
              refine ⟨50579948293197759583017677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33719965528798506388678451 50579948293197759583017677)
              ·
                refine ⟨18967480609949159843631629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50579948293197759583017677 18967480609949159843631629)
                ·
                  refine ⟨7112805228730934941361861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18967480609949159843631629 7112805228730934941361861)
                  ·
                    refine ⟨1333650980387050301505349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7112805228730934941361861 1333650980387050301505349)
                    ·
                      rfl

theorem cell22_3895914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_3895914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895914 prefixEnd_3895914 := by exact prefixLift 3895914
  have htrace : WordTrace (prefixWord ++ tailWord_3895914) baseStart_3895914 baseEnd_3895914 := by
    simpa [prefixWord, tailWord_3895914, baseEnd_3895914] using wordTrace_append hprefix tailTrace_3895914
  have hstable : (prefixWord ++ tailWord_3895914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895914).length < 2 ^ (prefixWord ++ tailWord_3895914).sum := by decide
  have hdescent : baseEnd_3895914 < baseStart_3895914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895946 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 6]
def baseStart_3895946 : Nat := 118140960795 + 3895946 * 2 ^ 59
def prefixEnd_3895946 : Nat := 4983230072969 + 3 ^ 40 * 3895946 * 2
def baseEnd_3895946 : Nat := 444553978213670961568417

theorem tailTrace_3895946 : CollatzResearch.WordTrace tailWord_3895946 prefixEnd_3895946 444553978213670961568417 := by
  unfold tailWord_3895946
  simp only [CollatzResearch.WordTrace]
  refine ⟨35524206085915122862182923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94731216229106994299154461 35524206085915122862182923)
  ·
    refine ⟨53286309128872684293274385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35524206085915122862182923 53286309128872684293274385)
    ·
      refine ⟨39964731846654513219955789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53286309128872684293274385 39964731846654513219955789)
      ·
        refine ⟨14986774442495442457483421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39964731846654513219955789 14986774442495442457483421)
        ·
          refine ⟨5620040415935790921556283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14986774442495442457483421 5620040415935790921556283)
          ·
            refine ⟨8430060623903686382334425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5620040415935790921556283 8430060623903686382334425)
            ·
              refine ⟨6322545467927764786750819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8430060623903686382334425 6322545467927764786750819)
              ·
                refine ⟨9483818201891647180126229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6322545467927764786750819 9483818201891647180126229)
                ·
                  refine ⟨444553978213670961568417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9483818201891647180126229 444553978213670961568417)
                  ·
                    rfl

theorem cell22_3895946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_3895946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895946 prefixEnd_3895946 := by exact prefixLift 3895946
  have htrace : WordTrace (prefixWord ++ tailWord_3895946) baseStart_3895946 baseEnd_3895946 := by
    simpa [prefixWord, tailWord_3895946, baseEnd_3895946] using wordTrace_append hprefix tailTrace_3895946
  have hstable : (prefixWord ++ tailWord_3895946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895946).length < 2 ^ (prefixWord ++ tailWord_3895946).sum := by decide
  have hdescent : baseEnd_3895946 < baseStart_3895946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895991 : List Nat := [1, 1, 3, 1, 7, 1, 8]
def baseStart_3895991 : Nat := 118140960795 + 3895991 * 2 ^ 59
def prefixEnd_3895991 : Nat := 4983230072969 + 3 ^ 40 * 3895991 * 2
def baseEnd_3895991 : Nat := 49395457002246213604819

theorem tailTrace_3895991 : CollatzResearch.WordTrace tailWord_3895991 prefixEnd_3895991 49395457002246213604819 := by
  unfold tailWord_3895991
  simp only [CollatzResearch.WordTrace]
  refine ⟨142098465628497464134119827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94732310418998309422746551 142098465628497464134119827)
  ·
    refine ⟨213147698442746196201179741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142098465628497464134119827 213147698442746196201179741)
    ·
      refine ⟨79930386916029823575442403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213147698442746196201179741 79930386916029823575442403)
      ·
        refine ⟨119895580374044735363163605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79930386916029823575442403 119895580374044735363163605)
        ·
          refine ⟨2810052665016673485074147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 119895580374044735363163605 2810052665016673485074147)
          ·
            refine ⟨4215078997525010227611221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810052665016673485074147 4215078997525010227611221)
            ·
              refine ⟨49395457002246213604819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4215078997525010227611221 49395457002246213604819)
              ·
                rfl

theorem cell22_3895991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 8].length) (baseStart_3895991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895991 prefixEnd_3895991 := by exact prefixLift 3895991
  have htrace : WordTrace (prefixWord ++ tailWord_3895991) baseStart_3895991 baseEnd_3895991 := by
    simpa [prefixWord, tailWord_3895991, baseEnd_3895991] using wordTrace_append hprefix tailTrace_3895991
  have hstable : (prefixWord ++ tailWord_3895991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895991).length < 2 ^ (prefixWord ++ tailWord_3895991).sum := by decide
  have hdescent : baseEnd_3895991 < baseStart_3895991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896096 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 1, 5]
def baseStart_3896096 : Nat := 118140960795 + 3896096 * 2 ^ 59
def prefixEnd_3896096 : Nat := 4983230072969 + 3 ^ 40 * 3896096 * 2
def baseEnd_3896096 : Nat := 1333713282706462493454791

theorem tailTrace_3896096 : CollatzResearch.WordTrace tailWord_3896096 prefixEnd_3896096 1333713282706462493454791 := by
  unfold tailWord_3896096
  simp only [CollatzResearch.WordTrace]
  refine ⟨71051147646558533533346071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94734863528744711377794761 71051147646558533533346071)
  ·
    refine ⟨106576721469837800300019107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71051147646558533533346071 106576721469837800300019107)
    ·
      refine ⟨159865082204756700450028661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106576721469837800300019107 159865082204756700450028661)
      ·
        refine ⟨14987351456695940667190187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159865082204756700450028661 14987351456695940667190187)
        ·
          refine ⟨22481027185043911000785281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14987351456695940667190187 22481027185043911000785281)
          ·
            refine ⟨16860770388782933250588961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22481027185043911000785281 16860770388782933250588961)
            ·
              refine ⟨12645577791587199937941721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16860770388782933250588961 12645577791587199937941721)
              ·
                refine ⟨9484183343690399953456291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12645577791587199937941721 9484183343690399953456291)
                ·
                  refine ⟨14226275015535599930184437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9484183343690399953456291 14226275015535599930184437)
                  ·
                    refine ⟨1333713282706462493454791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14226275015535599930184437 1333713282706462493454791)
                    ·
                      rfl

theorem cell22_3896096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_3896096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896096 prefixEnd_3896096 := by exact prefixLift 3896096
  have htrace : WordTrace (prefixWord ++ tailWord_3896096) baseStart_3896096 baseEnd_3896096 := by
    simpa [prefixWord, tailWord_3896096, baseEnd_3896096] using wordTrace_append hprefix tailTrace_3896096
  have hstable : (prefixWord ++ tailWord_3896096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896096).length < 2 ^ (prefixWord ++ tailWord_3896096).sum := by decide
  have hdescent : baseEnd_3896096 < baseStart_3896096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896098 : List Nat := [3, 3, 1, 1, 2, 2, 1, 5, 4]
def baseStart_3896098 : Nat := 118140960795 + 3896098 * 2 ^ 59
def prefixEnd_3896098 : Nat := 4983230072969 + 3 ^ 40 * 3896098 * 2
def baseEnd_3896098 : Nat := 444571322449111718301595

theorem tailTrace_3896098 : CollatzResearch.WordTrace tailWord_3896098 prefixEnd_3896098 444571322449111718301595 := by
  unfold tailWord_3896098
  simp only [CollatzResearch.WordTrace]
  refine ⟨35525592059777455352066237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94734912159406547605509965 35525592059777455352066237)
  ·
    refine ⟨13322097022416545757024839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35525592059777455352066237 13322097022416545757024839)
    ·
      refine ⟨19983145533624818635537259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13322097022416545757024839 19983145533624818635537259)
      ·
        refine ⟨29974718300437227953305889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19983145533624818635537259 29974718300437227953305889)
        ·
          refine ⟨22481038725327920964979417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29974718300437227953305889 22481038725327920964979417)
          ·
            refine ⟨16860779043995940723734563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22481038725327920964979417 16860779043995940723734563)
            ·
              refine ⟨25291168565993911085601845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16860779043995940723734563 25291168565993911085601845)
              ·
                refine ⟨2371047053061929164275173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25291168565993911085601845 2371047053061929164275173)
                ·
                  refine ⟨444571322449111718301595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371047053061929164275173 444571322449111718301595)
                  ·
                    rfl

theorem cell22_3896098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_3896098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896098 prefixEnd_3896098 := by exact prefixLift 3896098
  have htrace : WordTrace (prefixWord ++ tailWord_3896098) baseStart_3896098 baseEnd_3896098 := by
    simpa [prefixWord, tailWord_3896098, baseEnd_3896098] using wordTrace_append hprefix tailTrace_3896098
  have hstable : (prefixWord ++ tailWord_3896098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896098).length < 2 ^ (prefixWord ++ tailWord_3896098).sum := by decide
  have hdescent : baseEnd_3896098 < baseStart_3896098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896233 : List Nat := [1, 2, 1, 1, 1, 1, 7, 4, 4]
def baseStart_3896233 : Nat := 118140960795 + 3896233 * 2 ^ 59
def prefixEnd_3896233 : Nat := 4983230072969 + 3 ^ 40 * 3896233 * 2
def baseEnd_3896233 : Nat := 444586726868746600926457

theorem tailTrace_3896233 : CollatzResearch.WordTrace tailWord_3896233 prefixEnd_3896233 444586726868746600926457 := by
  unfold tailWord_3896233
  simp only [CollatzResearch.WordTrace]
  refine ⟨142107292093620739464429353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94738194729080492976286235 142107292093620739464429353)
  ·
    refine ⟨106580469070215554598322015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142107292093620739464429353 106580469070215554598322015)
    ·
      refine ⟨159870703605323331897483023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106580469070215554598322015 159870703605323331897483023)
      ·
        refine ⟨239806055407984997846224535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159870703605323331897483023 239806055407984997846224535)
        ·
          refine ⟨359709083111977496769336803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239806055407984997846224535 359709083111977496769336803)
          ·
            refine ⟨539563624667966245154005205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359709083111977496769336803 539563624667966245154005205)
            ·
              refine ⟨12646022453155458870796997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 539563624667966245154005205 12646022453155458870796997)
              ·
                refine ⟨2371129209966648538274437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12646022453155458870796997 2371129209966648538274437)
                ·
                  refine ⟨444586726868746600926457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371129209966648538274437 444586726868746600926457)
                  ·
                    rfl

theorem cell22_3896233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 4].length) (baseStart_3896233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896233 prefixEnd_3896233 := by exact prefixLift 3896233
  have htrace : WordTrace (prefixWord ++ tailWord_3896233) baseStart_3896233 baseEnd_3896233 := by
    simpa [prefixWord, tailWord_3896233, baseEnd_3896233] using wordTrace_append hprefix tailTrace_3896233
  have hstable : (prefixWord ++ tailWord_3896233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896233).length < 2 ^ (prefixWord ++ tailWord_3896233).sum := by decide
  have hdescent : baseEnd_3896233 < baseStart_3896233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896248 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 1, 5]
def baseStart_3896248 : Nat := 118140960795 + 3896248 * 2 ^ 59
def prefixEnd_3896248 : Nat := 4983230072969 + 3 ^ 40 * 3896248 * 2
def baseEnd_3896248 : Nat := 1333765315412784763654325

theorem tailTrace_3896248 : CollatzResearch.WordTrace tailWord_3896248 prefixEnd_3896248 1333765315412784763654325 := by
  unfold tailWord_3896248
  simp only [CollatzResearch.WordTrace]
  refine ⟨71053919594283198513112699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94738559459044264684150265 71053919594283198513112699)
  ·
    refine ⟨106580879391424797769669049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71053919594283198513112699 106580879391424797769669049)
    ·
      refine ⟨79935659543568598327251787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106580879391424797769669049 79935659543568598327251787)
      ·
        refine ⟨119903489315352897490877681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79935659543568598327251787 119903489315352897490877681)
        ·
          refine ⟨89927616986514673118158261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119903489315352897490877681 89927616986514673118158261)
          ·
            refine ⟨8430714092485750604827337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89927616986514673118158261 8430714092485750604827337)
            ·
              refine ⟨6323035569364312953620503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8430714092485750604827337 6323035569364312953620503)
              ·
                refine ⟨9484553354046469430430755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6323035569364312953620503 9484553354046469430430755)
                ·
                  refine ⟨14226830031069704145646133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9484553354046469430430755 14226830031069704145646133)
                  ·
                    refine ⟨1333765315412784763654325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14226830031069704145646133 1333765315412784763654325)
                    ·
                      rfl

theorem cell22_3896248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_3896248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896248 prefixEnd_3896248 := by exact prefixLift 3896248
  have htrace : WordTrace (prefixWord ++ tailWord_3896248) baseStart_3896248 baseEnd_3896248 := by
    simpa [prefixWord, tailWord_3896248, baseEnd_3896248] using wordTrace_append hprefix tailTrace_3896248
  have hstable : (prefixWord ++ tailWord_3896248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896248).length < 2 ^ (prefixWord ++ tailWord_3896248).sum := by decide
  have hdescent : baseEnd_3896248 < baseStart_3896248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896263 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 2, 4]
def baseStart_3896263 : Nat := 118140960795 + 3896263 * 2 ^ 59
def prefixEnd_3896263 : Nat := 4983230072969 + 3 ^ 40 * 3896263 * 2
def baseEnd_3896263 : Nat := 1333770450219329724529279

theorem tailTrace_3896263 : CollatzResearch.WordTrace tailWord_3896263 prefixEnd_3896263 1333770450219329724529279 := by
  unfold tailWord_3896263
  simp only [CollatzResearch.WordTrace]
  refine ⟨142108386283512054588021443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94738924189008036392014295 142108386283512054588021443)
  ·
    refine ⟨213162579425268081882032165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142108386283512054588021443 213162579425268081882032165)
    ·
      refine ⟨39967983642237765352881031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213162579425268081882032165 39967983642237765352881031)
      ·
        refine ⟨59951975463356648029321547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39967983642237765352881031 59951975463356648029321547)
        ·
          refine ⟨89927963195034972043982321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59951975463356648029321547 89927963195034972043982321)
          ·
            refine ⟨67445972396276229032986741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89927963195034972043982321 67445972396276229032986741)
            ·
              refine ⟨6323059912150896471842507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67445972396276229032986741 6323059912150896471842507)
              ·
                refine ⟨9484589868226344707763761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6323059912150896471842507 9484589868226344707763761)
                ·
                  refine ⟨7113442401169758530822821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9484589868226344707763761 7113442401169758530822821)
                  ·
                    refine ⟨1333770450219329724529279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7113442401169758530822821 1333770450219329724529279)
                    ·
                      rfl

theorem cell22_3896263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_3896263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896263 prefixEnd_3896263 := by exact prefixLift 3896263
  have htrace : WordTrace (prefixWord ++ tailWord_3896263) baseStart_3896263 baseEnd_3896263 := by
    simpa [prefixWord, tailWord_3896263, baseEnd_3896263] using wordTrace_append hprefix tailTrace_3896263
  have hstable : (prefixWord ++ tailWord_3896263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896263).length < 2 ^ (prefixWord ++ tailWord_3896263).sum := by decide
  have hdescent : baseEnd_3896263 < baseStart_3896263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896282 : List Nat := [3, 1, 1, 2, 4, 3, 1, 2, 2, 3]
def baseStart_3896282 : Nat := 118140960795 + 3896282 * 2 ^ 59
def prefixEnd_3896282 : Nat := 4983230072969 + 3 ^ 40 * 3896282 * 2
def baseEnd_3896282 : Nat := 1333776954307620008304221

theorem tailTrace_3896282 : CollatzResearch.WordTrace tailWord_3896282 prefixEnd_3896282 1333776954307620008304221 := by
  unfold tailWord_3896282
  simp only [CollatzResearch.WordTrace]
  refine ⟨35527269817610805208240775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94739386180295480555308733 35527269817610805208240775)
  ·
    refine ⟨53290904726416207812361163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35527269817610805208240775 53290904726416207812361163)
    ·
      refine ⟨79936357089624311718541745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53290904726416207812361163 79936357089624311718541745)
      ·
        refine ⟨59952267817218233788906309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79936357089624311718541745 59952267817218233788906309)
        ·
          refine ⟨11241050215728418835419933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59952267817218233788906309 11241050215728418835419933)
          ·
            refine ⟨4215393830898157063282475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11241050215728418835419933 4215393830898157063282475)
            ·
              refine ⟨6323090746347235594923713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4215393830898157063282475 6323090746347235594923713)
              ·
                refine ⟨4742318059760426696192785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6323090746347235594923713 4742318059760426696192785)
                ·
                  refine ⟨3556738544820320022144589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4742318059760426696192785 3556738544820320022144589)
                  ·
                    refine ⟨1333776954307620008304221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3556738544820320022144589 1333776954307620008304221)
                    ·
                      rfl

theorem cell22_3896282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_3896282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896282 prefixEnd_3896282 := by exact prefixLift 3896282
  have htrace : WordTrace (prefixWord ++ tailWord_3896282) baseStart_3896282 baseEnd_3896282 := by
    simpa [prefixWord, tailWord_3896282, baseEnd_3896282] using wordTrace_append hprefix tailTrace_3896282
  have hstable : (prefixWord ++ tailWord_3896282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896282).length < 2 ^ (prefixWord ++ tailWord_3896282).sum := by decide
  have hdescent : baseEnd_3896282 < baseStart_3896282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896344 : List Nat := [2, 1, 2, 3, 2, 3, 3, 2, 1, 3]
def baseStart_3896344 : Nat := 118140960795 + 3896344 * 2 ^ 59
def prefixEnd_3896344 : Nat := 4983230072969 + 3 ^ 40 * 3896344 * 2
def baseEnd_3896344 : Nat := 1333798178174672513254031

theorem tailTrace_3896344 : CollatzResearch.WordTrace tailWord_3896344 prefixEnd_3896344 1333798178174672513254031 := by
  unfold tailWord_3896344
  simp only [CollatzResearch.WordTrace]
  refine ⟨71055670298109302710860043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94740893730812403614480057 71055670298109302710860043)
  ·
    refine ⟨106583505447163954066290065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71055670298109302710860043 106583505447163954066290065)
    ·
      refine ⟨79937629085372965549717549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106583505447163954066290065 79937629085372965549717549)
      ·
        refine ⟨29976610907014862081144081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79937629085372965549717549 29976610907014862081144081)
        ·
          refine ⟨22482458180261146560858061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29976610907014862081144081 22482458180261146560858061)
          ·
            refine ⟨8430921817597929960321773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22482458180261146560858061 8430921817597929960321773)
            ·
              refine ⟨3161595681599223735120665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8430921817597929960321773 3161595681599223735120665)
              ·
                refine ⟨2371196761199417801340499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161595681599223735120665 2371196761199417801340499)
                ·
                  refine ⟨3556795141799126702010749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371196761199417801340499 3556795141799126702010749)
                  ·
                    refine ⟨1333798178174672513254031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3556795141799126702010749 1333798178174672513254031)
                    ·
                      rfl

theorem cell22_3896344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_3896344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896344 prefixEnd_3896344 := by exact prefixLift 3896344
  have htrace : WordTrace (prefixWord ++ tailWord_3896344) baseStart_3896344 baseEnd_3896344 := by
    simpa [prefixWord, tailWord_3896344, baseEnd_3896344] using wordTrace_append hprefix tailTrace_3896344
  have hstable : (prefixWord ++ tailWord_3896344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896344).length < 2 ^ (prefixWord ++ tailWord_3896344).sum := by decide
  have hdescent : baseEnd_3896344 < baseStart_3896344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896402 : List Nat := [3, 2, 2, 1, 3, 2, 1, 4, 4]
def baseStart_3896402 : Nat := 118140960795 + 3896402 * 2 ^ 59
def prefixEnd_3896402 : Nat := 4983230072969 + 3 ^ 40 * 3896402 * 2
def baseEnd_3896402 : Nat := 444606010919993231767951

theorem tailTrace_3896402 : CollatzResearch.WordTrace tailWord_3896402 prefixEnd_3896402 444606010919993231767951 := by
  unfold tailWord_3896402
  simp only [CollatzResearch.WordTrace]
  refine ⟨35528364007502120331832865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94742304020005654218220973 35528364007502120331832865)
  ·
    refine ⟨26646273005626590248874649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35528364007502120331832865 26646273005626590248874649)
    ·
      refine ⟨19984704754219942686655987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26646273005626590248874649 19984704754219942686655987)
      ·
        refine ⟨29977057131329914029983981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19984704754219942686655987 29977057131329914029983981)
        ·
          refine ⟨11241396424248717761243993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29977057131329914029983981 11241396424248717761243993)
          ·
            refine ⟨8431047318186538320932995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11241396424248717761243993 8431047318186538320932995)
            ·
              refine ⟨12646570977279807481399493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8431047318186538320932995 12646570977279807481399493)
              ·
                refine ⟨2371232058239963902762405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12646570977279807481399493 2371232058239963902762405)
                ·
                  refine ⟨444606010919993231767951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371232058239963902762405 444606010919993231767951)
                  ·
                    rfl

theorem cell22_3896402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_3896402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896402 prefixEnd_3896402 := by exact prefixLift 3896402
  have htrace : WordTrace (prefixWord ++ tailWord_3896402) baseStart_3896402 baseEnd_3896402 := by
    simpa [prefixWord, tailWord_3896402, baseEnd_3896402] using wordTrace_append hprefix tailTrace_3896402
  have hstable : (prefixWord ++ tailWord_3896402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896402).length < 2 ^ (prefixWord ++ tailWord_3896402).sum := by decide
  have hdescent : baseEnd_3896402 < baseStart_3896402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896445 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_3896445 : Nat := 118140960795 + 3896445 * 2 ^ 59
def prefixEnd_3896445 : Nat := 4983230072969 + 3 ^ 40 * 3896445 * 2
def baseEnd_3896445 : Nat := 1333832752538741916478721

theorem tailTrace_3896445 : CollatzResearch.WordTrace tailWord_3896445 prefixEnd_3896445 1333832752538741916478721 := by
  unfold tailWord_3896445
  simp only [CollatzResearch.WordTrace]
  refine ⟨142115024368852699671146789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94743349579235133114097859 142115024368852699671146789)
  ·
    refine ⟨26646567069159881188340023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142115024368852699671146789 26646567069159881188340023)
    ·
      refine ⟨39969850603739821782510035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26646567069159881188340023 39969850603739821782510035)
      ·
        refine ⟨59954775905609732673765053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39969850603739821782510035 59954775905609732673765053)
        ·
          refine ⟨22483040964603649752661895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59954775905609732673765053 22483040964603649752661895)
          ·
            refine ⟨33724561446905474628992843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22483040964603649752661895 33724561446905474628992843)
            ·
              refine ⟨50586842170358211943489265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33724561446905474628992843 50586842170358211943489265)
              ·
                refine ⟨37940131627768658957616949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50586842170358211943489265 37940131627768658957616949)
                ·
                  refine ⟨3556887340103311777276589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37940131627768658957616949 3556887340103311777276589)
                  ·
                    refine ⟨1333832752538741916478721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3556887340103311777276589 1333832752538741916478721)
                    ·
                      rfl

theorem cell22_3896445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_3896445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896445 prefixEnd_3896445 := by exact prefixLift 3896445
  have htrace : WordTrace (prefixWord ++ tailWord_3896445) baseStart_3896445 baseEnd_3896445 := by
    simpa [prefixWord, tailWord_3896445, baseEnd_3896445] using wordTrace_append hprefix tailTrace_3896445
  have hstable : (prefixWord ++ tailWord_3896445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896445).length < 2 ^ (prefixWord ++ tailWord_3896445).sum := by decide
  have hdescent : baseEnd_3896445 < baseStart_3896445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896462 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_3896462 : Nat := 118140960795 + 3896462 * 2 ^ 59
def prefixEnd_3896462 : Nat := 4983230072969 + 3 ^ 40 * 3896462 * 2
def baseEnd_3896462 : Nat := 1333838571986159538803669

theorem tailTrace_3896462 : CollatzResearch.WordTrace tailWord_3896462 prefixEnd_3896462 1333838571986159538803669 := by
  unfold tailWord_3896462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17764455551223888946814455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94743762939860741049677093 17764455551223888946814455)
  ·
    refine ⟨26646683326835833420221683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17764455551223888946814455 26646683326835833420221683)
    ·
      refine ⟨39970024990253750130332525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26646683326835833420221683 39970024990253750130332525)
      ·
        refine ⟨14988759371345156298874697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39970024990253750130332525 14988759371345156298874697)
        ·
          refine ⟨11241569528508867224156023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14988759371345156298874697 11241569528508867224156023)
          ·
            refine ⟨16862354292763300836234035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11241569528508867224156023 16862354292763300836234035)
            ·
              refine ⟨25293531439144951254351053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16862354292763300836234035 25293531439144951254351053)
              ·
                refine ⟨9485074289679356720381645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25293531439144951254351053 9485074289679356720381645)
                ·
                  refine ⟨3556902858629758770143117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9485074289679356720381645 3556902858629758770143117)
                  ·
                    refine ⟨1333838571986159538803669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3556902858629758770143117 1333838571986159538803669)
                    ·
                      rfl

theorem cell22_3896462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_3896462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896462 prefixEnd_3896462 := by exact prefixLift 3896462
  have htrace : WordTrace (prefixWord ++ tailWord_3896462) baseStart_3896462 baseEnd_3896462 := by
    simpa [prefixWord, tailWord_3896462, baseEnd_3896462] using wordTrace_append hprefix tailTrace_3896462
  have hstable : (prefixWord ++ tailWord_3896462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896462).length < 2 ^ (prefixWord ++ tailWord_3896462).sum := by decide
  have hdescent : baseEnd_3896462 < baseStart_3896462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896513 : List Nat := [1, 2, 6, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3896513 : Nat := 118140960795 + 3896513 * 2 ^ 59
def prefixEnd_3896513 : Nat := 4983230072969 + 3 ^ 40 * 3896513 * 2
def baseEnd_3896513 : Nat := 1333856030328412405778513

theorem tailTrace_3896513 : CollatzResearch.WordTrace tailWord_3896513 prefixEnd_3896513 1333856030328412405778513 := by
  unfold tailWord_3896513
  simp only [CollatzResearch.WordTrace]
  refine ⟨142117504532606347284622193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94745003021737564856414795 142117504532606347284622193)
  ·
    refine ⟨106588128399454760463466645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142117504532606347284622193 106588128399454760463466645)
    ·
      refine ⟨4996318518724441896724999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106588128399454760463466645 4996318518724441896724999)
      ·
        refine ⟨7494477778086662845087499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4996318518724441896724999 7494477778086662845087499)
        ·
          refine ⟨11241716667129994267631249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7494477778086662845087499 11241716667129994267631249)
          ·
            refine ⟨8431287500347495700723437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11241716667129994267631249 8431287500347495700723437)
            ·
              refine ⟨3161732812630310887771289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8431287500347495700723437 3161732812630310887771289)
              ·
                refine ⟨2371299609472733165828467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161732812630310887771289 2371299609472733165828467)
                ·
                  refine ⟨3556949414209099748742701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371299609472733165828467 3556949414209099748742701)
                  ·
                    refine ⟨1333856030328412405778513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3556949414209099748742701 1333856030328412405778513)
                    ·
                      rfl

theorem cell22_3896513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3896513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896513 prefixEnd_3896513 := by exact prefixLift 3896513
  have htrace : WordTrace (prefixWord ++ tailWord_3896513) baseStart_3896513 baseEnd_3896513 := by
    simpa [prefixWord, tailWord_3896513, baseEnd_3896513] using wordTrace_append hprefix tailTrace_3896513
  have hstable : (prefixWord ++ tailWord_3896513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896513).length < 2 ^ (prefixWord ++ tailWord_3896513).sum := by decide
  have hdescent : baseEnd_3896513 < baseStart_3896513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896520 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 6]
def baseStart_3896520 : Nat := 118140960795 + 3896520 * 2 ^ 59
def prefixEnd_3896520 : Nat := 4983230072969 + 3 ^ 40 * 3896520 * 2
def baseEnd_3896520 : Nat := 444619475523822240284497

theorem tailTrace_3896520 : CollatzResearch.WordTrace tailWord_3896520 prefixEnd_3896520 444619475523822240284497 := by
  unfold tailWord_3896520
  simp only [CollatzResearch.WordTrace]
  refine ⟨71058879921790493740063507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94745173229053991653418009 71058879921790493740063507)
  ·
    refine ⟨106588319882685740610095261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71058879921790493740063507 106588319882685740610095261)
    ·
      refine ⟨39970619956007152728785723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106588319882685740610095261 39970619956007152728785723)
      ·
        refine ⟨59955929934010729093178585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39970619956007152728785723 59955929934010729093178585)
        ·
          refine ⟨44966947450508046819883939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59955929934010729093178585 44966947450508046819883939)
          ·
            refine ⟨67450421175762070229825909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44966947450508046819883939 67450421175762070229825909)
            ·
              refine ⟨6323476985227694084046179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67450421175762070229825909 6323476985227694084046179)
              ·
                refine ⟨9485215477841541126069269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6323476985227694084046179 9485215477841541126069269)
                ·
                  refine ⟨444619475523822240284497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9485215477841541126069269 444619475523822240284497)
                  ·
                    rfl

theorem cell22_3896520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_3896520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896520 prefixEnd_3896520 := by exact prefixLift 3896520
  have htrace : WordTrace (prefixWord ++ tailWord_3896520) baseStart_3896520 baseEnd_3896520 := by
    simpa [prefixWord, tailWord_3896520, baseEnd_3896520] using wordTrace_append hprefix tailTrace_3896520
  have hstable : (prefixWord ++ tailWord_3896520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896520).length < 2 ^ (prefixWord ++ tailWord_3896520).sum := by decide
  have hdescent : baseEnd_3896520 < baseStart_3896520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896526 : List Nat := [4, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_3896526 : Nat := 118140960795 + 3896526 * 2 ^ 59
def prefixEnd_3896526 : Nat := 4983230072969 + 3 ^ 40 * 3896526 * 2
def baseEnd_3896526 : Nat := 444620160164694901734491

theorem tailTrace_3896526 : CollatzResearch.WordTrace tailWord_3896526 prefixEnd_3896526 444620160164694901734491 := by
  unfold tailWord_3896526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17764747335194906313105679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94745319121039500336563621 17764747335194906313105679)
  ·
    refine ⟨26647121002792359469658519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17764747335194906313105679 26647121002792359469658519)
    ·
      refine ⟨39970681504188539204487779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26647121002792359469658519 39970681504188539204487779)
      ·
        refine ⟨59956022256282808806731669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39970681504188539204487779 59956022256282808806731669)
        ·
          refine ⟨2810438543263256662815547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59956022256282808806731669 2810438543263256662815547)
          ·
            refine ⟨4215657814894884994223321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810438543263256662815547 4215657814894884994223321)
            ·
              refine ⟨3161743361171163745667491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4215657814894884994223321 3161743361171163745667491)
              ·
                refine ⟨4742615041756745618501237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161743361171163745667491 4742615041756745618501237)
                ·
                  refine ⟨444620160164694901734491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4742615041756745618501237 444620160164694901734491)
                  ·
                    rfl

theorem cell22_3896526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_3896526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896526 prefixEnd_3896526 := by exact prefixLift 3896526
  have htrace : WordTrace (prefixWord ++ tailWord_3896526) baseStart_3896526 baseEnd_3896526 := by
    simpa [prefixWord, tailWord_3896526, baseEnd_3896526] using wordTrace_append hprefix tailTrace_3896526
  have hstable : (prefixWord ++ tailWord_3896526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896526).length < 2 ^ (prefixWord ++ tailWord_3896526).sum := by decide
  have hdescent : baseEnd_3896526 < baseStart_3896526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896564 : List Nat := [2, 6, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3896564 : Nat := 118140960795 + 3896564 * 2 ^ 59
def prefixEnd_3896564 : Nat := 4983230072969 + 3 ^ 40 * 3896564 * 2
def baseEnd_3896564 : Nat := 1333873488670665272753357

theorem tailTrace_3896564 : CollatzResearch.WordTrace tailWord_3896564 prefixEnd_3896564 1333873488670665272753357 := by
  unfold tailWord_3896564
  simp only [CollatzResearch.WordTrace]
  refine ⟨71059682327710791497364373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94746243103614388663152497 71059682327710791497364373)
  ·
    refine ⟨3330922609111443351438955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71059682327710791497364373 3330922609111443351438955)
    ·
      refine ⟨4996383913667165027158433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3330922609111443351438955 4996383913667165027158433)
      ·
        refine ⟨3747287935250373770368825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4996383913667165027158433 3747287935250373770368825)
        ·
          refine ⟨2810465951437780327776619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3747287935250373770368825 2810465951437780327776619)
          ·
            refine ⟨4215698927156670491664929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810465951437780327776619 4215698927156670491664929)
            ·
              refine ⟨3161774195367502868748697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4215698927156670491664929 3161774195367502868748697)
              ·
                refine ⟨2371330646525627151561523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161774195367502868748697 2371330646525627151561523)
                ·
                  refine ⟨3556995969788440727342285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371330646525627151561523 3556995969788440727342285)
                  ·
                    refine ⟨1333873488670665272753357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3556995969788440727342285 1333873488670665272753357)
                    ·
                      rfl

theorem cell22_3896564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3896564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896564 prefixEnd_3896564 := by exact prefixLift 3896564
  have htrace : WordTrace (prefixWord ++ tailWord_3896564) baseStart_3896564 baseEnd_3896564 := by
    simpa [prefixWord, tailWord_3896564, baseEnd_3896564] using wordTrace_append hprefix tailTrace_3896564
  have hstable : (prefixWord ++ tailWord_3896564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896564).length < 2 ^ (prefixWord ++ tailWord_3896564).sum := by decide
  have hdescent : baseEnd_3896564 < baseStart_3896564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896627 : List Nat := [1, 1, 1, 2, 5, 2, 3, 2, 5]
def baseStart_3896627 : Nat := 118140960795 + 3896627 * 2 ^ 59
def prefixEnd_3896627 : Nat := 4983230072969 + 3 ^ 40 * 3896627 * 2
def baseEnd_3896627 : Nat := 444631684952718036142721

theorem tailTrace_3896627 : CollatzResearch.WordTrace tailWord_3896627 prefixEnd_3896627 444631684952718036142721 := by
  unfold tailWord_3896627
  simp only [CollatzResearch.WordTrace]
  refine ⟨142121662454193344754272135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94747774969462229836181423 142121662454193344754272135)
  ·
    refine ⟨213182493681290017131408203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142121662454193344754272135 213182493681290017131408203)
    ·
      refine ⟨319773740521935025697112305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213182493681290017131408203 319773740521935025697112305)
      ·
        refine ⟨239830305391451269272834229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319773740521935025697112305 239830305391451269272834229)
        ·
          refine ⟨22484091130448556494328209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239830305391451269272834229 22484091130448556494328209)
          ·
            refine ⟨16863068347836417370746157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22484091130448556494328209 16863068347836417370746157)
            ·
              refine ⟨6323650630438656514029809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16863068347836417370746157 6323650630438656514029809)
              ·
                refine ⟨4742737972828992385522357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6323650630438656514029809 4742737972828992385522357)
                ·
                  refine ⟨444631684952718036142721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4742737972828992385522357 444631684952718036142721)
                  ·
                    rfl

theorem cell22_3896627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 5].length) (baseStart_3896627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896627 prefixEnd_3896627 := by exact prefixLift 3896627
  have htrace : WordTrace (prefixWord ++ tailWord_3896627) baseStart_3896627 baseEnd_3896627 := by
    simpa [prefixWord, tailWord_3896627, baseEnd_3896627] using wordTrace_append hprefix tailTrace_3896627
  have hstable : (prefixWord ++ tailWord_3896627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896627).length < 2 ^ (prefixWord ++ tailWord_3896627).sum := by decide
  have hdescent : baseEnd_3896627 < baseStart_3896627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896674 : List Nat := [3, 3, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3896674 : Nat := 118140960795 + 3896674 * 2 ^ 59
def prefixEnd_3896674 : Nat := 4983230072969 + 3 ^ 40 * 3896674 * 2
def baseEnd_3896674 : Nat := 1333911143918661652503019

theorem tailTrace_3896674 : CollatzResearch.WordTrace tailWord_3896674 prefixEnd_3896674 1333911143918661652503019 := by
  unfold tailWord_3896674
  simp only [CollatzResearch.WordTrace]
  refine ⟨35530844171255767945308269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94748917790015381187488717 35530844171255767945308269)
  ·
    refine ⟨13324066564220912979490601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35530844171255767945308269 13324066564220912979490601)
    ·
      refine ⟨9993049923165684734617951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13324066564220912979490601 9993049923165684734617951)
      ·
        refine ⟨14989574884748527101926927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9993049923165684734617951 14989574884748527101926927)
        ·
          refine ⟨22484362327122790652890391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14989574884748527101926927 22484362327122790652890391)
          ·
            refine ⟨33726543490684185979335587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22484362327122790652890391 33726543490684185979335587)
            ·
              refine ⟨50589815236026278969003381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33726543490684185979335587 50589815236026278969003381)
              ·
                refine ⟨4742795178377463653344067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50589815236026278969003381 4742795178377463653344067)
                ·
                  refine ⟨7114192767566195480016101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4742795178377463653344067 7114192767566195480016101)
                  ·
                    refine ⟨1333911143918661652503019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7114192767566195480016101 1333911143918661652503019)
                    ·
                      rfl

theorem cell22_3896674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3896674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896674 prefixEnd_3896674 := by exact prefixLift 3896674
  have htrace : WordTrace (prefixWord ++ tailWord_3896674) baseStart_3896674 baseEnd_3896674 := by
    simpa [prefixWord, tailWord_3896674, baseEnd_3896674] using wordTrace_append hprefix tailTrace_3896674
  have hstable : (prefixWord ++ tailWord_3896674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896674).length < 2 ^ (prefixWord ++ tailWord_3896674).sum := by decide
  have hdescent : baseEnd_3896674 < baseStart_3896674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896687 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 4, 3]
def baseStart_3896687 : Nat := 118140960795 + 3896687 * 2 ^ 59
def prefixEnd_3896687 : Nat := 4983230072969 + 3 ^ 40 * 3896687 * 2
def baseEnd_3896687 : Nat := 1333915594084333951927979

theorem tailTrace_3896687 : CollatzResearch.WordTrace tailWord_3896687 prefixEnd_3896687 1333915594084333951927979 := by
  unfold tailWord_3896687
  simp only [CollatzResearch.WordTrace]
  refine ⟨142123850833975975001456315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94749233889317316667637543 142123850833975975001456315)
  ·
    refine ⟨213185776250963962502184473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142123850833975975001456315 213185776250963962502184473)
    ·
      refine ⟨159889332188222971876638355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213185776250963962502184473 159889332188222971876638355)
      ·
        refine ⟨239833998282334457814957533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159889332188222971876638355 239833998282334457814957533)
        ·
          refine ⟨89937749355875421680609075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239833998282334457814957533 89937749355875421680609075)
          ·
            refine ⟨134906624033813132520913613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89937749355875421680609075 134906624033813132520913613)
            ·
              refine ⟨50589984012679924695342605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134906624033813132520913613 50589984012679924695342605)
              ·
                refine ⟨18971244004754971760753477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50589984012679924695342605 18971244004754971760753477)
                ·
                  refine ⟨3557108250891557205141277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18971244004754971760753477 3557108250891557205141277)
                  ·
                    refine ⟨1333915594084333951927979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3557108250891557205141277 1333915594084333951927979)
                    ·
                      rfl

theorem cell22_3896687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 3].length) (baseStart_3896687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896687 prefixEnd_3896687 := by exact prefixLift 3896687
  have htrace : WordTrace (prefixWord ++ tailWord_3896687) baseStart_3896687 baseEnd_3896687 := by
    simpa [prefixWord, tailWord_3896687, baseEnd_3896687] using wordTrace_append hprefix tailTrace_3896687
  have hstable : (prefixWord ++ tailWord_3896687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896687).length < 2 ^ (prefixWord ++ tailWord_3896687).sum := by decide
  have hdescent : baseEnd_3896687 < baseStart_3896687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896734 : List Nat := [4, 3, 1, 2, 2, 10]
def baseStart_3896734 : Nat := 118140960795 + 3896734 * 2 ^ 59
def prefixEnd_3896734 : Nat := 4983230072969 + 3 ^ 40 * 3896734 * 2
def baseEnd_3896734 : Nat := 16468292384504216000035

theorem tailTrace_3896734 : CollatzResearch.WordTrace tailWord_3896734 prefixEnd_3896734 16468292384504216000035 := by
  unfold tailWord_3896734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17765695633100712753552157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94750376709870468018944837 17765695633100712753552157)
  ·
    refine ⟨6662135862412767282582059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17765695633100712753552157 6662135862412767282582059)
    ·
      refine ⟨9993203793619150923873089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6662135862412767282582059 9993203793619150923873089)
      ·
        refine ⟨7494902845214363192904817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9993203793619150923873089 7494902845214363192904817)
        ·
          refine ⟨5621177133910772394678613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7494902845214363192904817 5621177133910772394678613)
          ·
            refine ⟨16468292384504216000035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5621177133910772394678613 16468292384504216000035)
            ·
              rfl

theorem cell22_3896734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 10].length) (baseStart_3896734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896734 prefixEnd_3896734 := by exact prefixLift 3896734
  have htrace : WordTrace (prefixWord ++ tailWord_3896734) baseStart_3896734 baseEnd_3896734 := by
    simpa [prefixWord, tailWord_3896734, baseEnd_3896734] using wordTrace_append hprefix tailTrace_3896734
  have hstable : (prefixWord ++ tailWord_3896734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896734).length < 2 ^ (prefixWord ++ tailWord_3896734).sum := by decide
  have hdescent : baseEnd_3896734 < baseStart_3896734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896770 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3896770 : Nat := 118140960795 + 3896770 * 2 ^ 59
def prefixEnd_3896770 : Nat := 4983230072969 + 3 ^ 40 * 3896770 * 2
def baseEnd_3896770 : Nat := 1333944006680549402102725

theorem tailTrace_3896770 : CollatzResearch.WordTrace tailWord_3896770 prefixEnd_3896770 1333944006680549402102725 := by
  unfold tailWord_3896770
  simp only [CollatzResearch.WordTrace]
  refine ⟨35531719523168820044181941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94751252061783520117818509 35531719523168820044181941)
  ·
    refine ⟨3331098705297076879142057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35531719523168820044181941 3331098705297076879142057)
    ·
      refine ⟨2498324028972807659356543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3331098705297076879142057 2498324028972807659356543)
      ·
        refine ⟨3747486043459211489034815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2498324028972807659356543 3747486043459211489034815)
        ·
          refine ⟨5621229065188817233552223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747486043459211489034815 5621229065188817233552223)
          ·
            refine ⟨8431843597783225850328335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621229065188817233552223 8431843597783225850328335)
            ·
              refine ⟨12647765396674838775492503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8431843597783225850328335 12647765396674838775492503)
              ·
                refine ⟨18971648095012258163238755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12647765396674838775492503 18971648095012258163238755)
                ·
                  refine ⟨28457472142518387244858133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18971648095012258163238755 28457472142518387244858133)
                  ·
                    refine ⟨1333944006680549402102725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28457472142518387244858133 1333944006680549402102725)
                    ·
                      rfl

theorem cell22_3896770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3896770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896770 prefixEnd_3896770 := by exact prefixLift 3896770
  have htrace : WordTrace (prefixWord ++ tailWord_3896770) baseStart_3896770 baseEnd_3896770 := by
    simpa [prefixWord, tailWord_3896770, baseEnd_3896770] using wordTrace_append hprefix tailTrace_3896770
  have hstable : (prefixWord ++ tailWord_3896770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896770).length < 2 ^ (prefixWord ++ tailWord_3896770).sum := by decide
  have hdescent : baseEnd_3896770 < baseStart_3896770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896813 : List Nat := [1, 5, 1, 3, 2, 1, 3, 1, 5]
def baseStart_3896813 : Nat := 118140960795 + 3896813 * 2 ^ 59
def prefixEnd_3896813 : Nat := 4983230072969 + 3 ^ 40 * 3896813 * 2
def baseEnd_3896813 : Nat := 444652908819770541092531

theorem tailTrace_3896813 : CollatzResearch.WordTrace tailWord_3896813 prefixEnd_3896813 444652908819770541092531 := by
  unfold tailWord_3896813
  simp only [CollatzResearch.WordTrace]
  refine ⟨142128446431519498520543093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94752297621012999013695395 142128446431519498520543093)
  ·
    refine ⟨13324541852954952986300915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142128446431519498520543093 13324541852954952986300915)
    ·
      refine ⟨19986812779432429479451373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13324541852954952986300915 19986812779432429479451373)
      ·
        refine ⟨7495054792287161054794265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19986812779432429479451373 7495054792287161054794265)
        ·
          refine ⟨5621291094215370791095699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7495054792287161054794265 5621291094215370791095699)
          ·
            refine ⟨8431936641323056186643549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621291094215370791095699 8431936641323056186643549)
            ·
              refine ⟨3161976240496146069991331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8431936641323056186643549 3161976240496146069991331)
              ·
                refine ⟨4742964360744219104986997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161976240496146069991331 4742964360744219104986997)
                ·
                  refine ⟨444652908819770541092531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4742964360744219104986997 444652908819770541092531)
                  ·
                    rfl

theorem cell22_3896813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_3896813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896813 prefixEnd_3896813 := by exact prefixLift 3896813
  have htrace : WordTrace (prefixWord ++ tailWord_3896813) baseStart_3896813 baseEnd_3896813 := by
    simpa [prefixWord, tailWord_3896813, baseEnd_3896813] using wordTrace_append hprefix tailTrace_3896813
  have hstable : (prefixWord ++ tailWord_3896813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896813).length < 2 ^ (prefixWord ++ tailWord_3896813).sum := by decide
  have hdescent : baseEnd_3896813 < baseStart_3896813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896929 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 2, 5]
def baseStart_3896929 : Nat := 118140960795 + 3896929 * 2 ^ 59
def prefixEnd_3896929 : Nat := 4983230072969 + 3 ^ 40 * 3896929 * 2
def baseEnd_3896929 : Nat := 1333998435629925987377237

theorem tailTrace_3896929 : CollatzResearch.WordTrace tailWord_3896929 prefixEnd_3896929 1333998435629925987377237 := by
  unfold tailWord_3896929
  simp only [CollatzResearch.WordTrace]
  refine ⟨142132677299099250331765841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94755118199399500221177227 142132677299099250331765841)
  ·
    refine ⟨106599507974324437748824381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142132677299099250331765841 106599507974324437748824381)
    ·
      refine ⟨39974815490371664155809143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106599507974324437748824381 39974815490371664155809143)
      ·
        refine ⟨59962223235557496233713715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39974815490371664155809143 59962223235557496233713715)
        ·
          refine ⟨89943334853336244350570573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59962223235557496233713715 89943334853336244350570573)
          ·
            refine ⟨33728750570001091631463965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89943334853336244350570573 33728750570001091631463965)
            ·
              refine ⟨12648281463750409361798987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33728750570001091631463965 12648281463750409361798987)
              ·
                refine ⟨18972422195625614042698481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12648281463750409361798987 18972422195625614042698481)
                ·
                  refine ⟨14229316646719210532023861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18972422195625614042698481 14229316646719210532023861)
                  ·
                    refine ⟨1333998435629925987377237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14229316646719210532023861 1333998435629925987377237)
                    ·
                      rfl

theorem cell22_3896929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_3896929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3896929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3896929 prefixEnd_3896929 := by exact prefixLift 3896929
  have htrace : WordTrace (prefixWord ++ tailWord_3896929) baseStart_3896929 baseEnd_3896929 := by
    simpa [prefixWord, tailWord_3896929, baseEnd_3896929] using wordTrace_append hprefix tailTrace_3896929
  have hstable : (prefixWord ++ tailWord_3896929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896929).length < 2 ^ (prefixWord ++ tailWord_3896929).sum := by decide
  have hdescent : baseEnd_3896929 < baseStart_3896929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897042 : List Nat := [3, 2, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_3897042 : Nat := 118140960795 + 3897042 * 2 ^ 59
def prefixEnd_3897042 : Nat := 4983230072969 + 3 ^ 40 * 3897042 * 2
def baseEnd_3897042 : Nat := 1334037117839231359301891

theorem tailTrace_3897042 : CollatzResearch.WordTrace tailWord_3897042 prefixEnd_3897042 1334037117839231359301891 := by
  unfold tailWord_3897042
  simp only [CollatzResearch.WordTrace]
  refine ⟨35534199686922467657657345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94757865831793247087086253 35534199686922467657657345)
  ·
    refine ⟨26650649765191850743243009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35534199686922467657657345 26650649765191850743243009)
    ·
      refine ⟨19987987323893888057432257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26650649765191850743243009 19987987323893888057432257)
      ·
        refine ⟨14990990492920416043074193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19987987323893888057432257 14990990492920416043074193)
        ·
          refine ⟨11243242869690312032305645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14990990492920416043074193 11243242869690312032305645)
          ·
            refine ⟨4216216076133867012114617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11243242869690312032305645 4216216076133867012114617)
            ·
              refine ⟨3162162057100400259085963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4216216076133867012114617 3162162057100400259085963)
              ·
                refine ⟨4743243085650600388628945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162162057100400259085963 4743243085650600388628945)
                ·
                  refine ⟨3557432314237950291471709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4743243085650600388628945 3557432314237950291471709)
                  ·
                    refine ⟨1334037117839231359301891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3557432314237950291471709 1334037117839231359301891)
                    ·
                      rfl

theorem cell22_3897042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_3897042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897042 prefixEnd_3897042 := by exact prefixLift 3897042
  have htrace : WordTrace (prefixWord ++ tailWord_3897042) baseStart_3897042 baseEnd_3897042 := by
    simpa [prefixWord, tailWord_3897042, baseEnd_3897042] using wordTrace_append hprefix tailTrace_3897042
  have hstable : (prefixWord ++ tailWord_3897042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897042).length < 2 ^ (prefixWord ++ tailWord_3897042).sum := by decide
  have hdescent : baseEnd_3897042 < baseStart_3897042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897070 : List Nat := [4, 1, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_3897070 : Nat := 118140960795 + 3897070 * 2 ^ 59
def prefixEnd_3897070 : Nat := 4983230072969 + 3 ^ 40 * 3897070 * 2
def baseEnd_3897070 : Nat := 1334046702811448619601805

theorem tailTrace_3897070 : CollatzResearch.WordTrace tailWord_3897070 prefixEnd_3897070 1334046702811448619601805 := by
  unfold tailWord_3897070
  simp only [CollatzResearch.WordTrace]
  refine ⟨17767227498948553926581083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94758546661058954275099109 17767227498948553926581083)
  ·
    refine ⟨26650841248422830889871625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17767227498948553926581083 26650841248422830889871625)
    ·
      refine ⟨19988130936317123167403719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26650841248422830889871625 19988130936317123167403719)
      ·
        refine ⟨29982196404475684751105579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19988130936317123167403719 29982196404475684751105579)
        ·
          refine ⟨44973294606713527126658369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29982196404475684751105579 44973294606713527126658369)
          ·
            refine ⟨33729970955035145344993777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44973294606713527126658369 33729970955035145344993777)
            ·
              refine ⟨25297478216276359008745333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33729970955035145344993777 25297478216276359008745333)
              ·
                refine ⟨2371638582775908657069875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25297478216276359008745333 2371638582775908657069875)
                ·
                  refine ⟨3557457874163862985604813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371638582775908657069875 3557457874163862985604813)
                  ·
                    refine ⟨1334046702811448619601805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3557457874163862985604813 1334046702811448619601805)
                    ·
                      rfl

theorem cell22_3897070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_3897070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897070 prefixEnd_3897070 := by exact prefixLift 3897070
  have htrace : WordTrace (prefixWord ++ tailWord_3897070) baseStart_3897070 baseEnd_3897070 := by
    simpa [prefixWord, tailWord_3897070, baseEnd_3897070] using wordTrace_append hprefix tailTrace_3897070
  have hstable : (prefixWord ++ tailWord_3897070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897070).length < 2 ^ (prefixWord ++ tailWord_3897070).sum := by decide
  have hdescent : baseEnd_3897070 < baseStart_3897070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897096 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 5, 4]
def baseStart_3897096 : Nat := 118140960795 + 3897096 * 2 ^ 59
def prefixEnd_3897096 : Nat := 4983230072969 + 3 ^ 40 * 3897096 * 2
def baseEnd_3897096 : Nat := 1334055603142793218451725

theorem tailTrace_3897096 : CollatzResearch.WordTrace tailWord_3897096 prefixEnd_3897096 1334055603142793218451725 := by
  unfold tailWord_3897096
  simp only [CollatzResearch.WordTrace]
  refine ⟨71069384144747118926547571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94759178859662825235396761 71069384144747118926547571)
  ·
    refine ⟨106604076217120678389821357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71069384144747118926547571 106604076217120678389821357)
    ·
      refine ⟨39976528581420254396183009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106604076217120678389821357 39976528581420254396183009)
      ·
        refine ⟨29982396436065190797137257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39976528581420254396183009 29982396436065190797137257)
        ·
          refine ⟨22486797327048893097852943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29982396436065190797137257 22486797327048893097852943)
          ·
            refine ⟨33730195990573339646779415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22486797327048893097852943 33730195990573339646779415)
            ·
              refine ⟨50595293985860009470169123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33730195990573339646779415 50595293985860009470169123)
              ·
                refine ⟨75892940978790014205253685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50595293985860009470169123 75892940978790014205253685)
                ·
                  refine ⟨7114963216761563831742533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75892940978790014205253685 7114963216761563831742533)
                  ·
                    refine ⟨1334055603142793218451725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7114963216761563831742533 1334055603142793218451725)
                    ·
                      rfl

theorem cell22_3897096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_3897096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897096 prefixEnd_3897096 := by exact prefixLift 3897096
  have htrace : WordTrace (prefixWord ++ tailWord_3897096) baseStart_3897096 baseEnd_3897096 := by
    simpa [prefixWord, tailWord_3897096, baseEnd_3897096] using wordTrace_append hprefix tailTrace_3897096
  have hstable : (prefixWord ++ tailWord_3897096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897096).length < 2 ^ (prefixWord ++ tailWord_3897096).sum := by decide
  have hdescent : baseEnd_3897096 < baseStart_3897096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897111 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 8]
def baseStart_3897111 : Nat := 118140960795 + 3897111 * 2 ^ 59
def prefixEnd_3897111 : Nat := 4983230072969 + 3 ^ 40 * 3897111 * 2
def baseEnd_3897111 : Nat := 444686912649779393108893

theorem tailTrace_3897111 : CollatzResearch.WordTrace tailWord_3897111 prefixEnd_3897111 444686912649779393108893 := by
  unfold tailWord_3897111
  simp only [CollatzResearch.WordTrace]
  refine ⟨142139315384439895414891187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94759543589626596943260791 142139315384439895414891187)
  ·
    refine ⟨213208973076659843122336781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142139315384439895414891187 213208973076659843122336781)
    ·
      refine ⟨79953364903747441170876293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213208973076659843122336781 79953364903747441170876293)
      ·
        refine ⟨14991255919452645219539305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79953364903747441170876293 14991255919452645219539305)
        ·
          refine ⟨11243441939589483914654479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14991255919452645219539305 11243441939589483914654479)
          ·
            refine ⟨16865162909384225871981719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11243441939589483914654479 16865162909384225871981719)
            ·
              refine ⟨25297744364076338807972579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16865162909384225871981719 25297744364076338807972579)
              ·
                refine ⟨37946616546114508211958869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25297744364076338807972579 37946616546114508211958869)
                ·
                  refine ⟨444686912649779393108893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37946616546114508211958869 444686912649779393108893)
                  ·
                    rfl

theorem cell22_3897111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 8].length) (baseStart_3897111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897111 prefixEnd_3897111 := by exact prefixLift 3897111
  have htrace : WordTrace (prefixWord ++ tailWord_3897111) baseStart_3897111 baseEnd_3897111 := by
    simpa [prefixWord, tailWord_3897111, baseEnd_3897111] using wordTrace_append hprefix tailTrace_3897111
  have hstable : (prefixWord ++ tailWord_3897111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897111).length < 2 ^ (prefixWord ++ tailWord_3897111).sum := by decide
  have hdescent : baseEnd_3897111 < baseStart_3897111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897143 : List Nat := [1, 1, 3, 1, 2, 1, 2, 6, 2, 3]
def baseStart_3897143 : Nat := 118140960795 + 3897143 * 2 ^ 59
def prefixEnd_3897143 : Nat := 4983230072969 + 3 ^ 40 * 3897143 * 2
def baseEnd_3897143 : Nat := 1334071692203300762526581

theorem tailTrace_3897143 : CollatzResearch.WordTrace tailWord_3897143 prefixEnd_3897143 1334071692203300762526581 := by
  unfold tailWord_3897143
  simp only [CollatzResearch.WordTrace]
  refine ⟨142140482520323964880056083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94760321680215976586704055 142140482520323964880056083)
  ·
    refine ⟨213210723780485947320084125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142140482520323964880056083 213210723780485947320084125)
    ·
      refine ⟨79954021417682230245031547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213210723780485947320084125 79954021417682230245031547)
      ·
        refine ⟨119931032126523345367547321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79954021417682230245031547 119931032126523345367547321)
        ·
          refine ⟨89948274094892509025660491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119931032126523345367547321 89948274094892509025660491)
          ·
            refine ⟨134922411142338763538490737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89948274094892509025660491 134922411142338763538490737)
            ·
              refine ⟨101191808356754072653868053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134922411142338763538490737 101191808356754072653868053)
              ·
                refine ⟨4743366016722847155650065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101191808356754072653868053 4743366016722847155650065)
                ·
                  refine ⟨3557524512542135366737549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4743366016722847155650065 3557524512542135366737549)
                  ·
                    refine ⟨1334071692203300762526581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3557524512542135366737549 1334071692203300762526581)
                    ·
                      rfl

theorem cell22_3897143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_3897143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897143 prefixEnd_3897143 := by exact prefixLift 3897143
  have htrace : WordTrace (prefixWord ++ tailWord_3897143) baseStart_3897143 baseEnd_3897143 := by
    simpa [prefixWord, tailWord_3897143, baseEnd_3897143] using wordTrace_append hprefix tailTrace_3897143
  have hstable : (prefixWord ++ tailWord_3897143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897143).length < 2 ^ (prefixWord ++ tailWord_3897143).sum := by decide
  have hdescent : baseEnd_3897143 < baseStart_3897143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897145 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 6]
def baseStart_3897145 : Nat := 118140960795 + 3897145 * 2 ^ 59
def prefixEnd_3897145 : Nat := 4983230072969 + 3 ^ 40 * 3897145 * 2
def baseEnd_3897145 : Nat := 444690792281391141325525

theorem tailTrace_3897145 : CollatzResearch.WordTrace tailWord_3897145 prefixEnd_3897145 444690792281391141325525 := by
  unfold tailWord_3897145
  simp only [CollatzResearch.WordTrace]
  refine ⟨142140555466316719221628889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94760370310877812814419259 142140555466316719221628889)
  ·
    refine ⟨106605416599737539416221667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142140555466316719221628889 106605416599737539416221667)
    ·
      refine ⟨159908124899606309124332501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106605416599737539416221667 159908124899606309124332501)
      ·
        refine ⟨3747846677334522870101543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 159908124899606309124332501 3747846677334522870101543)
        ·
          refine ⟨5621770016001784305152315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747846677334522870101543 5621770016001784305152315)
          ·
            refine ⟨8432655024002676457728473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621770016001784305152315 8432655024002676457728473)
            ·
              refine ⟨6324491268002007343296355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8432655024002676457728473 6324491268002007343296355)
              ·
                refine ⟨9486736902003011014944533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6324491268002007343296355 9486736902003011014944533)
                ·
                  refine ⟨444690792281391141325525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9486736902003011014944533 444690792281391141325525)
                  ·
                    rfl

theorem cell22_3897145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 6].length) (baseStart_3897145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897145 prefixEnd_3897145 := by exact prefixLift 3897145
  have htrace : WordTrace (prefixWord ++ tailWord_3897145) baseStart_3897145 baseEnd_3897145 := by
    simpa [prefixWord, tailWord_3897145, baseEnd_3897145] using wordTrace_append hprefix tailTrace_3897145
  have hstable : (prefixWord ++ tailWord_3897145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897145).length < 2 ^ (prefixWord ++ tailWord_3897145).sum := by decide
  have hdescent : baseEnd_3897145 < baseStart_3897145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897173 : List Nat := [1, 3, 2, 2, 2, 2, 4, 6]
def baseStart_3897173 : Nat := 118140960795 + 3897173 * 2 ^ 59
def prefixEnd_3897173 : Nat := 4983230072969 + 3 ^ 40 * 3897173 * 2
def baseEnd_3897173 : Nat := 148231329090710076030721

theorem tailTrace_3897173 : CollatzResearch.WordTrace tailWord_3897173 prefixEnd_3897173 148231329090710076030721 := by
  unfold tailWord_3897173
  simp only [CollatzResearch.WordTrace]
  refine ⟨142141576710215280003648173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94761051140143520002432115 142141576710215280003648173)
  ·
    refine ⟨53303091266330730001368065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142141576710215280003648173 53303091266330730001368065)
    ·
      refine ⟨39977318449748047501026049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53303091266330730001368065 39977318449748047501026049)
      ·
        refine ⟨29982988837311035625769537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39977318449748047501026049 29982988837311035625769537)
        ·
          refine ⟨22487241627983276719327153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29982988837311035625769537 22487241627983276719327153)
          ·
            refine ⟨16865431220987457539495365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22487241627983276719327153 16865431220987457539495365)
            ·
              refine ⟨3162268353935148288655381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16865431220987457539495365 3162268353935148288655381)
              ·
                refine ⟨148231329090710076030721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3162268353935148288655381 148231329090710076030721)
                ·
                  rfl

theorem cell22_3897173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 6].length) (baseStart_3897173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897173 prefixEnd_3897173 := by exact prefixLift 3897173
  have htrace : WordTrace (prefixWord ++ tailWord_3897173) baseStart_3897173 baseEnd_3897173 := by
    simpa [prefixWord, tailWord_3897173, baseEnd_3897173] using wordTrace_append hprefix tailTrace_3897173
  have hstable : (prefixWord ++ tailWord_3897173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897173).length < 2 ^ (prefixWord ++ tailWord_3897173).sum := by decide
  have hdescent : baseEnd_3897173 < baseStart_3897173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897201 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 7]
def baseStart_3897201 : Nat := 118140960795 + 3897201 * 2 ^ 59
def prefixEnd_3897201 : Nat := 4983230072969 + 3 ^ 40 * 3897201 * 2
def baseEnd_3897201 : Nat := 444697182262869314858801

theorem tailTrace_3897201 : CollatzResearch.WordTrace tailWord_3897201 prefixEnd_3897201 444697182262869314858801 := by
  unfold tailWord_3897201
  simp only [CollatzResearch.WordTrace]
  refine ⟨142142597954113840785667457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94761731969409227190444971 142142597954113840785667457)
  ·
    refine ⟨106606948465585380589250593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142142597954113840785667457 106606948465585380589250593)
    ·
      refine ⟨79955211349189035441937945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106606948465585380589250593 79955211349189035441937945)
      ·
        refine ⟨59966408511891776581453459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79955211349189035441937945 59966408511891776581453459)
        ·
          refine ⟨89949612767837664872180189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59966408511891776581453459 89949612767837664872180189)
          ·
            refine ⟨33731104787939124327067571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89949612767837664872180189 33731104787939124327067571)
            ·
              refine ⟨50596657181908686490601357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33731104787939124327067571 50596657181908686490601357)
              ·
                refine ⟨18973746443215757433975509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50596657181908686490601357 18973746443215757433975509)
                ·
                  refine ⟨444697182262869314858801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18973746443215757433975509 444697182262869314858801)
                  ·
                    rfl

theorem cell22_3897201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_3897201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897201 prefixEnd_3897201 := by exact prefixLift 3897201
  have htrace : WordTrace (prefixWord ++ tailWord_3897201) baseStart_3897201 baseEnd_3897201 := by
    simpa [prefixWord, tailWord_3897201, baseEnd_3897201] using wordTrace_append hprefix tailTrace_3897201
  have hstable : (prefixWord ++ tailWord_3897201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897201).length < 2 ^ (prefixWord ++ tailWord_3897201).sum := by decide
  have hdescent : baseEnd_3897201 < baseStart_3897201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897216 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 1, 7]
def baseStart_3897216 : Nat := 118140960795 + 3897216 * 2 ^ 59
def prefixEnd_3897216 : Nat := 4983230072969 + 3 ^ 40 * 3897216 * 2
def baseEnd_3897216 : Nat := 1334096681595152905451357

theorem tailTrace_3897216 : CollatzResearch.WordTrace tailWord_3897216 prefixEnd_3897216 1334096681595152905451357 := by
  unfold tailWord_3897216
  simp only [CollatzResearch.WordTrace]
  refine ⟨71071572524529749173731751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94762096699372998898309001 71071572524529749173731751)
  ·
    refine ⟨106607358786794623760597627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71071572524529749173731751 106607358786794623760597627)
    ·
      refine ⟨159911038180191935640896441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106607358786794623760597627 159911038180191935640896441)
      ·
        refine ⟨119933278635143951730672331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159911038180191935640896441 119933278635143951730672331)
        ·
          refine ⟨179899917952715927596008497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119933278635143951730672331 179899917952715927596008497)
          ·
            refine ⟨134924938464536945697006373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179899917952715927596008497 134924938464536945697006373)
            ·
              refine ⟨25298425962100677318188695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134924938464536945697006373 25298425962100677318188695)
              ·
                refine ⟨37947638943151015977283043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25298425962100677318188695 37947638943151015977283043)
                ·
                  refine ⟨56921458414726523965924565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37947638943151015977283043 56921458414726523965924565)
                  ·
                    refine ⟨1334096681595152905451357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56921458414726523965924565 1334096681595152905451357)
                    ·
                      rfl

theorem cell22_3897216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_3897216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897216 prefixEnd_3897216 := by exact prefixLift 3897216
  have htrace : WordTrace (prefixWord ++ tailWord_3897216) baseStart_3897216 baseEnd_3897216 := by
    simpa [prefixWord, tailWord_3897216, baseEnd_3897216] using wordTrace_append hprefix tailTrace_3897216
  have hstable : (prefixWord ++ tailWord_3897216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897216).length < 2 ^ (prefixWord ++ tailWord_3897216).sum := by decide
  have hdescent : baseEnd_3897216 < baseStart_3897216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897256 : List Nat := [2, 1, 6, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3897256 : Nat := 118140960795 + 3897256 * 2 ^ 59
def prefixEnd_3897256 : Nat := 4983230072969 + 3 ^ 40 * 3897256 * 2
def baseEnd_3897256 : Nat := 1334110374412606134451235

theorem tailTrace_3897256 : CollatzResearch.WordTrace tailWord_3897256 prefixEnd_3897256 1334110374412606134451235 := by
  unfold tailWord_3897256
  simp only [CollatzResearch.WordTrace]
  refine ⟨71072301984457292589459811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94763069312609723452613081 71072301984457292589459811)
  ·
    refine ⟨106608452976685938884189717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71072301984457292589459811 106608452976685938884189717)
    ·
      refine ⟨4997271233282153385196393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106608452976685938884189717 4997271233282153385196393)
      ·
        refine ⟨3747953424961615038897295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4997271233282153385196393 3747953424961615038897295)
        ·
          refine ⟨5621930137442422558345943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747953424961615038897295 5621930137442422558345943)
          ·
            refine ⟨8432895206163633837518915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621930137442422558345943 8432895206163633837518915)
            ·
              refine ⟨12649342809245450756278373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8432895206163633837518915 12649342809245450756278373)
              ·
                refine ⟨2371751776733522016802195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12649342809245450756278373 2371751776733522016802195)
                ·
                  refine ⟨3557627665100283025203293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371751776733522016802195 3557627665100283025203293)
                  ·
                    refine ⟨1334110374412606134451235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3557627665100283025203293 1334110374412606134451235)
                    ·
                      rfl

theorem cell22_3897256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3897256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897256 prefixEnd_3897256 := by exact prefixLift 3897256
  have htrace : WordTrace (prefixWord ++ tailWord_3897256) baseStart_3897256 baseEnd_3897256 := by
    simpa [prefixWord, tailWord_3897256, baseEnd_3897256] using wordTrace_append hprefix tailTrace_3897256
  have hstable : (prefixWord ++ tailWord_3897256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897256).length < 2 ^ (prefixWord ++ tailWord_3897256).sum := by decide
  have hdescent : baseEnd_3897256 < baseStart_3897256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897329 : List Nat := [1, 2, 2, 2, 5, 1, 3, 1, 2, 3]
def baseStart_3897329 : Nat := 118140960795 + 3897329 * 2 ^ 59
def prefixEnd_3897329 : Nat := 4983230072969 + 3 ^ 40 * 3897329 * 2
def baseEnd_3897329 : Nat := 1334135363804458277376011

theorem tailTrace_3897329 : CollatzResearch.WordTrace tailWord_3897329 prefixEnd_3897329 1334135363804458277376011 := by
  unfold tailWord_3897329
  simp only [CollatzResearch.WordTrace]
  refine ⟨142147266497650118646327041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94764844331766745764218027 142147266497650118646327041)
  ·
    refine ⟨106610449873237588984745281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142147266497650118646327041 106610449873237588984745281)
    ·
      refine ⟨79957837404928191738558961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106610449873237588984745281 79957837404928191738558961)
      ·
        refine ⟨59968378053696143803919221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79957837404928191738558961 59968378053696143803919221)
        ·
          refine ⟨5622035442534013481617427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59968378053696143803919221 5622035442534013481617427)
          ·
            refine ⟨8433053163801020222426141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622035442534013481617427 8433053163801020222426141)
            ·
              refine ⟨3162394936425382583409803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8433053163801020222426141 3162394936425382583409803)
              ·
                refine ⟨4743592404638073875114705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162394936425382583409803 4743592404638073875114705)
                ·
                  refine ⟨3557694303478555406336029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4743592404638073875114705 3557694303478555406336029)
                  ·
                    refine ⟨1334135363804458277376011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3557694303478555406336029 1334135363804458277376011)
                    ·
                      rfl

theorem cell22_3897329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_3897329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897329 prefixEnd_3897329 := by exact prefixLift 3897329
  have htrace : WordTrace (prefixWord ++ tailWord_3897329) baseStart_3897329 baseEnd_3897329 := by
    simpa [prefixWord, tailWord_3897329, baseEnd_3897329] using wordTrace_append hprefix tailTrace_3897329
  have hstable : (prefixWord ++ tailWord_3897329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897329).length < 2 ^ (prefixWord ++ tailWord_3897329).sum := by decide
  have hdescent : baseEnd_3897329 < baseStart_3897329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897340 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 3, 3]
def baseStart_3897340 : Nat := 118140960795 + 3897340 * 2 ^ 59
def prefixEnd_3897340 : Nat := 4983230072969 + 3 ^ 40 * 3897340 * 2
def baseEnd_3897340 : Nat := 1334139129329257915350977

theorem tailTrace_3897340 : CollatzResearch.WordTrace tailWord_3897340 prefixEnd_3897340 1334139129329257915350977 := by
  unfold tailWord_3897340
  simp only [CollatzResearch.WordTrace]
  refine ⟨71073833850305133762488737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94765111800406845016651649 71073833850305133762488737)
  ·
    refine ⟨53305375387728850321866553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71073833850305133762488737 53305375387728850321866553)
    ·
      refine ⟨39979031540796637741399915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53305375387728850321866553 39979031540796637741399915)
      ·
        refine ⟨59968547311194956612099873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39979031540796637741399915 59968547311194956612099873)
        ·
          refine ⟨44976410483396217459074905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59968547311194956612099873 44976410483396217459074905)
          ·
            refine ⟨33732307862547163094306179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44976410483396217459074905 33732307862547163094306179)
            ·
              refine ⟨50598461793820744641459269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33732307862547163094306179 50598461793820744641459269)
              ·
                refine ⟨9487211586341389620273613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50598461793820744641459269 9487211586341389620273613)
                ·
                  refine ⟨3557704344878021107602605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9487211586341389620273613 3557704344878021107602605)
                  ·
                    refine ⟨1334139129329257915350977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3557704344878021107602605 1334139129329257915350977)
                    ·
                      rfl

theorem cell22_3897340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_3897340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897340 prefixEnd_3897340 := by exact prefixLift 3897340
  have htrace : WordTrace (prefixWord ++ tailWord_3897340) baseStart_3897340 baseEnd_3897340 := by
    simpa [prefixWord, tailWord_3897340, baseEnd_3897340] using wordTrace_append hprefix tailTrace_3897340
  have hstable : (prefixWord ++ tailWord_3897340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897340).length < 2 ^ (prefixWord ++ tailWord_3897340).sum := by decide
  have hdescent : baseEnd_3897340 < baseStart_3897340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897342 : List Nat := [4, 2, 2, 2, 1, 1, 4, 6]
def baseStart_3897342 : Nat := 118140960795 + 3897342 * 2 ^ 59
def prefixEnd_3897342 : Nat := 4983230072969 + 3 ^ 40 * 3897342 * 2
def baseEnd_3897342 : Nat := 148237757107792286311219

theorem tailTrace_3897342 : CollatzResearch.WordTrace tailWord_3897342 prefixEnd_3897342 148237757107792286311219 := by
  unfold tailWord_3897342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17768467580825377733318785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94765160431068681244366853 17768467580825377733318785)
  ·
    refine ⟨13326350685619033299989089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17768467580825377733318785 13326350685619033299989089)
    ·
      refine ⟨9994763014214274974991817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13326350685619033299989089 9994763014214274974991817)
      ·
        refine ⟨7496072260660706231243863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9994763014214274974991817 7496072260660706231243863)
        ·
          refine ⟨11244108390991059346865795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7496072260660706231243863 11244108390991059346865795)
          ·
            refine ⟨16866162586486589020298693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11244108390991059346865795 16866162586486589020298693)
            ·
              refine ⟨3162405484966235441306005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16866162586486589020298693 3162405484966235441306005)
              ·
                refine ⟨148237757107792286311219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3162405484966235441306005 148237757107792286311219)
                ·
                  rfl

theorem cell22_3897342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_3897342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897342 prefixEnd_3897342 := by exact prefixLift 3897342
  have htrace : WordTrace (prefixWord ++ tailWord_3897342) baseStart_3897342 baseEnd_3897342 := by
    simpa [prefixWord, tailWord_3897342, baseEnd_3897342] using wordTrace_append hprefix tailTrace_3897342
  have hstable : (prefixWord ++ tailWord_3897342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897342).length < 2 ^ (prefixWord ++ tailWord_3897342).sum := by decide
  have hdescent : baseEnd_3897342 < baseStart_3897342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897417 : List Nat := [1, 2, 1, 1, 2, 2, 7, 1, 1, 4]
def baseStart_3897417 : Nat := 118140960795 + 3897417 * 2 ^ 59
def prefixEnd_3897417 : Nat := 4983230072969 + 3 ^ 40 * 3897417 * 2
def baseEnd_3897417 : Nat := 1334165488002855381175741

theorem tailTrace_3897417 : CollatzResearch.WordTrace tailWord_3897417 prefixEnd_3897417 1334165488002855381175741 := by
  unfold tailWord_3897417
  simp only [CollatzResearch.WordTrace]
  refine ⟨142150476121331309675530505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94766984080887539783687003 142150476121331309675530505)
  ·
    refine ⟨106612857090998482256647879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142150476121331309675530505 106612857090998482256647879)
    ·
      refine ⟨159919285636497723384971819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106612857090998482256647879 159919285636497723384971819)
      ·
        refine ⟨239878928454746585077457729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159919285636497723384971819 239878928454746585077457729)
        ·
          refine ⟨179909196341059938808093297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239878928454746585077457729 179909196341059938808093297)
          ·
            refine ⟨134931897255794954106069973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179909196341059938808093297 134931897255794954106069973)
            ·
              refine ⟨3162466341932694236861015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 134931897255794954106069973 3162466341932694236861015)
              ·
                refine ⟨4743699512899041355291523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162466341932694236861015 4743699512899041355291523)
                ·
                  refine ⟨7115549269348562032937285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4743699512899041355291523 7115549269348562032937285)
                  ·
                    refine ⟨1334165488002855381175741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7115549269348562032937285 1334165488002855381175741)
                    ·
                      rfl

theorem cell22_3897417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 1, 4].length) (baseStart_3897417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897417 prefixEnd_3897417 := by exact prefixLift 3897417
  have htrace : WordTrace (prefixWord ++ tailWord_3897417) baseStart_3897417 baseEnd_3897417 := by
    simpa [prefixWord, tailWord_3897417, baseEnd_3897417] using wordTrace_append hprefix tailTrace_3897417
  have hstable : (prefixWord ++ tailWord_3897417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897417).length < 2 ^ (prefixWord ++ tailWord_3897417).sum := by decide
  have hdescent : baseEnd_3897417 < baseStart_3897417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897432 : List Nat := [2, 1, 2, 2, 1, 5, 1, 4, 4]
def baseStart_3897432 : Nat := 118140960795 + 3897432 * 2 ^ 59
def prefixEnd_3897432 : Nat := 4983230072969 + 3 ^ 40 * 3897432 * 2
def baseEnd_3897432 : Nat := 444723540936466780683565

theorem tailTrace_3897432 : CollatzResearch.WordTrace tailWord_3897432 prefixEnd_3897432 444723540936466780683565 := by
  unfold tailWord_3897432
  simp only [CollatzResearch.WordTrace]
  refine ⟨71075511608138483618663275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94767348810851311491551033 71075511608138483618663275)
  ·
    refine ⟨106613267412207725427994913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71075511608138483618663275 106613267412207725427994913)
    ·
      refine ⟨79959950559155794070996185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106613267412207725427994913 79959950559155794070996185)
      ·
        refine ⟨59969962919366845553247139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79959950559155794070996185 59969962919366845553247139)
        ·
          refine ⟨89954944379050268329870709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59969962919366845553247139 89954944379050268329870709)
          ·
            refine ⟨8433276035535962655925379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89954944379050268329870709 8433276035535962655925379)
            ·
              refine ⟨12649914053303943983888069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8433276035535962655925379 12649914053303943983888069)
              ·
                refine ⟨2371858884994489496979013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12649914053303943983888069 2371858884994489496979013)
                ·
                  refine ⟨444723540936466780683565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371858884994489496979013 444723540936466780683565)
                  ·
                    rfl

theorem cell22_3897432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 4].length) (baseStart_3897432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897432 prefixEnd_3897432 := by exact prefixLift 3897432
  have htrace : WordTrace (prefixWord ++ tailWord_3897432) baseStart_3897432 baseEnd_3897432 := by
    simpa [prefixWord, tailWord_3897432, baseEnd_3897432] using wordTrace_append hprefix tailTrace_3897432
  have hstable : (prefixWord ++ tailWord_3897432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897432).length < 2 ^ (prefixWord ++ tailWord_3897432).sum := by decide
  have hdescent : baseEnd_3897432 < baseStart_3897432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897447 : List Nat := [1, 1, 5, 1, 1, 2, 1, 5, 2, 3]
def baseStart_3897447 : Nat := 118140960795 + 3897447 * 2 ^ 59
def prefixEnd_3897447 : Nat := 4983230072969 + 3 ^ 40 * 3897447 * 2
def baseEnd_3897447 : Nat := 1334175757615945302925649

theorem tailTrace_3897447 : CollatzResearch.WordTrace tailWord_3897447 prefixEnd_3897447 1334175757615945302925649 := by
  unfold tailWord_3897447
  simp only [CollatzResearch.WordTrace]
  refine ⟨142151570311222624799122595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94767713540815083199415063 142151570311222624799122595)
  ·
    refine ⟨213227355466833937198683893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142151570311222624799122595 213227355466833937198683893)
    ·
      refine ⟨19990064575015681612376615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213227355466833937198683893 19990064575015681612376615)
      ·
        refine ⟨29985096862523522418564923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19990064575015681612376615 29985096862523522418564923)
        ·
          refine ⟨44977645293785283627847385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29985096862523522418564923 44977645293785283627847385)
          ·
            refine ⟨33733233970338962720885539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44977645293785283627847385 33733233970338962720885539)
            ·
              refine ⟨50599850955508444081328309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33733233970338962720885539 50599850955508444081328309)
              ·
                refine ⟨4743736027078916632624529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50599850955508444081328309 4743736027078916632624529)
                ·
                  refine ⟨3557802020309187474468397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4743736027078916632624529 3557802020309187474468397)
                  ·
                    refine ⟨1334175757615945302925649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3557802020309187474468397 1334175757615945302925649)
                    ·
                      rfl

theorem cell22_3897447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_3897447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897447 prefixEnd_3897447 := by exact prefixLift 3897447
  have htrace : WordTrace (prefixWord ++ tailWord_3897447) baseStart_3897447 baseEnd_3897447 := by
    simpa [prefixWord, tailWord_3897447, baseEnd_3897447] using wordTrace_append hprefix tailTrace_3897447
  have hstable : (prefixWord ++ tailWord_3897447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897447).length < 2 ^ (prefixWord ++ tailWord_3897447).sum := by decide
  have hdescent : baseEnd_3897447 < baseStart_3897447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897462 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_3897462 : Nat := 118140960795 + 3897462 * 2 ^ 59
def prefixEnd_3897462 : Nat := 4983230072969 + 3 ^ 40 * 3897462 * 2
def baseEnd_3897462 : Nat := 1334180892422490263800603

theorem tailTrace_3897462 : CollatzResearch.WordTrace tailWord_3897462 prefixEnd_3897462 1334180892422490263800603 := by
  unfold tailWord_3897462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8884507337885517647557415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94768078270778854907279093 8884507337885517647557415)
  ·
    refine ⟨13326761006828276471336123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8884507337885517647557415 13326761006828276471336123)
    ·
      refine ⟨19990141510242414707004185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13326761006828276471336123 19990141510242414707004185)
      ·
        refine ⟨14992606132681811030253139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19990141510242414707004185 14992606132681811030253139)
        ·
          refine ⟨22488909199022716545379709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14992606132681811030253139 22488909199022716545379709)
          ·
            refine ⟨8433340949633518704517391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22488909199022716545379709 8433340949633518704517391)
            ·
              refine ⟨12650011424450278056776087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8433340949633518704517391 12650011424450278056776087)
              ·
                refine ⟨18975017136675417085164131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12650011424450278056776087 18975017136675417085164131)
                ·
                  refine ⟨28462525705013125627746197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18975017136675417085164131 28462525705013125627746197)
                  ·
                    refine ⟨1334180892422490263800603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28462525705013125627746197 1334180892422490263800603)
                    ·
                      rfl

theorem cell22_3897462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_3897462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897462 prefixEnd_3897462 := by exact prefixLift 3897462
  have htrace : WordTrace (prefixWord ++ tailWord_3897462) baseStart_3897462 baseEnd_3897462 := by
    simpa [prefixWord, tailWord_3897462, baseEnd_3897462] using wordTrace_append hprefix tailTrace_3897462
  have hstable : (prefixWord ++ tailWord_3897462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897462).length < 2 ^ (prefixWord ++ tailWord_3897462).sum := by decide
  have hdescent : baseEnd_3897462 < baseStart_3897462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897511 : List Nat := [1, 1, 6, 2, 3, 1, 2, 6]
def baseStart_3897511 : Nat := 118140960795 + 3897511 * 2 ^ 59
def prefixEnd_3897511 : Nat := 4983230072969 + 3 ^ 40 * 3897511 * 2
def baseEnd_3897511 : Nat := 148244185124874496591717

theorem tailTrace_3897511 : CollatzResearch.WordTrace tailWord_3897511 prefixEnd_3897511 148244185124874496591717 := by
  unfold tailWord_3897511
  simp only [CollatzResearch.WordTrace]
  refine ⟨142153904582990763729452387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94769269721993842486301591 142153904582990763729452387)
  ·
    refine ⟨213230856874486145594178581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142153904582990763729452387 213230856874486145594178581)
    ·
      refine ⟨9995196415991538074727121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 213230856874486145594178581 9995196415991538074727121)
      ·
        refine ⟨7496397311993653556045341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9995196415991538074727121 7496397311993653556045341)
        ·
          refine ⟨2811148991997620083517003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7496397311993653556045341 2811148991997620083517003)
          ·
            refine ⟨4216723487996430125275505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811148991997620083517003 4216723487996430125275505)
            ·
              refine ⟨3162542615997322593956629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4216723487996430125275505 3162542615997322593956629)
              ·
                refine ⟨148244185124874496591717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3162542615997322593956629 148244185124874496591717)
                ·
                  rfl

theorem cell22_3897511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 6].length) (baseStart_3897511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897511 prefixEnd_3897511 := by exact prefixLift 3897511
  have htrace : WordTrace (prefixWord ++ tailWord_3897511) baseStart_3897511 baseEnd_3897511 := by
    simpa [prefixWord, tailWord_3897511, baseEnd_3897511] using wordTrace_append hprefix tailTrace_3897511
  have hstable : (prefixWord ++ tailWord_3897511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897511).length < 2 ^ (prefixWord ++ tailWord_3897511).sum := by decide
  have hdescent : baseEnd_3897511 < baseStart_3897511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897535 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 5, 4]
def baseStart_3897535 : Nat := 118140960795 + 3897535 * 2 ^ 59
def prefixEnd_3897535 : Nat := 4983230072969 + 3 ^ 40 * 3897535 * 2
def baseEnd_3897535 : Nat := 1334205881814342406725379

theorem tailTrace_3897535 : CollatzResearch.WordTrace tailWord_3897535 prefixEnd_3897535 1334205881814342406725379 := by
  unfold tailWord_3897535
  simp only [CollatzResearch.WordTrace]
  refine ⟨142154779934903815828326059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94769853289935877218884039 142154779934903815828326059)
  ·
    refine ⟨213232169902355723742489089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142154779934903815828326059 213232169902355723742489089)
    ·
      refine ⟨159924127426766792806866817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213232169902355723742489089 159924127426766792806866817)
      ·
        refine ⟨119943095570075094605150113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159924127426766792806866817 119943095570075094605150113)
        ·
          refine ⟨89957321677556320953862585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119943095570075094605150113 89957321677556320953862585)
          ·
            refine ⟨67467991258167240715396939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89957321677556320953862585 67467991258167240715396939)
            ·
              refine ⟨101201986887250861073095409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67467991258167240715396939 101201986887250861073095409)
              ·
                refine ⟨75901490165438145804821557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101201986887250861073095409 75901490165438145804821557)
                ·
                  refine ⟨7115764703009826169202021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75901490165438145804821557 7115764703009826169202021)
                  ·
                    refine ⟨1334205881814342406725379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7115764703009826169202021 1334205881814342406725379)
                    ·
                      rfl

theorem cell22_3897535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_3897535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897535 prefixEnd_3897535 := by exact prefixLift 3897535
  have htrace : WordTrace (prefixWord ++ tailWord_3897535) baseStart_3897535 baseEnd_3897535 := by
    simpa [prefixWord, tailWord_3897535, baseEnd_3897535] using wordTrace_append hprefix tailTrace_3897535
  have hstable : (prefixWord ++ tailWord_3897535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897535).length < 2 ^ (prefixWord ++ tailWord_3897535).sum := by decide
  have hdescent : baseEnd_3897535 < baseStart_3897535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897586 : List Nat := [3, 2, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_3897586 : Nat := 118140960795 + 3897586 * 2 ^ 59
def prefixEnd_3897586 : Nat := 4983230072969 + 3 ^ 40 * 3897586 * 2
def baseEnd_3897586 : Nat := 1334223340156595273700223

theorem tailTrace_3897586 : CollatzResearch.WordTrace tailWord_3897586 prefixEnd_3897586 1334223340156595273700223 := by
  unfold tailWord_3897586
  simp only [CollatzResearch.WordTrace]
  refine ⟨35539160014429762884608153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94771093371812701025621741 35539160014429762884608153)
  ·
    refine ⟨26654370010822322163456115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35539160014429762884608153 26654370010822322163456115)
    ·
      refine ⟨39981555016233483245184173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26654370010822322163456115 39981555016233483245184173)
      ·
        refine ⟨14993083131087556216944065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39981555016233483245184173 14993083131087556216944065)
        ·
          refine ⟨11244812348315667162708049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14993083131087556216944065 11244812348315667162708049)
          ·
            refine ⟨8433609261236750372031037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11244812348315667162708049 8433609261236750372031037)
            ·
              refine ⟨3162603472963781389511639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8433609261236750372031037 3162603472963781389511639)
              ·
                refine ⟨4743905209445672084267459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162603472963781389511639 4743905209445672084267459)
                ·
                  refine ⟨7115857814168508126401189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4743905209445672084267459 7115857814168508126401189)
                  ·
                    refine ⟨1334223340156595273700223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7115857814168508126401189 1334223340156595273700223)
                    ·
                      rfl

theorem cell22_3897586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_3897586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897586 prefixEnd_3897586 := by exact prefixLift 3897586
  have htrace : WordTrace (prefixWord ++ tailWord_3897586) baseStart_3897586 baseEnd_3897586 := by
    simpa [prefixWord, tailWord_3897586, baseEnd_3897586] using wordTrace_append hprefix tailTrace_3897586
  have hstable : (prefixWord ++ tailWord_3897586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897586).length < 2 ^ (prefixWord ++ tailWord_3897586).sum := by decide
  have hdescent : baseEnd_3897586 < baseStart_3897586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897599 : List Nat := [1, 1, 2, 2, 1, 4, 4, 2, 2, 3]
def baseStart_3897599 : Nat := 118140960795 + 3897599 * 2 ^ 59
def prefixEnd_3897599 : Nat := 4983230072969 + 3 ^ 40 * 3897599 * 2
def baseEnd_3897599 : Nat := 1334227790322267573125183

theorem tailTrace_3897599 : CollatzResearch.WordTrace tailWord_3897599 prefixEnd_3897599 1334227790322267573125183 := by
  unfold tailWord_3897599
  simp only [CollatzResearch.WordTrace]
  refine ⟨142157114206671954758655851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94771409471114636505770567 142157114206671954758655851)
  ·
    refine ⟨213235671310007932137983777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142157114206671954758655851 213235671310007932137983777)
    ·
      refine ⟨159926753482505949103487833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213235671310007932137983777 159926753482505949103487833)
      ·
        refine ⟨119945065111879461827615875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159926753482505949103487833 119945065111879461827615875)
        ·
          refine ⟨179917597667819192741423813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119945065111879461827615875 179917597667819192741423813)
          ·
            refine ⟨33734549562716098639016965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179917597667819192741423813 33734549562716098639016965)
            ·
              refine ⟨6325228043009268494815681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33734549562716098639016965 6325228043009268494815681)
              ·
                refine ⟨4743921032256951371111761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6325228043009268494815681 4743921032256951371111761)
                ·
                  refine ⟨3557940774192713528333821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4743921032256951371111761 3557940774192713528333821)
                  ·
                    refine ⟨1334227790322267573125183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3557940774192713528333821 1334227790322267573125183)
                    ·
                      rfl

theorem cell22_3897599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 3].length) (baseStart_3897599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897599 prefixEnd_3897599 := by exact prefixLift 3897599
  have htrace : WordTrace (prefixWord ++ tailWord_3897599) baseStart_3897599 baseEnd_3897599 := by
    simpa [prefixWord, tailWord_3897599, baseEnd_3897599] using wordTrace_append hprefix tailTrace_3897599
  have hstable : (prefixWord ++ tailWord_3897599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897599).length < 2 ^ (prefixWord ++ tailWord_3897599).sum := by decide
  have hdescent : baseEnd_3897599 < baseStart_3897599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897627 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 5, 3]
def baseStart_3897627 : Nat := 118140960795 + 3897627 * 2 ^ 59
def prefixEnd_3897627 : Nat := 4983230072969 + 3 ^ 40 * 3897627 * 2
def baseEnd_3897627 : Nat := 1334237375294484833425097

theorem tailTrace_3897627 : CollatzResearch.WordTrace tailWord_3897627 prefixEnd_3897627 1334237375294484833425097 := by
  unfold tailWord_3897627
  simp only [CollatzResearch.WordTrace]
  refine ⟨142158135450570515540675135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94772090300380343693783423 142158135450570515540675135)
  ·
    refine ⟨213237203175855773311012703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142158135450570515540675135 213237203175855773311012703)
    ·
      refine ⟨319855804763783659966519055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213237203175855773311012703 319855804763783659966519055)
      ·
        refine ⟨479783707145675489949778583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319855804763783659966519055 479783707145675489949778583)
        ·
          refine ⟨719675560718513234924667875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479783707145675489949778583 719675560718513234924667875)
          ·
            refine ⟨1079513341077769852387001813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719675560718513234924667875 1079513341077769852387001813)
            ·
              refine ⟨25301093931510230915320355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1079513341077769852387001813 25301093931510230915320355)
              ·
                refine ⟨37951640897265346372980533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25301093931510230915320355 37951640897265346372980533)
                ·
                  refine ⟨3557966334118626222466925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37951640897265346372980533 3557966334118626222466925)
                  ·
                    refine ⟨1334237375294484833425097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3557966334118626222466925 1334237375294484833425097)
                    ·
                      rfl

theorem cell22_3897627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 3].length) (baseStart_3897627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897627 prefixEnd_3897627 := by exact prefixLift 3897627
  have htrace : WordTrace (prefixWord ++ tailWord_3897627) baseStart_3897627 baseEnd_3897627 := by
    simpa [prefixWord, tailWord_3897627, baseEnd_3897627] using wordTrace_append hprefix tailTrace_3897627
  have hstable : (prefixWord ++ tailWord_3897627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897627).length < 2 ^ (prefixWord ++ tailWord_3897627).sum := by decide
  have hdescent : baseEnd_3897627 < baseStart_3897627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897672 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 2, 5]
def baseStart_3897672 : Nat := 118140960795 + 3897672 * 2 ^ 59
def prefixEnd_3897672 : Nat := 4983230072969 + 3 ^ 40 * 3897672 * 2
def baseEnd_3897672 : Nat := 1334252779714119716049959

theorem tailTrace_3897672 : CollatzResearch.WordTrace tailWord_3897672 prefixEnd_3897672 1334252779714119716049959 := by
  unfold tailWord_3897672
  simp only [CollatzResearch.WordTrace]
  refine ⟨71079888367703744113031635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94773184490271658817375513 71079888367703744113031635)
  ·
    refine ⟨106619832551555616169547453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71079888367703744113031635 106619832551555616169547453)
    ·
      refine ⟨39982437206833356063580295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106619832551555616169547453 39982437206833356063580295)
      ·
        refine ⟨59973655810250034095370443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39982437206833356063580295 59973655810250034095370443)
        ·
          refine ⟨89960483715375051143055665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59973655810250034095370443 89960483715375051143055665)
          ·
            refine ⟨67470362786531288357291749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89960483715375051143055665 67470362786531288357291749)
            ·
              refine ⟨12650693022474616566992203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67470362786531288357291749 12650693022474616566992203)
              ·
                refine ⟨18976039533711924850488305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12650693022474616566992203 18976039533711924850488305)
                ·
                  refine ⟨14232029650283943637866229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18976039533711924850488305 14232029650283943637866229)
                  ·
                    refine ⟨1334252779714119716049959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14232029650283943637866229 1334252779714119716049959)
                    ·
                      rfl

theorem cell22_3897672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_3897672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897672 prefixEnd_3897672 := by exact prefixLift 3897672
  have htrace : WordTrace (prefixWord ++ tailWord_3897672) baseStart_3897672 baseEnd_3897672 := by
    simpa [prefixWord, tailWord_3897672, baseEnd_3897672] using wordTrace_append hprefix tailTrace_3897672
  have hstable : (prefixWord ++ tailWord_3897672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897672).length < 2 ^ (prefixWord ++ tailWord_3897672).sum := by decide
  have hdescent : baseEnd_3897672 < baseStart_3897672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897768 : List Nat := [2, 1, 6, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3897768 : Nat := 118140960795 + 3897768 * 2 ^ 59
def prefixEnd_3897768 : Nat := 4983230072969 + 3 ^ 40 * 3897768 * 2
def baseEnd_3897768 : Nat := 1334285642476007465649665

theorem tailTrace_3897768 : CollatzResearch.WordTrace tailWord_3897768 prefixEnd_3897768 1334285642476007465649665 := by
  unfold tailWord_3897768
  simp only [CollatzResearch.WordTrace]
  refine ⟨71081639071529848310778979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94775518762039797747705305 71081639071529848310778979)
  ·
    refine ⟨106622458607294772466168469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71081639071529848310778979 106622458607294772466168469)
    ·
      refine ⟨4997927747216942459351647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106622458607294772466168469 4997927747216942459351647)
      ·
        refine ⟨7496891620825413689027471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4997927747216942459351647 7496891620825413689027471)
        ·
          refine ⟨11245337431238120533541207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7496891620825413689027471 11245337431238120533541207)
          ·
            refine ⟨16868006146857180800311811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11245337431238120533541207 16868006146857180800311811)
            ·
              refine ⟨25302009220285771200467717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16868006146857180800311811 25302009220285771200467717)
              ·
                refine ⟨4744126728803582100087697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25302009220285771200467717 4744126728803582100087697)
                ·
                  refine ⟨3558095046602686575065773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4744126728803582100087697 3558095046602686575065773)
                  ·
                    refine ⟨1334285642476007465649665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3558095046602686575065773 1334285642476007465649665)
                    ·
                      rfl

theorem cell22_3897768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3897768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897768 prefixEnd_3897768 := by exact prefixLift 3897768
  have htrace : WordTrace (prefixWord ++ tailWord_3897768) baseStart_3897768 baseEnd_3897768 := by
    simpa [prefixWord, tailWord_3897768, baseEnd_3897768] using wordTrace_append hprefix tailTrace_3897768
  have hstable : (prefixWord ++ tailWord_3897768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897768).length < 2 ^ (prefixWord ++ tailWord_3897768).sum := by decide
  have hdescent : baseEnd_3897768 < baseStart_3897768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897781 : List Nat := [1, 3, 3, 2, 3, 2, 1, 7]
def baseStart_3897781 : Nat := 118140960795 + 3897781 * 2 ^ 59
def prefixEnd_3897781 : Nat := 4983230072969 + 3 ^ 40 * 3897781 * 2
def baseEnd_3897781 : Nat := 148254454737964418341625

theorem tailTrace_3897781 : CollatzResearch.WordTrace tailWord_3897781 prefixEnd_3897781 148254454737964418341625 := by
  unfold tailWord_3897781
  simp only [CollatzResearch.WordTrace]
  refine ⟨142163752292012599841781197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94775834861341733227854131 142163752292012599841781197)
  ·
    refine ⟨53311407109504724940667949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142163752292012599841781197 53311407109504724940667949)
    ·
      refine ⟨19991777666064271852750481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53311407109504724940667949 19991777666064271852750481)
      ·
        refine ⟨14993833249548203889562861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19991777666064271852750481 14993833249548203889562861)
        ·
          refine ⟨5622687468580576458586073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14993833249548203889562861 5622687468580576458586073)
          ·
            refine ⟨4217015601435432343939555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5622687468580576458586073 4217015601435432343939555)
            ·
              refine ⟨6325523402153148515909333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217015601435432343939555 6325523402153148515909333)
              ·
                refine ⟨148254454737964418341625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6325523402153148515909333 148254454737964418341625)
                ·
                  rfl

theorem cell22_3897781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 7].length) (baseStart_3897781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897781 prefixEnd_3897781 := by exact prefixLift 3897781
  have htrace : WordTrace (prefixWord ++ tailWord_3897781) baseStart_3897781 baseEnd_3897781 := by
    simpa [prefixWord, tailWord_3897781, baseEnd_3897781] using wordTrace_append hprefix tailTrace_3897781
  have hstable : (prefixWord ++ tailWord_3897781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897781).length < 2 ^ (prefixWord ++ tailWord_3897781).sum := by decide
  have hdescent : baseEnd_3897781 < baseStart_3897781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897792 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 9]
def baseStart_3897792 : Nat := 118140960795 + 3897792 * 2 ^ 59
def prefixEnd_3897792 : Nat := 4983230072969 + 3 ^ 40 * 3897792 * 2
def baseEnd_3897792 : Nat := 444764619388826467683197

theorem tailTrace_3897792 : CollatzResearch.WordTrace tailWord_3897792 prefixEnd_3897792 444764619388826467683197 := by
  unfold tailWord_3897792
  simp only [CollatzResearch.WordTrace]
  refine ⟨71082076747486374360215815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94776102329981832480287753 71082076747486374360215815)
  ·
    refine ⟨106623115121229561540323723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71082076747486374360215815 106623115121229561540323723)
    ·
      refine ⟨159934672681844342310485585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106623115121229561540323723 159934672681844342310485585)
      ·
        refine ⟨119951004511383256732864189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159934672681844342310485585 119951004511383256732864189)
        ·
          refine ⟨44981626691768721274824071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119951004511383256732864189 44981626691768721274824071)
          ·
            refine ⟨67472440037653081912236107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44981626691768721274824071 67472440037653081912236107)
            ·
              refine ⟨101208660056479622868354161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67472440037653081912236107 101208660056479622868354161)
              ·
                refine ⟨75906495042359717151265621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101208660056479622868354161 75906495042359717151265621)
                ·
                  refine ⟨444764619388826467683197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75906495042359717151265621 444764619388826467683197)
                  ·
                    rfl

theorem cell22_3897792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_3897792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897792 prefixEnd_3897792 := by exact prefixLift 3897792
  have htrace : WordTrace (prefixWord ++ tailWord_3897792) baseStart_3897792 baseEnd_3897792 := by
    simpa [prefixWord, tailWord_3897792, baseEnd_3897792] using wordTrace_append hprefix tailTrace_3897792
  have hstable : (prefixWord ++ tailWord_3897792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897792).length < 2 ^ (prefixWord ++ tailWord_3897792).sum := by decide
  have hdescent : baseEnd_3897792 < baseStart_3897792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897807 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 3, 7]
def baseStart_3897807 : Nat := 118140960795 + 3897807 * 2 ^ 59
def prefixEnd_3897807 : Nat := 4983230072969 + 3 ^ 40 * 3897807 * 2
def baseEnd_3897807 : Nat := 1334298992973024363924545

theorem tailTrace_3897807 : CollatzResearch.WordTrace tailWord_3897807 prefixEnd_3897807 1334298992973024363924545 := by
  unfold tailWord_3897807
  simp only [CollatzResearch.WordTrace]
  refine ⟨142164700589918406282227675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94776467059945604188151783 142164700589918406282227675)
  ·
    refine ⟨213247050884877609423341513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142164700589918406282227675 213247050884877609423341513)
    ·
      refine ⟨159935288163658207067506135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213247050884877609423341513 159935288163658207067506135)
      ·
        refine ⟨239902932245487310601259203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159935288163658207067506135 239902932245487310601259203)
        ·
          refine ⟨359854398368230965901888805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239902932245487310601259203 359854398368230965901888805)
          ·
            refine ⟨67472699694043306106604151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359854398368230965901888805 67472699694043306106604151)
            ·
              refine ⟨101209049541064959159906227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67472699694043306106604151 101209049541064959159906227)
              ·
                refine ⟨151813574311597438739859341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101209049541064959159906227 151813574311597438739859341)
                ·
                  refine ⟨56930090366849039527447253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151813574311597438739859341 56930090366849039527447253)
                  ·
                    refine ⟨1334298992973024363924545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56930090366849039527447253 1334298992973024363924545)
                    ·
                      rfl

theorem cell22_3897807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_3897807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897807 prefixEnd_3897807 := by exact prefixLift 3897807
  have htrace : WordTrace (prefixWord ++ tailWord_3897807) baseStart_3897807 baseEnd_3897807 := by
    simpa [prefixWord, tailWord_3897807, baseEnd_3897807] using wordTrace_append hprefix tailTrace_3897807
  have hstable : (prefixWord ++ tailWord_3897807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897807).length < 2 ^ (prefixWord ++ tailWord_3897807).sum := by decide
  have hdescent : baseEnd_3897807 < baseStart_3897807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897813 : List Nat := [1, 3, 2, 3, 1, 2, 1, 5, 1, 3]
def baseStart_3897813 : Nat := 118140960795 + 3897813 * 2 ^ 59
def prefixEnd_3897813 : Nat := 4983230072969 + 3 ^ 40 * 3897813 * 2
def baseEnd_3897813 : Nat := 1334301046895642348274527

theorem tailTrace_3897813 : CollatzResearch.WordTrace tailWord_3897813 prefixEnd_3897813 1334301046895642348274527 := by
  unfold tailWord_3897813
  simp only [CollatzResearch.WordTrace]
  refine ⟨142164919427896669306946093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94776612951931112871297395 142164919427896669306946093)
  ·
    refine ⟨53311844785461250990104785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142164919427896669306946093 53311844785461250990104785)
    ·
      refine ⟨39983883589095938242578589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53311844785461250990104785 39983883589095938242578589)
      ·
        refine ⟨14993956345910976840966971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39983883589095938242578589 14993956345910976840966971)
        ·
          refine ⟨22490934518866465261450457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14993956345910976840966971 22490934518866465261450457)
          ·
            refine ⟨16868200889149848946087843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22490934518866465261450457 16868200889149848946087843)
            ·
              refine ⟨25302301333724773419131765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16868200889149848946087843 25302301333724773419131765)
              ·
                refine ⟨2372090750036697508043603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25302301333724773419131765 2372090750036697508043603)
                ·
                  refine ⟨3558136125055046262065405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372090750036697508043603 3558136125055046262065405)
                  ·
                    refine ⟨1334301046895642348274527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3558136125055046262065405 1334301046895642348274527)
                    ·
                      rfl

theorem cell22_3897813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_3897813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897813 prefixEnd_3897813 := by exact prefixLift 3897813
  have htrace : WordTrace (prefixWord ++ tailWord_3897813) baseStart_3897813 baseEnd_3897813 := by
    simpa [prefixWord, tailWord_3897813, baseEnd_3897813] using wordTrace_append hprefix tailTrace_3897813
  have hstable : (prefixWord ++ tailWord_3897813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897813).length < 2 ^ (prefixWord ++ tailWord_3897813).sum := by decide
  have hdescent : baseEnd_3897813 < baseStart_3897813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897888 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 6]
def baseStart_3897888 : Nat := 118140960795 + 3897888 * 2 ^ 59
def prefixEnd_3897888 : Nat := 4983230072969 + 3 ^ 40 * 3897888 * 2
def baseEnd_3897888 : Nat := 444775573642789050883099

theorem tailTrace_3897888 : CollatzResearch.WordTrace tailWord_3897888 prefixEnd_3897888 444775573642789050883099 := by
  unfold tailWord_3897888
  simp only [CollatzResearch.WordTrace]
  refine ⟨71083827451312478557963159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94778436601749971410617545 71083827451312478557963159)
  ·
    refine ⟨106625741176968717836944739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71083827451312478557963159 106625741176968717836944739)
    ·
      refine ⟨159938611765453076755417109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106625741176968717836944739 159938611765453076755417109)
      ·
        refine ⟨7497122426505612972910177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159938611765453076755417109 7497122426505612972910177)
        ·
          refine ⟨5622841819879209729682633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7497122426505612972910177 5622841819879209729682633)
          ·
            refine ⟨4217131364909407297261975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5622841819879209729682633 4217131364909407297261975)
            ·
              refine ⟨6325697047364110945892963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217131364909407297261975 6325697047364110945892963)
              ·
                refine ⟨9488545571046166418839445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6325697047364110945892963 9488545571046166418839445)
                ·
                  refine ⟨444775573642789050883099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9488545571046166418839445 444775573642789050883099)
                  ·
                    rfl

theorem cell22_3897888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 6].length) (baseStart_3897888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897888 prefixEnd_3897888 := by exact prefixLift 3897888
  have htrace : WordTrace (prefixWord ++ tailWord_3897888) baseStart_3897888 baseEnd_3897888 := by
    simpa [prefixWord, tailWord_3897888, baseEnd_3897888] using wordTrace_append hprefix tailTrace_3897888
  have hstable : (prefixWord ++ tailWord_3897888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897888).length < 2 ^ (prefixWord ++ tailWord_3897888).sum := by decide
  have hdescent : baseEnd_3897888 < baseStart_3897888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897924 : List Nat := [2, 3, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3897924 : Nat := 118140960795 + 3897924 * 2 ^ 59
def prefixEnd_3897924 : Nat := 4983230072969 + 3 ^ 40 * 3897924 * 2
def baseEnd_3897924 : Nat := 1334339044464075058749187

theorem tailTrace_3897924 : CollatzResearch.WordTrace tailWord_3897924 prefixEnd_3897924 1334339044464075058749187 := by
  unfold tailWord_3897924
  simp only [CollatzResearch.WordTrace]
  refine ⟨71084483965247267632118413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94779311953663023509491217 71084483965247267632118413)
  ·
    refine ⟨26656681486967725362044405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71084483965247267632118413 26656681486967725362044405)
    ·
      refine ⟨2499063889403224252691663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26656681486967725362044405 2499063889403224252691663)
      ·
        refine ⟨3748595834104836379037495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499063889403224252691663 3748595834104836379037495)
        ·
          refine ⟨5622893751157254568556243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3748595834104836379037495 5622893751157254568556243)
          ·
            refine ⟨8434340626735881852834365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622893751157254568556243 8434340626735881852834365)
            ·
              refine ⟨3162877735025955694812887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8434340626735881852834365 3162877735025955694812887)
              ·
                refine ⟨4744316602538933542219331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162877735025955694812887 4744316602538933542219331)
                ·
                  refine ⟨7116474903808400313328997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744316602538933542219331 7116474903808400313328997)
                  ·
                    refine ⟨1334339044464075058749187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7116474903808400313328997 1334339044464075058749187)
                    ·
                      rfl

theorem cell22_3897924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3897924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897924 prefixEnd_3897924 := by exact prefixLift 3897924
  have htrace : WordTrace (prefixWord ++ tailWord_3897924) baseStart_3897924 baseEnd_3897924 := by
    simpa [prefixWord, tailWord_3897924, baseEnd_3897924] using wordTrace_append hprefix tailTrace_3897924
  have hstable : (prefixWord ++ tailWord_3897924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897924).length < 2 ^ (prefixWord ++ tailWord_3897924).sum := by decide
  have hdescent : baseEnd_3897924 < baseStart_3897924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897944 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 7]
def baseStart_3897944 : Nat := 118140960795 + 3897944 * 2 ^ 59
def prefixEnd_3897944 : Nat := 4983230072969 + 3 ^ 40 * 3897944 * 2
def baseEnd_3897944 : Nat := 444781963624267224416375

theorem tailTrace_3897944 : CollatzResearch.WordTrace tailWord_3897944 prefixEnd_3897944 444781963624267224416375 := by
  unfold tailWord_3897944
  simp only [CollatzResearch.WordTrace]
  refine ⟨71084848695211039339982443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94779798260281385786643257 71084848695211039339982443)
  ·
    refine ⟨106627273042816559009973665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71084848695211039339982443 106627273042816559009973665)
    ·
      refine ⟨79970454782112419257480249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106627273042816559009973665 79970454782112419257480249)
      ·
        refine ⟨59977841086584314443110187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79970454782112419257480249 59977841086584314443110187)
        ·
          refine ⟨89966761629876471664665281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59977841086584314443110187 89966761629876471664665281)
          ·
            refine ⟨67475071222407353748498961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89966761629876471664665281 67475071222407353748498961)
            ·
              refine ⟨50606303416805515311374221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67475071222407353748498961 50606303416805515311374221)
              ·
                refine ⟨18977363781302068241765333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50606303416805515311374221 18977363781302068241765333)
                ·
                  refine ⟨444781963624267224416375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18977363781302068241765333 444781963624267224416375)
                  ·
                    rfl

theorem cell22_3897944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_3897944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3897944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3897944 prefixEnd_3897944 := by exact prefixLift 3897944
  have htrace : WordTrace (prefixWord ++ tailWord_3897944) baseStart_3897944 baseEnd_3897944 := by
    simpa [prefixWord, tailWord_3897944, baseEnd_3897944] using wordTrace_append hprefix tailTrace_3897944
  have hstable : (prefixWord ++ tailWord_3897944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897944).length < 2 ^ (prefixWord ++ tailWord_3897944).sum := by decide
  have hdescent : baseEnd_3897944 < baseStart_3897944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898072 : List Nat := [2, 1, 2, 2, 3, 4, 2, 1, 2, 3]
def baseStart_3898072 : Nat := 118140960795 + 3898072 * 2 ^ 59
def prefixEnd_3898072 : Nat := 4983230072969 + 3 ^ 40 * 3898072 * 2
def baseEnd_3898072 : Nat := 1334389707888652006048733

theorem tailTrace_3898072 : CollatzResearch.WordTrace tailWord_3898072 prefixEnd_3898072 1334389707888652006048733 := by
  unfold tailWord_3898072
  simp only [CollatzResearch.WordTrace]
  refine ⟨71087182966979178270312235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94782910622638904360416313 71087182966979178270312235)
  ·
    refine ⟨106630774450468767405468353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71087182966979178270312235 106630774450468767405468353)
    ·
      refine ⟨79973080837851575554101265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106630774450468767405468353 79973080837851575554101265)
      ·
        refine ⟨59979810628388681665575949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79973080837851575554101265 59979810628388681665575949)
        ·
          refine ⟨22492428985645755624590981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59979810628388681665575949 22492428985645755624590981)
          ·
            refine ⟨4217330434808579179610809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22492428985645755624590981 4217330434808579179610809)
            ·
              refine ⟨3162997826106434384708107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4217330434808579179610809 3162997826106434384708107)
              ·
                refine ⟨4744496739159651577062161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162997826106434384708107 4744496739159651577062161)
                ·
                  refine ⟨3558372554369738682796621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4744496739159651577062161 3558372554369738682796621)
                  ·
                    refine ⟨1334389707888652006048733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3558372554369738682796621 1334389707888652006048733)
                    ·
                      rfl

theorem cell22_3898072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_3898072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898072 prefixEnd_3898072 := by exact prefixLift 3898072
  have htrace : WordTrace (prefixWord ++ tailWord_3898072) baseStart_3898072 baseEnd_3898072 := by
    simpa [prefixWord, tailWord_3898072, baseEnd_3898072] using wordTrace_append hprefix tailTrace_3898072
  have hstable : (prefixWord ++ tailWord_3898072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898072).length < 2 ^ (prefixWord ++ tailWord_3898072).sum := by decide
  have hdescent : baseEnd_3898072 < baseStart_3898072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898111 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 2, 5]
def baseStart_3898111 : Nat := 118140960795 + 3898111 * 2 ^ 59
def prefixEnd_3898111 : Nat := 4983230072969 + 3 ^ 40 * 3898111 * 2
def baseEnd_3898111 : Nat := 1334403058385668904323613

theorem tailTrace_3898111 : CollatzResearch.WordTrace tailWord_3898111 prefixEnd_3898111 1334403058385668904323613 := by
  unfold tailWord_3898111
  simp only [CollatzResearch.WordTrace]
  refine ⟨142175788380817066201294187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94783858920544710800862791 142175788380817066201294187)
  ·
    refine ⟨213263682571225599301941281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142175788380817066201294187 213263682571225599301941281)
    ·
      refine ⟨159947761928419199476455961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213263682571225599301941281 159947761928419199476455961)
      ·
        refine ⟨119960821446314399607341971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159947761928419199476455961 119960821446314399607341971)
        ·
          refine ⟨179941232169471599411012957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119960821446314399607341971 179941232169471599411012957)
          ·
            refine ⟨67477962063551849779129859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179941232169471599411012957 67477962063551849779129859)
            ·
              refine ⟨101216943095327774668694789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67477962063551849779129859 101216943095327774668694789)
              ·
                refine ⟨18978176830373957750380273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101216943095327774668694789 18978176830373957750380273)
                ·
                  refine ⟨14233632622780468312785205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18978176830373957750380273 14233632622780468312785205)
                  ·
                    refine ⟨1334403058385668904323613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14233632622780468312785205 1334403058385668904323613)
                    ·
                      rfl

theorem cell22_3898111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_3898111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898111 prefixEnd_3898111 := by exact prefixLift 3898111
  have htrace : WordTrace (prefixWord ++ tailWord_3898111) baseStart_3898111 baseEnd_3898111 := by
    simpa [prefixWord, tailWord_3898111, baseEnd_3898111] using wordTrace_append hprefix tailTrace_3898111
  have hstable : (prefixWord ++ tailWord_3898111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898111).length < 2 ^ (prefixWord ++ tailWord_3898111).sum := by decide
  have hdescent : baseEnd_3898111 < baseStart_3898111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898143 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 3, 4]
def baseStart_3898143 : Nat := 118140960795 + 3898143 * 2 ^ 59
def prefixEnd_3898143 : Nat := 4983230072969 + 3 ^ 40 * 3898143 * 2
def baseEnd_3898143 : Nat := 1334414012639631487523515

theorem tailTrace_3898143 : CollatzResearch.WordTrace tailWord_3898143 prefixEnd_3898143 1334414012639631487523515 := by
  unfold tailWord_3898143
  simp only [CollatzResearch.WordTrace]
  refine ⟨142176955516701135666459083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94784637011134090444306055 142176955516701135666459083)
  ·
    refine ⟨213265433275051703499688625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142176955516701135666459083 213265433275051703499688625)
    ·
      refine ⟨159949074956288777624766469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213265433275051703499688625 159949074956288777624766469)
      ·
        refine ⟨29990451554304145804643713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159949074956288777624766469 29990451554304145804643713)
        ·
          refine ⟨22492838665728109353482785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29990451554304145804643713 22492838665728109353482785)
          ·
            refine ⟨16869628999296082015112089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22492838665728109353482785 16869628999296082015112089)
            ·
              refine ⟨12652221749472061511334067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16869628999296082015112089 12652221749472061511334067)
              ·
                refine ⟨18978332624208092267001101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12652221749472061511334067 18978332624208092267001101)
                ·
                  refine ⟨7116874734078034600125413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18978332624208092267001101 7116874734078034600125413)
                  ·
                    refine ⟨1334414012639631487523515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7116874734078034600125413 1334414012639631487523515)
                    ·
                      rfl

theorem cell22_3898143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_3898143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898143 prefixEnd_3898143 := by exact prefixLift 3898143
  have htrace : WordTrace (prefixWord ++ tailWord_3898143) baseStart_3898143 baseEnd_3898143 := by
    simpa [prefixWord, tailWord_3898143, baseEnd_3898143] using wordTrace_append hprefix tailTrace_3898143
  have hstable : (prefixWord ++ tailWord_3898143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898143).length < 2 ^ (prefixWord ++ tailWord_3898143).sum := by decide
  have hdescent : baseEnd_3898143 < baseStart_3898143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898164 : List Nat := [2, 5, 1, 1, 4, 1, 1, 2, 5]
def baseStart_3898164 : Nat := 118140960795 + 3898164 * 2 ^ 59
def prefixEnd_3898164 : Nat := 4983230072969 + 3 ^ 40 * 3898164 * 2
def baseEnd_3898164 : Nat := 444807067122931477582817

theorem tailTrace_3898164 : CollatzResearch.WordTrace tailWord_3898164 prefixEnd_3898164 444807067122931477582817 := by
  unfold tailWord_3898164
  simp only [CollatzResearch.WordTrace]
  refine ⟨71088860724812528126486773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94785147633083370835315697 71088860724812528126486773)
  ·
    refine ⟨6664580692951174511858135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71088860724812528126486773 6664580692951174511858135)
    ·
      refine ⟨9996871039426761767787203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6664580692951174511858135 9996871039426761767787203)
      ·
        refine ⟨14995306559140142651680805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9996871039426761767787203 14995306559140142651680805)
        ·
          refine ⟨2811619979838776747190151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14995306559140142651680805 2811619979838776747190151)
          ·
            refine ⟨4217429969758165120785227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811619979838776747190151 4217429969758165120785227)
            ·
              refine ⟨6326144954637247681177841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217429969758165120785227 6326144954637247681177841)
              ·
                refine ⟨4744608715977935760883381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6326144954637247681177841 4744608715977935760883381)
                ·
                  refine ⟨444807067122931477582817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4744608715977935760883381 444807067122931477582817)
                  ·
                    rfl

theorem cell22_3898164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_3898164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898164 prefixEnd_3898164 := by exact prefixLift 3898164
  have htrace : WordTrace (prefixWord ++ tailWord_3898164) baseStart_3898164 baseEnd_3898164 := by
    simpa [prefixWord, tailWord_3898164, baseEnd_3898164] using wordTrace_append hprefix tailTrace_3898164
  have hstable : (prefixWord ++ tailWord_3898164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898164).length < 2 ^ (prefixWord ++ tailWord_3898164).sum := by decide
  have hdescent : baseEnd_3898164 < baseStart_3898164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898175 : List Nat := [1, 1, 2, 2, 5, 1, 2, 4, 4]
def baseStart_3898175 : Nat := 118140960795 + 3898175 * 2 ^ 59
def prefixEnd_3898175 : Nat := 4983230072969 + 3 ^ 40 * 3898175 * 2
def baseEnd_3898175 : Nat := 444808322297864690241139

theorem tailTrace_3898175 : CollatzResearch.WordTrace tailWord_3898175 prefixEnd_3898175 444808322297864690241139 := by
  unfold tailWord_3898175
  simp only [CollatzResearch.WordTrace]
  refine ⟨142178122652585205131623979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94785415101723470087749319 142178122652585205131623979)
  ·
    refine ⟨213267183978877807697435969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142178122652585205131623979 213267183978877807697435969)
    ·
      refine ⟨159950387984158355773076977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213267183978877807697435969 159950387984158355773076977)
      ·
        refine ⟨119962790988118766829807733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159950387984158355773076977 119962790988118766829807733)
        ·
          refine ⟨11246511655136134390294475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119962790988118766829807733 11246511655136134390294475)
          ·
            refine ⟨16869767482704201585441713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11246511655136134390294475 16869767482704201585441713)
            ·
              refine ⟨12652325612028151189081285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16869767482704201585441713 12652325612028151189081285)
              ·
                refine ⟨2372311052255278347952741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12652325612028151189081285 2372311052255278347952741)
                ·
                  refine ⟨444808322297864690241139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2372311052255278347952741 444808322297864690241139)
                  ·
                    rfl

theorem cell22_3898175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 4].length) (baseStart_3898175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898175 prefixEnd_3898175 := by exact prefixLift 3898175
  have htrace : WordTrace (prefixWord ++ tailWord_3898175) baseStart_3898175 baseEnd_3898175 := by
    simpa [prefixWord, tailWord_3898175, baseEnd_3898175] using wordTrace_append hprefix tailTrace_3898175
  have hstable : (prefixWord ++ tailWord_3898175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898175).length < 2 ^ (prefixWord ++ tailWord_3898175).sum := by decide
  have hdescent : baseEnd_3898175 < baseStart_3898175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898188 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_3898188 : Nat := 118140960795 + 3898188 * 2 ^ 59
def prefixEnd_3898188 : Nat := 4983230072969 + 3 ^ 40 * 3898188 * 2
def baseEnd_3898188 : Nat := 1334429417059266370148377

theorem tailTrace_3898188 : CollatzResearch.WordTrace tailWord_3898188 prefixEnd_3898188 1334429417059266370148377 := by
  unfold tailWord_3898188
  simp only [CollatzResearch.WordTrace]
  refine ⟨71089298400769054175923609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94785731201025405567898145 71089298400769054175923609)
  ·
    refine ⟨53316973800576790631942707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71089298400769054175923609 53316973800576790631942707)
    ·
      refine ⟨79975460700865185947914061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53316973800576790631942707 79975460700865185947914061)
      ·
        refine ⟨29990797762824444730467773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79975460700865185947914061 29990797762824444730467773)
        ·
          refine ⟨11246549161059166773925415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29990797762824444730467773 11246549161059166773925415)
          ·
            refine ⟨16869823741588750160888123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11246549161059166773925415 16869823741588750160888123)
            ·
              refine ⟨25304735612383125241332185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16869823741588750160888123 25304735612383125241332185)
              ·
                refine ⟨18978551709287343930999139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25304735612383125241332185 18978551709287343930999139)
                ·
                  refine ⟨28467827563931015896498709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18978551709287343930999139 28467827563931015896498709)
                  ·
                    refine ⟨1334429417059266370148377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28467827563931015896498709 1334429417059266370148377)
                    ·
                      rfl

theorem cell22_3898188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_3898188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898188 prefixEnd_3898188 := by exact prefixLift 3898188
  have htrace : WordTrace (prefixWord ++ tailWord_3898188) baseStart_3898188 baseEnd_3898188 := by
    simpa [prefixWord, tailWord_3898188, baseEnd_3898188] using wordTrace_append hprefix tailTrace_3898188
  have hstable : (prefixWord ++ tailWord_3898188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898188).length < 2 ^ (prefixWord ++ tailWord_3898188).sum := by decide
  have hdescent : baseEnd_3898188 < baseStart_3898188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898190 : List Nat := [4, 1, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_3898190 : Nat := 118140960795 + 3898190 * 2 ^ 59
def prefixEnd_3898190 : Nat := 4983230072969 + 3 ^ 40 * 3898190 * 2
def baseEnd_3898190 : Nat := 1334430101700139031598371

theorem tailTrace_3898190 : CollatzResearch.WordTrace tailWord_3898190 prefixEnd_3898190 1334430101700139031598371 := by
  unfold tailWord_3898190
  simp only [CollatzResearch.WordTrace]
  refine ⟨17772333718441357836677503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94785779831687241795613349 17772333718441357836677503)
  ·
    refine ⟨26658500577662036755016255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17772333718441357836677503 26658500577662036755016255)
    ·
      refine ⟨39987750866493055132524383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26658500577662036755016255 39987750866493055132524383)
      ·
        refine ⟨59981626299739582698786575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39987750866493055132524383 59981626299739582698786575)
        ·
          refine ⟨89972439449609374048179863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59981626299739582698786575 89972439449609374048179863)
          ·
            refine ⟨134958659174414061072269795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89972439449609374048179863 134958659174414061072269795)
            ·
              refine ⟨202437988761621091608404693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134958659174414061072269795 202437988761621091608404693)
              ·
                refine ⟨4744640361600494334571985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 202437988761621091608404693 4744640361600494334571985)
                ·
                  refine ⟨3558480271200370750928989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4744640361600494334571985 3558480271200370750928989)
                  ·
                    refine ⟨1334430101700139031598371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3558480271200370750928989 1334430101700139031598371)
                    ·
                      rfl

theorem cell22_3898190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_3898190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898190 prefixEnd_3898190 := by exact prefixLift 3898190
  have htrace : WordTrace (prefixWord ++ tailWord_3898190) baseStart_3898190 baseEnd_3898190 := by
    simpa [prefixWord, tailWord_3898190, baseEnd_3898190] using wordTrace_append hprefix tailTrace_3898190
  have hstable : (prefixWord ++ tailWord_3898190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898190).length < 2 ^ (prefixWord ++ tailWord_3898190).sum := by decide
  have hdescent : baseEnd_3898190 < baseStart_3898190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898222 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_3898222 : Nat := 118140960795 + 3898222 * 2 ^ 59
def prefixEnd_3898222 : Nat := 4983230072969 + 3 ^ 40 * 3898222 * 2
def baseEnd_3898222 : Nat := 1334441055954101614798273

theorem tailTrace_3898222 : CollatzResearch.WordTrace tailWord_3898222 prefixEnd_3898222 1334441055954101614798273 := by
  unfold tailWord_3898222
  simp only [CollatzResearch.WordTrace]
  refine ⟨17772479610426866519823115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94786557922276621439056613 17772479610426866519823115)
  ·
    refine ⟨26658719415640299779734673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17772479610426866519823115 26658719415640299779734673)
    ·
      refine ⟨19994039561730224834801005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26658719415640299779734673 19994039561730224834801005)
      ·
        refine ⟨7497764835648834313050377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19994039561730224834801005 7497764835648834313050377)
        ·
          refine ⟨5623323626736625734787783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7497764835648834313050377 5623323626736625734787783)
          ·
            refine ⟨8434985440104938602181675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5623323626736625734787783 8434985440104938602181675)
            ·
              refine ⟨12652478160157407903272513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8434985440104938602181675 12652478160157407903272513)
              ·
                refine ⟨9489358620118055927454385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12652478160157407903272513 9489358620118055927454385)
                ·
                  refine ⟨7117018965088541945590789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9489358620118055927454385 7117018965088541945590789)
                  ·
                    refine ⟨1334441055954101614798273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7117018965088541945590789 1334441055954101614798273)
                    ·
                      rfl

theorem cell22_3898222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_3898222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898222 prefixEnd_3898222 := by exact prefixLift 3898222
  have htrace : WordTrace (prefixWord ++ tailWord_3898222) baseStart_3898222 baseEnd_3898222 := by
    simpa [prefixWord, tailWord_3898222, baseEnd_3898222] using wordTrace_append hprefix tailTrace_3898222
  have hstable : (prefixWord ++ tailWord_3898222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898222).length < 2 ^ (prefixWord ++ tailWord_3898222).sum := by decide
  have hdescent : baseEnd_3898222 < baseStart_3898222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898235 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 3, 3]
def baseStart_3898235 : Nat := 118140960795 + 3898235 * 2 ^ 59
def prefixEnd_3898235 : Nat := 4983230072969 + 3 ^ 40 * 3898235 * 2
def baseEnd_3898235 : Nat := 1334445506119773914223233

theorem tailTrace_3898235 : CollatzResearch.WordTrace tailWord_3898235 prefixEnd_3898235 1334445506119773914223233 := by
  unfold tailWord_3898235
  simp only [CollatzResearch.WordTrace]
  refine ⟨142180311032367835378808159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94786874021578556919205439 142180311032367835378808159)
  ·
    refine ⟨213270466548551753068212239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142180311032367835378808159 213270466548551753068212239)
    ·
      refine ⟨319905699822827629602318359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213270466548551753068212239 319905699822827629602318359)
      ·
        refine ⟨479858549734241444403477539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319905699822827629602318359 479858549734241444403477539)
        ·
          refine ⟨719787824601362166605216309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479858549734241444403477539 719787824601362166605216309)
          ·
            refine ⟨67480108556377703119239029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 719787824601362166605216309 67480108556377703119239029)
            ·
              refine ⟨6326260177160409667428659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67480108556377703119239029 6326260177160409667428659)
              ·
                refine ⟨9489390265740614501142989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6326260177160409667428659 9489390265740614501142989)
                ·
                  refine ⟨3558521349652730437928621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9489390265740614501142989 3558521349652730437928621)
                  ·
                    refine ⟨1334445506119773914223233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3558521349652730437928621 1334445506119773914223233)
                    ·
                      rfl

theorem cell22_3898235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 3].length) (baseStart_3898235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898235 prefixEnd_3898235 := by exact prefixLift 3898235
  have htrace : WordTrace (prefixWord ++ tailWord_3898235) baseStart_3898235 baseEnd_3898235 := by
    simpa [prefixWord, tailWord_3898235, baseEnd_3898235] using wordTrace_append hprefix tailTrace_3898235
  have hstable : (prefixWord ++ tailWord_3898235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898235).length < 2 ^ (prefixWord ++ tailWord_3898235).sum := by decide
  have hdescent : baseEnd_3898235 < baseStart_3898235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898329 : List Nat := [1, 2, 1, 2, 5, 3, 2, 1, 1, 4]
def baseStart_3898329 : Nat := 118140960795 + 3898329 * 2 ^ 59
def prefixEnd_3898329 : Nat := 4983230072969 + 3 ^ 40 * 3898329 * 2
def baseEnd_3898329 : Nat := 1334477684240789002372945

theorem tailTrace_3898329 : CollatzResearch.WordTrace tailWord_3898329 prefixEnd_3898329 1334477684240789002372945 := by
  unfold tailWord_3898329
  simp only [CollatzResearch.WordTrace]
  refine ⟨142183739494027289432730041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94789159662684859621820027 142183739494027289432730041)
  ·
    refine ⟨106637804620520467074547531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142183739494027289432730041 106637804620520467074547531)
    ·
      refine ⟨159956706930780700611821297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106637804620520467074547531 159956706930780700611821297)
      ·
        refine ⟨119967530198085525458865973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159956706930780700611821297 119967530198085525458865973)
        ·
          refine ⟨11246955956070518011768685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119967530198085525458865973 11246955956070518011768685)
          ·
            refine ⟨4217608483526444254413257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11246955956070518011768685 4217608483526444254413257)
            ·
              refine ⟨3163206362644833190809943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4217608483526444254413257 3163206362644833190809943)
              ·
                refine ⟨4744809543967249786214915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3163206362644833190809943 4744809543967249786214915)
                ·
                  refine ⟨7117214315950874679322373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744809543967249786214915 7117214315950874679322373)
                  ·
                    refine ⟨1334477684240789002372945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7117214315950874679322373 1334477684240789002372945)
                    ·
                      rfl

theorem cell22_3898329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 1, 4].length) (baseStart_3898329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898329 prefixEnd_3898329 := by exact prefixLift 3898329
  have htrace : WordTrace (prefixWord ++ tailWord_3898329) baseStart_3898329 baseEnd_3898329 := by
    simpa [prefixWord, tailWord_3898329, baseEnd_3898329] using wordTrace_append hprefix tailTrace_3898329
  have hstable : (prefixWord ++ tailWord_3898329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898329).length < 2 ^ (prefixWord ++ tailWord_3898329).sum := by decide
  have hdescent : baseEnd_3898329 < baseStart_3898329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898368 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 3, 8]
def baseStart_3898368 : Nat := 118140960795 + 3898368 * 2 ^ 59
def prefixEnd_3898368 : Nat := 4983230072969 + 3 ^ 40 * 3898368 * 2
def baseEnd_3898368 : Nat := 1334491034737805900647825

theorem tailTrace_3898368 : CollatzResearch.WordTrace tailWord_3898368 prefixEnd_3898368 1334491034737805900647825 := by
  unfold tailWord_3898368
  simp only [CollatzResearch.WordTrace]
  refine ⟨71092580970442999546699879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94790107960590666062266505 71092580970442999546699879)
  ·
    refine ⟨106638871455664499320049819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71092580970442999546699879 106638871455664499320049819)
    ·
      refine ⟨159958307183496748980074729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106638871455664499320049819 159958307183496748980074729)
      ·
        refine ⟨119968730387622561735056047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159958307183496748980074729 119968730387622561735056047)
        ·
          refine ⟨179953095581433842602584071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119968730387622561735056047 179953095581433842602584071)
          ·
            refine ⟨269929643372150763903876107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179953095581433842602584071 269929643372150763903876107)
            ·
              refine ⟨404894465058226145855814161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269929643372150763903876107 404894465058226145855814161)
              ·
                refine ⟨303670848793669609391860621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404894465058226145855814161 303670848793669609391860621)
                ·
                  refine ⟨113876568297626103521947733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303670848793669609391860621 113876568297626103521947733)
                  ·
                    refine ⟨1334491034737805900647825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113876568297626103521947733 1334491034737805900647825)
                    ·
                      rfl

theorem cell22_3898368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_3898368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898368 prefixEnd_3898368 := by exact prefixLift 3898368
  have htrace : WordTrace (prefixWord ++ tailWord_3898368) baseStart_3898368 baseEnd_3898368 := by
    simpa [prefixWord, tailWord_3898368, baseEnd_3898368] using wordTrace_append hprefix tailTrace_3898368
  have hstable : (prefixWord ++ tailWord_3898368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898368).length < 2 ^ (prefixWord ++ tailWord_3898368).sum := by decide
  have hdescent : baseEnd_3898368 < baseStart_3898368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898404 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_3898404 : Nat := 118140960795 + 3898404 * 2 ^ 59
def prefixEnd_3898404 : Nat := 4983230072969 + 3 ^ 40 * 3898404 * 2
def baseEnd_3898404 : Nat := 1334503358273513806747715

theorem tailTrace_3898404 : CollatzResearch.WordTrace tailWord_3898404 prefixEnd_3898404 1334503358273513806747715 := by
  unfold tailWord_3898404
  simp only [CollatzResearch.WordTrace]
  refine ⟨71093237484377788620855133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94790983312503718161140177 71093237484377788620855133)
  ·
    refine ⟨26659964056641670732820675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71093237484377788620855133 26659964056641670732820675)
    ·
      refine ⟨39989946084962506099231013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26659964056641670732820675 39989946084962506099231013)
      ·
        refine ⟨7498114890930469893605815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39989946084962506099231013 7498114890930469893605815)
        ·
          refine ⟨11247172336395704840408723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7498114890930469893605815 11247172336395704840408723)
          ·
            refine ⟨16870758504593557260613085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11247172336395704840408723 16870758504593557260613085)
            ·
              refine ⟨6326534439222583972729907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16870758504593557260613085 6326534439222583972729907)
              ·
                refine ⟨9489801658833875959094861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6326534439222583972729907 9489801658833875959094861)
                ·
                  refine ⟨3558675622062703484660573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9489801658833875959094861 3558675622062703484660573)
                  ·
                    refine ⟨1334503358273513806747715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3558675622062703484660573 1334503358273513806747715)
                    ·
                      rfl

theorem cell22_3898404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_3898404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898404 prefixEnd_3898404 := by exact prefixLift 3898404
  have htrace : WordTrace (prefixWord ++ tailWord_3898404) baseStart_3898404 baseEnd_3898404 := by
    simpa [prefixWord, tailWord_3898404, baseEnd_3898404] using wordTrace_append hprefix tailTrace_3898404
  have hstable : (prefixWord ++ tailWord_3898404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898404).length < 2 ^ (prefixWord ++ tailWord_3898404).sum := by decide
  have hdescent : baseEnd_3898404 < baseStart_3898404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898477 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3898477 : Nat := 118140960795 + 3898477 * 2 ^ 59
def prefixEnd_3898477 : Nat := 4983230072969 + 3 ^ 40 * 3898477 * 2
def baseEnd_3898477 : Nat := 1334528347665365949672491

theorem tailTrace_3898477 : CollatzResearch.WordTrace tailWord_3898477 prefixEnd_3898477 1334528347665365949672491 := by
  unfold tailWord_3898477
  simp only [CollatzResearch.WordTrace]
  refine ⟨142189137497491110709117685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94792758331660740472745123 142189137497491110709117685)
  ·
    refine ⟨13330231640389791628979783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142189137497491110709117685 13330231640389791628979783)
    ·
      refine ⟨19995347460584687443469675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13330231640389791628979783 19995347460584687443469675)
      ·
        refine ⟨29993021190877031165204513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19995347460584687443469675 29993021190877031165204513)
        ·
          refine ⟨22494765893157773373903385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29993021190877031165204513 22494765893157773373903385)
          ·
            refine ⟨16871074419868330030427539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22494765893157773373903385 16871074419868330030427539)
            ·
              refine ⟨25306611629802495045641309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16871074419868330030427539 25306611629802495045641309)
              ·
                refine ⟨9489979361175935642115491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25306611629802495045641309 9489979361175935642115491)
                ·
                  refine ⟨14234969041763903463173237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9489979361175935642115491 14234969041763903463173237)
                  ·
                    refine ⟨1334528347665365949672491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14234969041763903463173237 1334528347665365949672491)
                    ·
                      rfl

theorem cell22_3898477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3898477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898477 prefixEnd_3898477 := by exact prefixLift 3898477
  have htrace : WordTrace (prefixWord ++ tailWord_3898477) baseStart_3898477 baseEnd_3898477 := by
    simpa [prefixWord, tailWord_3898477, baseEnd_3898477] using wordTrace_append hprefix tailTrace_3898477
  have hstable : (prefixWord ++ tailWord_3898477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898477).length < 2 ^ (prefixWord ++ tailWord_3898477).sum := by decide
  have hdescent : baseEnd_3898477 < baseStart_3898477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898541 : List Nat := [1, 5, 2, 1, 3, 2, 2, 6]
def baseStart_3898541 : Nat := 118140960795 + 3898541 * 2 ^ 59
def prefixEnd_3898541 : Nat := 4983230072969 + 3 ^ 40 * 3898541 * 2
def baseEnd_3898541 : Nat := 148283361797032346230255

theorem tailTrace_3898541 : CollatzResearch.WordTrace tailWord_3898541 prefixEnd_3898541 148283361797032346230255 := by
  unfold tailWord_3898541
  simp only [CollatzResearch.WordTrace]
  refine ⟨142191471769259249639447477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94794314512839499759631651 142191471769259249639447477)
  ·
    refine ⟨13330450478368054653698201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142191471769259249639447477 13330450478368054653698201)
    ·
      refine ⟨9997837858776040990273651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13330450478368054653698201 9997837858776040990273651)
      ·
        refine ⟨14996756788164061485410477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9997837858776040990273651 14996756788164061485410477)
        ·
          refine ⟨5623783795561523057028929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14996756788164061485410477 5623783795561523057028929)
          ·
            refine ⟨4217837846671142292771697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5623783795561523057028929 4217837846671142292771697)
            ·
              refine ⟨3163378385003356719578773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4217837846671142292771697 3163378385003356719578773)
              ·
                refine ⟨148283361797032346230255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3163378385003356719578773 148283361797032346230255)
                ·
                  rfl

theorem cell22_3898541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 6].length) (baseStart_3898541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898541 prefixEnd_3898541 := by exact prefixLift 3898541
  have htrace : WordTrace (prefixWord ++ tailWord_3898541) baseStart_3898541 baseEnd_3898541 := by
    simpa [prefixWord, tailWord_3898541, baseEnd_3898541] using wordTrace_append hprefix tailTrace_3898541
  have hstable : (prefixWord ++ tailWord_3898541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898541).length < 2 ^ (prefixWord ++ tailWord_3898541).sum := by decide
  have hdescent : baseEnd_3898541 < baseStart_3898541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898659 : List Nat := [1, 1, 1, 4, 2, 4, 3, 6]
def baseStart_3898659 : Nat := 118140960795 + 3898659 * 2 ^ 59
def prefixEnd_3898659 : Nat := 4983230072969 + 3 ^ 40 * 3898659 * 2
def baseEnd_3898659 : Nat := 148287849998308682402437

theorem tailTrace_3898659 : CollatzResearch.WordTrace tailWord_3898659 prefixEnd_3898659 148287849998308682402437 := by
  unfold tailWord_3898659
  simp only [CollatzResearch.WordTrace]
  refine ⟨142195775582831755792243031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94797183721887837194828687 142195775582831755792243031)
  ·
    refine ⟨213293663374247633688364547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142195775582831755792243031 213293663374247633688364547)
    ·
      refine ⟨319940495061371450532546821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213293663374247633688364547 319940495061371450532546821)
      ·
        refine ⟨59988842824007146974852529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319940495061371450532546821 59988842824007146974852529)
        ·
          refine ⟨44991632118005360231139397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59988842824007146974852529 44991632118005360231139397)
          ·
            refine ⟨8435931022126005043338637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44991632118005360231139397 8435931022126005043338637)
            ·
              refine ⟨3163474133297251891251989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8435931022126005043338637 3163474133297251891251989)
              ·
                refine ⟨148287849998308682402437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3163474133297251891251989 148287849998308682402437)
                ·
                  rfl

theorem cell22_3898659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 6].length) (baseStart_3898659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898659 prefixEnd_3898659 := by exact prefixLift 3898659
  have htrace : WordTrace (prefixWord ++ tailWord_3898659) baseStart_3898659 baseEnd_3898659 := by
    simpa [prefixWord, tailWord_3898659, baseEnd_3898659] using wordTrace_append hprefix tailTrace_3898659
  have hstable : (prefixWord ++ tailWord_3898659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898659).length < 2 ^ (prefixWord ++ tailWord_3898659).sum := by decide
  have hdescent : baseEnd_3898659 < baseStart_3898659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898661 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 2, 4]
def baseStart_3898661 : Nat := 118140960795 + 3898661 * 2 ^ 59
def prefixEnd_3898661 : Nat := 4983230072969 + 3 ^ 40 * 3898661 * 2
def baseEnd_3898661 : Nat := 1334591334625650803071927

theorem tailTrace_3898661 : CollatzResearch.WordTrace tailWord_3898661 prefixEnd_3898661 1334591334625650803071927 := by
  unfold tailWord_3898661
  simp only [CollatzResearch.WordTrace]
  refine ⟨142195848528824510133815837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94797232352549673422543891 142195848528824510133815837)
  ·
    refine ⟨53323443198309191300180939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142195848528824510133815837 53323443198309191300180939)
    ·
      refine ⟨79985164797463786950271409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53323443198309191300180939 79985164797463786950271409)
      ·
        refine ⟨59988873598097840212703557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79985164797463786950271409 59988873598097840212703557)
        ·
          refine ⟨11247913799643345039881917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59988873598097840212703557 11247913799643345039881917)
          ·
            refine ⟨4217967674866254389955719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11247913799643345039881917 4217967674866254389955719)
            ·
              refine ⟨6326951512299381584933579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217967674866254389955719 6326951512299381584933579)
              ·
                refine ⟨9490427268449072377400369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6326951512299381584933579 9490427268449072377400369)
                ·
                  refine ⟨7117820451336804283050277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9490427268449072377400369 7117820451336804283050277)
                  ·
                    refine ⟨1334591334625650803071927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7117820451336804283050277 1334591334625650803071927)
                    ·
                      rfl

theorem cell22_3898661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_3898661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898661 prefixEnd_3898661 := by exact prefixLift 3898661
  have htrace : WordTrace (prefixWord ++ tailWord_3898661) baseStart_3898661 baseEnd_3898661 := by
    simpa [prefixWord, tailWord_3898661, baseEnd_3898661] using wordTrace_append hprefix tailTrace_3898661
  have hstable : (prefixWord ++ tailWord_3898661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898661).length < 2 ^ (prefixWord ++ tailWord_3898661).sum := by decide
  have hdescent : baseEnd_3898661 < baseStart_3898661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898710 : List Nat := [5, 2, 3, 1, 1, 1, 1, 8]
def baseStart_3898710 : Nat := 118140960795 + 3898710 * 2 ^ 59
def prefixEnd_3898710 : Nat := 4983230072969 + 3 ^ 40 * 3898710 * 2
def baseEnd_3898710 : Nat := 148289789814114556510753

theorem tailTrace_3898710 : CollatzResearch.WordTrace tailWord_3898710 prefixEnd_3898710 148289789814114556510753 := by
  unfold tailWord_3898710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8887352231602936968896849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94798423803764661001566389 8887352231602936968896849)
  ·
    refine ⟨6665514173702202726672637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8887352231602936968896849 6665514173702202726672637)
    ·
      refine ⟨2499567815138326022502239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6665514173702202726672637 2499567815138326022502239)
      ·
        refine ⟨3749351722707489033753359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499567815138326022502239 3749351722707489033753359)
        ·
          refine ⟨5624027584061233550630039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3749351722707489033753359 5624027584061233550630039)
          ·
            refine ⟨8436041376091850325945059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624027584061233550630039 8436041376091850325945059)
            ·
              refine ⟨12654062064137775488917589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8436041376091850325945059 12654062064137775488917589)
              ·
                refine ⟨148289789814114556510753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12654062064137775488917589 148289789814114556510753)
                ·
                  rfl

theorem cell22_3898710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_3898710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898710 prefixEnd_3898710 := by exact prefixLift 3898710
  have htrace : WordTrace (prefixWord ++ tailWord_3898710) baseStart_3898710 baseEnd_3898710 := by
    simpa [prefixWord, tailWord_3898710, baseEnd_3898710] using wordTrace_append hprefix tailTrace_3898710
  have hstable : (prefixWord ++ tailWord_3898710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898710).length < 2 ^ (prefixWord ++ tailWord_3898710).sum := by decide
  have hdescent : baseEnd_3898710 < baseStart_3898710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898764 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_3898764 : Nat := 118140960795 + 3898764 * 2 ^ 59
def prefixEnd_3898764 : Nat := 4983230072969 + 3 ^ 40 * 3898764 * 2
def baseEnd_3898764 : Nat := 1334626593630592867746611

theorem tailTrace_3898764 : CollatzResearch.WordTrace tailWord_3898764 prefixEnd_3898764 1334626593630592867746611 := by
  unfold tailWord_3898764
  simp only [CollatzResearch.WordTrace]
  refine ⟨71099802623725679362407673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94799736831634239149876897 71099802623725679362407673)
  ·
    refine ⟨53324851967794259521805755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71099802623725679362407673 53324851967794259521805755)
    ·
      refine ⟨79987277951691389282708633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53324851967794259521805755 79987277951691389282708633)
      ·
        refine ⟨59990458463768541962031475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79987277951691389282708633 59990458463768541962031475)
        ·
          refine ⟨89985687695652812943047213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59990458463768541962031475 89985687695652812943047213)
          ·
            refine ⟨33744632885869804853642705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89985687695652812943047213 33744632885869804853642705)
            ·
              refine ⟨25308474664402353640232029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33744632885869804853642705 25308474664402353640232029)
              ·
                refine ⟨9490677999150882615087011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25308474664402353640232029 9490677999150882615087011)
                ·
                  refine ⟨14236016998726323922630517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9490677999150882615087011 14236016998726323922630517)
                  ·
                    refine ⟨1334626593630592867746611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14236016998726323922630517 1334626593630592867746611)
                    ·
                      rfl

theorem cell22_3898764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_3898764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898764 prefixEnd_3898764 := by exact prefixLift 3898764
  have htrace : WordTrace (prefixWord ++ tailWord_3898764) baseStart_3898764 baseEnd_3898764 := by
    simpa [prefixWord, tailWord_3898764, baseEnd_3898764] using wordTrace_append hprefix tailTrace_3898764
  have hstable : (prefixWord ++ tailWord_3898764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898764).length < 2 ^ (prefixWord ++ tailWord_3898764).sum := by decide
  have hdescent : baseEnd_3898764 < baseStart_3898764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898781 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3898781 : Nat := 118140960795 + 3898781 * 2 ^ 59
def prefixEnd_3898781 : Nat := 4983230072969 + 3 ^ 40 * 3898781 * 2
def baseEnd_3898781 : Nat := 1334632413078010490071559

theorem tailTrace_3898781 : CollatzResearch.WordTrace tailWord_3898781 prefixEnd_3898781 1334632413078010490071559 := by
  unfold tailWord_3898781
  simp only [CollatzResearch.WordTrace]
  refine ⟨142200225288389770628184197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94800150192259847085456131 142200225288389770628184197)
  ·
    refine ⟨26662542241573081992784537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142200225288389770628184197 26662542241573081992784537)
    ·
      refine ⟨19996906681179811494588403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26662542241573081992784537 19996906681179811494588403)
      ·
        refine ⟨29995360021769717241882605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19996906681179811494588403 29995360021769717241882605)
        ·
          refine ⟨11248260008163643965705977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29995360021769717241882605 11248260008163643965705977)
          ·
            refine ⟨8436195006122732974279483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11248260008163643965705977 8436195006122732974279483)
            ·
              refine ⟨12654292509184099461419225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8436195006122732974279483 12654292509184099461419225)
              ·
                refine ⟨9490719381888074596064419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12654292509184099461419225 9490719381888074596064419)
                ·
                  refine ⟨14236079072832111894096629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9490719381888074596064419 14236079072832111894096629)
                  ·
                    refine ⟨1334632413078010490071559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14236079072832111894096629 1334632413078010490071559)
                    ·
                      rfl

theorem cell22_3898781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3898781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898781 prefixEnd_3898781 := by exact prefixLift 3898781
  have htrace : WordTrace (prefixWord ++ tailWord_3898781) baseStart_3898781 baseEnd_3898781 := by
    simpa [prefixWord, tailWord_3898781, baseEnd_3898781] using wordTrace_append hprefix tailTrace_3898781
  have hstable : (prefixWord ++ tailWord_3898781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898781).length < 2 ^ (prefixWord ++ tailWord_3898781).sum := by decide
  have hdescent : baseEnd_3898781 < baseStart_3898781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898824 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 2, 6]
def baseStart_3898824 : Nat := 118140960795 + 3898824 * 2 ^ 59
def prefixEnd_3898824 : Nat := 4983230072969 + 3 ^ 40 * 3898824 * 2
def baseEnd_3898824 : Nat := 1334647132856772711246427

theorem tailTrace_3898824 : CollatzResearch.WordTrace tailWord_3898824 prefixEnd_3898824 1334647132856772711246427 := by
  unfold tailWord_3898824
  simp only [CollatzResearch.WordTrace]
  refine ⟨71100896813616994485999763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94801195751489325981333017 71100896813616994485999763)
  ·
    refine ⟨106651345220425491728999645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71100896813616994485999763 106651345220425491728999645)
    ·
      refine ⟨39994254457659559398374867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106651345220425491728999645 39994254457659559398374867)
      ·
        refine ⟨59991381686489339097562301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39994254457659559398374867 59991381686489339097562301)
        ·
          refine ⟨22496768132433502161585863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59991381686489339097562301 22496768132433502161585863)
          ·
            refine ⟨33745152198650253242378795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22496768132433502161585863 33745152198650253242378795)
            ·
              refine ⟨50617728297975379863568193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33745152198650253242378795 50617728297975379863568193)
              ·
                refine ⟨37963296223481534897676145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50617728297975379863568193 37963296223481534897676145)
                ·
                  refine ⟨28472472167611151173257109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37963296223481534897676145 28472472167611151173257109)
                  ·
                    refine ⟨1334647132856772711246427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28472472167611151173257109 1334647132856772711246427)
                    ·
                      rfl

theorem cell22_3898824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_3898824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898824 prefixEnd_3898824 := by exact prefixLift 3898824
  have htrace : WordTrace (prefixWord ++ tailWord_3898824) baseStart_3898824 baseEnd_3898824 := by
    simpa [prefixWord, tailWord_3898824, baseEnd_3898824] using wordTrace_append hprefix tailTrace_3898824
  have hstable : (prefixWord ++ tailWord_3898824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898824).length < 2 ^ (prefixWord ++ tailWord_3898824).sum := by decide
  have hdescent : baseEnd_3898824 < baseStart_3898824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898826 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 5, 3]
def baseStart_3898826 : Nat := 118140960795 + 3898826 * 2 ^ 59
def prefixEnd_3898826 : Nat := 4983230072969 + 3 ^ 40 * 3898826 * 2
def baseEnd_3898826 : Nat := 1334647817497645372696421

theorem tailTrace_3898826 : CollatzResearch.WordTrace tailWord_3898826 prefixEnd_3898826 1334647817497645372696421 := by
  unfold tailWord_3898826
  simp only [CollatzResearch.WordTrace]
  refine ⟨35550466643306685828393083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94801244382151162209048221 35550466643306685828393083)
  ·
    refine ⟨53325699964960028742589625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35550466643306685828393083 53325699964960028742589625)
    ·
      refine ⟨39994274973720021556942219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53325699964960028742589625 39994274973720021556942219)
      ·
        refine ⟨59991412460580032335413329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39994274973720021556942219 59991412460580032335413329)
        ·
          refine ⟨44993559345435024251559997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59991412460580032335413329 44993559345435024251559997)
          ·
            refine ⟨16872584754538134094334999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44993559345435024251559997 16872584754538134094334999)
            ·
              refine ⟨25308877131807201141502499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16872584754538134094334999 25308877131807201141502499)
              ·
                refine ⟨37963315697710801712253749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25308877131807201141502499 37963315697710801712253749)
                ·
                  refine ⟨3559060846660387660523789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37963315697710801712253749 3559060846660387660523789)
                  ·
                    refine ⟨1334647817497645372696421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3559060846660387660523789 1334647817497645372696421)
                    ·
                      rfl

theorem cell22_3898826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_3898826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898826 prefixEnd_3898826 := by exact prefixLift 3898826
  have htrace : WordTrace (prefixWord ++ tailWord_3898826) baseStart_3898826 baseEnd_3898826 := by
    simpa [prefixWord, tailWord_3898826, baseEnd_3898826] using wordTrace_append hprefix tailTrace_3898826
  have hstable : (prefixWord ++ tailWord_3898826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898826).length < 2 ^ (prefixWord ++ tailWord_3898826).sum := by decide
  have hdescent : baseEnd_3898826 < baseStart_3898826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898894 : List Nat := [4, 1, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_3898894 : Nat := 118140960795 + 3898894 * 2 ^ 59
def prefixEnd_3898894 : Nat := 4983230072969 + 3 ^ 40 * 3898894 * 2
def baseEnd_3898894 : Nat := 1334671095287315861996213

theorem tailTrace_3898894 : CollatzResearch.WordTrace tailWord_3898894 prefixEnd_3898894 1334671095287315861996213 := by
  unfold tailWord_3898894
  simp only [CollatzResearch.WordTrace]
  refine ⟨17775543342122548865880967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94802897824653593951365157 17775543342122548865880967)
  ·
    refine ⟨26663315013183823298821451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17775543342122548865880967 26663315013183823298821451)
    ·
      refine ⟨39994972519775734948232177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26663315013183823298821451 39994972519775734948232177)
      ·
        refine ⟨29996229389831801211174133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39994972519775734948232177 29996229389831801211174133)
        ·
          refine ⟨2812146505296731363547575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29996229389831801211174133 2812146505296731363547575)
          ·
            refine ⟨4218219757945097045321363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812146505296731363547575 4218219757945097045321363)
            ·
              refine ⟨6327329636917645567982045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4218219757945097045321363 6327329636917645567982045)
              ·
                refine ⟨2372748613844117087993267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6327329636917645567982045 2372748613844117087993267)
                ·
                  refine ⟨3559122920766175631989901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372748613844117087993267 3559122920766175631989901)
                  ·
                    refine ⟨1334671095287315861996213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3559122920766175631989901 1334671095287315861996213)
                    ·
                      rfl

theorem cell22_3898894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_3898894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898894 prefixEnd_3898894 := by exact prefixLift 3898894
  have htrace : WordTrace (prefixWord ++ tailWord_3898894) baseStart_3898894 baseEnd_3898894 := by
    simpa [prefixWord, tailWord_3898894, baseEnd_3898894] using wordTrace_append hprefix tailTrace_3898894
  have hstable : (prefixWord ++ tailWord_3898894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898894).length < 2 ^ (prefixWord ++ tailWord_3898894).sum := by decide
  have hdescent : baseEnd_3898894 < baseStart_3898894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899053 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 6]
def baseStart_3899053 : Nat := 118140960795 + 3899053 * 2 ^ 59
def prefixEnd_3899053 : Nat := 4983230072969 + 3 ^ 40 * 3899053 * 2
def baseEnd_3899053 : Nat := 444908508078897482423575

theorem tailTrace_3899053 : CollatzResearch.WordTrace tailWord_3899053 prefixEnd_3899053 444908508078897482423575 := by
  unfold tailWord_3899053
  simp only [CollatzResearch.WordTrace]
  refine ⟨142210145943404361082085813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94806763962269574054723875 142210145943404361082085813)
  ·
    refine ⟨13332201182194158851445545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142210145943404361082085813 13332201182194158851445545)
    ·
      refine ⟨9999150886645619138584159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13332201182194158851445545 9999150886645619138584159)
      ·
        refine ⟨14998726329968428707876239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9999150886645619138584159 14998726329968428707876239)
        ·
          refine ⟨22498089494952643061814359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14998726329968428707876239 22498089494952643061814359)
          ·
            refine ⟨33747134242428964592721539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22498089494952643061814359 33747134242428964592721539)
            ·
              refine ⟨50620701363643446889082309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33747134242428964592721539 50620701363643446889082309)
              ·
                refine ⟨9491381505683146291702933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50620701363643446889082309 9491381505683146291702933)
                ·
                  refine ⟨444908508078897482423575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9491381505683146291702933 444908508078897482423575)
                  ·
                    rfl

theorem cell22_3899053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_3899053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899053 prefixEnd_3899053 := by exact prefixLift 3899053
  have htrace : WordTrace (prefixWord ++ tailWord_3899053) baseStart_3899053 baseEnd_3899053 := by
    simpa [prefixWord, tailWord_3899053, baseEnd_3899053] using wordTrace_append hprefix tailTrace_3899053
  have hstable : (prefixWord ++ tailWord_3899053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899053).length < 2 ^ (prefixWord ++ tailWord_3899053).sum := by decide
  have hdescent : baseEnd_3899053 < baseStart_3899053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899098 : List Nat := [3, 1, 1, 2, 2, 4, 2, 7]
def baseStart_3899098 : Nat := 118140960795 + 3899098 * 2 ^ 59
def prefixEnd_3899098 : Nat := 4983230072969 + 3 ^ 40 * 3899098 * 2
def baseEnd_3899098 : Nat := 148304547628480814432843

theorem tailTrace_3899098 : CollatzResearch.WordTrace tailWord_3899098 prefixEnd_3899098 148304547628480814432843 := by
  unfold tailWord_3899098
  simp only [CollatzResearch.WordTrace]
  refine ⟨35552946807060333441868487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94807858152160889178315965 35552946807060333441868487)
  ·
    refine ⟨53329420210590500162802731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35552946807060333441868487 53329420210590500162802731)
    ·
      refine ⟨79994130315885750244204097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53329420210590500162802731 79994130315885750244204097)
      ·
        refine ⟨59995597736914312683153073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79994130315885750244204097 59995597736914312683153073)
        ·
          refine ⟨44996698302685734512364805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59995597736914312683153073 44996698302685734512364805)
          ·
            refine ⟨8436880931753575221068401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44996698302685734512364805 8436880931753575221068401)
            ·
              refine ⟨6327660698815181415801301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8436880931753575221068401 6327660698815181415801301)
              ·
                refine ⟨148304547628480814432843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6327660698815181415801301 148304547628480814432843)
                ·
                  rfl

theorem cell22_3899098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_3899098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899098 prefixEnd_3899098 := by exact prefixLift 3899098
  have htrace : WordTrace (prefixWord ++ tailWord_3899098) baseStart_3899098 baseEnd_3899098 := by
    simpa [prefixWord, tailWord_3899098, baseEnd_3899098] using wordTrace_append hprefix tailTrace_3899098
  have hstable : (prefixWord ++ tailWord_3899098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899098).length < 2 ^ (prefixWord ++ tailWord_3899098).sum := by decide
  have hdescent : baseEnd_3899098 < baseStart_3899098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899113 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 5, 3]
def baseStart_3899113 : Nat := 118140960795 + 3899113 * 2 ^ 59
def prefixEnd_3899113 : Nat := 4983230072969 + 3 ^ 40 * 3899113 * 2
def baseEnd_3899113 : Nat := 1334746063462872290770541

theorem tailTrace_3899113 : CollatzResearch.WordTrace tailWord_3899113 prefixEnd_3899113 1334746063462872290770541 := by
  unfold tailWord_3899113
  simp only [CollatzResearch.WordTrace]
  refine ⟨142212334323186991329269993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94808222882124660886179995 142212334323186991329269993)
  ·
    refine ⟨106659250742390243496952495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142212334323186991329269993 106659250742390243496952495)
    ·
      refine ⟨159988876113585365245428743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106659250742390243496952495 159988876113585365245428743)
      ·
        refine ⟨239983314170378047868143115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159988876113585365245428743 239983314170378047868143115)
        ·
          refine ⟨359974971255567071802214673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239983314170378047868143115 359974971255567071802214673)
          ·
            refine ⟨269981228441675303851661005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359974971255567071802214673 269981228441675303851661005)
            ·
              refine ⟨101242960665628238944372877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269981228441675303851661005 101242960665628238944372877)
              ·
                refine ⟨37966110249610589604139829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101242960665628238944372877 37966110249610589604139829)
                ·
                  refine ⟨3559322835900992775388109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37966110249610589604139829 3559322835900992775388109)
                  ·
                    refine ⟨1334746063462872290770541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3559322835900992775388109 1334746063462872290770541)
                    ·
                      rfl

theorem cell22_3899113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 3].length) (baseStart_3899113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899113 prefixEnd_3899113 := by exact prefixLift 3899113
  have htrace : WordTrace (prefixWord ++ tailWord_3899113) baseStart_3899113 baseEnd_3899113 := by
    simpa [prefixWord, tailWord_3899113, baseEnd_3899113] using wordTrace_append hprefix tailTrace_3899113
  have hstable : (prefixWord ++ tailWord_3899113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899113).length < 2 ^ (prefixWord ++ tailWord_3899113).sum := by decide
  have hdescent : baseEnd_3899113 < baseStart_3899113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899205 : List Nat := [1, 3, 1, 1, 1, 2, 3, 6, 4]
def baseStart_3899205 : Nat := 118140960795 + 3899205 * 2 ^ 59
def prefixEnd_3899205 : Nat := 4983230072969 + 3 ^ 40 * 3899205 * 2
def baseEnd_3899205 : Nat := 444925852314338239156753

theorem tailTrace_3899205 : CollatzResearch.WordTrace tailWord_3899205 prefixEnd_3899205 444925852314338239156753 := by
  unfold tailWord_3899205
  simp only [CollatzResearch.WordTrace]
  refine ⟨142215689838853691041619069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94810459892569127361079379 142215689838853691041619069)
  ·
    refine ⟨53330883689570134140607151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142215689838853691041619069 53330883689570134140607151)
    ·
      refine ⟨79996325534355201210910727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53330883689570134140607151 79996325534355201210910727)
      ·
        refine ⟨119994488301532801816366091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79996325534355201210910727 119994488301532801816366091)
        ·
          refine ⟨179991732452299202724549137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119994488301532801816366091 179991732452299202724549137)
          ·
            refine ⟨134993799339224402043411853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179991732452299202724549137 134993799339224402043411853)
            ·
              refine ⟨50622674752209150766279445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134993799339224402043411853 50622674752209150766279445)
              ·
                refine ⟨2372937879009803942169349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50622674752209150766279445 2372937879009803942169349)
                ·
                  refine ⟨444925852314338239156753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2372937879009803942169349 444925852314338239156753)
                  ·
                    rfl

theorem cell22_3899205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_3899205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899205 prefixEnd_3899205 := by exact prefixLift 3899205
  have htrace : WordTrace (prefixWord ++ tailWord_3899205) baseStart_3899205 baseEnd_3899205 := by
    simpa [prefixWord, tailWord_3899205, baseEnd_3899205] using wordTrace_append hprefix tailTrace_3899205
  have hstable : (prefixWord ++ tailWord_3899205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899205).length < 2 ^ (prefixWord ++ tailWord_3899205).sum := by decide
  have hdescent : baseEnd_3899205 < baseStart_3899205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899233 : List Nat := [1, 2, 3, 1, 1, 1, 5, 8]
def baseStart_3899233 : Nat := 118140960795 + 3899233 * 2 ^ 59
def prefixEnd_3899233 : Nat := 4983230072969 + 3 ^ 40 * 3899233 * 2
def baseEnd_3899233 : Nat := 148309682435025775307797

theorem tailTrace_3899233 : CollatzResearch.WordTrace tailWord_3899233 prefixEnd_3899233 148309682435025775307797 := by
  unfold tailWord_3899233
  simp only [CollatzResearch.WordTrace]
  refine ⟨142216711082752251823638353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94811140721834834549092235 142216711082752251823638353)
  ·
    refine ⟨106662533312064188867728765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142216711082752251823638353 106662533312064188867728765)
    ·
      refine ⟨39998449992024070825398287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106662533312064188867728765 39998449992024070825398287)
      ·
        refine ⟨59997674988036106238097431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39998449992024070825398287 59997674988036106238097431)
        ·
          refine ⟨89996512482054159357146147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59997674988036106238097431 89996512482054159357146147)
          ·
            refine ⟨134994768723081239035719221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89996512482054159357146147 134994768723081239035719221)
            ·
              refine ⟨12655759567788866159598677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134994768723081239035719221 12655759567788866159598677)
              ·
                refine ⟨148309682435025775307797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12655759567788866159598677 148309682435025775307797)
                ·
                  rfl

theorem cell22_3899233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 8].length) (baseStart_3899233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899233 prefixEnd_3899233 := by exact prefixLift 3899233
  have htrace : WordTrace (prefixWord ++ tailWord_3899233) baseStart_3899233 baseEnd_3899233 := by
    simpa [prefixWord, tailWord_3899233, baseEnd_3899233] using wordTrace_append hprefix tailTrace_3899233
  have hstable : (prefixWord ++ tailWord_3899233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899233).length < 2 ^ (prefixWord ++ tailWord_3899233).sum := by decide
  have hdescent : baseEnd_3899233 < baseStart_3899233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899263 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 2, 6]
def baseStart_3899263 : Nat := 118140960795 + 3899263 * 2 ^ 59
def prefixEnd_3899263 : Nat := 4983230072969 + 3 ^ 40 * 3899263 * 2
def baseEnd_3899263 : Nat := 1334797411528321899520081

theorem tailTrace_3899263 : CollatzResearch.WordTrace tailWord_3899263 prefixEnd_3899263 1334797411528321899520081 := by
  unfold tailWord_3899263
  simp only [CollatzResearch.WordTrace]
  refine ⟨142217805272643566947230443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94811870181762377964820295 142217805272643566947230443)
  ·
    refine ⟨213326707908965350420845665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142217805272643566947230443 213326707908965350420845665)
    ·
      refine ⟨159995030931724012815634249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213326707908965350420845665 159995030931724012815634249)
      ·
        refine ⟨119996273198793009611725687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159995030931724012815634249 119996273198793009611725687)
        ·
          refine ⟨179994409798189514417588531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119996273198793009611725687 179994409798189514417588531)
          ·
            refine ⟨269991614697284271626382797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179994409798189514417588531 269991614697284271626382797)
            ·
              refine ⟨101246855511481601859893549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269991614697284271626382797 101246855511481601859893549)
              ·
                refine ⟨37967570816805600697460081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101246855511481601859893549 37967570816805600697460081)
                ·
                  refine ⟨28475678112604200523095061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37967570816805600697460081 28475678112604200523095061)
                  ·
                    refine ⟨1334797411528321899520081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28475678112604200523095061 1334797411528321899520081)
                    ·
                      rfl

theorem cell22_3899263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_3899263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899263 prefixEnd_3899263 := by exact prefixLift 3899263
  have htrace : WordTrace (prefixWord ++ tailWord_3899263) baseStart_3899263 baseEnd_3899263 := by
    simpa [prefixWord, tailWord_3899263, baseEnd_3899263] using wordTrace_append hprefix tailTrace_3899263
  have hstable : (prefixWord ++ tailWord_3899263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899263).length < 2 ^ (prefixWord ++ tailWord_3899263).sum := by decide
  have hdescent : baseEnd_3899263 < baseStart_3899263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899271 : List Nat := [1, 1, 4, 2, 4, 2, 2, 1, 2, 3]
def baseStart_3899271 : Nat := 118140960795 + 3899271 * 2 ^ 59
def prefixEnd_3899271 : Nat := 4983230072969 + 3 ^ 40 * 3899271 * 2
def baseEnd_3899271 : Nat := 1334800150091812545320057

theorem tailTrace_3899271 : CollatzResearch.WordTrace tailWord_3899271 prefixEnd_3899271 1334800150091812545320057 := by
  unfold tailWord_3899271
  simp only [CollatzResearch.WordTrace]
  refine ⟨142218097056614584313521667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94812064704409722875681111 142218097056614584313521667)
  ·
    refine ⟨213327145584921876470282501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142218097056614584313521667 213327145584921876470282501)
    ·
      refine ⟨39998839797172851838177969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213327145584921876470282501 39998839797172851838177969)
      ·
        refine ⟨29999129847879638878633477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39998839797172851838177969 29999129847879638878633477)
        ·
          refine ⟨5624836846477432289743777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29999129847879638878633477 5624836846477432289743777)
          ·
            refine ⟨4218627634858074217307833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5624836846477432289743777 4218627634858074217307833)
            ·
              refine ⟨3163970726143555662980875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4218627634858074217307833 3163970726143555662980875)
              ·
                refine ⟨4745956089215333494471313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3163970726143555662980875 4745956089215333494471313)
                ·
                  refine ⟨3559467066911500120853485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4745956089215333494471313 3559467066911500120853485)
                  ·
                    refine ⟨1334800150091812545320057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3559467066911500120853485 1334800150091812545320057)
                    ·
                      rfl

theorem cell22_3899271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_3899271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899271 prefixEnd_3899271 := by exact prefixLift 3899271
  have htrace : WordTrace (prefixWord ++ tailWord_3899271) baseStart_3899271 baseEnd_3899271 := by
    simpa [prefixWord, tailWord_3899271, baseEnd_3899271] using wordTrace_append hprefix tailTrace_3899271
  have hstable : (prefixWord ++ tailWord_3899271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899271).length < 2 ^ (prefixWord ++ tailWord_3899271).sum := by decide
  have hdescent : baseEnd_3899271 < baseStart_3899271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899340 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 8]
def baseStart_3899340 : Nat := 118140960795 + 3899340 * 2 ^ 59
def prefixEnd_3899340 : Nat := 4983230072969 + 3 ^ 40 * 3899340 * 2
def baseEnd_3899340 : Nat := 444941256733973121781615

theorem tailTrace_3899340 : CollatzResearch.WordTrace tailWord_3899340 prefixEnd_3899340 444941256733973121781615 := by
  unfold tailWord_3899340
  simp only [CollatzResearch.WordTrace]
  refine ⟨71110306846682304548891737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94813742462243072731855649 71110306846682304548891737)
  ·
    refine ⟨53332730135011728411668803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71110306846682304548891737 53332730135011728411668803)
    ·
      refine ⟨79999095202517592617503205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53332730135011728411668803 79999095202517592617503205)
      ·
        refine ⟨14999830350472048615781851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79999095202517592617503205 14999830350472048615781851)
        ·
          refine ⟨22499745525708072923672777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14999830350472048615781851 22499745525708072923672777)
          ·
            refine ⟨16874809144281054692754583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22499745525708072923672777 16874809144281054692754583)
            ·
              refine ⟨25312213716421582039131875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16874809144281054692754583 25312213716421582039131875)
              ·
                refine ⟨37968320574632373058697813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25312213716421582039131875 37968320574632373058697813)
                ·
                  refine ⟨444941256733973121781615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37968320574632373058697813 444941256733973121781615)
                  ·
                    rfl

theorem cell22_3899340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_3899340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899340 prefixEnd_3899340 := by exact prefixLift 3899340
  have htrace : WordTrace (prefixWord ++ tailWord_3899340) baseStart_3899340 baseEnd_3899340 := by
    simpa [prefixWord, tailWord_3899340, baseEnd_3899340] using wordTrace_append hprefix tailTrace_3899340
  have hstable : (prefixWord ++ tailWord_3899340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899340).length < 2 ^ (prefixWord ++ tailWord_3899340).sum := by decide
  have hdescent : baseEnd_3899340 < baseStart_3899340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899342 : List Nat := [4, 1, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_3899342 : Nat := 118140960795 + 3899342 * 2 ^ 59
def prefixEnd_3899342 : Nat := 4983230072969 + 3 ^ 40 * 3899342 * 2
def baseEnd_3899342 : Nat := 1334824454842792026794839

theorem tailTrace_3899342 : CollatzResearch.WordTrace tailWord_3899342 prefixEnd_3899342 1334824454842792026794839 := by
  unfold tailWord_3899342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17777585829919670429919535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94813791092904908959570853 17777585829919670429919535)
  ·
    refine ⟨26666378744879505644879303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17777585829919670429919535 26666378744879505644879303)
    ·
      refine ⟨39999568117319258467318955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26666378744879505644879303 39999568117319258467318955)
      ·
        refine ⟨59999352175978887700978433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39999568117319258467318955 59999352175978887700978433)
        ·
          refine ⟨44999514131984165775733825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59999352175978887700978433 44999514131984165775733825)
          ·
            refine ⟨33749635598988124331800369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44999514131984165775733825 33749635598988124331800369)
            ·
              refine ⟨25312226699241093248850277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33749635598988124331800369 25312226699241093248850277)
              ·
                refine ⟨4746042506107704984159427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25312226699241093248850277 4746042506107704984159427)
                ·
                  refine ⟨7119063759161557476239141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746042506107704984159427 7119063759161557476239141)
                  ·
                    refine ⟨1334824454842792026794839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7119063759161557476239141 1334824454842792026794839)
                    ·
                      rfl

theorem cell22_3899342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_3899342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899342 prefixEnd_3899342 := by exact prefixLift 3899342
  have htrace : WordTrace (prefixWord ++ tailWord_3899342) baseStart_3899342 baseEnd_3899342 := by
    simpa [prefixWord, tailWord_3899342, baseEnd_3899342] using wordTrace_append hprefix tailTrace_3899342
  have hstable : (prefixWord ++ tailWord_3899342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899342).length < 2 ^ (prefixWord ++ tailWord_3899342).sum := by decide
  have hdescent : baseEnd_3899342 < baseStart_3899342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899359 : List Nat := [1, 1, 2, 3, 4, 1, 4, 1, 1, 4]
def baseStart_3899359 : Nat := 118140960795 + 3899359 * 2 ^ 59
def prefixEnd_3899359 : Nat := 4983230072969 + 3 ^ 40 * 3899359 * 2
def baseEnd_3899359 : Nat := 1334830274290209649119787

theorem tailTrace_3899359 : CollatzResearch.WordTrace tailWord_3899359 prefixEnd_3899359 1334830274290209649119787 := by
  unfold tailWord_3899359
  simp only [CollatzResearch.WordTrace]
  refine ⟨142221306680295775342725131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94814204453530516895150087 142221306680295775342725131)
  ·
    refine ⟨213331960020443663014087697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142221306680295775342725131 213331960020443663014087697)
    ·
      refine ⟨159998970015332747260565773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213331960020443663014087697 159998970015332747260565773)
      ·
        refine ⟨59999613755749780222712165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159998970015332747260565773 59999613755749780222712165)
        ·
          refine ⟨11249927579203083791758531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59999613755749780222712165 11249927579203083791758531)
          ·
            refine ⟨16874891368804625687637797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11249927579203083791758531 16874891368804625687637797)
            ·
              refine ⟨3164042131650867316432087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16874891368804625687637797 3164042131650867316432087)
              ·
                refine ⟨4746063197476300974648131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164042131650867316432087 4746063197476300974648131)
                ·
                  refine ⟨7119094796214451461972197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746063197476300974648131 7119094796214451461972197)
                  ·
                    refine ⟨1334830274290209649119787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7119094796214451461972197 1334830274290209649119787)
                    ·
                      rfl

theorem cell22_3899359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 1, 4].length) (baseStart_3899359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899359 prefixEnd_3899359 := by exact prefixLift 3899359
  have htrace : WordTrace (prefixWord ++ tailWord_3899359) baseStart_3899359 baseEnd_3899359 := by
    simpa [prefixWord, tailWord_3899359, baseEnd_3899359] using wordTrace_append hprefix tailTrace_3899359
  have hstable : (prefixWord ++ tailWord_3899359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899359).length < 2 ^ (prefixWord ++ tailWord_3899359).sum := by decide
  have hdescent : baseEnd_3899359 < baseStart_3899359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899374 : List Nat := [4, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_3899374 : Nat := 118140960795 + 3899374 * 2 ^ 59
def prefixEnd_3899374 : Nat := 4983230072969 + 3 ^ 40 * 3899374 * 2
def baseEnd_3899374 : Nat := 444945136365584869998247

theorem tailTrace_3899374 : CollatzResearch.WordTrace tailWord_3899374 prefixEnd_3899374 444945136365584869998247 := by
  unfold tailWord_3899374
  simp only [CollatzResearch.WordTrace]
  refine ⟨17777731721905179113065147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94814569183494288603014117 17777731721905179113065147)
  ·
    refine ⟨26666597582857768669597721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17777731721905179113065147 26666597582857768669597721)
    ·
      refine ⟨19999948187143326502198291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26666597582857768669597721 19999948187143326502198291)
      ·
        refine ⟨29999922280714989753297437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19999948187143326502198291 29999922280714989753297437)
        ·
          refine ⟨11249970855268121157486539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29999922280714989753297437 11249970855268121157486539)
          ·
            refine ⟨16874956282902181736229809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11249970855268121157486539 16874956282902181736229809)
            ·
              refine ⟨12656217212176636302172357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16874956282902181736229809 12656217212176636302172357)
              ·
                refine ⟨2373040727283119306657317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12656217212176636302172357 2373040727283119306657317)
                ·
                  refine ⟨444945136365584869998247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2373040727283119306657317 444945136365584869998247)
                  ·
                    rfl

theorem cell22_3899374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_3899374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899374 prefixEnd_3899374 := by exact prefixLift 3899374
  have htrace : WordTrace (prefixWord ++ tailWord_3899374) baseStart_3899374 baseEnd_3899374 := by
    simpa [prefixWord, tailWord_3899374, baseEnd_3899374] using wordTrace_append hprefix tailTrace_3899374
  have hstable : (prefixWord ++ tailWord_3899374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899374).length < 2 ^ (prefixWord ++ tailWord_3899374).sum := by decide
  have hdescent : baseEnd_3899374 < baseStart_3899374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899400 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 2, 7]
def baseStart_3899400 : Nat := 118140960795 + 3899400 * 2 ^ 59
def prefixEnd_3899400 : Nat := 4983230072969 + 3 ^ 40 * 3899400 * 2
def baseEnd_3899400 : Nat := 1334844309428099208844661

theorem tailTrace_3899400 : CollatzResearch.WordTrace tailWord_3899400 prefixEnd_3899400 1334844309428099208844661 := by
  unfold tailWord_3899400
  simp only [CollatzResearch.WordTrace]
  refine ⟨71111401036573619672483827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94815201382098159563311769 71111401036573619672483827)
  ·
    refine ⟨106667101554860429508725741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71111401036573619672483827 106667101554860429508725741)
    ·
      refine ⟨40000163083072661065772153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106667101554860429508725741 40000163083072661065772153)
      ·
        refine ⟨30000122312304495799329115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40000163083072661065772153 30000122312304495799329115)
        ·
          refine ⟨45000183468456743698993673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30000122312304495799329115 45000183468456743698993673)
          ·
            refine ⟨33750137601342557774245255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45000183468456743698993673 33750137601342557774245255)
            ·
              refine ⟨50625206402013836661367883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33750137601342557774245255 50625206402013836661367883)
              ·
                refine ⟨75937809603020754992051825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50625206402013836661367883 75937809603020754992051825)
                ·
                  refine ⟨56953357202265566244038869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75937809603020754992051825 56953357202265566244038869)
                  ·
                    refine ⟨1334844309428099208844661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56953357202265566244038869 1334844309428099208844661)
                    ·
                      rfl

theorem cell22_3899400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_3899400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899400 prefixEnd_3899400 := by exact prefixLift 3899400
  have htrace : WordTrace (prefixWord ++ tailWord_3899400) baseStart_3899400 baseEnd_3899400 := by
    simpa [prefixWord, tailWord_3899400, baseEnd_3899400] using wordTrace_append hprefix tailTrace_3899400
  have hstable : (prefixWord ++ tailWord_3899400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899400).length < 2 ^ (prefixWord ++ tailWord_3899400).sum := by decide
  have hdescent : baseEnd_3899400 < baseStart_3899400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899402 : List Nat := [3, 1, 2, 2, 4, 1, 1, 8]
def baseStart_3899402 : Nat := 118140960795 + 3899402 * 2 ^ 59
def prefixEnd_3899402 : Nat := 4983230072969 + 3 ^ 40 * 3899402 * 2
def baseEnd_3899402 : Nat := 148316110452107985588295

theorem tailTrace_3899402 : CollatzResearch.WordTrace tailWord_3899402 prefixEnd_3899402 148316110452107985588295 := by
  unfold tailWord_3899402
  simp only [CollatzResearch.WordTrace]
  refine ⟨35555718754784998421635115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94815250012759995791026973 35555718754784998421635115)
  ·
    refine ⟨53333578132177497632452673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35555718754784998421635115 53333578132177497632452673)
    ·
      refine ⟨40000183599133123224339505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53333578132177497632452673 40000183599133123224339505)
      ·
        refine ⟨30000137699349842418254629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40000183599133123224339505 30000137699349842418254629)
        ·
          refine ⟨5625025818628095453422743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30000137699349842418254629 5625025818628095453422743)
          ·
            refine ⟨8437538727942143180134115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5625025818628095453422743 8437538727942143180134115)
            ·
              refine ⟨12656308091913214770201173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8437538727942143180134115 12656308091913214770201173)
              ·
                refine ⟨148316110452107985588295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12656308091913214770201173 148316110452107985588295)
                ·
                  rfl

theorem cell22_3899402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_3899402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899402 prefixEnd_3899402 := by exact prefixLift 3899402
  have htrace : WordTrace (prefixWord ++ tailWord_3899402) baseStart_3899402 baseEnd_3899402 := by
    simpa [prefixWord, tailWord_3899402, baseEnd_3899402] using wordTrace_append hprefix tailTrace_3899402
  have hstable : (prefixWord ++ tailWord_3899402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899402).length < 2 ^ (prefixWord ++ tailWord_3899402).sum := by decide
  have hdescent : baseEnd_3899402 < baseStart_3899402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899485 : List Nat := [1, 4, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3899485 : Nat := 118140960795 + 3899485 * 2 ^ 59
def prefixEnd_3899485 : Nat := 4983230072969 + 3 ^ 40 * 3899485 * 2
def baseEnd_3899485 : Nat := 1334873406665187320469401

theorem tailTrace_3899485 : CollatzResearch.WordTrace tailWord_3899485 prefixEnd_3899485 1334873406665187320469401 := by
  unfold tailWord_3899485
  simp only [CollatzResearch.WordTrace]
  refine ⟨142225902277839298861811909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94817268185226199241207939 142225902277839298861811909)
  ·
    refine ⟨26667356677094868536589733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142225902277839298861811909 26667356677094868536589733)
    ·
      refine ⟨5000129376955287850610575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26667356677094868536589733 5000129376955287850610575)
      ·
        refine ⟨7500194065432931775915863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5000129376955287850610575 7500194065432931775915863)
        ·
          refine ⟨11250291098149397663873795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7500194065432931775915863 11250291098149397663873795)
          ·
            refine ⟨16875436647224096495810693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11250291098149397663873795 16875436647224096495810693)
            ·
              refine ⟨3164144371354518092964505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16875436647224096495810693 3164144371354518092964505)
              ·
                refine ⟨2373108278515888569723379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3164144371354518092964505 2373108278515888569723379)
                ·
                  refine ⟨3559662417773832854585069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373108278515888569723379 3559662417773832854585069)
                  ·
                    refine ⟨1334873406665187320469401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3559662417773832854585069 1334873406665187320469401)
                    ·
                      rfl

theorem cell22_3899485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3899485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899485 prefixEnd_3899485 := by exact prefixLift 3899485
  have htrace : WordTrace (prefixWord ++ tailWord_3899485) baseStart_3899485 baseEnd_3899485 := by
    simpa [prefixWord, tailWord_3899485, baseEnd_3899485] using wordTrace_append hprefix tailTrace_3899485
  have hstable : (prefixWord ++ tailWord_3899485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899485).length < 2 ^ (prefixWord ++ tailWord_3899485).sum := by decide
  have hdescent : baseEnd_3899485 < baseStart_3899485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899524 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_3899524 : Nat := 118140960795 + 3899524 * 2 ^ 59
def prefixEnd_3899524 : Nat := 4983230072969 + 3 ^ 40 * 3899524 * 2
def baseEnd_3899524 : Nat := 1334886757162204218744281

theorem tailTrace_3899524 : CollatzResearch.WordTrace tailWord_3899524 prefixEnd_3899524 1334886757162204218744281 := by
  unfold tailWord_3899524
  simp only [CollatzResearch.WordTrace]
  refine ⟨71113662362349004261240813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94818216483132005681654417 71113662362349004261240813)
  ·
    refine ⟨26667623385880876597965305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71113662362349004261240813 26667623385880876597965305)
    ·
      refine ⟨20000717539410657448473979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26667623385880876597965305 20000717539410657448473979)
      ·
        refine ⟨30001076309115986172710969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20000717539410657448473979 30001076309115986172710969)
        ·
          refine ⟨22500807231836989629533227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30001076309115986172710969 22500807231836989629533227)
          ·
            refine ⟨33751210847755484444299841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22500807231836989629533227 33751210847755484444299841)
            ·
              refine ⟨25313408135816613333224881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33751210847755484444299841 25313408135816613333224881)
              ·
                refine ⟨18985056101862459999918661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25313408135816613333224881 18985056101862459999918661)
                ·
                  refine ⟨3559698019099211249984749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18985056101862459999918661 3559698019099211249984749)
                  ·
                    refine ⟨1334886757162204218744281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3559698019099211249984749 1334886757162204218744281)
                    ·
                      rfl

theorem cell22_3899524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_3899524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899524 prefixEnd_3899524 := by exact prefixLift 3899524
  have htrace : WordTrace (prefixWord ++ tailWord_3899524) baseStart_3899524 baseEnd_3899524 := by
    simpa [prefixWord, tailWord_3899524, baseEnd_3899524] using wordTrace_append hprefix tailTrace_3899524
  have hstable : (prefixWord ++ tailWord_3899524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899524).length < 2 ^ (prefixWord ++ tailWord_3899524).sum := by decide
  have hdescent : baseEnd_3899524 < baseStart_3899524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899528 : List Nat := [2, 1, 3, 4, 1, 3, 2, 1, 1, 4]
def baseStart_3899528 : Nat := 118140960795 + 3899528 * 2 ^ 59
def prefixEnd_3899528 : Nat := 4983230072969 + 3 ^ 40 * 3899528 * 2
def baseEnd_3899528 : Nat := 1334888126443949541644269

theorem tailTrace_3899528 : CollatzResearch.WordTrace tailWord_3899528 prefixEnd_3899528 1334888126443949541644269 := by
  unfold tailWord_3899528
  simp only [CollatzResearch.WordTrace]
  refine ⟨71113735308341758602813619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94818313744455678137084825 71113735308341758602813619)
  ·
    refine ⟨106670602962512637904220429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71113735308341758602813619 106670602962512637904220429)
    ·
      refine ⟨40001476110942239214082661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106670602962512637904220429 40001476110942239214082661)
      ·
        refine ⟨7500276770801669852640499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40001476110942239214082661 7500276770801669852640499)
        ·
          refine ⟨11250415156202504778960749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7500276770801669852640499 11250415156202504778960749)
          ·
            refine ⟨4218905683575939292110281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11250415156202504778960749 4218905683575939292110281)
            ·
              refine ⟨3164179262681954469082711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4218905683575939292110281 3164179262681954469082711)
              ·
                refine ⟨4746268894022931703624067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164179262681954469082711 4746268894022931703624067)
                ·
                  refine ⟨7119403341034397555436101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746268894022931703624067 7119403341034397555436101)
                  ·
                    refine ⟨1334888126443949541644269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7119403341034397555436101 1334888126443949541644269)
                    ·
                      rfl

theorem cell22_3899528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_3899528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899528 prefixEnd_3899528 := by exact prefixLift 3899528
  have htrace : WordTrace (prefixWord ++ tailWord_3899528) baseStart_3899528 baseEnd_3899528 := by
    simpa [prefixWord, tailWord_3899528, baseEnd_3899528] using wordTrace_append hprefix tailTrace_3899528
  have hstable : (prefixWord ++ tailWord_3899528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899528).length < 2 ^ (prefixWord ++ tailWord_3899528).sum := by decide
  have hdescent : baseEnd_3899528 < baseStart_3899528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899627 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 8]
def baseStart_3899627 : Nat := 118140960795 + 3899627 * 2 ^ 59
def prefixEnd_3899627 : Nat := 4983230072969 + 3 ^ 40 * 3899627 * 2
def baseEnd_3899627 : Nat := 444974005389048761139655

theorem tailTrace_3899627 : CollatzResearch.WordTrace tailWord_3899627 prefixEnd_3899627 444974005389048761139655 := by
  unfold tailWord_3899627
  simp only [CollatzResearch.WordTrace]
  refine ⟨142231081443324857113481135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94820720962216571408987423 142231081443324857113481135)
  ·
    refine ⟨213346622164987285670221703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142231081443324857113481135 213346622164987285670221703)
    ·
      refine ⟨320019933247480928505332555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213346622164987285670221703 320019933247480928505332555)
      ·
        refine ⟨480029899871221392757998833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320019933247480928505332555 480029899871221392757998833)
        ·
          refine ⟨360022424903416044568499125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480029899871221392757998833 360022424903416044568499125)
          ·
            refine ⟨33752102334695254178296793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 360022424903416044568499125 33752102334695254178296793)
            ·
              refine ⟨25314076751021440633722595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33752102334695254178296793 25314076751021440633722595)
              ·
                refine ⟨37971115126532160950583893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25314076751021440633722595 37971115126532160950583893)
                ·
                  refine ⟨444974005389048761139655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37971115126532160950583893 444974005389048761139655)
                  ·
                    rfl

theorem cell22_3899627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 8].length) (baseStart_3899627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899627 prefixEnd_3899627 := by exact prefixLift 3899627
  have htrace : WordTrace (prefixWord ++ tailWord_3899627) baseStart_3899627 baseEnd_3899627 := by
    simpa [prefixWord, tailWord_3899627, baseEnd_3899627] using wordTrace_append hprefix tailTrace_3899627
  have hstable : (prefixWord ++ tailWord_3899627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899627).length < 2 ^ (prefixWord ++ tailWord_3899627).sum := by decide
  have hdescent : baseEnd_3899627 < baseStart_3899627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899678 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_3899678 : Nat := 118140960795 + 3899678 * 2 ^ 59
def prefixEnd_3899678 : Nat := 4983230072969 + 3 ^ 40 * 3899678 * 2
def baseEnd_3899678 : Nat := 444979824836466383464603

theorem tailTrace_3899678 : CollatzResearch.WordTrace tailWord_3899678 prefixEnd_3899678 444979824836466383464603 := by
  unfold tailWord_3899678
  simp only [CollatzResearch.WordTrace]
  refine ⟨17779117695767511602948461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94821961044093395215725125 17779117695767511602948461)
  ·
    refine ⟨6667169135912816851105673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17779117695767511602948461 6667169135912816851105673)
    ·
      refine ⟨5000376851934612638329255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6667169135912816851105673 5000376851934612638329255)
      ·
        refine ⟨7500565277901918957493883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5000376851934612638329255 7500565277901918957493883)
        ·
          refine ⟨11250847916852878436240825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7500565277901918957493883 11250847916852878436240825)
          ·
            refine ⟨8438135937639658827180619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11250847916852878436240825 8438135937639658827180619)
            ·
              refine ⟨12657203906459488240770929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8438135937639658827180619 12657203906459488240770929)
              ·
                refine ⟨9492902929844616180578197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12657203906459488240770929 9492902929844616180578197)
                ·
                  refine ⟨444979824836466383464603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9492902929844616180578197 444979824836466383464603)
                  ·
                    rfl

theorem cell22_3899678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_3899678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899678 prefixEnd_3899678 := by exact prefixLift 3899678
  have htrace : WordTrace (prefixWord ++ tailWord_3899678) baseStart_3899678 baseEnd_3899678 := by
    simpa [prefixWord, tailWord_3899678, baseEnd_3899678] using wordTrace_append hprefix tailTrace_3899678
  have hstable : (prefixWord ++ tailWord_3899678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899678).length < 2 ^ (prefixWord ++ tailWord_3899678).sum := by decide
  have hdescent : baseEnd_3899678 < baseStart_3899678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899710 : List Nat := [4, 2, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_3899710 : Nat := 118140960795 + 3899710 * 2 ^ 59
def prefixEnd_3899710 : Nat := 4983230072969 + 3 ^ 40 * 3899710 * 2
def baseEnd_3899710 : Nat := 1334950428763361733593711

theorem tailTrace_3899710 : CollatzResearch.WordTrace tailWord_3899710 prefixEnd_3899710 1334950428763361733593711 := by
  unfold tailWord_3899710
  simp only [CollatzResearch.WordTrace]
  refine ⟨17779263587753020286094073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94822739134682774859168389 17779263587753020286094073)
  ·
    refine ⟨13334447690814765214570555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17779263587753020286094073 13334447690814765214570555)
    ·
      refine ⟨20001671536222147821855833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13334447690814765214570555 20001671536222147821855833)
      ·
        refine ⟨15001253652166610866391875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20001671536222147821855833 15001253652166610866391875)
        ·
          refine ⟨22501880478249916299587813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15001253652166610866391875 22501880478249916299587813)
          ·
            refine ⟨4219102589671859306172715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22501880478249916299587813 4219102589671859306172715)
            ·
              refine ⟨6328653884507788959259073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4219102589671859306172715 6328653884507788959259073)
              ·
                refine ⟨4746490413380841719444305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6328653884507788959259073 4746490413380841719444305)
                ·
                  refine ⟨3559867810035631289583229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4746490413380841719444305 3559867810035631289583229)
                  ·
                    refine ⟨1334950428763361733593711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3559867810035631289583229 1334950428763361733593711)
                    ·
                      rfl

theorem cell22_3899710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_3899710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899710 prefixEnd_3899710 := by exact prefixLift 3899710
  have htrace : WordTrace (prefixWord ++ tailWord_3899710) baseStart_3899710 baseEnd_3899710 := by
    simpa [prefixWord, tailWord_3899710, baseEnd_3899710] using wordTrace_append hprefix tailTrace_3899710
  have hstable : (prefixWord ++ tailWord_3899710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899710).length < 2 ^ (prefixWord ++ tailWord_3899710).sum := by decide
  have hdescent : baseEnd_3899710 < baseStart_3899710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899740 : List Nat := [2, 2, 4, 3, 1, 2, 2, 6]
def baseStart_3899740 : Nat := 118140960795 + 3899740 * 2 ^ 59
def prefixEnd_3899740 : Nat := 4983230072969 + 3 ^ 40 * 3899740 * 2
def baseEnd_3899740 : Nat := 148328966486272406149291

theorem tailTrace_3899740 : CollatzResearch.WordTrace tailWord_3899740 prefixEnd_3899740 148328966486272406149291 := by
  unfold tailWord_3899740
  simp only [CollatzResearch.WordTrace]
  refine ⟨71117601445957738706172337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94823468594610318274896449 71117601445957738706172337)
  ·
    refine ⟨53338201084468304029629253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71117601445957738706172337 53338201084468304029629253)
    ·
      refine ⟨10000912703337807005555485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53338201084468304029629253 10000912703337807005555485)
      ·
        refine ⟨3750342263751677627083307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10000912703337807005555485 3750342263751677627083307)
        ·
          refine ⟨5625513395627516440624961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3750342263751677627083307 5625513395627516440624961)
          ·
            refine ⟨4219135046720637330468721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5625513395627516440624961 4219135046720637330468721)
            ·
              refine ⟨3164351285040477997851541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4219135046720637330468721 3164351285040477997851541)
              ·
                refine ⟨148328966486272406149291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3164351285040477997851541 148328966486272406149291)
                ·
                  rfl

theorem cell22_3899740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 6].length) (baseStart_3899740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899740 prefixEnd_3899740 := by exact prefixLift 3899740
  have htrace : WordTrace (prefixWord ++ tailWord_3899740) baseStart_3899740 baseEnd_3899740 := by
    simpa [prefixWord, tailWord_3899740, baseEnd_3899740] using wordTrace_append hprefix tailTrace_3899740
  have hstable : (prefixWord ++ tailWord_3899740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899740).length < 2 ^ (prefixWord ++ tailWord_3899740).sum := by decide
  have hdescent : baseEnd_3899740 < baseStart_3899740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899811 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 1, 5]
def baseStart_3899811 : Nat := 118140960795 + 3899811 * 2 ^ 59
def prefixEnd_3899811 : Nat := 4983230072969 + 3 ^ 40 * 3899811 * 2
def baseEnd_3899811 : Nat := 1334985003127431136818401

theorem tailTrace_3899811 : CollatzResearch.WordTrace tailWord_3899811 prefixEnd_3899811 1334985003127431136818401 := by
  unfold tailWord_3899811
  simp only [CollatzResearch.WordTrace]
  refine ⟨142237792474658256538179287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94825194983105504358786191 142237792474658256538179287)
  ·
    refine ⟨213356688711987384807268931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142237792474658256538179287 213356688711987384807268931)
    ·
      refine ⟨320035033067981077210903397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213356688711987384807268931 320035033067981077210903397)
      ·
        refine ⟨60006568700246451977044387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320035033067981077210903397 60006568700246451977044387)
        ·
          refine ⟨90009853050369677965566581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60006568700246451977044387 90009853050369677965566581)
          ·
            refine ⟨8438423723472157309271867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90009853050369677965566581 8438423723472157309271867)
            ·
              refine ⟨12657635585208235963907801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8438423723472157309271867 12657635585208235963907801)
              ·
                refine ⟨9493226688906176972930851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12657635585208235963907801 9493226688906176972930851)
                ·
                  refine ⟨14239840033359265459396277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9493226688906176972930851 14239840033359265459396277)
                  ·
                    refine ⟨1334985003127431136818401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14239840033359265459396277 1334985003127431136818401)
                    ·
                      rfl

theorem cell22_3899811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 5].length) (baseStart_3899811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899811 prefixEnd_3899811 := by exact prefixLift 3899811
  have htrace : WordTrace (prefixWord ++ tailWord_3899811) baseStart_3899811 baseEnd_3899811 := by
    simpa [prefixWord, tailWord_3899811, baseEnd_3899811] using wordTrace_append hprefix tailTrace_3899811
  have hstable : (prefixWord ++ tailWord_3899811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899811).length < 2 ^ (prefixWord ++ tailWord_3899811).sum := by decide
  have hdescent : baseEnd_3899811 < baseStart_3899811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899815 : List Nat := [1, 1, 6, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3899815 : Nat := 118140960795 + 3899815 * 2 ^ 59
def prefixEnd_3899815 : Nat := 4983230072969 + 3 ^ 40 * 3899815 * 2
def baseEnd_3899815 : Nat := 1334986372409176459718389

theorem tailTrace_3899815 : CollatzResearch.WordTrace tailWord_3899815 prefixEnd_3899815 1334986372409176459718389 := by
  unfold tailWord_3899815
  simp only [CollatzResearch.WordTrace]
  refine ⟨142237938366643765221324899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94825292244429176814216599 142237938366643765221324899)
  ·
    refine ⟨213356907549965647831987349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142237938366643765221324899 213356907549965647831987349)
    ·
      refine ⟨10001105041404639742124407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 213356907549965647831987349 10001105041404639742124407)
      ·
        refine ⟨15001657562106959613186611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10001105041404639742124407 15001657562106959613186611)
        ·
          refine ⟨22502486343160439419779917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15001657562106959613186611 22502486343160439419779917)
          ·
            refine ⟨8438432378685164782417469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22502486343160439419779917 8438432378685164782417469)
            ·
              refine ⟨3164412142006936793406551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8438432378685164782417469 3164412142006936793406551)
              ·
                refine ⟨4746618213010405190109827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164412142006936793406551 4746618213010405190109827)
                ·
                  refine ⟨7119927319515607785164741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746618213010405190109827 7119927319515607785164741)
                  ·
                    refine ⟨1334986372409176459718389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7119927319515607785164741 1334986372409176459718389)
                    ·
                      rfl

theorem cell22_3899815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3899815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899815 prefixEnd_3899815 := by exact prefixLift 3899815
  have htrace : WordTrace (prefixWord ++ tailWord_3899815) baseStart_3899815 baseEnd_3899815 := by
    simpa [prefixWord, tailWord_3899815, baseEnd_3899815] using wordTrace_append hprefix tailTrace_3899815
  have hstable : (prefixWord ++ tailWord_3899815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899815).length < 2 ^ (prefixWord ++ tailWord_3899815).sum := by decide
  have hdescent : baseEnd_3899815 < baseStart_3899815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899826 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_3899826 : Nat := 118140960795 + 3899826 * 2 ^ 59
def prefixEnd_3899826 : Nat := 4983230072969 + 3 ^ 40 * 3899826 * 2
def baseEnd_3899826 : Nat := 1334990137933976097693355

theorem tailTrace_3899826 : CollatzResearch.WordTrace tailWord_3899826 prefixEnd_3899826 1334990137933976097693355 := by
  unfold tailWord_3899826
  simp only [CollatzResearch.WordTrace]
  refine ⟨35559584892400978524993833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94825559713069276066650221 35559584892400978524993833)
  ·
    refine ⟨26669688669300733893745375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35559584892400978524993833 26669688669300733893745375)
    ·
      refine ⟨40004533003951100840618063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26669688669300733893745375 40004533003951100840618063)
      ·
        refine ⟨60006799505926651260927095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40004533003951100840618063 60006799505926651260927095)
        ·
          refine ⟨90010199258889976891390643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60006799505926651260927095 90010199258889976891390643)
          ·
            refine ⟨135015298888334965337085965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90010199258889976891390643 135015298888334965337085965)
            ·
              refine ⟨50630737083125612001407237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135015298888334965337085965 50630737083125612001407237)
              ·
                refine ⟨9493263203086052250263857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50630737083125612001407237 9493263203086052250263857)
                ·
                  refine ⟨7119947402314539187697893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9493263203086052250263857 7119947402314539187697893)
                  ·
                    refine ⟨1334990137933976097693355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7119947402314539187697893 1334990137933976097693355)
                    ·
                      rfl

theorem cell22_3899826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_3899826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899826 prefixEnd_3899826 := by exact prefixLift 3899826
  have htrace : WordTrace (prefixWord ++ tailWord_3899826) baseStart_3899826 baseEnd_3899826 := by
    simpa [prefixWord, tailWord_3899826, baseEnd_3899826] using wordTrace_append hprefix tailTrace_3899826
  have hstable : (prefixWord ++ tailWord_3899826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899826).length < 2 ^ (prefixWord ++ tailWord_3899826).sum := by decide
  have hdescent : baseEnd_3899826 < baseStart_3899826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899839 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 4, 7]
def baseStart_3899839 : Nat := 118140960795 + 3899839 * 2 ^ 59
def prefixEnd_3899839 : Nat := 4983230072969 + 3 ^ 40 * 3899839 * 2
def baseEnd_3899839 : Nat := 1334994588099648397118315

theorem tailTrace_3899839 : CollatzResearch.WordTrace tailWord_3899839 prefixEnd_3899839 1334994588099648397118315 := by
  unfold tailWord_3899839
  simp only [CollatzResearch.WordTrace]
  refine ⟨142238813718556817320198571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94825875812371211546799047 142238813718556817320198571)
  ·
    refine ⟨213358220577835225980297857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142238813718556817320198571 213358220577835225980297857)
    ·
      refine ⟨160018665433376419485223393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213358220577835225980297857 160018665433376419485223393)
      ·
        refine ⟨120013999075032314613917545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160018665433376419485223393 120013999075032314613917545)
        ·
          refine ⟨90010499306274235960438159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120013999075032314613917545 90010499306274235960438159)
          ·
            refine ⟨135015748959411353940657239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90010499306274235960438159 135015748959411353940657239)
            ·
              refine ⟨202523623439117030910985859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135015748959411353940657239 202523623439117030910985859)
              ·
                refine ⟨303785435158675546366478789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202523623439117030910985859 303785435158675546366478789)
                ·
                  refine ⟨56959769092251664943714773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303785435158675546366478789 56959769092251664943714773)
                  ·
                    refine ⟨1334994588099648397118315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56959769092251664943714773 1334994588099648397118315)
                    ·
                      rfl

theorem cell22_3899839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_3899839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899839 prefixEnd_3899839 := by exact prefixLift 3899839
  have htrace : WordTrace (prefixWord ++ tailWord_3899839) baseStart_3899839 baseEnd_3899839 := by
    simpa [prefixWord, tailWord_3899839, baseEnd_3899839] using wordTrace_append hprefix tailTrace_3899839
  have hstable : (prefixWord ++ tailWord_3899839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899839).length < 2 ^ (prefixWord ++ tailWord_3899839).sum := by decide
  have hdescent : baseEnd_3899839 < baseStart_3899839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899860 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_3899860 : Nat := 118140960795 + 3899860 * 2 ^ 59
def prefixEnd_3899860 : Nat := 4983230072969 + 3 ^ 40 * 3899860 * 2
def baseEnd_3899860 : Nat := 1335001776828811342343251

theorem tailTrace_3899860 : CollatzResearch.WordTrace tailWord_3899860 prefixEnd_3899860 1335001776828811342343251 := by
  unfold tailWord_3899860
  simp only [CollatzResearch.WordTrace]
  refine ⟨71119789825740368953356517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94826386434320491937808689 71119789825740368953356517)
  ·
    refine ⟨13334960592326319178754347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71119789825740368953356517 13334960592326319178754347)
    ·
      refine ⟨20002440888489478768131521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13334960592326319178754347 20002440888489478768131521)
      ·
        refine ⟨15001830666367109076098641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20002440888489478768131521 15001830666367109076098641)
        ·
          refine ⟨11251372999775331807073981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15001830666367109076098641 11251372999775331807073981)
          ·
            refine ⟨4219264874915749427652743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11251372999775331807073981 4219264874915749427652743)
            ·
              refine ⟨6328897312373624141479115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4219264874915749427652743 6328897312373624141479115)
              ·
                refine ⟨9493345968560436212218673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6328897312373624141479115 9493345968560436212218673)
                ·
                  refine ⟨7120009476420327159164005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9493345968560436212218673 7120009476420327159164005)
                  ·
                    refine ⟨1335001776828811342343251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7120009476420327159164005 1335001776828811342343251)
                    ·
                      rfl

theorem cell22_3899860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_3899860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899860 prefixEnd_3899860 := by exact prefixLift 3899860
  have htrace : WordTrace (prefixWord ++ tailWord_3899860) baseStart_3899860 baseEnd_3899860 := by
    simpa [prefixWord, tailWord_3899860, baseEnd_3899860] using wordTrace_append hprefix tailTrace_3899860
  have hstable : (prefixWord ++ tailWord_3899860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899860).length < 2 ^ (prefixWord ++ tailWord_3899860).sum := by decide
  have hdescent : baseEnd_3899860 < baseStart_3899860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899901 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3899901 : Nat := 118140960795 + 3899901 * 2 ^ 59
def prefixEnd_3899901 : Nat := 4983230072969 + 3 ^ 40 * 3899901 * 2
def baseEnd_3899901 : Nat := 1335015811966700902068125

theorem tailTrace_3899901 : CollatzResearch.WordTrace tailWord_3899901 prefixEnd_3899901 1335015811966700902068125 := by
  unfold tailWord_3899901
  simp only [CollatzResearch.WordTrace]
  refine ⟨142241075044332201908955557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94827383362888134605970371 142241075044332201908955557)
  ·
    refine ⟨26670201570812287857929167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142241075044332201908955557 26670201570812287857929167)
    ·
      refine ⟨40005302356218431786893751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26670201570812287857929167 40005302356218431786893751)
      ·
        refine ⟨60007953534327647680340627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40005302356218431786893751 60007953534327647680340627)
        ·
          refine ⟨90011930301491471520510941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60007953534327647680340627 90011930301491471520510941)
          ·
            refine ⟨33754473863059301820191603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90011930301491471520510941 33754473863059301820191603)
            ·
              refine ⟨50631710794588952730287405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33754473863059301820191603 50631710794588952730287405)
              ·
                refine ⟨18986891547970857273857777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50631710794588952730287405 18986891547970857273857777)
                ·
                  refine ⟨14240168660978142955393333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18986891547970857273857777 14240168660978142955393333)
                  ·
                    refine ⟨1335015811966700902068125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14240168660978142955393333 1335015811966700902068125)
                    ·
                      rfl

theorem cell22_3899901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3899901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899901 prefixEnd_3899901 := by exact prefixLift 3899901
  have htrace : WordTrace (prefixWord ++ tailWord_3899901) baseStart_3899901 baseEnd_3899901 := by
    simpa [prefixWord, tailWord_3899901, baseEnd_3899901] using wordTrace_append hprefix tailTrace_3899901
  have hstable : (prefixWord ++ tailWord_3899901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899901).length < 2 ^ (prefixWord ++ tailWord_3899901).sum := by decide
  have hdescent : baseEnd_3899901 < baseStart_3899901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899903 : List Nat := [1, 1, 2, 2, 1, 2, 7, 1, 5]
def baseStart_3899903 : Nat := 118140960795 + 3899903 * 2 ^ 59
def prefixEnd_3899903 : Nat := 4983230072969 + 3 ^ 40 * 3899903 * 2
def baseEnd_3899903 : Nat := 445005498869191187839373

theorem tailTrace_3899903 : CollatzResearch.WordTrace tailWord_3899903 prefixEnd_3899903 445005498869191187839373 := by
  unfold tailWord_3899903
  simp only [CollatzResearch.WordTrace]
  refine ⟨142241147990324956250528363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94827431993549970833685575 142241147990324956250528363)
  ·
    refine ⟨213361721985487434375792545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142241147990324956250528363 213361721985487434375792545)
    ·
      refine ⟨160021291489115575781844409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213361721985487434375792545 160021291489115575781844409)
      ·
        refine ⟨120015968616836681836383307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160021291489115575781844409 120015968616836681836383307)
        ·
          refine ⟨180023952925255022754574961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120015968616836681836383307 180023952925255022754574961)
          ·
            refine ⟨135017964693941267065931221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180023952925255022754574961 135017964693941267065931221)
            ·
              refine ⟨3164483547514248446857763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 135017964693941267065931221 3164483547514248446857763)
              ·
                refine ⟨4746725321271372670286645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164483547514248446857763 4746725321271372670286645)
                ·
                  refine ⟨445005498869191187839373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4746725321271372670286645 445005498869191187839373)
                  ·
                    rfl

theorem cell22_3899903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 5].length) (baseStart_3899903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899903 prefixEnd_3899903 := by exact prefixLift 3899903
  have htrace : WordTrace (prefixWord ++ tailWord_3899903) baseStart_3899903 baseEnd_3899903 := by
    simpa [prefixWord, tailWord_3899903, baseEnd_3899903] using wordTrace_append hprefix tailTrace_3899903
  have hstable : (prefixWord ++ tailWord_3899903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899903).length < 2 ^ (prefixWord ++ tailWord_3899903).sum := by decide
  have hdescent : baseEnd_3899903 < baseStart_3899903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899924 : List Nat := [2, 4, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3899924 : Nat := 118140960795 + 3899924 * 2 ^ 59
def prefixEnd_3899924 : Nat := 4983230072969 + 3 ^ 40 * 3899924 * 2
def baseEnd_3899924 : Nat := 1335023685336736508743055

theorem tailTrace_3899924 : CollatzResearch.WordTrace tailWord_3899924 prefixEnd_3899924 1335023685336736508743055 := by
  unfold tailWord_3899924
  simp only [CollatzResearch.WordTrace]
  refine ⟨71120956961624438418521413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94827942615499251224695217 71120956961624438418521413)
  ·
    refine ⟨13335179430304582203472765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71120956961624438418521413 13335179430304582203472765)
    ·
      refine ⟨5000692286364218326302287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13335179430304582203472765 5000692286364218326302287)
      ·
        refine ⟨7501038429546327489453431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5000692286364218326302287 7501038429546327489453431)
        ·
          refine ⟨11251557644319491234180147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7501038429546327489453431 11251557644319491234180147)
          ·
            refine ⟨16877336466479236851270221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11251557644319491234180147 16877336466479236851270221)
            ·
              refine ⟨6329001174929713819226333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16877336466479236851270221 6329001174929713819226333)
              ·
                refine ⟨2373375440598642682209875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6329001174929713819226333 2373375440598642682209875)
                ·
                  refine ⟨3560063160897964023314813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373375440598642682209875 3560063160897964023314813)
                  ·
                    refine ⟨1335023685336736508743055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3560063160897964023314813 1335023685336736508743055)
                    ·
                      rfl

theorem cell22_3899924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3899924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899924 prefixEnd_3899924 := by exact prefixLift 3899924
  have htrace : WordTrace (prefixWord ++ tailWord_3899924) baseStart_3899924 baseEnd_3899924 := by
    simpa [prefixWord, tailWord_3899924, baseEnd_3899924] using wordTrace_append hprefix tailTrace_3899924
  have hstable : (prefixWord ++ tailWord_3899924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899924).length < 2 ^ (prefixWord ++ tailWord_3899924).sum := by decide
  have hdescent : baseEnd_3899924 < baseStart_3899924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899948 : List Nat := [2, 2, 1, 1, 1, 2, 1, 8, 4]
def baseStart_3899948 : Nat := 118140960795 + 3899948 * 2 ^ 59
def prefixEnd_3899948 : Nat := 4983230072969 + 3 ^ 40 * 3899948 * 2
def baseEnd_3899948 : Nat := 445010633675736148714327

theorem tailTrace_3899948 : CollatzResearch.WordTrace tailWord_3899948 prefixEnd_3899948 445010633675736148714327 := by
  unfold tailWord_3899948
  simp only [CollatzResearch.WordTrace]
  refine ⟨71121394637580964467958249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94828526183441285957277665 71121394637580964467958249)
  ·
    refine ⟨53341045978185723350968687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71121394637580964467958249 53341045978185723350968687)
    ·
      refine ⟨80011568967278585026453031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53341045978185723350968687 80011568967278585026453031)
      ·
        refine ⟨120017353450917877539679547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80011568967278585026453031 120017353450917877539679547)
        ·
          refine ⟨180026030176376816309519321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120017353450917877539679547 180026030176376816309519321)
          ·
            refine ⟨135019522632282612232139491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180026030176376816309519321 135019522632282612232139491)
            ·
              refine ⟨202529283948423918348209237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135019522632282612232139491 202529283948423918348209237)
              ·
                refine ⟨2373390046270592793143077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 202529283948423918348209237 2373390046270592793143077)
                ·
                  refine ⟨445010633675736148714327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2373390046270592793143077 445010633675736148714327)
                  ·
                    rfl

theorem cell22_3899948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_3899948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899948 prefixEnd_3899948 := by exact prefixLift 3899948
  have htrace : WordTrace (prefixWord ++ tailWord_3899948) baseStart_3899948 baseEnd_3899948 := by
    simpa [prefixWord, tailWord_3899948, baseEnd_3899948] using wordTrace_append hprefix tailTrace_3899948
  have hstable : (prefixWord ++ tailWord_3899948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899948).length < 2 ^ (prefixWord ++ tailWord_3899948).sum := by decide
  have hdescent : baseEnd_3899948 < baseStart_3899948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899978 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_3899978 : Nat := 118140960795 + 3899978 * 2 ^ 59
def prefixEnd_3899978 : Nat := 4983230072969 + 3 ^ 40 * 3899978 * 2
def baseEnd_3899978 : Nat := 1335042170640298367892889

theorem tailTrace_3899978 : CollatzResearch.WordTrace tailWord_3899978 prefixEnd_3899978 1335042170640298367892889 := by
  unfold tailWord_3899978
  simp only [CollatzResearch.WordTrace]
  refine ⟨35560970866263311014877147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94829255643368829373005725 35560970866263311014877147)
  ·
    refine ⟨53341456299394966522315721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35560970866263311014877147 53341456299394966522315721)
    ·
      refine ⟨40006092224546224891736791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53341456299394966522315721 40006092224546224891736791)
      ·
        refine ⟨60009138336819337337605187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40006092224546224891736791 60009138336819337337605187)
        ·
          refine ⟨90013707505229006006407781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60009138336819337337605187 90013707505229006006407781)
          ·
            refine ⟨16877570157230438626201459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90013707505229006006407781 16877570157230438626201459)
            ·
              refine ⟨25316355235845657939302189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16877570157230438626201459 25316355235845657939302189)
              ·
                refine ⟨9493633213442121727238321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25316355235845657939302189 9493633213442121727238321)
                ·
                  refine ⟨7120224910081591295428741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9493633213442121727238321 7120224910081591295428741)
                  ·
                    refine ⟨1335042170640298367892889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7120224910081591295428741 1335042170640298367892889)
                    ·
                      rfl

theorem cell22_3899978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_3899978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3899978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3899978 prefixEnd_3899978 := by exact prefixLift 3899978
  have htrace : WordTrace (prefixWord ++ tailWord_3899978) baseStart_3899978 baseEnd_3899978 := by
    simpa [prefixWord, tailWord_3899978, baseEnd_3899978] using wordTrace_append hprefix tailTrace_3899978
  have hstable : (prefixWord ++ tailWord_3899978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899978).length < 2 ^ (prefixWord ++ tailWord_3899978).sum := by decide
  have hdescent : baseEnd_3899978 < baseStart_3899978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900025 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 3, 3]
def baseStart_3900025 : Nat := 118140960795 + 3900025 * 2 ^ 59
def prefixEnd_3900025 : Nat := 4983230072969 + 3 ^ 40 * 3900025 * 2
def baseEnd_3900025 : Nat := 1335058259700805911967745

theorem tailTrace_3900025 : CollatzResearch.WordTrace tailWord_3900025 prefixEnd_3900025 1335058259700805911967745 := by
  unfold tailWord_3900025
  simp only [CollatzResearch.WordTrace]
  refine ⟨142245597695882971086469529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94830398463921980724313019 142245597695882971086469529)
  ·
    refine ⟨106684198271912228314852147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142245597695882971086469529 106684198271912228314852147)
    ·
      refine ⟨160026297407868342472278221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106684198271912228314852147 160026297407868342472278221)
      ·
        refine ⟨60009861527950628427104333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160026297407868342472278221 60009861527950628427104333)
        ·
          refine ⟨22503698072981485660164125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60009861527950628427104333 22503698072981485660164125)
          ·
            refine ⟨8438886777368057122561547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22503698072981485660164125 8438886777368057122561547)
            ·
              refine ⟨12658330166052085683842321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8438886777368057122561547 12658330166052085683842321)
              ·
                refine ⟨9493747624539064262881741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12658330166052085683842321 9493747624539064262881741)
                ·
                  refine ⟨3560155359202149098580653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9493747624539064262881741 3560155359202149098580653)
                  ·
                    refine ⟨1335058259700805911967745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3560155359202149098580653 1335058259700805911967745)
                    ·
                      rfl

theorem cell22_3900025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 3].length) (baseStart_3900025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900025 prefixEnd_3900025 := by exact prefixLift 3900025
  have htrace : WordTrace (prefixWord ++ tailWord_3900025) baseStart_3900025 baseEnd_3900025 := by
    simpa [prefixWord, tailWord_3900025, baseEnd_3900025] using wordTrace_append hprefix tailTrace_3900025
  have hstable : (prefixWord ++ tailWord_3900025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900025).length < 2 ^ (prefixWord ++ tailWord_3900025).sum := by decide
  have hdescent : baseEnd_3900025 < baseStart_3900025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900083 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 6]
def baseStart_3900083 : Nat := 118140960795 + 3900083 * 2 ^ 59
def prefixEnd_3900083 : Nat := 4983230072969 + 3 ^ 40 * 3900083 * 2
def baseEnd_3900083 : Nat := 445026038095371031339189

theorem tailTrace_3900083 : CollatzResearch.WordTrace tailWord_3900083 prefixEnd_3900083 445026038095371031339189 := by
  unfold tailWord_3900083
  simp only [CollatzResearch.WordTrace]
  refine ⟨142247713129672846992080903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94831808753115231328053935 142247713129672846992080903)
  ·
    refine ⟨213371569694509270488121355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142247713129672846992080903 213371569694509270488121355)
    ·
      refine ⟨320057354541763905732182033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213371569694509270488121355 320057354541763905732182033)
      ·
        refine ⟨240043015906322929299136525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320057354541763905732182033 240043015906322929299136525)
        ·
          refine ⟨90016130964871098487176197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240043015906322929299136525 90016130964871098487176197)
          ·
            refine ⟨16878024555913330966345537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90016130964871098487176197 16878024555913330966345537)
            ·
              refine ⟨12658518416934998224759153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16878024555913330966345537 12658518416934998224759153)
              ·
                refine ⟨9493888812701248668569365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12658518416934998224759153 9493888812701248668569365)
                ·
                  refine ⟨445026038095371031339189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9493888812701248668569365 445026038095371031339189)
                  ·
                    rfl

theorem cell22_3900083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 6].length) (baseStart_3900083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900083 prefixEnd_3900083 := by exact prefixLift 3900083
  have htrace : WordTrace (prefixWord ++ tailWord_3900083) baseStart_3900083 baseEnd_3900083 := by
    simpa [prefixWord, tailWord_3900083, baseEnd_3900083] using wordTrace_append hprefix tailTrace_3900083
  have hstable : (prefixWord ++ tailWord_3900083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900083).length < 2 ^ (prefixWord ++ tailWord_3900083).sum := by decide
  have hdescent : baseEnd_3900083 < baseStart_3900083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900132 : List Nat := [2, 3, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_3900132 : Nat := 118140960795 + 3900132 * 2 ^ 59
def prefixEnd_3900132 : Nat := 4983230072969 + 3 ^ 40 * 3900132 * 2
def baseEnd_3900132 : Nat := 1335094887987493299542417

theorem tailTrace_3900132 : CollatzResearch.WordTrace tailWord_3900132 prefixEnd_3900132 1335094887987493299542417 := by
  unfold tailWord_3900132
  simp only [CollatzResearch.WordTrace]
  refine ⟨71124750153247664180307325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94833000204330218907076433 71124750153247664180307325)
  ·
    refine ⟨26671781307467874067615247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71124750153247664180307325 26671781307467874067615247)
    ·
      refine ⟨40007671961201811101422871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26671781307467874067615247 40007671961201811101422871)
      ·
        refine ⟨60011507941802716652134307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40007671961201811101422871 60011507941802716652134307)
        ·
          refine ⟨90017261912704074978201461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60011507941802716652134307 90017261912704074978201461)
          ·
            refine ⟨8439118304316007029206387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90017261912704074978201461 8439118304316007029206387)
            ·
              refine ⟨12658677456474010543809581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8439118304316007029206387 12658677456474010543809581)
              ·
                refine ⟨4747004046177753953928593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12658677456474010543809581 4747004046177753953928593)
                ·
                  refine ⟨3560253034633315465446445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4747004046177753953928593 3560253034633315465446445)
                  ·
                    refine ⟨1335094887987493299542417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3560253034633315465446445 1335094887987493299542417)
                    ·
                      rfl

theorem cell22_3900132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_3900132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900132 prefixEnd_3900132 := by exact prefixLift 3900132
  have htrace : WordTrace (prefixWord ++ tailWord_3900132) baseStart_3900132 baseEnd_3900132 := by
    simpa [prefixWord, tailWord_3900132, baseEnd_3900132] using wordTrace_append hprefix tailTrace_3900132
  have hstable : (prefixWord ++ tailWord_3900132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900132).length < 2 ^ (prefixWord ++ tailWord_3900132).sum := by decide
  have hdescent : baseEnd_3900132 < baseStart_3900132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900252 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 6]
def baseStart_3900252 : Nat := 118140960795 + 3900252 * 2 ^ 59
def prefixEnd_3900252 : Nat := 4983230072969 + 3 ^ 40 * 3900252 * 2
def baseEnd_3900252 : Nat := 445045322146617662180683

theorem tailTrace_3900252 : CollatzResearch.WordTrace tailWord_3900252 prefixEnd_3900252 445045322146617662180683 := by
  unfold tailWord_3900252
  simp only [CollatzResearch.WordTrace]
  refine ⟨71126938533030294427491505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94835918044040392569988673 71126938533030294427491505)
  ·
    refine ⟨53345203899772720820618629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71126938533030294427491505 53345203899772720820618629)
    ·
      refine ⟨10002225731207385153865993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53345203899772720820618629 10002225731207385153865993)
      ·
        refine ⟨7501669298405538865399495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10002225731207385153865993 7501669298405538865399495)
        ·
          refine ⟨11252503947608308298099243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7501669298405538865399495 11252503947608308298099243)
          ·
            refine ⟨16878755921412462447148865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11252503947608308298099243 16878755921412462447148865)
            ·
              refine ⟨12659066941059346835361649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16878755921412462447148865 12659066941059346835361649)
              ·
                refine ⟨9494300205794510126521237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12659066941059346835361649 9494300205794510126521237)
                ·
                  refine ⟨445045322146617662180683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9494300205794510126521237 445045322146617662180683)
                  ·
                    rfl

theorem cell22_3900252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_3900252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900252 prefixEnd_3900252 := by exact prefixLift 3900252
  have htrace : WordTrace (prefixWord ++ tailWord_3900252) baseStart_3900252 baseEnd_3900252 := by
    simpa [prefixWord, tailWord_3900252, baseEnd_3900252] using wordTrace_append hprefix tailTrace_3900252
  have hstable : (prefixWord ++ tailWord_3900252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900252).length < 2 ^ (prefixWord ++ tailWord_3900252).sum := by decide
  have hdescent : baseEnd_3900252 < baseStart_3900252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900286 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_3900286 : Nat := 118140960795 + 3900286 * 2 ^ 59
def prefixEnd_3900286 : Nat := 4983230072969 + 3 ^ 40 * 3900286 * 2
def baseEnd_3900286 : Nat := 445049201778229410397315

theorem tailTrace_3900286 : CollatzResearch.WordTrace tailWord_3900286 prefixEnd_3900286 445049201778229410397315 := by
  unfold tailWord_3900286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17781889643492176582715089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94836744765291608441147141 17781889643492176582715089)
  ·
    refine ⟨13336417232619132437036317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17781889643492176582715089 13336417232619132437036317)
    ·
      refine ⟨5001156462232174663888619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13336417232619132437036317 5001156462232174663888619)
      ·
        refine ⟨7501734693348261995832929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5001156462232174663888619 7501734693348261995832929)
        ·
          refine ⟨5626301020011196496874697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7501734693348261995832929 5626301020011196496874697)
          ·
            refine ⟨4219725765008397372656023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5626301020011196496874697 4219725765008397372656023)
            ·
              refine ⟨6329588647512596058984035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4219725765008397372656023 6329588647512596058984035)
              ·
                refine ⟨9494382971268894088476053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6329588647512596058984035 9494382971268894088476053)
                ·
                  refine ⟨445049201778229410397315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9494382971268894088476053 445049201778229410397315)
                  ·
                    rfl

theorem cell22_3900286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_3900286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900286 prefixEnd_3900286 := by exact prefixLift 3900286
  have htrace : WordTrace (prefixWord ++ tailWord_3900286) baseStart_3900286 baseEnd_3900286 := by
    simpa [prefixWord, tailWord_3900286, baseEnd_3900286] using wordTrace_append hprefix tailTrace_3900286
  have hstable : (prefixWord ++ tailWord_3900286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900286).length < 2 ^ (prefixWord ++ tailWord_3900286).sum := by decide
  have hdescent : baseEnd_3900286 < baseStart_3900286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900329 : List Nat := [1, 2, 1, 1, 1, 1, 6, 5, 1, 3]
def baseStart_3900329 : Nat := 118140960795 + 3900329 * 2 ^ 59
def prefixEnd_3900329 : Nat := 4983230072969 + 3 ^ 40 * 3900329 * 2
def baseEnd_3900329 : Nat := 1335162325113450452366813

theorem tailTrace_3900329 : CollatzResearch.WordTrace tailWord_3900329 prefixEnd_3900329 1335162325113450452366813 := by
  unfold tailWord_3900329
  simp only [CollatzResearch.WordTrace]
  refine ⟨142256685486781631005536041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94837790324521087337024027 142256685486781631005536041)
  ·
    refine ⟨106692514115086223254152031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142256685486781631005536041 106692514115086223254152031)
    ·
      refine ⟨160038771172629334881228047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106692514115086223254152031 160038771172629334881228047)
      ·
        refine ⟨240058156758944002321842071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160038771172629334881228047 240058156758944002321842071)
        ·
          refine ⟨360087235138416003482763107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240058156758944002321842071 360087235138416003482763107)
          ·
            refine ⟨540130852707624005224144661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360087235138416003482763107 540130852707624005224144661)
            ·
              refine ⟨25318633720669875244881781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 540130852707624005224144661 25318633720669875244881781)
              ·
                refine ⟨2373621911312800804207667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25318633720669875244881781 2373621911312800804207667)
                ·
                  refine ⟨3560432866969201206311501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373621911312800804207667 3560432866969201206311501)
                  ·
                    refine ⟨1335162325113450452366813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3560432866969201206311501 1335162325113450452366813)
                    ·
                      rfl

theorem cell22_3900329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 1, 3].length) (baseStart_3900329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900329 prefixEnd_3900329 := by exact prefixLift 3900329
  have htrace : WordTrace (prefixWord ++ tailWord_3900329) baseStart_3900329 baseEnd_3900329 := by
    simpa [prefixWord, tailWord_3900329, baseEnd_3900329] using wordTrace_append hprefix tailTrace_3900329
  have hstable : (prefixWord ++ tailWord_3900329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900329).length < 2 ^ (prefixWord ++ tailWord_3900329).sum := by decide
  have hdescent : baseEnd_3900329 < baseStart_3900329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900417 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3900417 : Nat := 118140960795 + 3900417 * 2 ^ 59
def prefixEnd_3900417 : Nat := 4983230072969 + 3 ^ 40 * 3900417 * 2
def baseEnd_3900417 : Nat := 1335192449311847556166543

theorem tailTrace_3900417 : CollatzResearch.WordTrace tailWord_3900417 prefixEnd_3900417 1335192449311847556166543 := by
  unfold tailWord_3900417
  simp only [CollatzResearch.WordTrace]
  refine ⟨142259895110462822034739505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94839930073641881356493003 142259895110462822034739505)
  ·
    refine ⟨106694921332847116526054629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142259895110462822034739505 106694921332847116526054629)
    ·
      refine ⟨20005297749908834348635243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106694921332847116526054629 20005297749908834348635243)
      ·
        refine ⟨30007946624863251522952865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20005297749908834348635243 30007946624863251522952865)
        ·
          refine ⟨22505959968647438642214649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30007946624863251522952865 22505959968647438642214649)
          ·
            refine ⟨16879469976485578981660987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22505959968647438642214649 16879469976485578981660987)
            ·
              refine ⟨25319204964728368472491481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16879469976485578981660987 25319204964728368472491481)
              ·
                refine ⟨18989403723546276354368611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25319204964728368472491481 18989403723546276354368611)
                ·
                  refine ⟨28484105585319414531552917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18989403723546276354368611 28484105585319414531552917)
                  ·
                    refine ⟨1335192449311847556166543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28484105585319414531552917 1335192449311847556166543)
                    ·
                      rfl

theorem cell22_3900417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3900417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900417 prefixEnd_3900417 := by exact prefixLift 3900417
  have htrace : WordTrace (prefixWord ++ tailWord_3900417) baseStart_3900417 baseEnd_3900417 := by
    simpa [prefixWord, tailWord_3900417, baseEnd_3900417] using wordTrace_append hprefix tailTrace_3900417
  have hstable : (prefixWord ++ tailWord_3900417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900417).length < 2 ^ (prefixWord ++ tailWord_3900417).sum := by decide
  have hdescent : baseEnd_3900417 < baseStart_3900417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900470 : List Nat := [5, 1, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_3900470 : Nat := 118140960795 + 3900470 * 2 ^ 59
def prefixEnd_3900470 : Nat := 4983230072969 + 3 ^ 40 * 3900470 * 2
def baseEnd_3900470 : Nat := 1335210592294973084591381

theorem tailTrace_3900470 : CollatzResearch.WordTrace tailWord_3900470 prefixEnd_3900470 1335210592294973084591381 := by
  unfold tailWord_3900470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8891364261204425755401179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94841218786180541390945909 8891364261204425755401179)
  ·
    refine ⟨13337046391806638633101769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8891364261204425755401179 13337046391806638633101769)
    ·
      refine ⟨10002784793854978974826327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13337046391806638633101769 10002784793854978974826327)
      ·
        refine ⟨15004177190782468462239491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10002784793854978974826327 15004177190782468462239491)
        ·
          refine ⟨22506265786173702693359237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15004177190782468462239491 22506265786173702693359237)
          ·
            refine ⟨4219924834907569255004857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22506265786173702693359237 4219924834907569255004857)
            ·
              refine ⟨3164943626180676941253643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4219924834907569255004857 3164943626180676941253643)
              ·
                refine ⟨4747415439271015411880465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164943626180676941253643 4747415439271015411880465)
                ·
                  refine ⟨3560561579453261558910349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4747415439271015411880465 3560561579453261558910349)
                  ·
                    refine ⟨1335210592294973084591381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3560561579453261558910349 1335210592294973084591381)
                    ·
                      rfl

theorem cell22_3900470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_3900470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900470 prefixEnd_3900470 := by exact prefixLift 3900470
  have htrace : WordTrace (prefixWord ++ tailWord_3900470) baseStart_3900470 baseEnd_3900470 := by
    simpa [prefixWord, tailWord_3900470, baseEnd_3900470] using wordTrace_append hprefix tailTrace_3900470
  have hstable : (prefixWord ++ tailWord_3900470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900470).length < 2 ^ (prefixWord ++ tailWord_3900470).sum := by decide
  have hdescent : baseEnd_3900470 < baseStart_3900470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900492 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_3900492 : Nat := 118140960795 + 3900492 * 2 ^ 59
def prefixEnd_3900492 : Nat := 4983230072969 + 3 ^ 40 * 3900492 * 2
def baseEnd_3900492 : Nat := 1335218123344572360541313

theorem tailTrace_3900492 : CollatzResearch.WordTrace tailWord_3900492 prefixEnd_3900492 1335218123344572360541313 := by
  unfold tailWord_3900492
  simp only [CollatzResearch.WordTrace]
  refine ⟨71131315292595554921859865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94841753723460739895813153 71131315292595554921859865)
  ·
    refine ⟨53348486469446666191394899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71131315292595554921859865 53348486469446666191394899)
    ·
      refine ⟨80022729704169999287092349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53348486469446666191394899 80022729704169999287092349)
      ·
        refine ⟨30008523639063749732659631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80022729704169999287092349 30008523639063749732659631)
        ·
          refine ⟨45012785458595624598989447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30008523639063749732659631 45012785458595624598989447)
          ·
            refine ⟨67519178187893436898484171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45012785458595624598989447 67519178187893436898484171)
            ·
              refine ⟨101278767281840155347726257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67519178187893436898484171 101278767281840155347726257)
              ·
                refine ⟨75959075461380116510794693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101278767281840155347726257 75959075461380116510794693)
                ·
                  refine ⟨14242326649008771845774005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75959075461380116510794693 14242326649008771845774005)
                  ·
                    refine ⟨1335218123344572360541313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14242326649008771845774005 1335218123344572360541313)
                    ·
                      rfl

theorem cell22_3900492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_3900492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900492 prefixEnd_3900492 := by exact prefixLift 3900492
  have htrace : WordTrace (prefixWord ++ tailWord_3900492) baseStart_3900492 baseEnd_3900492 := by
    simpa [prefixWord, tailWord_3900492, baseEnd_3900492] using wordTrace_append hprefix tailTrace_3900492
  have hstable : (prefixWord ++ tailWord_3900492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900492).length < 2 ^ (prefixWord ++ tailWord_3900492).sum := by decide
  have hdescent : baseEnd_3900492 < baseStart_3900492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900554 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_3900554 : Nat := 118140960795 + 3900554 * 2 ^ 59
def prefixEnd_3900554 : Nat := 4983230072969 + 3 ^ 40 * 3900554 * 2
def baseEnd_3900554 : Nat := 1335239347211624865491123

theorem tailTrace_3900554 : CollatzResearch.WordTrace tailWord_3900554 prefixEnd_3900554 1335239347211624865491123 := by
  unfold tailWord_3900554
  simp only [CollatzResearch.WordTrace]
  refine ⟨35566222977741623608119179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94843261273977662954984477 35566222977741623608119179)
  ·
    refine ⟨53349334466612435412178769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35566222977741623608119179 53349334466612435412178769)
    ·
      refine ⟨40012000849959326559134077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53349334466612435412178769 40012000849959326559134077)
      ·
        refine ⟨15004500318734747459675279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40012000849959326559134077 15004500318734747459675279)
        ·
          refine ⟨22506750478102121189512919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15004500318734747459675279 22506750478102121189512919)
          ·
            refine ⟨33760125717153181784269379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22506750478102121189512919 33760125717153181784269379)
            ·
              refine ⟨50640188575729772676404069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33760125717153181784269379 50640188575729772676404069)
              ·
                refine ⟨9495035357949332376825763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50640188575729772676404069 9495035357949332376825763)
                ·
                  refine ⟨14242553036923998565238645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9495035357949332376825763 14242553036923998565238645)
                  ·
                    refine ⟨1335239347211624865491123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14242553036923998565238645 1335239347211624865491123)
                    ·
                      rfl

theorem cell22_3900554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_3900554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900554 prefixEnd_3900554 := by exact prefixLift 3900554
  have htrace : WordTrace (prefixWord ++ tailWord_3900554) baseStart_3900554 baseEnd_3900554 := by
    simpa [prefixWord, tailWord_3900554, baseEnd_3900554] using wordTrace_append hprefix tailTrace_3900554
  have hstable : (prefixWord ++ tailWord_3900554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900554).length < 2 ^ (prefixWord ++ tailWord_3900554).sum := by decide
  have hdescent : baseEnd_3900554 < baseStart_3900554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900558 : List Nat := [4, 1, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_3900558 : Nat := 118140960795 + 3900558 * 2 ^ 59
def prefixEnd_3900558 : Nat := 4983230072969 + 3 ^ 40 * 3900558 * 2
def baseEnd_3900558 : Nat := 1335240716493370188391111

theorem tailTrace_3900558 : CollatzResearch.WordTrace tailWord_3900558 prefixEnd_3900558 1335240716493370188391111 := by
  unfold tailWord_3900558
  simp only [CollatzResearch.WordTrace]
  refine ⟨17783129725369000389452791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94843358535301335410414885 17783129725369000389452791)
  ·
    refine ⟨26674694588053500584179187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17783129725369000389452791 26674694588053500584179187)
    ·
      refine ⟨40012041882080250876268781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26674694588053500584179187 40012041882080250876268781)
      ·
        refine ⟨15004515705780094078600793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40012041882080250876268781 15004515705780094078600793)
        ·
          refine ⟨11253386779335070558950595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15004515705780094078600793 11253386779335070558950595)
          ·
            refine ⟨16880080169002605838425893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11253386779335070558950595 16880080169002605838425893)
            ·
              refine ⟨3165015031687988594704855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16880080169002605838425893 3165015031687988594704855)
              ·
                refine ⟨4747522547531982892057283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165015031687988594704855 4747522547531982892057283)
                ·
                  refine ⟨7121283821297974338085925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4747522547531982892057283 7121283821297974338085925)
                  ·
                    refine ⟨1335240716493370188391111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7121283821297974338085925 1335240716493370188391111)
                    ·
                      rfl

theorem cell22_3900558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_3900558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900558 prefixEnd_3900558 := by exact prefixLift 3900558
  have htrace : WordTrace (prefixWord ++ tailWord_3900558) baseStart_3900558 baseEnd_3900558 := by
    simpa [prefixWord, tailWord_3900558, baseEnd_3900558] using wordTrace_append hprefix tailTrace_3900558
  have hstable : (prefixWord ++ tailWord_3900558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900558).length < 2 ^ (prefixWord ++ tailWord_3900558).sum := by decide
  have hdescent : baseEnd_3900558 < baseStart_3900558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900586 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3900586 : Nat := 118140960795 + 3900586 * 2 ^ 59
def prefixEnd_3900586 : Nat := 4983230072969 + 3 ^ 40 * 3900586 * 2
def baseEnd_3900586 : Nat := 1335250301465587448691025

theorem tailTrace_3900586 : CollatzResearch.WordTrace tailWord_3900586 prefixEnd_3900586 1335250301465587448691025 := by
  unfold tailWord_3900586
  simp only [CollatzResearch.WordTrace]
  refine ⟨35566514761712640974410403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94844039364567042598427741 35566514761712640974410403)
  ·
    refine ⟨53349772142568961461615605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35566514761712640974410403 53349772142568961461615605)
    ·
      refine ⟨5001541138365840137026463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53349772142568961461615605 5001541138365840137026463)
      ·
        refine ⟨7502311707548760205539695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5001541138365840137026463 7502311707548760205539695)
        ·
          refine ⟨11253467561323140308309543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502311707548760205539695 11253467561323140308309543)
          ·
            refine ⟨16880201341984710462464315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11253467561323140308309543 16880201341984710462464315)
            ·
              refine ⟨25320302012977065693696473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16880201341984710462464315 25320302012977065693696473)
              ·
                refine ⟨18990226509732799270272355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25320302012977065693696473 18990226509732799270272355)
                ·
                  refine ⟨28485339764599198905408533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18990226509732799270272355 28485339764599198905408533)
                  ·
                    refine ⟨1335250301465587448691025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28485339764599198905408533 1335250301465587448691025)
                    ·
                      rfl

theorem cell22_3900586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3900586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900586 prefixEnd_3900586 := by exact prefixLift 3900586
  have htrace : WordTrace (prefixWord ++ tailWord_3900586) baseStart_3900586 baseEnd_3900586 := by
    simpa [prefixWord, tailWord_3900586, baseEnd_3900586] using wordTrace_append hprefix tailTrace_3900586
  have hstable : (prefixWord ++ tailWord_3900586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900586).length < 2 ^ (prefixWord ++ tailWord_3900586).sum := by decide
  have hdescent : baseEnd_3900586 < baseStart_3900586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900601 : List Nat := [1, 2, 1, 4, 1, 5, 2, 6]
def baseStart_3900601 : Nat := 118140960795 + 3900601 * 2 ^ 59
def prefixEnd_3900601 : Nat := 4983230072969 + 3 ^ 40 * 3900601 * 2
def baseEnd_3900601 : Nat := 148361715141348045507331

theorem tailTrace_3900601 : CollatzResearch.WordTrace tailWord_3900601 prefixEnd_3900601 148361715141348045507331 := by
  unfold tailWord_3900601
  simp only [CollatzResearch.WordTrace]
  refine ⟨142266606141796221459437657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94844404094530814306291771 142266606141796221459437657)
  ·
    refine ⟨106699954606347166094578243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142266606141796221459437657 106699954606347166094578243)
    ·
      refine ⟨160049931909520749141867365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106699954606347166094578243 160049931909520749141867365)
      ·
        refine ⟨30009362233035140464100131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160049931909520749141867365 30009362233035140464100131)
        ·
          refine ⟨45014043349552710696150197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30009362233035140464100131 45014043349552710696150197)
          ·
            refine ⟨4220066564020566627764081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45014043349552710696150197 4220066564020566627764081)
            ·
              refine ⟨3165049923015424970823061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4220066564020566627764081 3165049923015424970823061)
              ·
                refine ⟨148361715141348045507331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3165049923015424970823061 148361715141348045507331)
                ·
                  rfl

theorem cell22_3900601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 6].length) (baseStart_3900601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900601 prefixEnd_3900601 := by exact prefixLift 3900601
  have htrace : WordTrace (prefixWord ++ tailWord_3900601) baseStart_3900601 baseEnd_3900601 := by
    simpa [prefixWord, tailWord_3900601, baseEnd_3900601] using wordTrace_append hprefix tailTrace_3900601
  have hstable : (prefixWord ++ tailWord_3900601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900601).length < 2 ^ (prefixWord ++ tailWord_3900601).sum := by decide
  have hdescent : baseEnd_3900601 < baseStart_3900601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900644 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_3900644 : Nat := 118140960795 + 3900644 * 2 ^ 59
def prefixEnd_3900644 : Nat := 4983230072969 + 3 ^ 40 * 3900644 * 2
def baseEnd_3900644 : Nat := 1335270156050894630740847

theorem tailTrace_3900644 : CollatzResearch.WordTrace tailWord_3900644 prefixEnd_3900644 1335270156050894630740847 := by
  unfold tailWord_3900644
  simp only [CollatzResearch.WordTrace]
  refine ⟨71134087240320219901626493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94845449653760293202168657 71134087240320219901626493)
  ·
    refine ⟨26675282715120082463109935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71134087240320219901626493 26675282715120082463109935)
    ·
      refine ⟨40012924072680123694664903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26675282715120082463109935 40012924072680123694664903)
      ·
        refine ⟨60019386109020185541997355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40012924072680123694664903 60019386109020185541997355)
        ·
          refine ⟨90029079163530278312996033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60019386109020185541997355 90029079163530278312996033)
          ·
            refine ⟨67521809372647708734747025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90029079163530278312996033 67521809372647708734747025)
            ·
              refine ⟨50641357029485781551060269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67521809372647708734747025 50641357029485781551060269)
              ·
                refine ⟨18990508886057168081647601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50641357029485781551060269 18990508886057168081647601)
                ·
                  refine ⟨14242881664542876061235701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18990508886057168081647601 14242881664542876061235701)
                  ·
                    refine ⟨1335270156050894630740847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14242881664542876061235701 1335270156050894630740847)
                    ·
                      rfl

theorem cell22_3900644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_3900644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900644 prefixEnd_3900644 := by exact prefixLift 3900644
  have htrace : WordTrace (prefixWord ++ tailWord_3900644) baseStart_3900644 baseEnd_3900644 := by
    simpa [prefixWord, tailWord_3900644, baseEnd_3900644] using wordTrace_append hprefix tailTrace_3900644
  have hstable : (prefixWord ++ tailWord_3900644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900644).length < 2 ^ (prefixWord ++ tailWord_3900644).sum := by decide
  have hdescent : baseEnd_3900644 < baseStart_3900644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900689 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 3, 5]
def baseStart_3900689 : Nat := 118140960795 + 3900689 * 2 ^ 59
def prefixEnd_3900689 : Nat := 4983230072969 + 3 ^ 40 * 3900689 * 2
def baseEnd_3900689 : Nat := 1335285560470529513365709

theorem tailTrace_3900689 : CollatzResearch.WordTrace tailWord_3900689 prefixEnd_3900689 1335285560470529513365709 := by
  unfold tailWord_3900689
  simp only [CollatzResearch.WordTrace]
  refine ⟨142269815765477412488641121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94846543843651608325760747 142269815765477412488641121)
  ·
    refine ⟨106702361824108059366480841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142269815765477412488641121 106702361824108059366480841)
    ·
      refine ⟨80026771368081044524860631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106702361824108059366480841 80026771368081044524860631)
      ·
        refine ⟨120040157052121566787290947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80026771368081044524860631 120040157052121566787290947)
        ·
          refine ⟨180060235578182350180936421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120040157052121566787290947 180060235578182350180936421)
          ·
            refine ⟨33761294170909190658925579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180060235578182350180936421 33761294170909190658925579)
            ·
              refine ⟨50641941256363785988388369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33761294170909190658925579 50641941256363785988388369)
              ·
                refine ⟨37981455942272839491291277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50641941256363785988388369 37981455942272839491291277)
                ·
                  refine ⟨14243045978352314809234229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37981455942272839491291277 14243045978352314809234229)
                  ·
                    refine ⟨1335285560470529513365709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14243045978352314809234229 1335285560470529513365709)
                    ·
                      rfl

theorem cell22_3900689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_3900689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900689 prefixEnd_3900689 := by exact prefixLift 3900689
  have htrace : WordTrace (prefixWord ++ tailWord_3900689) baseStart_3900689 baseEnd_3900689 := by
    simpa [prefixWord, tailWord_3900689, baseEnd_3900689] using wordTrace_append hprefix tailTrace_3900689
  have hstable : (prefixWord ++ tailWord_3900689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900689).length < 2 ^ (prefixWord ++ tailWord_3900689).sum := by decide
  have hdescent : baseEnd_3900689 < baseStart_3900689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900721 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 1, 6]
def baseStart_3900721 : Nat := 118140960795 + 3900721 * 2 ^ 59
def prefixEnd_3900721 : Nat := 4983230072969 + 3 ^ 40 * 3900721 * 2
def baseEnd_3900721 : Nat := 1335296514724492096565611

theorem tailTrace_3900721 : CollatzResearch.WordTrace tailWord_3900721 prefixEnd_3900721 1335296514724492096565611 := by
  unfold tailWord_3900721
  simp only [CollatzResearch.WordTrace]
  refine ⟨142270982901361481953806017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94847321934240987969204011 142270982901361481953806017)
  ·
    refine ⟨106703237176021111465354513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142270982901361481953806017 106703237176021111465354513)
    ·
      refine ⟨80027427882015833599015885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106703237176021111465354513 80027427882015833599015885)
      ·
        refine ⟨30010285455755937599630957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80027427882015833599015885 30010285455755937599630957)
        ·
          refine ⟨11253857045908476599861609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30010285455755937599630957 11253857045908476599861609)
          ·
            refine ⟨8440392784431357449896207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11253857045908476599861609 8440392784431357449896207)
            ·
              refine ⟨12660589176647036174844311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8440392784431357449896207 12660589176647036174844311)
              ·
                refine ⟨18990883764970554262266467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12660589176647036174844311 18990883764970554262266467)
                ·
                  refine ⟨28486325647455831393399701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18990883764970554262266467 28486325647455831393399701)
                  ·
                    refine ⟨1335296514724492096565611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28486325647455831393399701 1335296514724492096565611)
                    ·
                      rfl

theorem cell22_3900721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_3900721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900721 prefixEnd_3900721 := by exact prefixLift 3900721
  have htrace : WordTrace (prefixWord ++ tailWord_3900721) baseStart_3900721 baseEnd_3900721 := by
    simpa [prefixWord, tailWord_3900721, baseEnd_3900721] using wordTrace_append hprefix tailTrace_3900721
  have hstable : (prefixWord ++ tailWord_3900721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900721).length < 2 ^ (prefixWord ++ tailWord_3900721).sum := by decide
  have hdescent : baseEnd_3900721 < baseStart_3900721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900740 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3900740 : Nat := 118140960795 + 3900740 * 2 ^ 59
def prefixEnd_3900740 : Nat := 4983230072969 + 3 ^ 40 * 3900740 * 2
def baseEnd_3900740 : Nat := 1335303018812782380340553

theorem tailTrace_3900740 : CollatzResearch.WordTrace tailWord_3900740 prefixEnd_3900740 1335303018812782380340553 := by
  unfold tailWord_3900740
  simp only [CollatzResearch.WordTrace]
  refine ⟨71135837944146324099373837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94847783925528432132498449 71135837944146324099373837)
  ·
    refine ⟨26675939229054871537265189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71135837944146324099373837 26675939229054871537265189)
    ·
      refine ⟨5001738605447788413237223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26675939229054871537265189 5001738605447788413237223)
      ·
        refine ⟨7502607908171682619855835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5001738605447788413237223 7502607908171682619855835)
        ·
          refine ⟨11253911862257523929783753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502607908171682619855835 11253911862257523929783753)
          ·
            refine ⟨8440433896693142947337815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11253911862257523929783753 8440433896693142947337815)
            ·
              refine ⟨12660650845039714421006723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8440433896693142947337815 12660650845039714421006723)
              ·
                refine ⟨18990976267559571631510085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12660650845039714421006723 18990976267559571631510085)
                ·
                  refine ⟨3560808050167419680908141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18990976267559571631510085 3560808050167419680908141)
                  ·
                    refine ⟨1335303018812782380340553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3560808050167419680908141 1335303018812782380340553)
                    ·
                      rfl

theorem cell22_3900740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3900740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900740 prefixEnd_3900740 := by exact prefixLift 3900740
  have htrace : WordTrace (prefixWord ++ tailWord_3900740) baseStart_3900740 baseEnd_3900740 := by
    simpa [prefixWord, tailWord_3900740, baseEnd_3900740] using wordTrace_append hprefix tailTrace_3900740
  have hstable : (prefixWord ++ tailWord_3900740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900740).length < 2 ^ (prefixWord ++ tailWord_3900740).sum := by decide
  have hdescent : baseEnd_3900740 < baseStart_3900740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900742 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_3900742 : Nat := 118140960795 + 3900742 * 2 ^ 59
def prefixEnd_3900742 : Nat := 4983230072969 + 3 ^ 40 * 3900742 * 2
def baseEnd_3900742 : Nat := 445101234484551680596849

theorem tailTrace_3900742 : CollatzResearch.WordTrace tailWord_3900742 prefixEnd_3900742 445101234484551680596849 := by
  unfold tailWord_3900742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4445992151071418829385015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94847832556190268360213653 4445992151071418829385015)
  ·
    refine ⟨6668988226607128244077523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4445992151071418829385015 6668988226607128244077523)
    ·
      refine ⟨10003482339910692366116285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6668988226607128244077523 10003482339910692366116285)
      ·
        refine ⟨3751305877466509637293607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10003482339910692366116285 3751305877466509637293607)
        ·
          refine ⟨5626958816199764455940411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751305877466509637293607 5626958816199764455940411)
          ·
            refine ⟨8440438224299646683910617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5626958816199764455940411 8440438224299646683910617)
            ·
              refine ⟨6330328668224735012932963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8440438224299646683910617 6330328668224735012932963)
              ·
                refine ⟨9495493002337102519399445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330328668224735012932963 9495493002337102519399445)
                ·
                  refine ⟨445101234484551680596849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9495493002337102519399445 445101234484551680596849)
                  ·
                    rfl

theorem cell22_3900742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_3900742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900742 prefixEnd_3900742 := by exact prefixLift 3900742
  have htrace : WordTrace (prefixWord ++ tailWord_3900742) baseStart_3900742 baseEnd_3900742 := by
    simpa [prefixWord, tailWord_3900742, baseEnd_3900742] using wordTrace_append hprefix tailTrace_3900742
  have hstable : (prefixWord ++ tailWord_3900742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900742).length < 2 ^ (prefixWord ++ tailWord_3900742).sum := by decide
  have hdescent : baseEnd_3900742 < baseStart_3900742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900768 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 3, 3]
def baseStart_3900768 : Nat := 118140960795 + 3900768 * 2 ^ 59
def prefixEnd_3900768 : Nat := 4983230072969 + 3 ^ 40 * 3900768 * 2
def baseEnd_3900768 : Nat := 1335312603784999640640467

theorem tailTrace_3900768 : CollatzResearch.WordTrace tailWord_3900768 prefixEnd_3900768 1335312603784999640640467 := by
  unfold tailWord_3900768
  simp only [CollatzResearch.WordTrace]
  refine ⟨71136348566095604490383479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94848464754794139320511305 71136348566095604490383479)
  ·
    refine ⟨106704522849143406735575219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71136348566095604490383479 106704522849143406735575219)
    ·
      refine ⟨160056784273715110103362829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106704522849143406735575219 160056784273715110103362829)
      ·
        refine ⟨60021294102643166288761061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160056784273715110103362829 60021294102643166288761061)
        ·
          refine ⟨11253992644245593679142699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60021294102643166288761061 11253992644245593679142699)
          ·
            refine ⟨16880988966368390518714049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11253992644245593679142699 16880988966368390518714049)
            ·
              refine ⟨12660741724776292889035537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16880988966368390518714049 12660741724776292889035537)
              ·
                refine ⟨9495556293582219666776653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12660741724776292889035537 9495556293582219666776653)
                ·
                  refine ⟨3560833610093332375041245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9495556293582219666776653 3560833610093332375041245)
                  ·
                    refine ⟨1335312603784999640640467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3560833610093332375041245 1335312603784999640640467)
                    ·
                      rfl

theorem cell22_3900768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 3, 3].length) (baseStart_3900768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900768 prefixEnd_3900768 := by exact prefixLift 3900768
  have htrace : WordTrace (prefixWord ++ tailWord_3900768) baseStart_3900768 baseEnd_3900768 := by
    simpa [prefixWord, tailWord_3900768, baseEnd_3900768] using wordTrace_append hprefix tailTrace_3900768
  have hstable : (prefixWord ++ tailWord_3900768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900768).length < 2 ^ (prefixWord ++ tailWord_3900768).sum := by decide
  have hdescent : baseEnd_3900768 < baseStart_3900768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900781 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 7]
def baseStart_3900781 : Nat := 118140960795 + 3900781 * 2 ^ 59
def prefixEnd_3900781 : Nat := 4983230072969 + 3 ^ 40 * 3900781 * 2
def baseEnd_3900781 : Nat := 445105684650223980021809

theorem tailTrace_3900781 : CollatzResearch.WordTrace tailWord_3900781 prefixEnd_3900781 445105684650223980021809 := by
  unfold tailWord_3900781
  simp only [CollatzResearch.WordTrace]
  refine ⟨142273171281144112200990197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94848780854096074800660131 142273171281144112200990197)
  ·
    refine ⟨13338109807607260518842831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142273171281144112200990197 13338109807607260518842831)
    ·
      refine ⟨20007164711410890778264247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13338109807607260518842831 20007164711410890778264247)
      ·
        refine ⟨30010747067116336167396371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20007164711410890778264247 30010747067116336167396371)
        ·
          refine ⟨45016120600674504251094557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30010747067116336167396371 45016120600674504251094557)
          ·
            refine ⟨16881045225252939094160459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45016120600674504251094557 16881045225252939094160459)
            ·
              refine ⟨25321567837879408641240689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16881045225252939094160459 25321567837879408641240689)
              ·
                refine ⟨18991175878409556480930517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25321567837879408641240689 18991175878409556480930517)
                ·
                  refine ⟨445105684650223980021809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18991175878409556480930517 445105684650223980021809)
                  ·
                    rfl

theorem cell22_3900781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_3900781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900781 prefixEnd_3900781 := by exact prefixLift 3900781
  have htrace : WordTrace (prefixWord ++ tailWord_3900781) baseStart_3900781 baseEnd_3900781 := by
    simpa [prefixWord, tailWord_3900781, baseEnd_3900781] using wordTrace_append hprefix tailTrace_3900781
  have hstable : (prefixWord ++ tailWord_3900781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900781).length < 2 ^ (prefixWord ++ tailWord_3900781).sum := by decide
  have hdescent : baseEnd_3900781 < baseStart_3900781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900785 : List Nat := [1, 2, 2, 2, 1, 2, 5, 3, 1, 3]
def baseStart_3900785 : Nat := 118140960795 + 3900785 * 2 ^ 59
def prefixEnd_3900785 : Nat := 4983230072969 + 3 ^ 40 * 3900785 * 2
def baseEnd_3900785 : Nat := 1335318423232417262965415

theorem tailTrace_3900785 : CollatzResearch.WordTrace tailWord_3900785 prefixEnd_3900785 1335318423232417262965415 := by
  unfold tailWord_3900785
  simp only [CollatzResearch.WordTrace]
  refine ⟨142273317173129620884135809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94848878115419747256090539 142273317173129620884135809)
  ·
    refine ⟨106704987879847215663101857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142273317173129620884135809 106704987879847215663101857)
    ·
      refine ⟨80028740909885411747326393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106704987879847215663101857 80028740909885411747326393)
      ·
        refine ⟨60021555682414058810494795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80028740909885411747326393 60021555682414058810494795)
        ·
          refine ⟨90032333523621088215742193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60021555682414058810494795 90032333523621088215742193)
          ·
            refine ⟨67524250142715816161806645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90032333523621088215742193 67524250142715816161806645)
            ·
              refine ⟨6330398450879607765169373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67524250142715816161806645 6330398450879607765169373)
              ·
                refine ⟨2373899419079852911938515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6330398450879607765169373 2373899419079852911938515)
                ·
                  refine ⟨3560849128619779367907773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373899419079852911938515 3560849128619779367907773)
                  ·
                    refine ⟨1335318423232417262965415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3560849128619779367907773 1335318423232417262965415)
                    ·
                      rfl

theorem cell22_3900785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_3900785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900785 prefixEnd_3900785 := by exact prefixLift 3900785
  have htrace : WordTrace (prefixWord ++ tailWord_3900785) baseStart_3900785 baseEnd_3900785 := by
    simpa [prefixWord, tailWord_3900785, baseEnd_3900785] using wordTrace_append hprefix tailTrace_3900785
  have hstable : (prefixWord ++ tailWord_3900785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900785).length < 2 ^ (prefixWord ++ tailWord_3900785).sum := by decide
  have hdescent : baseEnd_3900785 < baseStart_3900785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900802 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3900802 : Nat := 118140960795 + 3900802 * 2 ^ 59
def prefixEnd_3900802 : Nat := 4983230072969 + 3 ^ 40 * 3900802 * 2
def baseEnd_3900802 : Nat := 1335324242679834885290363

theorem tailTrace_3900802 : CollatzResearch.WordTrace tailWord_3900802 prefixEnd_3900802 1335324242679834885290363 := by
  unfold tailWord_3900802
  simp only [CollatzResearch.WordTrace]
  refine ⟨35568484303517008196876165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94849291476045355191669773 35568484303517008196876165)
  ·
    refine ⟨6669090806909439036914281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35568484303517008196876165 6669090806909439036914281)
    ·
      refine ⟨5001818105182079277685711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6669090806909439036914281 5001818105182079277685711)
      ·
        refine ⟨7502727157773118916528567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5001818105182079277685711 7502727157773118916528567)
        ·
          refine ⟨11254090736659678374792851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502727157773118916528567 11254090736659678374792851)
          ·
            refine ⟨16881136104989517562189277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11254090736659678374792851 16881136104989517562189277)
            ·
              refine ⟨6330426039371069085820979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16881136104989517562189277 6330426039371069085820979)
              ·
                refine ⟨9495639059056603628731469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330426039371069085820979 9495639059056603628731469)
                ·
                  refine ⟨3560864647146226360774301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9495639059056603628731469 3560864647146226360774301)
                  ·
                    refine ⟨1335324242679834885290363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3560864647146226360774301 1335324242679834885290363)
                    ·
                      rfl

theorem cell22_3900802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3900802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900802 prefixEnd_3900802 := by exact prefixLift 3900802
  have htrace : WordTrace (prefixWord ++ tailWord_3900802) baseStart_3900802 baseEnd_3900802 := by
    simpa [prefixWord, tailWord_3900802, baseEnd_3900802] using wordTrace_append hprefix tailTrace_3900802
  have hstable : (prefixWord ++ tailWord_3900802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900802).length < 2 ^ (prefixWord ++ tailWord_3900802).sum := by decide
  have hdescent : baseEnd_3900802 < baseStart_3900802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900811 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 3, 4]
def baseStart_3900811 : Nat := 118140960795 + 3900811 * 2 ^ 59
def prefixEnd_3900811 : Nat := 4983230072969 + 3 ^ 40 * 3900811 * 2
def baseEnd_3900811 : Nat := 1335327323563761861815335

theorem tailTrace_3900811 : CollatzResearch.WordTrace tailWord_3900811 prefixEnd_3900811 1335327323563761861815335 := by
  unfold tailWord_3900811
  simp only [CollatzResearch.WordTrace]
  refine ⟨142274265471035427324582287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94849510314023618216388191 142274265471035427324582287)
  ·
    refine ⟨213411398206553140986873431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142274265471035427324582287 213411398206553140986873431)
    ·
      refine ⟨320117097309829711480310147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213411398206553140986873431 320117097309829711480310147)
      ·
        refine ⟨480175645964744567220465221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320117097309829711480310147 480175645964744567220465221)
        ·
          refine ⟨90032933618389606353837229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 480175645964744567220465221 90032933618389606353837229)
          ·
            refine ⟨33762350106896102382688961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90032933618389606353837229 33762350106896102382688961)
            ·
              refine ⟨25321762580172076787016721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33762350106896102382688961 25321762580172076787016721)
              ·
                refine ⟨18991321935129057590262541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25321762580172076787016721 18991321935129057590262541)
                ·
                  refine ⟨7121745725673396596348453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18991321935129057590262541 7121745725673396596348453)
                  ·
                    refine ⟨1335327323563761861815335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7121745725673396596348453 1335327323563761861815335)
                    ·
                      rfl

theorem cell22_3900811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 4].length) (baseStart_3900811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900811 prefixEnd_3900811 := by exact prefixLift 3900811
  have htrace : WordTrace (prefixWord ++ tailWord_3900811) baseStart_3900811 baseEnd_3900811 := by
    simpa [prefixWord, tailWord_3900811, baseEnd_3900811] using wordTrace_append hprefix tailTrace_3900811
  have hstable : (prefixWord ++ tailWord_3900811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900811).length < 2 ^ (prefixWord ++ tailWord_3900811).sum := by decide
  have hdescent : baseEnd_3900811 < baseStart_3900811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900826 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 8]
def baseStart_3900826 : Nat := 118140960795 + 3900826 * 2 ^ 59
def prefixEnd_3900826 : Nat := 4983230072969 + 3 ^ 40 * 3900826 * 2
def baseEnd_3900826 : Nat := 445110819456768940896763

theorem tailTrace_3900826 : CollatzResearch.WordTrace tailWord_3900826 prefixEnd_3900826 445110819456768940896763 := by
  unfold tailWord_3900826
  simp only [CollatzResearch.WordTrace]
  refine ⟨35568703141495271221594583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94849875043987389924252221 35568703141495271221594583)
  ·
    refine ⟨53353054712242906832391875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35568703141495271221594583 53353054712242906832391875)
    ·
      refine ⟨80029582068364360248587813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53353054712242906832391875 80029582068364360248587813)
      ·
        refine ⟨15005546637818317546610215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80029582068364360248587813 15005546637818317546610215)
        ·
          refine ⟨22508319956727476319915323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15005546637818317546610215 22508319956727476319915323)
          ·
            refine ⟨33762479935091214479872985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22508319956727476319915323 33762479935091214479872985)
            ·
              refine ⟨25321859951318410859904739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33762479935091214479872985 25321859951318410859904739)
              ·
                refine ⟨37982789926977616289857109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25321859951318410859904739 37982789926977616289857109)
                ·
                  refine ⟨445110819456768940896763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37982789926977616289857109 445110819456768940896763)
                  ·
                    rfl

theorem cell22_3900826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_3900826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900826 prefixEnd_3900826 := by exact prefixLift 3900826
  have htrace : WordTrace (prefixWord ++ tailWord_3900826) baseStart_3900826 baseEnd_3900826 := by
    simpa [prefixWord, tailWord_3900826, baseEnd_3900826] using wordTrace_append hprefix tailTrace_3900826
  have hstable : (prefixWord ++ tailWord_3900826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900826).length < 2 ^ (prefixWord ++ tailWord_3900826).sum := by decide
  have hdescent : baseEnd_3900826 < baseStart_3900826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900890 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 2, 4]
def baseStart_3900890 : Nat := 118140960795 + 3900890 * 2 ^ 59
def prefixEnd_3900890 : Nat := 4983230072969 + 3 ^ 40 * 3900890 * 2
def baseEnd_3900890 : Nat := 1335354366878231989090093

theorem tailTrace_3900890 : CollatzResearch.WordTrace tailWord_3900890 prefixEnd_3900890 1335354366878231989090093 := by
  unfold tailWord_3900890
  simp only [CollatzResearch.WordTrace]
  refine ⟨35569286709437305954177031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94851431225166149211138749 35569286709437305954177031)
  ·
    refine ⟨53353930064155958931265547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35569286709437305954177031 53353930064155958931265547)
    ·
      refine ⟨80030895096233938396898321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53353930064155958931265547 80030895096233938396898321)
      ·
        refine ⟨60023171322175453797673741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80030895096233938396898321 60023171322175453797673741)
        ·
          refine ⟨22508689245815795174127653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60023171322175453797673741 22508689245815795174127653)
          ·
            refine ⟨4220379233590461595148935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22508689245815795174127653 4220379233590461595148935)
            ·
              refine ⟨6330568850385692392723403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4220379233590461595148935 6330568850385692392723403)
              ·
                refine ⟨9495853275578538589085105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330568850385692392723403 9495853275578538589085105)
                ·
                  refine ⟨7121889956683903941813829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9495853275578538589085105 7121889956683903941813829)
                  ·
                    refine ⟨1335354366878231989090093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7121889956683903941813829 1335354366878231989090093)
                    ·
                      rfl

theorem cell22_3900890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_3900890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900890 prefixEnd_3900890 := by exact prefixLift 3900890
  have htrace : WordTrace (prefixWord ++ tailWord_3900890) baseStart_3900890 baseEnd_3900890 := by
    simpa [prefixWord, tailWord_3900890, baseEnd_3900890] using wordTrace_append hprefix tailTrace_3900890
  have hstable : (prefixWord ++ tailWord_3900890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900890).length < 2 ^ (prefixWord ++ tailWord_3900890).sum := by decide
  have hdescent : baseEnd_3900890 < baseStart_3900890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900909 : List Nat := [1, 5, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_3900909 : Nat := 118140960795 + 3900909 * 2 ^ 59
def prefixEnd_3900909 : Nat := 4983230072969 + 3 ^ 40 * 3900909 * 2
def baseEnd_3900909 : Nat := 1335360870966522272865035

theorem tailTrace_3900909 : CollatzResearch.WordTrace tailWord_3900909 prefixEnd_3900909 1335360870966522272865035 := by
  unfold tailWord_3900909
  simp only [CollatzResearch.WordTrace]
  refine ⟨142277839824680390061649781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94851893216453593374433187 142277839824680390061649781)
  ·
    refine ⟨13338547483563786568279667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142277839824680390061649781 13338547483563786568279667)
    ·
      refine ⟨20007821225345679852419501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13338547483563786568279667 20007821225345679852419501)
      ·
        refine ⟨7502932959504629944657313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20007821225345679852419501 7502932959504629944657313)
        ·
          refine ⟨5627199719628472458492985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7502932959504629944657313 5627199719628472458492985)
          ·
            refine ⟨4220399789721354343869739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5627199719628472458492985 4220399789721354343869739)
            ·
              refine ⟨6330599684582031515804609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4220399789721354343869739 6330599684582031515804609)
              ·
                refine ⟨4747949763436523636853457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6330599684582031515804609 4747949763436523636853457)
                ·
                  refine ⟨3560962322577392727640093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4747949763436523636853457 3560962322577392727640093)
                  ·
                    refine ⟨1335360870966522272865035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3560962322577392727640093 1335360870966522272865035)
                    ·
                      rfl

theorem cell22_3900909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_3900909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900909 prefixEnd_3900909 := by exact prefixLift 3900909
  have htrace : WordTrace (prefixWord ++ tailWord_3900909) baseStart_3900909 baseEnd_3900909 := by
    simpa [prefixWord, tailWord_3900909, baseEnd_3900909] using wordTrace_append hprefix tailTrace_3900909
  have hstable : (prefixWord ++ tailWord_3900909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900909).length < 2 ^ (prefixWord ++ tailWord_3900909).sum := by decide
  have hdescent : baseEnd_3900909 < baseStart_3900909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900920 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 3, 3]
def baseStart_3900920 : Nat := 118140960795 + 3900920 * 2 ^ 59
def prefixEnd_3900920 : Nat := 4983230072969 + 3 ^ 40 * 3900920 * 2
def baseEnd_3900920 : Nat := 1335364636491321910840001

theorem tailTrace_3900920 : CollatzResearch.WordTrace tailWord_3900920 prefixEnd_3900920 1335364636491321910840001 := by
  unfold tailWord_3900920
  simp only [CollatzResearch.WordTrace]
  refine ⟨71139120513820269470150107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94852160685093692626866809 71139120513820269470150107)
  ·
    refine ⟨106708680770730404205225161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71139120513820269470150107 106708680770730404205225161)
    ·
      refine ⟨80031510578047803153918871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106708680770730404205225161 80031510578047803153918871)
      ·
        refine ⟨120047265867071704730878307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80031510578047803153918871 120047265867071704730878307)
        ·
          refine ⟨180070898800607557096317461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120047265867071704730878307 180070898800607557096317461)
          ·
            refine ⟨8440823381278479238889881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180070898800607557096317461 8440823381278479238889881)
            ·
              refine ⟨6330617535958859429167411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8440823381278479238889881 6330617535958859429167411)
              ·
                refine ⟨9495926303938289143751117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330617535958859429167411 9495926303938289143751117)
                ·
                  refine ⟨3560972363976858428906669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9495926303938289143751117 3560972363976858428906669)
                  ·
                    refine ⟨1335364636491321910840001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3560972363976858428906669 1335364636491321910840001)
                    ·
                      rfl

theorem cell22_3900920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_3900920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900920 prefixEnd_3900920 := by exact prefixLift 3900920
  have htrace : WordTrace (prefixWord ++ tailWord_3900920) baseStart_3900920 baseEnd_3900920 := by
    simpa [prefixWord, tailWord_3900920, baseEnd_3900920] using wordTrace_append hprefix tailTrace_3900920
  have hstable : (prefixWord ++ tailWord_3900920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900920).length < 2 ^ (prefixWord ++ tailWord_3900920).sum := by decide
  have hdescent : baseEnd_3900920 < baseStart_3900920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900926 : List Nat := [4, 2, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3900926 : Nat := 118140960795 + 3900926 * 2 ^ 59
def prefixEnd_3900926 : Nat := 4983230072969 + 3 ^ 40 * 3900926 * 2
def baseEnd_3900926 : Nat := 1335366690413939895189983

theorem tailTrace_3900926 : CollatzResearch.WordTrace tailWord_3900926 prefixEnd_3900926 1335366690413939895189983 := by
  unfold tailWord_3900926
  simp only [CollatzResearch.WordTrace]
  refine ⟨17784807483202350245627329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94852306577079201310012421 17784807483202350245627329)
  ·
    refine ⟨13338605612401762684220497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17784807483202350245627329 13338605612401762684220497)
    ·
      refine ⟨10003954209301322013165373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13338605612401762684220497 10003954209301322013165373)
      ·
        refine ⟨3751482828487995754937015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10003954209301322013165373 3751482828487995754937015)
        ·
          refine ⟨5627224242731993632405523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751482828487995754937015 5627224242731993632405523)
          ·
            refine ⟨8440836364097990448608285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627224242731993632405523 8440836364097990448608285)
            ·
              refine ⟨3165313636536746418228107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8440836364097990448608285 3165313636536746418228107)
              ·
                refine ⟨4747970454805119627342161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165313636536746418228107 4747970454805119627342161)
                ·
                  refine ⟨3560977841103839720506621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4747970454805119627342161 3560977841103839720506621)
                  ·
                    refine ⟨1335366690413939895189983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3560977841103839720506621 1335366690413939895189983)
                    ·
                      rfl

theorem cell22_3900926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3900926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900926 prefixEnd_3900926 := by exact prefixLift 3900926
  have htrace : WordTrace (prefixWord ++ tailWord_3900926) baseStart_3900926 baseEnd_3900926 := by
    simpa [prefixWord, tailWord_3900926, baseEnd_3900926] using wordTrace_append hprefix tailTrace_3900926
  have hstable : (prefixWord ++ tailWord_3900926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900926).length < 2 ^ (prefixWord ++ tailWord_3900926).sum := by decide
  have hdescent : baseEnd_3900926 < baseStart_3900926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900931 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 1, 7]
def baseStart_3900931 : Nat := 118140960795 + 3900931 * 2 ^ 59
def prefixEnd_3900931 : Nat := 4983230072969 + 3 ^ 40 * 3900931 * 2
def baseEnd_3900931 : Nat := 1335368402016121548814967

theorem tailTrace_3900931 : CollatzResearch.WordTrace tailWord_3900931 prefixEnd_3900931 1335368402016121548814967 := by
  unfold tailWord_3900931
  simp only [CollatzResearch.WordTrace]
  refine ⟨142278642230600687818950647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94852428153733791879300431 142278642230600687818950647)
  ·
    refine ⟨213417963345901031728425971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142278642230600687818950647 213417963345901031728425971)
    ·
      refine ⟨320126945018851547592638957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213417963345901031728425971 320126945018851547592638957)
      ·
        refine ⟨120047604382069330347239609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320126945018851547592638957 120047604382069330347239609)
        ·
          refine ⟨90035703286551997760429707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120047604382069330347239609 90035703286551997760429707)
          ·
            refine ⟨135053554929827996640644561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90035703286551997760429707 135053554929827996640644561)
            ·
              refine ⟨101290166197370997480483421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135053554929827996640644561 101290166197370997480483421)
              ·
                refine ⟨37983812324014124055181283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101290166197370997480483421 37983812324014124055181283)
                ·
                  refine ⟨56975718486021186082771925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37983812324014124055181283 56975718486021186082771925)
                  ·
                    refine ⟨1335368402016121548814967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56975718486021186082771925 1335368402016121548814967)
                    ·
                      rfl

theorem cell22_3900931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_3900931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3900931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3900931 prefixEnd_3900931 := by exact prefixLift 3900931
  have htrace : WordTrace (prefixWord ++ tailWord_3900931) baseStart_3900931 baseEnd_3900931 := by
    simpa [prefixWord, tailWord_3900931, baseEnd_3900931] using wordTrace_append hprefix tailTrace_3900931
  have hstable : (prefixWord ++ tailWord_3900931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900931).length < 2 ^ (prefixWord ++ tailWord_3900931).sum := by decide
  have hdescent : baseEnd_3900931 < baseStart_3900931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901010 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_3901010 : Nat := 118140960795 + 3901010 * 2 ^ 59
def prefixEnd_3901010 : Nat := 4983230072969 + 3 ^ 40 * 3901010 * 2
def baseEnd_3901010 : Nat := 1335395445330591676089725

theorem tailTrace_3901010 : CollatzResearch.WordTrace tailWord_3901010 prefixEnd_3901010 1335395445330591676089725 := by
  unfold tailWord_3901010
  simp only [CollatzResearch.WordTrace]
  refine ⟨35570380899328621077769121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94854349064876322874050989 35570380899328621077769121)
  ·
    refine ⟨26677785674496465808326841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35570380899328621077769121 26677785674496465808326841)
    ·
      refine ⟨20008339255872349356245131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26677785674496465808326841 20008339255872349356245131)
      ·
        refine ⟨30012508883808524034367697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20008339255872349356245131 30012508883808524034367697)
        ·
          refine ⟨22509381662856393025775773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30012508883808524034367697 22509381662856393025775773)
          ·
            refine ⟨8441018123571147384665915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22509381662856393025775773 8441018123571147384665915)
            ·
              refine ⟨12661527185356721076998873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8441018123571147384665915 12661527185356721076998873)
              ·
                refine ⟨9496145389017540807749155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12661527185356721076998873 9496145389017540807749155)
                ·
                  refine ⟨14244218083526311211623733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9496145389017540807749155 14244218083526311211623733)
                  ·
                    refine ⟨1335395445330591676089725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14244218083526311211623733 1335395445330591676089725)
                    ·
                      rfl

theorem cell22_3901010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_3901010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901010 prefixEnd_3901010 := by exact prefixLift 3901010
  have htrace : WordTrace (prefixWord ++ tailWord_3901010) baseStart_3901010 baseEnd_3901010 := by
    simpa [prefixWord, tailWord_3901010, baseEnd_3901010] using wordTrace_append hprefix tailTrace_3901010
  have hstable : (prefixWord ++ tailWord_3901010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901010).length < 2 ^ (prefixWord ++ tailWord_3901010).sum := by decide
  have hdescent : baseEnd_3901010 < baseStart_3901010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901027 : List Nat := [1, 1, 1, 5, 1, 4, 2, 2, 2, 3]
def baseStart_3901027 : Nat := 118140960795 + 3901027 * 2 ^ 59
def prefixEnd_3901027 : Nat := 4983230072969 + 3 ^ 40 * 3901027 * 2
def baseEnd_3901027 : Nat := 1335401264778009298414673

theorem tailTrace_3901027 : CollatzResearch.WordTrace tailWord_3901027 prefixEnd_3901027 1335401264778009298414673 := by
  unfold tailWord_3901027
  simp only [CollatzResearch.WordTrace]
  refine ⟨142282143638252896214445335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94854762425501930809630223 142282143638252896214445335)
  ·
    refine ⟨213423215457379344321668003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142282143638252896214445335 213423215457379344321668003)
    ·
      refine ⟨320134823186069016482502005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213423215457379344321668003 320134823186069016482502005)
      ·
        refine ⟨30012639673693970295234563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320134823186069016482502005 30012639673693970295234563)
        ·
          refine ⟨45018959510540955442851845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30012639673693970295234563 45018959510540955442851845)
          ·
            refine ⟨8441054908226429145534721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45018959510540955442851845 8441054908226429145534721)
            ·
              refine ⟨6330791181169821859151041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8441054908226429145534721 6330791181169821859151041)
              ·
                refine ⟨4748093385877366394363281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6330791181169821859151041 4748093385877366394363281)
                ·
                  refine ⟨3561070039408024795772461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4748093385877366394363281 3561070039408024795772461)
                  ·
                    refine ⟨1335401264778009298414673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3561070039408024795772461 1335401264778009298414673)
                    ·
                      rfl

theorem cell22_3901027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 3].length) (baseStart_3901027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901027 prefixEnd_3901027 := by exact prefixLift 3901027
  have htrace : WordTrace (prefixWord ++ tailWord_3901027) baseStart_3901027 baseEnd_3901027 := by
    simpa [prefixWord, tailWord_3901027, baseEnd_3901027] using wordTrace_append hprefix tailTrace_3901027
  have hstable : (prefixWord ++ tailWord_3901027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901027).length < 2 ^ (prefixWord ++ tailWord_3901027).sum := by decide
  have hdescent : baseEnd_3901027 < baseStart_3901027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901029 : List Nat := [1, 3, 1, 3, 3, 3, 2, 2, 4]
def baseStart_3901029 : Nat := 118140960795 + 3901029 * 2 ^ 59
def prefixEnd_3901029 : Nat := 4983230072969 + 3 ^ 40 * 3901029 * 2
def baseEnd_3901029 : Nat := 445133983139627319954889

theorem tailTrace_3901029 : CollatzResearch.WordTrace tailWord_3901029 prefixEnd_3901029 445133983139627319954889 := by
  unfold tailWord_3901029
  simp only [CollatzResearch.WordTrace]
  refine ⟨142282216584245650556018141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94854811056163767037345427 142282216584245650556018141)
  ·
    refine ⟨53355831219092118958506803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142282216584245650556018141 53355831219092118958506803)
    ·
      refine ⟨80033746828638178437760205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53355831219092118958506803 80033746828638178437760205)
      ·
        refine ⟨30012655060739316914160077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80033746828638178437760205 30012655060739316914160077)
        ·
          refine ⟨11254745647777243842810029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30012655060739316914160077 11254745647777243842810029)
          ·
            refine ⟨4220529617916466441053761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11254745647777243842810029 4220529617916466441053761)
            ·
              refine ⟨3165397213437349830790321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4220529617916466441053761 3165397213437349830790321)
              ·
                refine ⟨2374047910078012373092741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3165397213437349830790321 2374047910078012373092741)
                ·
                  refine ⟨445133983139627319954889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374047910078012373092741 445133983139627319954889)
                  ·
                    rfl

theorem cell22_3901029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_3901029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901029 prefixEnd_3901029 := by exact prefixLift 3901029
  have htrace : WordTrace (prefixWord ++ tailWord_3901029) baseStart_3901029 baseEnd_3901029 := by
    simpa [prefixWord, tailWord_3901029, baseEnd_3901029] using wordTrace_append hprefix tailTrace_3901029
  have hstable : (prefixWord ++ tailWord_3901029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901029).length < 2 ^ (prefixWord ++ tailWord_3901029).sum := by decide
  have hdescent : baseEnd_3901029 < baseStart_3901029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901040 : List Nat := [2, 1, 1, 1, 6, 3, 1, 7]
def baseStart_3901040 : Nat := 118140960795 + 3901040 * 2 ^ 59
def prefixEnd_3901040 : Nat := 4983230072969 + 3 ^ 40 * 3901040 * 2
def baseEnd_3901040 : Nat := 148378412771520177537737

theorem tailTrace_3901040 : CollatzResearch.WordTrace tailWord_3901040 prefixEnd_3901040 148378412771520177537737 := by
  unfold tailWord_3901040
  simp only [CollatzResearch.WordTrace]
  refine ⟨71141308893602899717334287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94855078524803866289779049 71141308893602899717334287)
  ·
    refine ⟨106711963340404349576001431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71141308893602899717334287 106711963340404349576001431)
    ·
      refine ⟨160067945010606524364002147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106711963340404349576001431 160067945010606524364002147)
      ·
        refine ⟨240101917515909786546003221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160067945010606524364002147 240101917515909786546003221)
        ·
          refine ⟨11254777383558271244343901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 240101917515909786546003221 11254777383558271244343901)
          ·
            refine ⟨4220541518834351716628963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11254777383558271244343901 4220541518834351716628963)
            ·
              refine ⟨6330812278251527574943445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4220541518834351716628963 6330812278251527574943445)
              ·
                refine ⟨148378412771520177537737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6330812278251527574943445 148378412771520177537737)
                ·
                  rfl

theorem cell22_3901040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 7].length) (baseStart_3901040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901040 prefixEnd_3901040 := by exact prefixLift 3901040
  have htrace : WordTrace (prefixWord ++ tailWord_3901040) baseStart_3901040 baseEnd_3901040 := by
    simpa [prefixWord, tailWord_3901040, baseEnd_3901040] using wordTrace_append hprefix tailTrace_3901040
  have hstable : (prefixWord ++ tailWord_3901040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901040).length < 2 ^ (prefixWord ++ tailWord_3901040).sum := by decide
  have hdescent : baseEnd_3901040 < baseStart_3901040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901068 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 7]
def baseStart_3901068 : Nat := 118140960795 + 3901068 * 2 ^ 59
def prefixEnd_3901068 : Nat := 4983230072969 + 3 ^ 40 * 3901068 * 2
def baseEnd_3901068 : Nat := 445138433305299619379849

theorem tailTrace_3901068 : CollatzResearch.WordTrace tailWord_3901068 prefixEnd_3901068 445138433305299619379849 := by
  unfold tailWord_3901068
  simp only [CollatzResearch.WordTrace]
  refine ⟨71141819515552180108343929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94855759354069573477791905 71141819515552180108343929)
  ·
    refine ⟨53356364636664135081257947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71141819515552180108343929 53356364636664135081257947)
    ·
      refine ⟨80034546954996202621886921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53356364636664135081257947 80034546954996202621886921)
      ·
        refine ⟨60025910216247151966415191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80034546954996202621886921 60025910216247151966415191)
        ·
          refine ⟨90038865324370727949622787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60025910216247151966415191 90038865324370727949622787)
          ·
            refine ⟨135058297986556091924434181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90038865324370727949622787 135058297986556091924434181)
            ·
              refine ⟨25323430872479267235831409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135058297986556091924434181 25323430872479267235831409)
              ·
                refine ⟨18992573154359450426873557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25323430872479267235831409 18992573154359450426873557)
                ·
                  refine ⟨445138433305299619379849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18992573154359450426873557 445138433305299619379849)
                  ·
                    rfl

theorem cell22_3901068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_3901068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901068 prefixEnd_3901068 := by exact prefixLift 3901068
  have htrace : WordTrace (prefixWord ++ tailWord_3901068) baseStart_3901068 baseEnd_3901068 := by
    simpa [prefixWord, tailWord_3901068, baseEnd_3901068] using wordTrace_append hprefix tailTrace_3901068
  have hstable : (prefixWord ++ tailWord_3901068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901068).length < 2 ^ (prefixWord ++ tailWord_3901068).sum := by decide
  have hdescent : baseEnd_3901068 < baseStart_3901068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901089 : List Nat := [1, 2, 3, 3, 2, 1, 2, 4, 1, 3]
def baseStart_3901089 : Nat := 118140960795 + 3901089 * 2 ^ 59
def prefixEnd_3901089 : Nat := 4983230072969 + 3 ^ 40 * 3901089 * 2
def baseEnd_3901089 : Nat := 1335422488645061803364483

theorem tailTrace_3901089 : CollatzResearch.WordTrace tailWord_3901089 prefixEnd_3901089 1335422488645061803364483 := by
  unfold tailWord_3901089
  simp only [CollatzResearch.WordTrace]
  refine ⟨142284404964028280803202321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94856269976018853868801547 142284404964028280803202321)
  ·
    refine ⟨106713303723021210602401741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142284404964028280803202321 106713303723021210602401741)
    ·
      refine ⟨40017488896132953975900653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106713303723021210602401741 40017488896132953975900653)
      ·
        refine ⟨15006558336049857740962745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40017488896132953975900653 15006558336049857740962745)
        ·
          refine ⟨11254918752037393305722059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15006558336049857740962745 11254918752037393305722059)
          ·
            refine ⟨16882378128056089958583089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11254918752037393305722059 16882378128056089958583089)
            ·
              refine ⟨12661783596042067468937317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16882378128056089958583089 12661783596042067468937317)
              ·
                refine ⟨2374084424257887650425747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12661783596042067468937317 2374084424257887650425747)
                ·
                  refine ⟨3561126636386831475638621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374084424257887650425747 3561126636386831475638621)
                  ·
                    refine ⟨1335422488645061803364483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3561126636386831475638621 1335422488645061803364483)
                    ·
                      rfl

theorem cell22_3901089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_3901089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901089 prefixEnd_3901089 := by exact prefixLift 3901089
  have htrace : WordTrace (prefixWord ++ tailWord_3901089) baseStart_3901089 baseEnd_3901089 := by
    simpa [prefixWord, tailWord_3901089, baseEnd_3901089] using wordTrace_append hprefix tailTrace_3901089
  have hstable : (prefixWord ++ tailWord_3901089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901089).length < 2 ^ (prefixWord ++ tailWord_3901089).sum := by decide
  have hdescent : baseEnd_3901089 < baseStart_3901089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901205 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_3901205 : Nat := 118140960795 + 3901205 * 2 ^ 59
def prefixEnd_3901205 : Nat := 4983230072969 + 3 ^ 40 * 3901205 * 2
def baseEnd_3901205 : Nat := 1335462197815676167464127

theorem tailTrace_3901205 : CollatzResearch.WordTrace tailWord_3901205 prefixEnd_3901205 1335462197815676167464127 := by
  unfold tailWord_3901205
  simp only [CollatzResearch.WordTrace]
  refine ⟨142288635831608032614425069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94859090554405355076283379 142288635831608032614425069)
  ·
    refine ⟨53358238436853012230409401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142288635831608032614425069 53358238436853012230409401)
    ·
      refine ⟨40018678827639759172807051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53358238436853012230409401 40018678827639759172807051)
      ·
        refine ⟨60028018241459638759210577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40018678827639759172807051 60028018241459638759210577)
        ·
          refine ⟨45021013681094729069407933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60028018241459638759210577 45021013681094729069407933)
          ·
            refine ⟨16882880130410523401027975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45021013681094729069407933 16882880130410523401027975)
            ·
              refine ⟨25324320195615785101541963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16882880130410523401027975 25324320195615785101541963)
              ·
                refine ⟨37986480293423677652312945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25324320195615785101541963 37986480293423677652312945)
                ·
                  refine ⟨28489860220067758239234709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37986480293423677652312945 28489860220067758239234709)
                  ·
                    refine ⟨1335462197815676167464127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28489860220067758239234709 1335462197815676167464127)
                    ·
                      rfl

theorem cell22_3901205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_3901205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901205 prefixEnd_3901205 := by exact prefixLift 3901205
  have htrace : WordTrace (prefixWord ++ tailWord_3901205) baseStart_3901205 baseEnd_3901205 := by
    simpa [prefixWord, tailWord_3901205, baseEnd_3901205] using wordTrace_append hprefix tailTrace_3901205
  have hstable : (prefixWord ++ tailWord_3901205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901205).length < 2 ^ (prefixWord ++ tailWord_3901205).sum := by decide
  have hdescent : baseEnd_3901205 < baseStart_3901205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901224 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3901224 : Nat := 118140960795 + 3901224 * 2 ^ 59
def prefixEnd_3901224 : Nat := 4983230072969 + 3 ^ 40 * 3901224 * 2
def baseEnd_3901224 : Nat := 1335468701903966451239069

theorem tailTrace_3901224 : CollatzResearch.WordTrace tailWord_3901224 prefixEnd_3901224 1335468701903966451239069 := by
  unfold tailWord_3901224
  simp only [CollatzResearch.WordTrace]
  refine ⟨71144664409269599429683363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94859552545692799239577817 71144664409269599429683363)
  ·
    refine ⟨106716996613904399144525045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71144664409269599429683363 106716996613904399144525045)
    ·
      refine ⟨10004718432553537419799223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106716996613904399144525045 10004718432553537419799223)
      ·
        refine ⟨15007077648830306129698835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10004718432553537419799223 15007077648830306129698835)
        ·
          refine ⟨22510616473245459194548253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15007077648830306129698835 22510616473245459194548253)
          ·
            refine ⟨8441481177467047197955595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22510616473245459194548253 8441481177467047197955595)
            ·
              refine ⟨12662221766200570796933393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8441481177467047197955595 12662221766200570796933393)
              ·
                refine ⟨9496666324650428097700045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12662221766200570796933393 9496666324650428097700045)
                ·
                  refine ⟨3561249871743910536637517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9496666324650428097700045 3561249871743910536637517)
                  ·
                    refine ⟨1335468701903966451239069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3561249871743910536637517 1335468701903966451239069)
                    ·
                      rfl

theorem cell22_3901224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3901224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901224 prefixEnd_3901224 := by exact prefixLift 3901224
  have htrace : WordTrace (prefixWord ++ tailWord_3901224) baseStart_3901224 baseEnd_3901224 := by
    simpa [prefixWord, tailWord_3901224, baseEnd_3901224] using wordTrace_append hprefix tailTrace_3901224
  have hstable : (prefixWord ++ tailWord_3901224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901224).length < 2 ^ (prefixWord ++ tailWord_3901224).sum := by decide
  have hdescent : baseEnd_3901224 < baseStart_3901224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901297 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 6, 3]
def baseStart_3901297 : Nat := 118140960795 + 3901297 * 2 ^ 59
def prefixEnd_3901297 : Nat := 4983230072969 + 3 ^ 40 * 3901297 * 2
def baseEnd_3901297 : Nat := 1335493691295818594163845

theorem tailTrace_3901297 : CollatzResearch.WordTrace tailWord_3901297 prefixEnd_3901297 1335493691295818594163845 := by
  unfold tailWord_3901297
  simp only [CollatzResearch.WordTrace]
  refine ⟨142291991347274732326774145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94861327564849821551182763 142291991347274732326774145)
  ·
    refine ⟨106718993510456049245080609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142291991347274732326774145 106718993510456049245080609)
    ·
      refine ⟨80039245132842036933810457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106718993510456049245080609 80039245132842036933810457)
      ·
        refine ⟨60029433849631527700357843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80039245132842036933810457 60029433849631527700357843)
        ·
          refine ⟨90044150774447291550536765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60029433849631527700357843 90044150774447291550536765)
          ·
            refine ⟨33766556540417734331451287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90044150774447291550536765 33766556540417734331451287)
            ·
              refine ⟨50649834810626601497176931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33766556540417734331451287 50649834810626601497176931)
              ·
                refine ⟨75974752215939902245765397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50649834810626601497176931 75974752215939902245765397)
                ·
                  refine ⟨3561316510122182917770253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75974752215939902245765397 3561316510122182917770253)
                  ·
                    refine ⟨1335493691295818594163845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3561316510122182917770253 1335493691295818594163845)
                    ·
                      rfl

theorem cell22_3901297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_3901297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901297 prefixEnd_3901297 := by exact prefixLift 3901297
  have htrace : WordTrace (prefixWord ++ tailWord_3901297) baseStart_3901297 baseEnd_3901297 := by
    simpa [prefixWord, tailWord_3901297, baseEnd_3901297] using wordTrace_append hprefix tailTrace_3901297
  have hstable : (prefixWord ++ tailWord_3901297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901297).length < 2 ^ (prefixWord ++ tailWord_3901297).sum := by decide
  have hdescent : baseEnd_3901297 < baseStart_3901297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901312 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 2, 4]
def baseStart_3901312 : Nat := 118140960795 + 3901312 * 2 ^ 59
def prefixEnd_3901312 : Nat := 4983230072969 + 3 ^ 40 * 3901312 * 2
def baseEnd_3901312 : Nat := 1335498826102363555038799

theorem tailTrace_3901312 : CollatzResearch.WordTrace tailWord_3901312 prefixEnd_3901312 1335498826102363555038799 := by
  unfold tailWord_3901312
  simp only [CollatzResearch.WordTrace]
  refine ⟨71146269221110194944285095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94861692294813593259046793 71146269221110194944285095)
  ·
    refine ⟨106719403831665292416427643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71146269221110194944285095 106719403831665292416427643)
    ·
      refine ⟨160079105747497938624641465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106719403831665292416427643 160079105747497938624641465)
      ·
        refine ⟨120059329310623453968481099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160079105747497938624641465 120059329310623453968481099)
        ·
          refine ⟨180088993965935180952721649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120059329310623453968481099 180088993965935180952721649)
          ·
            refine ⟨135066745474451385714541237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180088993965935180952721649 135066745474451385714541237)
            ·
              refine ⟨12662507388229817410738241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135066745474451385714541237 12662507388229817410738241)
              ·
                refine ⟨9496880541172363058053681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12662507388229817410738241 9496880541172363058053681)
                ·
                  refine ⟨7122660405879272293540261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9496880541172363058053681 7122660405879272293540261)
                  ·
                    refine ⟨1335498826102363555038799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7122660405879272293540261 1335498826102363555038799)
                    ·
                      rfl

theorem cell22_3901312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_3901312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901312 prefixEnd_3901312 := by exact prefixLift 3901312
  have htrace : WordTrace (prefixWord ++ tailWord_3901312) baseStart_3901312 baseEnd_3901312 := by
    simpa [prefixWord, tailWord_3901312, baseEnd_3901312] using wordTrace_append hprefix tailTrace_3901312
  have hstable : (prefixWord ++ tailWord_3901312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901312).length < 2 ^ (prefixWord ++ tailWord_3901312).sum := by decide
  have hdescent : baseEnd_3901312 < baseStart_3901312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901346 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3901346 : Nat := 118140960795 + 3901346 * 2 ^ 59
def prefixEnd_3901346 : Nat := 4983230072969 + 3 ^ 40 * 3901346 * 2
def baseEnd_3901346 : Nat := 1335510464997198799688695

theorem tailTrace_3901346 : CollatzResearch.WordTrace tailWord_3901346 prefixEnd_3901346 1335510464997198799688695 := by
  unfold tailWord_3901346
  simp only [CollatzResearch.WordTrace]
  refine ⟨35573444631024303423826973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94862519016064809130205261 35573444631024303423826973)
  ·
    refine ⟨13340041736634113783935115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35573444631024303423826973 13340041736634113783935115)
    ·
      refine ⟨20010062604951170675902673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13340041736634113783935115 20010062604951170675902673)
      ·
        refine ⟨15007546953713378006927005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20010062604951170675902673 15007546953713378006927005)
        ·
          refine ⟨5627830107642516752597627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15007546953713378006927005 5627830107642516752597627)
          ·
            refine ⟨8441745161463775128896441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627830107642516752597627 8441745161463775128896441)
            ·
              refine ⟨6331308871097831346672331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8441745161463775128896441 6331308871097831346672331)
              ·
                refine ⟨9496963306646747020008497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6331308871097831346672331 9496963306646747020008497)
                ·
                  refine ⟨7122722479985060265006373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9496963306646747020008497 7122722479985060265006373)
                  ·
                    refine ⟨1335510464997198799688695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7122722479985060265006373 1335510464997198799688695)
                    ·
                      rfl

theorem cell22_3901346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3901346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901346 prefixEnd_3901346 := by exact prefixLift 3901346
  have htrace : WordTrace (prefixWord ++ tailWord_3901346) baseStart_3901346 baseEnd_3901346 := by
    simpa [prefixWord, tailWord_3901346, baseEnd_3901346] using wordTrace_append hprefix tailTrace_3901346
  have hstable : (prefixWord ++ tailWord_3901346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901346).length < 2 ^ (prefixWord ++ tailWord_3901346).sum := by decide
  have hdescent : baseEnd_3901346 < baseStart_3901346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901376 : List Nat := [2, 1, 1, 2, 3, 2, 3, 4, 1, 3]
def baseStart_3901376 : Nat := 118140960795 + 3901376 * 2 ^ 59
def prefixEnd_3901376 : Nat := 4983230072969 + 3 ^ 40 * 3901376 * 2
def baseEnd_3901376 : Nat := 1335520734610288721438603

theorem tailTrace_3901376 : CollatzResearch.WordTrace tailWord_3901376 prefixEnd_3901376 1335520734610288721438603 := by
  unfold tailWord_3901376
  simp only [CollatzResearch.WordTrace]
  refine ⟨71147436356994264409449991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94863248475992352545933321 71147436356994264409449991)
  ·
    refine ⟨106721154535491396614174987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71147436356994264409449991 106721154535491396614174987)
    ·
      refine ⟨160081731803237094921262481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106721154535491396614174987 160081731803237094921262481)
      ·
        refine ⟨120061298852427821190946861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160081731803237094921262481 120061298852427821190946861)
        ·
          refine ⟨45022987069660432946605073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120061298852427821190946861 45022987069660432946605073)
          ·
            refine ⟨33767240302245324709953805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45022987069660432946605073 33767240302245324709953805)
            ·
              refine ⟨12662715113341996766232677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33767240302245324709953805 12662715113341996766232677)
              ·
                refine ⟨2374259083751624393668627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12662715113341996766232677 2374259083751624393668627)
                ·
                  refine ⟨3561388625627436590502941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374259083751624393668627 3561388625627436590502941)
                  ·
                    refine ⟨1335520734610288721438603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3561388625627436590502941 1335520734610288721438603)
                    ·
                      rfl

theorem cell22_3901376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 1, 3].length) (baseStart_3901376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901376 prefixEnd_3901376 := by exact prefixLift 3901376
  have htrace : WordTrace (prefixWord ++ tailWord_3901376) baseStart_3901376 baseEnd_3901376 := by
    simpa [prefixWord, tailWord_3901376, baseEnd_3901376] using wordTrace_append hprefix tailTrace_3901376
  have hstable : (prefixWord ++ tailWord_3901376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901376).length < 2 ^ (prefixWord ++ tailWord_3901376).sum := by decide
  have hdescent : baseEnd_3901376 < baseStart_3901376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901387 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 2, 5]
def baseStart_3901387 : Nat := 118140960795 + 3901387 * 2 ^ 59
def prefixEnd_3901387 : Nat := 4983230072969 + 3 ^ 40 * 3901387 * 2
def baseEnd_3901387 : Nat := 1335524500135088359413569

theorem tailTrace_3901387 : CollatzResearch.WordTrace tailWord_3901387 prefixEnd_3901387 1335524500135088359413569 := by
  unfold tailWord_3901387
  simp only [CollatzResearch.WordTrace]
  refine ⟨142295273916948677697550415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94863515944632451798366943 142295273916948677697550415)
  ·
    refine ⟨213442910875423016546325623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142295273916948677697550415 213442910875423016546325623)
    ·
      refine ⟨320164366313134524819488435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213442910875423016546325623 320164366313134524819488435)
      ·
        refine ⟨480246549469701787229232653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320164366313134524819488435 480246549469701787229232653)
        ·
          refine ⟨180092456051138170210962245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480246549469701787229232653 180092456051138170210962245)
          ·
            refine ⟨33767335509588406914555421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180092456051138170210962245 33767335509588406914555421)
            ·
              refine ⟨12662750816095652592958283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33767335509588406914555421 12662750816095652592958283)
              ·
                refine ⟨18994126224143478889437425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12662750816095652592958283 18994126224143478889437425)
                ·
                  refine ⟨14245594668107609167078069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18994126224143478889437425 14245594668107609167078069)
                  ·
                    refine ⟨1335524500135088359413569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14245594668107609167078069 1335524500135088359413569)
                    ·
                      rfl

theorem cell22_3901387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 5].length) (baseStart_3901387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901387 prefixEnd_3901387 := by exact prefixLift 3901387
  have htrace : WordTrace (prefixWord ++ tailWord_3901387) baseStart_3901387 baseEnd_3901387 := by
    simpa [prefixWord, tailWord_3901387, baseEnd_3901387] using wordTrace_append hprefix tailTrace_3901387
  have hstable : (prefixWord ++ tailWord_3901387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901387).length < 2 ^ (prefixWord ++ tailWord_3901387).sum := by decide
  have hdescent : baseEnd_3901387 < baseStart_3901387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901432 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 3, 5]
def baseStart_3901432 : Nat := 118140960795 + 3901432 * 2 ^ 59
def prefixEnd_3901432 : Nat := 4983230072969 + 3 ^ 40 * 3901432 * 2
def baseEnd_3901432 : Nat := 1335539904554723242038431

theorem tailTrace_3901432 : CollatzResearch.WordTrace tailWord_3901432 prefixEnd_3901432 1335539904554723242038431 := by
  unfold tailWord_3901432
  simp only [CollatzResearch.WordTrace]
  refine ⟨71148457600892825191469275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94864610134523766921959033 71148457600892825191469275)
  ·
    refine ⟨106722686401339237787203913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71148457600892825191469275 106722686401339237787203913)
    ·
      refine ⟨80042014801004428340402935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106722686401339237787203913 80042014801004428340402935)
      ·
        refine ⟨120063022201506642510604403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80042014801004428340402935 120063022201506642510604403)
        ·
          refine ⟨180094533302259963765906605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120063022201506642510604403 180094533302259963765906605)
          ·
            refine ⟨67535449988347486412214977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180094533302259963765906605 67535449988347486412214977)
            ·
              refine ⟨50651587491260614809161233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67535449988347486412214977 50651587491260614809161233)
              ·
                refine ⟨37988690618445461106870925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50651587491260614809161233 37988690618445461106870925)
                ·
                  refine ⟨14245758981917047915076597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37988690618445461106870925 14245758981917047915076597)
                  ·
                    refine ⟨1335539904554723242038431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14245758981917047915076597 1335539904554723242038431)
                    ·
                      rfl

theorem cell22_3901432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_3901432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901432 prefixEnd_3901432 := by exact prefixLift 3901432
  have htrace : WordTrace (prefixWord ++ tailWord_3901432) baseStart_3901432 baseEnd_3901432 := by
    simpa [prefixWord, tailWord_3901432, baseEnd_3901432] using wordTrace_append hprefix tailTrace_3901432
  have hstable : (prefixWord ++ tailWord_3901432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901432).length < 2 ^ (prefixWord ++ tailWord_3901432).sum := by decide
  have hdescent : baseEnd_3901432 < baseStart_3901432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901464 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 2, 4]
def baseStart_3901464 : Nat := 118140960795 + 3901464 * 2 ^ 59
def prefixEnd_3901464 : Nat := 4983230072969 + 3 ^ 40 * 3901464 * 2
def baseEnd_3901464 : Nat := 1335550858808685825238333

theorem tailTrace_3901464 : CollatzResearch.WordTrace tailWord_3901464 prefixEnd_3901464 1335550858808685825238333 := by
  unfold tailWord_3901464
  simp only [CollatzResearch.WordTrace]
  refine ⟨71149041168834859924051723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94865388225113146565402297 71149041168834859924051723)
  ·
    refine ⟨106723561753252289886077585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71149041168834859924051723 106723561753252289886077585)
    ·
      refine ⟨80042671314939217414558189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106723561753252289886077585 80042671314939217414558189)
      ·
        refine ⟨30016001743102206530459321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80042671314939217414558189 30016001743102206530459321)
        ·
          refine ⟨22512001307326654897844491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30016001743102206530459321 22512001307326654897844491)
          ·
            refine ⟨33768001960989982346766737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22512001307326654897844491 33768001960989982346766737)
            ·
              refine ⟨25326001470742486760075053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33768001960989982346766737 25326001470742486760075053)
              ·
                refine ⟨9497250551528432535028145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25326001470742486760075053 9497250551528432535028145)
                ·
                  refine ⟨7122937913646324401271109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9497250551528432535028145 7122937913646324401271109)
                  ·
                    refine ⟨1335550858808685825238333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7122937913646324401271109 1335550858808685825238333)
                    ·
                      rfl

theorem cell22_3901464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_3901464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901464 prefixEnd_3901464 := by exact prefixLift 3901464
  have htrace : WordTrace (prefixWord ++ tailWord_3901464) baseStart_3901464 baseEnd_3901464 := by
    simpa [prefixWord, tailWord_3901464, baseEnd_3901464] using wordTrace_append hprefix tailTrace_3901464
  have hstable : (prefixWord ++ tailWord_3901464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901464).length < 2 ^ (prefixWord ++ tailWord_3901464).sum := by decide
  have hdescent : baseEnd_3901464 < baseStart_3901464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901468 : List Nat := [2, 2, 3, 1, 3, 3, 1, 3, 4]
def baseStart_3901468 : Nat := 118140960795 + 3901468 * 2 ^ 59
def prefixEnd_3901468 : Nat := 4983230072969 + 3 ^ 40 * 3901468 * 2
def baseEnd_3901468 : Nat := 445184076030143716046107

theorem tailTrace_3901468 : CollatzResearch.WordTrace tailWord_3901468 prefixEnd_3901468 445184076030143716046107 := by
  unfold tailWord_3901468
  simp only [CollatzResearch.WordTrace]
  refine ⟨71149114114827614265624529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94865485486436819020832705 71149114114827614265624529)
  ·
    refine ⟨53361835586120710699218397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71149114114827614265624529 53361835586120710699218397)
    ·
      refine ⟨20010688344795266512206899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53361835586120710699218397 20010688344795266512206899)
      ·
        refine ⟨30016032517192899768310349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20010688344795266512206899 30016032517192899768310349)
        ·
          refine ⟨11256012193947337413116381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30016032517192899768310349 11256012193947337413116381)
          ·
            refine ⟨4221004572730251529918643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11256012193947337413116381 4221004572730251529918643)
            ·
              refine ⟨6331506859095377294877965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4221004572730251529918643 6331506859095377294877965)
              ·
                refine ⟨2374315072160766485579237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6331506859095377294877965 2374315072160766485579237)
                ·
                  refine ⟨445184076030143716046107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374315072160766485579237 445184076030143716046107)
                  ·
                    rfl

theorem cell22_3901468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_3901468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901468 prefixEnd_3901468 := by exact prefixLift 3901468
  have htrace : WordTrace (prefixWord ++ tailWord_3901468) baseStart_3901468 baseEnd_3901468 := by
    simpa [prefixWord, tailWord_3901468, baseEnd_3901468] using wordTrace_append hprefix tailTrace_3901468
  have hstable : (prefixWord ++ tailWord_3901468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901468).length < 2 ^ (prefixWord ++ tailWord_3901468).sum := by decide
  have hdescent : baseEnd_3901468 < baseStart_3901468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901507 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 9]
def baseStart_3901507 : Nat := 118140960795 + 3901507 * 2 ^ 59
def prefixEnd_3901507 : Nat := 4983230072969 + 3 ^ 40 * 3901507 * 2
def baseEnd_3901507 : Nat := 445188526195816015471067

theorem tailTrace_3901507 : CollatzResearch.WordTrace tailWord_3901507 prefixEnd_3901507 445188526195816015471067 := by
  unfold tailWord_3901507
  simp only [CollatzResearch.WordTrace]
  refine ⟨142299650676513938191918775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94866433784342625461279183 142299650676513938191918775)
  ·
    refine ⟨213449476014770907287878163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142299650676513938191918775 213449476014770907287878163)
    ·
      refine ⟨320174214022156360931817245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213449476014770907287878163 320174214022156360931817245)
      ·
        refine ⟨120065330258308635349431467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320174214022156360931817245 120065330258308635349431467)
        ·
          refine ⟨180097995387462953024147201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120065330258308635349431467 180097995387462953024147201)
          ·
            refine ⟨135073496540597214768110401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180097995387462953024147201 135073496540597214768110401)
            ·
              refine ⟨101305122405447911076082801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135073496540597214768110401 101305122405447911076082801)
              ·
                refine ⟨75978841804085933307062101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101305122405447911076082801 75978841804085933307062101)
                ·
                  refine ⟨445188526195816015471067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75978841804085933307062101 445188526195816015471067)
                  ·
                    rfl

theorem cell22_3901507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 9].length) (baseStart_3901507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901507 prefixEnd_3901507 := by exact prefixLift 3901507
  have htrace : WordTrace (prefixWord ++ tailWord_3901507) baseStart_3901507 baseEnd_3901507 := by
    simpa [prefixWord, tailWord_3901507, baseEnd_3901507] using wordTrace_append hprefix tailTrace_3901507
  have hstable : (prefixWord ++ tailWord_3901507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901507).length < 2 ^ (prefixWord ++ tailWord_3901507).sum := by decide
  have hdescent : baseEnd_3901507 < baseStart_3901507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901541 : List Nat := [1, 3, 1, 3, 2, 3, 2, 2, 5]
def baseStart_3901541 : Nat := 118140960795 + 3901541 * 2 ^ 59
def prefixEnd_3901541 : Nat := 4983230072969 + 3 ^ 40 * 3901541 * 2
def baseEnd_3901541 : Nat := 445192405827427763687699

theorem tailTrace_3901541 : CollatzResearch.WordTrace tailWord_3901541 prefixEnd_3901541 445192405827427763687699 := by
  unfold tailWord_3901541
  simp only [CollatzResearch.WordTrace]
  refine ⟨142300890758390761998656477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94867260505593841332437651 142300890758390761998656477)
  ·
    refine ⟨53362834034396535749496179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142300890758390761998656477 53362834034396535749496179)
    ·
      refine ⟨80044251051594803624244269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53362834034396535749496179 80044251051594803624244269)
      ·
        refine ⟨30016594144348051359091601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80044251051594803624244269 30016594144348051359091601)
        ·
          refine ⟨22512445608261038519318701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30016594144348051359091601 22512445608261038519318701)
          ·
            refine ⟨8442167103097889444744513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22512445608261038519318701 8442167103097889444744513)
            ·
              refine ⟨6331625327323417083558385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8442167103097889444744513 6331625327323417083558385)
              ·
                refine ⟨4748718995492562812668789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6331625327323417083558385 4748718995492562812668789)
                ·
                  refine ⟨445192405827427763687699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4748718995492562812668789 445192405827427763687699)
                  ·
                    rfl

theorem cell22_3901541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_3901541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901541 prefixEnd_3901541 := by exact prefixLift 3901541
  have htrace : WordTrace (prefixWord ++ tailWord_3901541) baseStart_3901541 baseEnd_3901541 := by
    simpa [prefixWord, tailWord_3901541, baseEnd_3901541] using wordTrace_append hprefix tailTrace_3901541
  have hstable : (prefixWord ++ tailWord_3901541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901541).length < 2 ^ (prefixWord ++ tailWord_3901541).sum := by decide
  have hdescent : baseEnd_3901541 < baseStart_3901541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901584 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 1, 5]
def baseStart_3901584 : Nat := 118140960795 + 3901584 * 2 ^ 59
def prefixEnd_3901584 : Nat := 4983230072969 + 3 ^ 40 * 3901584 * 2
def baseEnd_3901584 : Nat := 1335591937261045512237965

theorem tailTrace_3901584 : CollatzResearch.WordTrace tailWord_3901584 prefixEnd_3901584 1335591937261045512237965 := by
  unfold tailWord_3901584
  simp only [CollatzResearch.WordTrace]
  refine ⟨71151229548617490171235903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94868306064823320228314537 71151229548617490171235903)
  ·
    refine ⟨106726844322926235256853855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71151229548617490171235903 106726844322926235256853855)
    ·
      refine ⟨160090266484389352885280783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106726844322926235256853855 160090266484389352885280783)
      ·
        refine ⟨240135399726584029327921175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160090266484389352885280783 240135399726584029327921175)
        ·
          refine ⟨360203099589876043991881763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240135399726584029327921175 360203099589876043991881763)
          ·
            refine ⟨540304649384814065987822645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360203099589876043991881763 540304649384814065987822645)
            ·
              refine ⟨50653560879826318686358373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 540304649384814065987822645 50653560879826318686358373)
              ·
                refine ⟨9497542664967434753692195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50653560879826318686358373 9497542664967434753692195)
                ·
                  refine ⟨14246313997451152130538293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9497542664967434753692195 14246313997451152130538293)
                  ·
                    refine ⟨1335591937261045512237965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14246313997451152130538293 1335591937261045512237965)
                    ·
                      rfl

theorem cell22_3901584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_3901584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901584 prefixEnd_3901584 := by exact prefixLift 3901584
  have htrace : WordTrace (prefixWord ++ tailWord_3901584) baseStart_3901584 baseEnd_3901584 := by
    simpa [prefixWord, tailWord_3901584, baseEnd_3901584] using wordTrace_append hprefix tailTrace_3901584
  have hstable : (prefixWord ++ tailWord_3901584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901584).length < 2 ^ (prefixWord ++ tailWord_3901584).sum := by decide
  have hdescent : baseEnd_3901584 < baseStart_3901584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901629 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3901629 : Nat := 118140960795 + 3901629 * 2 ^ 59
def prefixEnd_3901629 : Nat := 4983230072969 + 3 ^ 40 * 3901629 * 2
def baseEnd_3901629 : Nat := 1335607341680680394862827

theorem tailTrace_3901629 : CollatzResearch.WordTrace tailWord_3901629 prefixEnd_3901629 1335607341680680394862827 := by
  unfold tailWord_3901629
  simp only [CollatzResearch.WordTrace]
  refine ⟨142304100382071953027859941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94869400254714635351906627 142304100382071953027859941)
  ·
    refine ⟨26682018821638491192723739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142304100382071953027859941 26682018821638491192723739)
    ·
      refine ⟨40023028232457736789085609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26682018821638491192723739 40023028232457736789085609)
      ·
        refine ⟨30017271174343302591814207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40023028232457736789085609 30017271174343302591814207)
        ·
          refine ⟨45025906761514953887721311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30017271174343302591814207 45025906761514953887721311)
          ·
            refine ⟨67538860142272430831581967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45025906761514953887721311 67538860142272430831581967)
            ·
              refine ⟨101308290213408646247372951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67538860142272430831581967 101308290213408646247372951)
              ·
                refine ⟨151962435320112969371059427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101308290213408646247372951 151962435320112969371059427)
                ·
                  refine ⟨227943652980169454056589141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151962435320112969371059427 227943652980169454056589141)
                  ·
                    refine ⟨1335607341680680394862827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 227943652980169454056589141 1335607341680680394862827)
                    ·
                      rfl

theorem cell22_3901629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3901629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901629 prefixEnd_3901629 := by exact prefixLift 3901629
  have htrace : WordTrace (prefixWord ++ tailWord_3901629) baseStart_3901629 baseEnd_3901629 := by
    simpa [prefixWord, tailWord_3901629, baseEnd_3901629] using wordTrace_append hprefix tailTrace_3901629
  have hstable : (prefixWord ++ tailWord_3901629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901629).length < 2 ^ (prefixWord ++ tailWord_3901629).sum := by decide
  have hdescent : baseEnd_3901629 < baseStart_3901629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901676 : List Nat := [2, 2, 1, 1, 2, 3, 3, 3, 5]
def baseStart_3901676 : Nat := 118140960795 + 3901676 * 2 ^ 59
def prefixEnd_3901676 : Nat := 4983230072969 + 3 ^ 40 * 3901676 * 2
def baseEnd_3901676 : Nat := 445207810247062646312561

theorem tailTrace_3901676 : CollatzResearch.WordTrace tailWord_3901676 prefixEnd_3901676 445207810247062646312561 := by
  unfold tailWord_3901676
  simp only [CollatzResearch.WordTrace]
  refine ⟨71152907306450840027410441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94870543075267786703213921 71152907306450840027410441)
  ·
    refine ⟨53364680479838130020557831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71152907306450840027410441 53364680479838130020557831)
    ·
      refine ⟨80047020719757195030836747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53364680479838130020557831 80047020719757195030836747)
      ·
        refine ⟨120070531079635792546255121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80047020719757195030836747 120070531079635792546255121)
        ·
          refine ⟨90052898309726844409691341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120070531079635792546255121 90052898309726844409691341)
          ·
            refine ⟨33769836866147566653634253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90052898309726844409691341 33769836866147566653634253)
            ·
              refine ⟨12663688824805337495112845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33769836866147566653634253 12663688824805337495112845)
              ·
                refine ⟨4748883309302001560667317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12663688824805337495112845 4748883309302001560667317)
                ·
                  refine ⟨445207810247062646312561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4748883309302001560667317 445207810247062646312561)
                  ·
                    rfl

theorem cell22_3901676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_3901676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901676 prefixEnd_3901676 := by exact prefixLift 3901676
  have htrace : WordTrace (prefixWord ++ tailWord_3901676) baseStart_3901676 baseEnd_3901676 := by
    simpa [prefixWord, tailWord_3901676, baseEnd_3901676] using wordTrace_append hprefix tailTrace_3901676
  have hstable : (prefixWord ++ tailWord_3901676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901676).length < 2 ^ (prefixWord ++ tailWord_3901676).sum := by decide
  have hdescent : baseEnd_3901676 < baseStart_3901676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901753 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 1, 5]
def baseStart_3901753 : Nat := 118140960795 + 3901753 * 2 ^ 59
def prefixEnd_3901753 : Nat := 4983230072969 + 3 ^ 40 * 3901753 * 2
def baseEnd_3901753 : Nat := 1335649789414785404762447

theorem tailTrace_3901753 : CollatzResearch.WordTrace tailWord_3901753 prefixEnd_3901753 1335649789414785404762447 := by
  unfold tailWord_3901753
  simp only [CollatzResearch.WordTrace]
  refine ⟨142308623033622722205373913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94872415355748481470249275 142308623033622722205373913)
  ·
    refine ⟨106731467275217041654030435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142308623033622722205373913 106731467275217041654030435)
    ·
      refine ⟨160097200912825562481045653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106731467275217041654030435 160097200912825562481045653)
      ·
        refine ⟨7504556292788698241299015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160097200912825562481045653 7504556292788698241299015)
        ·
          refine ⟨11256834439183047361948523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7504556292788698241299015 11256834439183047361948523)
          ·
            refine ⟨16885251658774571042922785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11256834439183047361948523 16885251658774571042922785)
            ·
              refine ⟨12663938744080928282192089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16885251658774571042922785 12663938744080928282192089)
              ·
                refine ⟨9497954058060696211644067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12663938744080928282192089 9497954058060696211644067)
                ·
                  refine ⟨14246931087091044317466101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9497954058060696211644067 14246931087091044317466101)
                  ·
                    refine ⟨1335649789414785404762447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14246931087091044317466101 1335649789414785404762447)
                    ·
                      rfl

theorem cell22_3901753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_3901753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901753 prefixEnd_3901753 := by exact prefixLift 3901753
  have htrace : WordTrace (prefixWord ++ tailWord_3901753) baseStart_3901753 baseEnd_3901753 := by
    simpa [prefixWord, tailWord_3901753, baseEnd_3901753] using wordTrace_append hprefix tailTrace_3901753
  have hstable : (prefixWord ++ tailWord_3901753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901753).length < 2 ^ (prefixWord ++ tailWord_3901753).sum := by decide
  have hdescent : baseEnd_3901753 < baseStart_3901753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901800 : List Nat := [2, 1, 4, 2, 2, 3, 2, 6]
def baseStart_3901800 : Nat := 118140960795 + 3901800 * 2 ^ 59
def prefixEnd_3901800 : Nat := 4983230072969 + 3 ^ 40 * 3901800 * 2
def baseEnd_3901800 : Nat := 148407319830588105426367

theorem tailTrace_3901800 : CollatzResearch.WordTrace tailWord_3901800 prefixEnd_3901800 148407319830588105426367 := by
  unfold tailWord_3901800
  simp only [CollatzResearch.WordTrace]
  refine ⟨71155168632226224616167427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94873558176301632821556569 71155168632226224616167427)
  ·
    refine ⟨106732752948339336924251141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71155168632226224616167427 106732752948339336924251141)
    ·
      refine ⟨20012391177813625673297089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106732752948339336924251141 20012391177813625673297089)
      ·
        refine ⟨15009293383360219254972817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20012391177813625673297089 15009293383360219254972817)
        ·
          refine ⟨11256970037520164441229613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15009293383360219254972817 11256970037520164441229613)
          ·
            refine ⟨4221363764070061665461105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11256970037520164441229613 4221363764070061665461105)
            ·
              refine ⟨3166022823052546249095829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4221363764070061665461105 3166022823052546249095829)
              ·
                refine ⟨148407319830588105426367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3166022823052546249095829 148407319830588105426367)
                ·
                  rfl

theorem cell22_3901800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 6].length) (baseStart_3901800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901800 prefixEnd_3901800 := by exact prefixLift 3901800
  have htrace : WordTrace (prefixWord ++ tailWord_3901800) baseStart_3901800 baseEnd_3901800 := by
    simpa [prefixWord, tailWord_3901800, baseEnd_3901800] using wordTrace_append hprefix tailTrace_3901800
  have hstable : (prefixWord ++ tailWord_3901800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901800).length < 2 ^ (prefixWord ++ tailWord_3901800).sum := by decide
  have hdescent : baseEnd_3901800 < baseStart_3901800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901815 : List Nat := [1, 1, 3, 1, 1, 2, 2, 7, 1, 3]
def baseStart_3901815 : Nat := 118140960795 + 3901815 * 2 ^ 59
def prefixEnd_3901815 : Nat := 4983230072969 + 3 ^ 40 * 3901815 * 2
def baseEnd_3901815 : Nat := 1335671013281837909712257

theorem tailTrace_3901815 : CollatzResearch.WordTrace tailWord_3901815 prefixEnd_3901815 1335671013281837909712257 := by
  unfold tailWord_3901815
  simp only [CollatzResearch.WordTrace]
  refine ⟨142310884359398106794130899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94873922906265404529420599 142310884359398106794130899)
  ·
    refine ⟨213466326539097160191196349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142310884359398106794130899 213466326539097160191196349)
    ·
      refine ⟨80049872452161435071698631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213466326539097160191196349 80049872452161435071698631)
      ·
        refine ⟨120074808678242152607547947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80049872452161435071698631 120074808678242152607547947)
        ·
          refine ⟨180112213017363228911321921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120074808678242152607547947 180112213017363228911321921)
          ·
            refine ⟨135084159763022421683491441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180112213017363228911321921 135084159763022421683491441)
            ·
              refine ⟨101313119822266816262618581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135084159763022421683491441 101313119822266816262618581)
              ·
                refine ⟨2374526245834378506155123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101313119822266816262618581 2374526245834378506155123)
                ·
                  refine ⟨3561789368751567759232685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374526245834378506155123 3561789368751567759232685)
                  ·
                    refine ⟨1335671013281837909712257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3561789368751567759232685 1335671013281837909712257)
                    ·
                      rfl

theorem cell22_3901815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_3901815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901815 prefixEnd_3901815 := by exact prefixLift 3901815
  have htrace : WordTrace (prefixWord ++ tailWord_3901815) baseStart_3901815 baseEnd_3901815 := by
    simpa [prefixWord, tailWord_3901815, baseEnd_3901815] using wordTrace_append hprefix tailTrace_3901815
  have hstable : (prefixWord ++ tailWord_3901815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901815).length < 2 ^ (prefixWord ++ tailWord_3901815).sum := by decide
  have hdescent : baseEnd_3901815 < baseStart_3901815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901828 : List Nat := [2, 3, 2, 1, 1, 2, 2, 4, 5]
def baseStart_3901828 : Nat := 118140960795 + 3901828 * 2 ^ 59
def prefixEnd_3901828 : Nat := 4983230072969 + 3 ^ 40 * 3901828 * 2
def baseEnd_3901828 : Nat := 445225154482503403045739

theorem tailTrace_3901828 : CollatzResearch.WordTrace tailWord_3901828 prefixEnd_3901828 445225154482503403045739 := by
  unfold tailWord_3901828
  simp only [CollatzResearch.WordTrace]
  refine ⟨71155679254175505007177069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94874239005567340009569425 71155679254175505007177069)
  ·
    refine ⟨26683379720315814377691401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71155679254175505007177069 26683379720315814377691401)
    ·
      refine ⟨20012534790236860783268551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26683379720315814377691401 20012534790236860783268551)
      ·
        refine ⟨30018802185355291174902827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20012534790236860783268551 30018802185355291174902827)
        ·
          refine ⟨45028203278032936762354241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30018802185355291174902827 45028203278032936762354241)
          ·
            refine ⟨33771152458524702571765681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45028203278032936762354241 33771152458524702571765681)
            ·
              refine ⟨25328364343893526928824261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33771152458524702571765681 25328364343893526928824261)
              ·
                refine ⟨4749068314480036299154549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25328364343893526928824261 4749068314480036299154549)
                ·
                  refine ⟨445225154482503403045739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4749068314480036299154549 445225154482503403045739)
                  ·
                    rfl

theorem cell22_3901828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_3901828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901828 prefixEnd_3901828 := by exact prefixLift 3901828
  have htrace : WordTrace (prefixWord ++ tailWord_3901828) baseStart_3901828 baseEnd_3901828 := by
    simpa [prefixWord, tailWord_3901828, baseEnd_3901828] using wordTrace_append hprefix tailTrace_3901828
  have hstable : (prefixWord ++ tailWord_3901828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901828).length < 2 ^ (prefixWord ++ tailWord_3901828).sum := by decide
  have hdescent : baseEnd_3901828 < baseStart_3901828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901978 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_3901978 : Nat := 118140960795 + 3901978 * 2 ^ 59
def prefixEnd_3901978 : Nat := 4983230072969 + 3 ^ 40 * 3901978 * 2
def baseEnd_3901978 : Nat := 1335726811512959817886757

theorem tailTrace_3901978 : CollatzResearch.WordTrace tailWord_3901978 prefixEnd_3901978 1335726811512959817886757 := by
  unfold tailWord_3901978
  simp only [CollatzResearch.WordTrace]
  refine ⟨35579207364451896408078647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94877886305205057088209725 35579207364451896408078647)
  ·
    refine ⟨53368811046677844612117971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35579207364451896408078647 53368811046677844612117971)
    ·
      refine ⟨80053216570016766918176957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53368811046677844612117971 80053216570016766918176957)
      ·
        refine ⟨30019956213756287594316359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80053216570016766918176957 30019956213756287594316359)
        ·
          refine ⟨45029934320634431391474539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30019956213756287594316359 45029934320634431391474539)
          ·
            refine ⟨67544901480951647087211809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45029934320634431391474539 67544901480951647087211809)
            ·
              refine ⟨50658676110713735315408857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67544901480951647087211809 50658676110713735315408857)
              ·
                refine ⟨37994007083035301486556643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50658676110713735315408857 37994007083035301486556643)
                ·
                  refine ⟨56991010624552952229834965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37994007083035301486556643 56991010624552952229834965)
                  ·
                    refine ⟨1335726811512959817886757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56991010624552952229834965 1335726811512959817886757)
                    ·
                      rfl

theorem cell22_3901978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_3901978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3901978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3901978 prefixEnd_3901978 := by exact prefixLift 3901978
  have htrace : WordTrace (prefixWord ++ tailWord_3901978) baseStart_3901978 baseEnd_3901978 := by
    simpa [prefixWord, tailWord_3901978, baseEnd_3901978] using wordTrace_append hprefix tailTrace_3901978
  have hstable : (prefixWord ++ tailWord_3901978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901978).length < 2 ^ (prefixWord ++ tailWord_3901978).sum := by decide
  have hdescent : baseEnd_3901978 < baseStart_3901978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902014 : List Nat := [4, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_3902014 : Nat := 118140960795 + 3902014 * 2 ^ 59
def prefixEnd_3902014 : Nat := 4983230072969 + 3 ^ 40 * 3902014 * 2
def baseEnd_3902014 : Nat := 445246378349555907995549

theorem tailTrace_3902014 : CollatzResearch.WordTrace tailWord_3902014 prefixEnd_3902014 445246378349555907995549 := by
  unfold tailWord_3902014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17789767810709645472578137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94878761657118109187083397 17789767810709645472578137)
  ·
    refine ⟨13342325858032234104433603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17789767810709645472578137 13342325858032234104433603)
    ·
      refine ⟨20013488787048351156650405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13342325858032234104433603 20013488787048351156650405)
      ·
        refine ⟨3752529147571565841871951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20013488787048351156650405 3752529147571565841871951)
        ·
          refine ⟨5628793721357348762807927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3752529147571565841871951 5628793721357348762807927)
          ·
            refine ⟨8443190582036023144211891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5628793721357348762807927 8443190582036023144211891)
            ·
              refine ⟨12664785873054034716317837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8443190582036023144211891 12664785873054034716317837)
              ·
                refine ⟨4749294702395263018619189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12664785873054034716317837 4749294702395263018619189)
                ·
                  refine ⟨445246378349555907995549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4749294702395263018619189 445246378349555907995549)
                  ·
                    rfl

theorem cell22_3902014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_3902014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902014 prefixEnd_3902014 := by exact prefixLift 3902014
  have htrace : WordTrace (prefixWord ++ tailWord_3902014) baseStart_3902014 baseEnd_3902014 := by
    simpa [prefixWord, tailWord_3902014, baseEnd_3902014] using wordTrace_append hprefix tailTrace_3902014
  have hstable : (prefixWord ++ tailWord_3902014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902014).length < 2 ^ (prefixWord ++ tailWord_3902014).sum := by decide
  have hdescent : baseEnd_3902014 < baseStart_3902014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902040 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 6, 3]
def baseStart_3902040 : Nat := 118140960795 + 3902040 * 2 ^ 59
def prefixEnd_3902040 : Nat := 4983230072969 + 3 ^ 40 * 3902040 * 2
def baseEnd_3902040 : Nat := 1335748035380012322836567

theorem tailTrace_3902040 : CollatzResearch.WordTrace tailWord_3902040 prefixEnd_3902040 1335748035380012322836567 := by
  unfold tailWord_3902040
  simp only [CollatzResearch.WordTrace]
  refine ⟨71159545391791485110535787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94879393855721980147381049 71159545391791485110535787)
  ·
    refine ⟨106739318087687227665803681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71159545391791485110535787 106739318087687227665803681)
    ·
      refine ⟨80054488565765420749352761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106739318087687227665803681 80054488565765420749352761)
      ·
        refine ⟨60040866424324065562014571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80054488565765420749352761 60040866424324065562014571)
        ·
          refine ⟨90061299636486098343021857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60040866424324065562014571 90061299636486098343021857)
          ·
            refine ⟨67545974727364573757266393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90061299636486098343021857 67545974727364573757266393)
            ·
              refine ⟨50659481045523430317949795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67545974727364573757266393 50659481045523430317949795)
              ·
                refine ⟨75989221568285145476924693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50659481045523430317949795 75989221568285145476924693)
                ·
                  refine ⟨3561994761013366194230845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75989221568285145476924693 3561994761013366194230845)
                  ·
                    refine ⟨1335748035380012322836567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3561994761013366194230845 1335748035380012322836567)
                    ·
                      rfl

theorem cell22_3902040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_3902040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902040 prefixEnd_3902040 := by exact prefixLift 3902040
  have htrace : WordTrace (prefixWord ++ tailWord_3902040) baseStart_3902040 baseEnd_3902040 := by
    simpa [prefixWord, tailWord_3902040, baseEnd_3902040] using wordTrace_append hprefix tailTrace_3902040
  have hstable : (prefixWord ++ tailWord_3902040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902040).length < 2 ^ (prefixWord ++ tailWord_3902040).sum := by decide
  have hdescent : baseEnd_3902040 < baseStart_3902040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902053 : List Nat := [1, 3, 1, 3, 14]
def baseStart_3902053 : Nat := 118140960795 + 3902053 * 2 ^ 59
def prefixEnd_3902053 : Nat := 4983230072969 + 3 ^ 40 * 3902053 * 2
def baseEnd_3902053 : Nat := 5496923808829977869389

theorem tailTrace_3902053 : CollatzResearch.WordTrace tailWord_3902053 prefixEnd_3902053 5496923808829977869389 := by
  unfold tailWord_3902053
  simp only [CollatzResearch.WordTrace]
  refine ⟨142319564932535873441294813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94879709955023915627529875 142319564932535873441294813)
  ·
    refine ⟨53369836849700952540485555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142319564932535873441294813 53369836849700952540485555)
    ·
      refine ⟨80054755274551428810728333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53369836849700952540485555 80054755274551428810728333)
      ·
        refine ⟨30020533227956785804023125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80054755274551428810728333 30020533227956785804023125)
        ·
          refine ⟨5496923808829977869389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 30020533227956785804023125 5496923808829977869389)
          ·
            rfl

theorem cell22_3902053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 14].length) (baseStart_3902053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902053 prefixEnd_3902053 := by exact prefixLift 3902053
  have htrace : WordTrace (prefixWord ++ tailWord_3902053) baseStart_3902053 baseEnd_3902053 := by
    simpa [prefixWord, tailWord_3902053, baseEnd_3902053] using wordTrace_append hprefix tailTrace_3902053
  have hstable : (prefixWord ++ tailWord_3902053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902053).length < 2 ^ (prefixWord ++ tailWord_3902053).sum := by decide
  have hdescent : baseEnd_3902053 < baseStart_3902053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902115 : List Nat := [1, 1, 1, 4, 1, 1, 2, 6, 5]
def baseStart_3902115 : Nat := 118140960795 + 3902115 * 2 ^ 59
def prefixEnd_3902115 : Nat := 4983230072969 + 3 ^ 40 * 3902115 * 2
def baseEnd_3902115 : Nat := 445257903137579042403779

theorem tailTrace_3902115 : CollatzResearch.WordTrace tailWord_3902115 prefixEnd_3902115 445257903137579042403779 := by
  unfold tailWord_3902115
  simp only [CollatzResearch.WordTrace]
  refine ⟨142321826258311258030051799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94881217505540838686701199 142321826258311258030051799)
  ·
    refine ⟨213482739387466887045077699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142321826258311258030051799 213482739387466887045077699)
    ·
      refine ⟨320224109081200330567616549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213482739387466887045077699 320224109081200330567616549)
      ·
        refine ⟨60042020452725061981428103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320224109081200330567616549 60042020452725061981428103)
        ·
          refine ⟨90063030679087592972142155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60042020452725061981428103 90063030679087592972142155)
          ·
            refine ⟨135094546018631389458213233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90063030679087592972142155 135094546018631389458213233)
            ·
              refine ⟨101320909513973542093659925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135094546018631389458213233 101320909513973542093659925)
              ·
                refine ⟨4749417633467509785640309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101320909513973542093659925 4749417633467509785640309)
                ·
                  refine ⟨445257903137579042403779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4749417633467509785640309 445257903137579042403779)
                  ·
                    rfl

theorem cell22_3902115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 5].length) (baseStart_3902115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902115 prefixEnd_3902115 := by exact prefixLift 3902115
  have htrace : WordTrace (prefixWord ++ tailWord_3902115) baseStart_3902115 baseEnd_3902115 := by
    simpa [prefixWord, tailWord_3902115, baseEnd_3902115] using wordTrace_append hprefix tailTrace_3902115
  have hstable : (prefixWord ++ tailWord_3902115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902115).length < 2 ^ (prefixWord ++ tailWord_3902115).sum := by decide
  have hdescent : baseEnd_3902115 < baseStart_3902115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902177 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 6]
def baseStart_3902177 : Nat := 118140960795 + 3902177 * 2 ^ 59
def prefixEnd_3902177 : Nat := 4983230072969 + 3 ^ 40 * 3902177 * 2
def baseEnd_3902177 : Nat := 445264977759929877387049

theorem tailTrace_3902177 : CollatzResearch.WordTrace tailWord_3902177 prefixEnd_3902177 445264977759929877387049 := by
  unfold tailWord_3902177
  simp only [CollatzResearch.WordTrace]
  refine ⟨142324087584086642618808785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94882725056057761745872523 142324087584086642618808785)
  ·
    refine ⟨106743065688064981964106589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142324087584086642618808785 106743065688064981964106589)
    ·
      refine ⟨40028649633024368236539971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106743065688064981964106589 40028649633024368236539971)
      ·
        refine ⟨60042974449536552354809957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40028649633024368236539971 60042974449536552354809957)
        ·
          refine ⟨11258057709288103566526867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60042974449536552354809957 11258057709288103566526867)
          ·
            refine ⟨16887086563932155349790301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11258057709288103566526867 16887086563932155349790301)
            ·
              refine ⟨6332657461474558256171363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16887086563932155349790301 6332657461474558256171363)
              ·
                refine ⟨9498986192211837384257045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6332657461474558256171363 9498986192211837384257045)
                ·
                  refine ⟨445264977759929877387049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9498986192211837384257045 445264977759929877387049)
                  ·
                    rfl

theorem cell22_3902177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_3902177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902177 prefixEnd_3902177 := by exact prefixLift 3902177
  have htrace : WordTrace (prefixWord ++ tailWord_3902177) baseStart_3902177 baseEnd_3902177 := by
    simpa [prefixWord, tailWord_3902177, baseEnd_3902177] using wordTrace_append hprefix tailTrace_3902177
  have hstable : (prefixWord ++ tailWord_3902177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902177).length < 2 ^ (prefixWord ++ tailWord_3902177).sum := by decide
  have hdescent : baseEnd_3902177 < baseStart_3902177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902205 : List Nat := [1, 4, 1, 1, 1, 1, 3, 10]
def baseStart_3902205 : Nat := 118140960795 + 3902205 * 2 ^ 59
def prefixEnd_3902205 : Nat := 4983230072969 + 3 ^ 40 * 3902205 * 2
def baseEnd_3902205 : Nat := 148422724250222988051229

theorem tailTrace_3902205 : CollatzResearch.WordTrace tailWord_3902205 prefixEnd_3902205 148422724250222988051229 := by
  unfold tailWord_3902205
  simp only [CollatzResearch.WordTrace]
  refine ⟨142325108827985203400828069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94883405885323468933885379 142325108827985203400828069)
  ·
    refine ⟨26685957905247225637655263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142325108827985203400828069 26685957905247225637655263)
    ·
      refine ⟨40028936857870838456482895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26685957905247225637655263 40028936857870838456482895)
      ·
        refine ⟨60043405286806257684724343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40028936857870838456482895 60043405286806257684724343)
        ·
          refine ⟨90065107930209386527086515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60043405286806257684724343 90065107930209386527086515)
          ·
            refine ⟨135097661895314079790629773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90065107930209386527086515 135097661895314079790629773)
            ·
              refine ⟨50661623210742779921486165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135097661895314079790629773 50661623210742779921486165)
              ·
                refine ⟨148422724250222988051229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50661623210742779921486165 148422724250222988051229)
                ·
                  rfl

theorem cell22_3902205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 10].length) (baseStart_3902205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902205 prefixEnd_3902205 := by exact prefixLift 3902205
  have htrace : WordTrace (prefixWord ++ tailWord_3902205) baseStart_3902205 baseEnd_3902205 := by
    simpa [prefixWord, tailWord_3902205, baseEnd_3902205] using wordTrace_append hprefix tailTrace_3902205
  have hstable : (prefixWord ++ tailWord_3902205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902205).length < 2 ^ (prefixWord ++ tailWord_3902205).sum := by decide
  have hdescent : baseEnd_3902205 < baseStart_3902205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902271 : List Nat := [1, 1, 2, 2, 5, 1, 1, 5, 1, 3]
def baseStart_3902271 : Nat := 118140960795 + 3902271 * 2 ^ 59
def prefixEnd_3902271 : Nat := 4983230072969 + 3 ^ 40 * 3902271 * 2
def baseEnd_3902271 : Nat := 1335827111400804720310859

theorem tailTrace_3902271 : CollatzResearch.WordTrace tailWord_3902271 prefixEnd_3902271 1335827111400804720310859 := by
  unfold tailWord_3902271
  simp only [CollatzResearch.WordTrace]
  refine ⟨142327516045746096672730667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94885010697164064448487111 142327516045746096672730667)
  ·
    refine ⟨213491274068619145009096001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142327516045746096672730667 213491274068619145009096001)
    ·
      refine ⟨160118455551464358756822001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213491274068619145009096001 160118455551464358756822001)
      ·
        refine ⟨120088841663598269067616501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160118455551464358756822001 120088841663598269067616501)
        ·
          refine ⟨11258328905962337725089047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120088841663598269067616501 11258328905962337725089047)
          ·
            refine ⟨16887493358943506587633571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11258328905962337725089047 16887493358943506587633571)
            ·
              refine ⟨25331240038415259881450357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16887493358943506587633571 25331240038415259881450357)
              ·
                refine ⟨2374803753601430613885971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25331240038415259881450357 2374803753601430613885971)
                ·
                  refine ⟨3562205630402145920828957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374803753601430613885971 3562205630402145920828957)
                  ·
                    refine ⟨1335827111400804720310859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3562205630402145920828957 1335827111400804720310859)
                    ·
                      rfl

theorem cell22_3902271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 1, 3].length) (baseStart_3902271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902271 prefixEnd_3902271 := by exact prefixLift 3902271
  have htrace : WordTrace (prefixWord ++ tailWord_3902271) baseStart_3902271 baseEnd_3902271 := by
    simpa [prefixWord, tailWord_3902271, baseEnd_3902271] using wordTrace_append hprefix tailTrace_3902271
  have hstable : (prefixWord ++ tailWord_3902271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902271).length < 2 ^ (prefixWord ++ tailWord_3902271).sum := by decide
  have hdescent : baseEnd_3902271 < baseStart_3902271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902284 : List Nat := [2, 2, 1, 3, 3, 1, 3, 2, 5]
def baseStart_3902284 : Nat := 118140960795 + 3902284 * 2 ^ 59
def prefixEnd_3902284 : Nat := 4983230072969 + 3 ^ 40 * 3902284 * 2
def baseEnd_3902284 : Nat := 445277187188825673245273

theorem tailTrace_3902284 : CollatzResearch.WordTrace tailWord_3902284 prefixEnd_3902284 445277187188825673245273 := by
  unfold tailWord_3902284
  simp only [CollatzResearch.WordTrace]
  refine ⟨71163995097349499946476953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94885326796465999928635937 71163995097349499946476953)
  ·
    refine ⟨53372996323012124959857715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71163995097349499946476953 53372996323012124959857715)
    ·
      refine ⟨80059494484518187439786573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53372996323012124959857715 80059494484518187439786573)
      ·
        refine ⟨30022310431694320289919965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80059494484518187439786573 30022310431694320289919965)
        ·
          refine ⟨11258366411885370108719987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30022310431694320289919965 11258366411885370108719987)
          ·
            refine ⟨16887549617828055163079981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11258366411885370108719987 16887549617828055163079981)
            ·
              refine ⟨6332831106685520686154993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16887549617828055163079981 6332831106685520686154993)
              ·
                refine ⟨4749623330014140514616245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6332831106685520686154993 4749623330014140514616245)
                ·
                  refine ⟨445277187188825673245273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4749623330014140514616245 445277187188825673245273)
                  ·
                    rfl

theorem cell22_3902284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_3902284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902284 prefixEnd_3902284 := by exact prefixLift 3902284
  have htrace : WordTrace (prefixWord ++ tailWord_3902284) baseStart_3902284 baseEnd_3902284 := by
    simpa [prefixWord, tailWord_3902284, baseEnd_3902284] using wordTrace_append hprefix tailTrace_3902284
  have hstable : (prefixWord ++ tailWord_3902284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902284).length < 2 ^ (prefixWord ++ tailWord_3902284).sum := by decide
  have hdescent : baseEnd_3902284 < baseStart_3902284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902327 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 1, 5]
def baseStart_3902327 : Nat := 118140960795 + 3902327 * 2 ^ 59
def prefixEnd_3902327 : Nat := 4983230072969 + 3 ^ 40 * 3902327 * 2
def baseEnd_3902327 : Nat := 1335846281345239240910687

theorem tailTrace_3902327 : CollatzResearch.WordTrace tailWord_3902327 prefixEnd_3902327 1335846281345239240910687 := by
  unfold tailWord_3902327
  simp only [CollatzResearch.WordTrace]
  refine ⟨142329558533543218236769235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94886372355695478824512823 142329558533543218236769235)
  ·
    refine ⟨213494337800314827355153853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142329558533543218236769235 213494337800314827355153853)
    ·
      refine ⟨80060376675118060258182695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213494337800314827355153853 80060376675118060258182695)
      ·
        refine ⟨120090565012677090387274043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80060376675118060258182695 120090565012677090387274043)
        ·
          refine ⟨180135847519015635580911065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120090565012677090387274043 180135847519015635580911065)
          ·
            refine ⟨135101885639261726685683299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180135847519015635580911065 135101885639261726685683299)
            ·
              refine ⟨202652828458892590028524949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135101885639261726685683299 202652828458892590028524949)
              ·
                refine ⟨9499351334010590157587107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 202652828458892590028524949 9499351334010590157587107)
                ·
                  refine ⟨14249027001015885236380661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9499351334010590157587107 14249027001015885236380661)
                  ·
                    refine ⟨1335846281345239240910687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14249027001015885236380661 1335846281345239240910687)
                    ·
                      rfl

theorem cell22_3902327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_3902327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902327 prefixEnd_3902327 := by exact prefixLift 3902327
  have htrace : WordTrace (prefixWord ++ tailWord_3902327) baseStart_3902327 baseEnd_3902327 := by
    simpa [prefixWord, tailWord_3902327, baseEnd_3902327] using wordTrace_append hprefix tailTrace_3902327
  have hstable : (prefixWord ++ tailWord_3902327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902327).length < 2 ^ (prefixWord ++ tailWord_3902327).sum := by decide
  have hdescent : baseEnd_3902327 < baseStart_3902327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902346 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 6]
def baseStart_3902346 : Nat := 118140960795 + 3902346 * 2 ^ 59
def prefixEnd_3902346 : Nat := 4983230072969 + 3 ^ 40 * 3902346 * 2
def baseEnd_3902346 : Nat := 445284261811176508228543

theorem tailTrace_3902346 : CollatzResearch.WordTrace tailWord_3902346 prefixEnd_3902346 445284261811176508228543 := by
  unfold tailWord_3902346
  simp only [CollatzResearch.WordTrace]
  refine ⟨35582562880118596120427723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94886834346982922987807261 35582562880118596120427723)
  ·
    refine ⟨53373844320177894180641585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35582562880118596120427723 53373844320177894180641585)
    ·
      refine ⟨40030383240133420635481189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53373844320177894180641585 40030383240133420635481189)
      ·
        refine ⟨7505696857525016369152723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40030383240133420635481189 7505696857525016369152723)
        ·
          refine ⟨11258545286287524553729085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7505696857525016369152723 11258545286287524553729085)
          ·
            refine ⟨4221954482357821707648407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11258545286287524553729085 4221954482357821707648407)
            ·
              refine ⟨6332931723536732561472611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4221954482357821707648407 6332931723536732561472611)
              ·
                refine ⟨9499397585305098842208917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6332931723536732561472611 9499397585305098842208917)
                ·
                  refine ⟨445284261811176508228543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9499397585305098842208917 445284261811176508228543)
                  ·
                    rfl

theorem cell22_3902346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_3902346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902346 prefixEnd_3902346 := by exact prefixLift 3902346
  have htrace : WordTrace (prefixWord ++ tailWord_3902346) baseStart_3902346 baseEnd_3902346 := by
    simpa [prefixWord, tailWord_3902346, baseEnd_3902346] using wordTrace_append hprefix tailTrace_3902346
  have hstable : (prefixWord ++ tailWord_3902346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902346).length < 2 ^ (prefixWord ++ tailWord_3902346).sum := by decide
  have hdescent : baseEnd_3902346 < baseStart_3902346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902357 : List Nat := [1, 3, 2, 1, 1, 4, 1, 9]
def baseStart_3902357 : Nat := 118140960795 + 3902357 * 2 ^ 59
def prefixEnd_3902357 : Nat := 4983230072969 + 3 ^ 40 * 3902357 * 2
def baseEnd_3902357 : Nat := 148428505662036573628955

theorem tailTrace_3902357 : CollatzResearch.WordTrace tailWord_3902357 prefixEnd_3902357 148428505662036573628955 := by
  unfold tailWord_3902357
  simp only [CollatzResearch.WordTrace]
  refine ⟨142330652723434533360361325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94887101815623022240240883 142330652723434533360361325)
  ·
    refine ⟨53373994771287950010135497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142330652723434533360361325 53373994771287950010135497)
    ·
      refine ⟨40030496078465962507601623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53373994771287950010135497 40030496078465962507601623)
      ·
        refine ⟨60045744117698943761402435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40030496078465962507601623 60045744117698943761402435)
        ·
          refine ⟨90068616176548415642103653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60045744117698943761402435 90068616176548415642103653)
          ·
            refine ⟨16887865533102827932894435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90068616176548415642103653 16887865533102827932894435)
            ·
              refine ⟨25331798299654241899341653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16887865533102827932894435 25331798299654241899341653)
              ·
                refine ⟨148428505662036573628955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25331798299654241899341653 148428505662036573628955)
                ·
                  rfl

theorem cell22_3902357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 9].length) (baseStart_3902357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902357 prefixEnd_3902357 := by exact prefixLift 3902357
  have htrace : WordTrace (prefixWord ++ tailWord_3902357) baseStart_3902357 baseEnd_3902357 := by
    simpa [prefixWord, tailWord_3902357, baseEnd_3902357] using wordTrace_append hprefix tailTrace_3902357
  have hstable : (prefixWord ++ tailWord_3902357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902357).length < 2 ^ (prefixWord ++ tailWord_3902357).sum := by decide
  have hdescent : baseEnd_3902357 < baseStart_3902357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902453 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 7]
def baseStart_3902453 : Nat := 118140960795 + 3902453 * 2 ^ 59
def prefixEnd_3902453 : Nat := 4983230072969 + 3 ^ 40 * 3902453 * 2
def baseEnd_3902453 : Nat := 445296471240072304086767

theorem tailTrace_3902453 : CollatzResearch.WordTrace tailWord_3902453 prefixEnd_3902453 445296471240072304086767 := by
  unfold tailWord_3902453
  simp only [CollatzResearch.WordTrace]
  refine ⟨142334154131086741755856013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94889436087391161170570675 142334154131086741755856013)
  ·
    refine ⟨53375307799157528158446005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142334154131086741755856013 53375307799157528158446005)
    ·
      refine ⟨5003935106171018264854313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53375307799157528158446005 5003935106171018264854313)
      ·
        refine ⟨3752951329628263698640735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5003935106171018264854313 3752951329628263698640735)
        ·
          refine ⟨5629426994442395547961103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3752951329628263698640735 5629426994442395547961103)
          ·
            refine ⟨8444140491663593321941655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5629426994442395547961103 8444140491663593321941655)
            ·
              refine ⟨12666210737495389982912483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8444140491663593321941655 12666210737495389982912483)
              ·
                refine ⟨18999316106243084974368725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12666210737495389982912483 18999316106243084974368725)
                ·
                  refine ⟨445296471240072304086767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18999316106243084974368725 445296471240072304086767)
                  ·
                    rfl

theorem cell22_3902453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_3902453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902453 prefixEnd_3902453 := by exact prefixLift 3902453
  have htrace : WordTrace (prefixWord ++ tailWord_3902453) baseStart_3902453 baseEnd_3902453 := by
    simpa [prefixWord, tailWord_3902453, baseEnd_3902453] using wordTrace_append hprefix tailTrace_3902453
  have hstable : (prefixWord ++ tailWord_3902453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902453).length < 2 ^ (prefixWord ++ tailWord_3902453).sum := by decide
  have hdescent : baseEnd_3902453 < baseStart_3902453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902498 : List Nat := [3, 3, 1, 1, 1, 3, 3, 3, 4]
def baseStart_3902498 : Nat := 118140960795 + 3902498 * 2 ^ 59
def prefixEnd_3902498 : Nat := 4983230072969 + 3 ^ 40 * 3902498 * 2
def baseEnd_3902498 : Nat := 445301606046617264961721

theorem tailTrace_3902498 : CollatzResearch.WordTrace tailWord_3902498 prefixEnd_3902498 445301606046617264961721 := by
  unfold tailWord_3902498
  simp only [CollatzResearch.WordTrace]
  refine ⟨35583948853980928610311037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94890530277282476294162765 35583948853980928610311037)
  ·
    refine ⟨13343980820242848228866639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35583948853980928610311037 13343980820242848228866639)
    ·
      refine ⟨20015971230364272343299959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13343980820242848228866639 20015971230364272343299959)
      ·
        refine ⟨30023956845546408514949939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20015971230364272343299959 30023956845546408514949939)
        ·
          refine ⟨45035935268319612772424909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30023956845546408514949939 45035935268319612772424909)
          ·
            refine ⟨16888475725619854789659341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45035935268319612772424909 16888475725619854789659341)
            ·
              refine ⟨6333178397107445546122253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16888475725619854789659341 6333178397107445546122253)
              ·
                refine ⟨2374941898915292079795845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6333178397107445546122253 2374941898915292079795845)
                ·
                  refine ⟨445301606046617264961721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374941898915292079795845 445301606046617264961721)
                  ·
                    rfl

theorem cell22_3902498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_3902498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902498 prefixEnd_3902498 := by exact prefixLift 3902498
  have htrace : WordTrace (prefixWord ++ tailWord_3902498) baseStart_3902498 baseEnd_3902498 := by
    simpa [prefixWord, tailWord_3902498, baseEnd_3902498] using wordTrace_append hprefix tailTrace_3902498
  have hstable : (prefixWord ++ tailWord_3902498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902498).length < 2 ^ (prefixWord ++ tailWord_3902498).sum := by decide
  have hdescent : baseEnd_3902498 < baseStart_3902498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902526 : List Nat := [4, 2, 1, 3, 1, 1, 1, 9]
def baseStart_3902526 : Nat := 118140960795 + 3902526 * 2 ^ 59
def prefixEnd_3902526 : Nat := 4983230072969 + 3 ^ 40 * 3902526 * 2
def baseEnd_3902526 : Nat := 148434933679118783909453

theorem tailTrace_3902526 : CollatzResearch.WordTrace tailWord_3902526 prefixEnd_3902526 148434933679118783909453 := by
  unfold tailWord_3902526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17792102082477784402907929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94891211106548183482175621 17792102082477784402907929)
  ·
    refine ⟨13344076561858338302180947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17792102082477784402907929 13344076561858338302180947)
    ·
      refine ⟨20016114842787507453271421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13344076561858338302180947 20016114842787507453271421)
      ·
        refine ⟨7506043066045315294976783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20016114842787507453271421 7506043066045315294976783)
        ·
          refine ⟨11259064599067972942465175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7506043066045315294976783 11259064599067972942465175)
          ·
            refine ⟨16888596898601959413697763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11259064599067972942465175 16888596898601959413697763)
            ·
              refine ⟨25332895347902939120546645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16888596898601959413697763 25332895347902939120546645)
              ·
                refine ⟨148434933679118783909453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25332895347902939120546645 148434933679118783909453)
                ·
                  rfl

theorem cell22_3902526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_3902526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902526 prefixEnd_3902526 := by exact prefixLift 3902526
  have htrace : WordTrace (prefixWord ++ tailWord_3902526) baseStart_3902526 baseEnd_3902526 := by
    simpa [prefixWord, tailWord_3902526, baseEnd_3902526] using wordTrace_append hprefix tailTrace_3902526
  have hstable : (prefixWord ++ tailWord_3902526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902526).length < 2 ^ (prefixWord ++ tailWord_3902526).sum := by decide
  have hdescent : baseEnd_3902526 < baseStart_3902526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902554 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 7]
def baseStart_3902554 : Nat := 118140960795 + 3902554 * 2 ^ 59
def prefixEnd_3902554 : Nat := 4983230072969 + 3 ^ 40 * 3902554 * 2
def baseEnd_3902554 : Nat := 445307996028095438494997

theorem tailTrace_3902554 : CollatzResearch.WordTrace tailWord_3902554 prefixEnd_3902554 445307996028095438494997 := by
  unfold tailWord_3902554
  simp only [CollatzResearch.WordTrace]
  refine ⟨35584459475930209001320679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94891891935813890670188477 35584459475930209001320679)
  ·
    refine ⟨53376689213895313501981019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35584459475930209001320679 53376689213895313501981019)
    ·
      refine ⟨80065033820842970252971529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53376689213895313501981019 80065033820842970252971529)
      ·
        refine ⟨60048775365632227689728647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80065033820842970252971529 60048775365632227689728647)
        ·
          refine ⟨90073163048448341534592971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60048775365632227689728647 90073163048448341534592971)
          ·
            refine ⟨135109744572672512301889457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90073163048448341534592971 135109744572672512301889457)
            ·
              refine ⟨101332308429504384226417093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135109744572672512301889457 101332308429504384226417093)
              ·
                refine ⟨18999807830532072042453205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101332308429504384226417093 18999807830532072042453205)
                ·
                  refine ⟨445307996028095438494997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18999807830532072042453205 445307996028095438494997)
                  ·
                    rfl

theorem cell22_3902554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_3902554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902554 prefixEnd_3902554 := by exact prefixLift 3902554
  have htrace : WordTrace (prefixWord ++ tailWord_3902554) baseStart_3902554 baseEnd_3902554 := by
    simpa [prefixWord, tailWord_3902554, baseEnd_3902554] using wordTrace_append hprefix tailTrace_3902554
  have hstable : (prefixWord ++ tailWord_3902554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902554).length < 2 ^ (prefixWord ++ tailWord_3902554).sum := by decide
  have hdescent : baseEnd_3902554 < baseStart_3902554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902601 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 3, 4]
def baseStart_3902601 : Nat := 118140960795 + 3902601 * 2 ^ 59
def prefixEnd_3902601 : Nat := 4983230072969 + 3 ^ 40 * 3902601 * 2
def baseEnd_3902601 : Nat := 1335940077144793859559847

theorem tailTrace_3902601 : CollatzResearch.WordTrace tailWord_3902601 prefixEnd_3902601 1335940077144793859559847 := by
  unfold tailWord_3902601
  simp only [CollatzResearch.WordTrace]
  refine ⟨142339552134550563032243657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94893034756367042021495771 142339552134550563032243657)
  ·
    refine ⟨106754664100912922274182743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142339552134550563032243657 106754664100912922274182743)
    ·
      refine ⟨160131996151369383411274115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106754664100912922274182743 160131996151369383411274115)
      ·
        refine ⟨240197994227054075116911173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160131996151369383411274115 240197994227054075116911173)
        ·
          refine ⟨45037123917572639084420845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240197994227054075116911173 45037123917572639084420845)
          ·
            refine ⟨16888921469089739656657817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45037123917572639084420845 16888921469089739656657817)
            ·
              refine ⟨12666691101817304742493363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16888921469089739656657817 12666691101817304742493363)
              ·
                refine ⟨19000036652725957113740045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12666691101817304742493363 19000036652725957113740045)
                ·
                  refine ⟨7125013744772233917652517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19000036652725957113740045 7125013744772233917652517)
                  ·
                    refine ⟨1335940077144793859559847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7125013744772233917652517 1335940077144793859559847)
                    ·
                      rfl

theorem cell22_3902601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_3902601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902601 prefixEnd_3902601 := by exact prefixLift 3902601
  have htrace : WordTrace (prefixWord ++ tailWord_3902601) baseStart_3902601 baseEnd_3902601 := by
    simpa [prefixWord, tailWord_3902601, baseEnd_3902601] using wordTrace_append hprefix tailTrace_3902601
  have hstable : (prefixWord ++ tailWord_3902601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902601).length < 2 ^ (prefixWord ++ tailWord_3902601).sum := by decide
  have hdescent : baseEnd_3902601 < baseStart_3902601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902744 : List Nat := [2, 1, 2, 3, 1, 5, 2, 2, 1, 3]
def baseStart_3902744 : Nat := 118140960795 + 3902744 * 2 ^ 59
def prefixEnd_3902744 : Nat := 4983230072969 + 3 ^ 40 * 3902744 * 2
def baseEnd_3902744 : Nat := 1335989028967189153234409

theorem tailTrace_3902744 : CollatzResearch.WordTrace tailWord_3902744 prefixEnd_3902744 1335989028967189153234409 := by
  unfold tailWord_3902744
  simp only [CollatzResearch.WordTrace]
  refine ⟨71172383886516249227349643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94896511848688332303132857 71172383886516249227349643)
  ·
    refine ⟨106758575829774373841024465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71172383886516249227349643 106758575829774373841024465)
    ·
      refine ⟨80068931872330780380768349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106758575829774373841024465 80068931872330780380768349)
      ·
        refine ⟨30025849452124042642788131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80068931872330780380768349 30025849452124042642788131)
        ·
          refine ⟨45038774178186063964182197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30025849452124042642788131 45038774178186063964182197)
          ·
            refine ⟨4222385079204943496642081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45038774178186063964182197 4222385079204943496642081)
            ·
              refine ⟨3166788809403707622481561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4222385079204943496642081 3166788809403707622481561)
              ·
                refine ⟨2375091607052780716861171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3166788809403707622481561 2375091607052780716861171)
                ·
                  refine ⟨3562637410579171075291757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375091607052780716861171 3562637410579171075291757)
                  ·
                    refine ⟨1335989028967189153234409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3562637410579171075291757 1335989028967189153234409)
                    ·
                      rfl

theorem cell22_3902744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_3902744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902744 prefixEnd_3902744 := by exact prefixLift 3902744
  have htrace : WordTrace (prefixWord ++ tailWord_3902744) baseStart_3902744 baseEnd_3902744 := by
    simpa [prefixWord, tailWord_3902744, baseEnd_3902744] using wordTrace_append hprefix tailTrace_3902744
  have hstable : (prefixWord ++ tailWord_3902744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902744).length < 2 ^ (prefixWord ++ tailWord_3902744).sum := by decide
  have hdescent : baseEnd_3902744 < baseStart_3902744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902783 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 1, 5]
def baseStart_3902783 : Nat := 118140960795 + 3902783 * 2 ^ 59
def prefixEnd_3902783 : Nat := 4983230072969 + 3 ^ 40 * 3902783 * 2
def baseEnd_3902783 : Nat := 1336002379464206051509289

theorem tailTrace_3902783 : CollatzResearch.WordTrace tailWord_3902783 prefixEnd_3902783 1336002379464206051509289 := by
  unfold tailWord_3902783
  simp only [CollatzResearch.WordTrace]
  refine ⟨142346190219891208115369003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94897460146594138743579335 142346190219891208115369003)
  ·
    refine ⟨213519285329836812173053505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142346190219891208115369003 213519285329836812173053505)
    ·
      refine ⟨160139463997377609129790129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213519285329836812173053505 160139463997377609129790129)
      ·
        refine ⟨120104597998033206847342597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160139463997377609129790129 120104597998033206847342597)
        ·
          refine ⟨22519612124631226283876737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120104597998033206847342597 22519612124631226283876737)
          ·
            refine ⟨16889709093473419712907553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22519612124631226283876737 16889709093473419712907553)
            ·
              refine ⟨12667281820105064784680665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16889709093473419712907553 12667281820105064784680665)
              ·
                refine ⟨9500461365078798588510499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12667281820105064784680665 9500461365078798588510499)
                ·
                  refine ⟨14250692047618197882765749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9500461365078798588510499 14250692047618197882765749)
                  ·
                    refine ⟨1336002379464206051509289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14250692047618197882765749 1336002379464206051509289)
                    ·
                      rfl

theorem cell22_3902783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_3902783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902783 prefixEnd_3902783 := by exact prefixLift 3902783
  have htrace : WordTrace (prefixWord ++ tailWord_3902783) baseStart_3902783 baseEnd_3902783 := by
    simpa [prefixWord, tailWord_3902783, baseEnd_3902783] using wordTrace_append hprefix tailTrace_3902783
  have hstable : (prefixWord ++ tailWord_3902783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902783).length < 2 ^ (prefixWord ++ tailWord_3902783).sum := by decide
  have hdescent : baseEnd_3902783 < baseStart_3902783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902798 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_3902798 : Nat := 118140960795 + 3902798 * 2 ^ 59
def prefixEnd_3902798 : Nat := 4983230072969 + 3 ^ 40 * 3902798 * 2
def baseEnd_3902798 : Nat := 1336007514270751012384243

theorem tailTrace_3902798 : CollatzResearch.WordTrace tailWord_3902798 prefixEnd_3902798 1336007514270751012384243 := by
  unfold tailWord_3902798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17793342164354608209645631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94897824876557910451443365 17793342164354608209645631)
  ·
    refine ⟨26690013246531912314468447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17793342164354608209645631 26690013246531912314468447)
    ·
      refine ⟨40035019869797868471702671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26690013246531912314468447 40035019869797868471702671)
      ·
        refine ⟨60052529804696802707554007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40035019869797868471702671 60052529804696802707554007)
        ·
          refine ⟨90078794707045204061331011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60052529804696802707554007 90078794707045204061331011)
          ·
            refine ⟨135118192060567806091996517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90078794707045204061331011 135118192060567806091996517)
            ·
              refine ⟨25334661011356463642249347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135118192060567806091996517 25334661011356463642249347)
              ·
                refine ⟨38001991517034695463374021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25334661011356463642249347 38001991517034695463374021)
                ·
                  refine ⟨7125373409444005399382629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38001991517034695463374021 7125373409444005399382629)
                  ·
                    refine ⟨1336007514270751012384243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7125373409444005399382629 1336007514270751012384243)
                    ·
                      rfl

theorem cell22_3902798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_3902798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902798 prefixEnd_3902798 := by exact prefixLift 3902798
  have htrace : WordTrace (prefixWord ++ tailWord_3902798) baseStart_3902798 baseEnd_3902798 := by
    simpa [prefixWord, tailWord_3902798, baseEnd_3902798] using wordTrace_append hprefix tailTrace_3902798
  have hstable : (prefixWord ++ tailWord_3902798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902798).length < 2 ^ (prefixWord ++ tailWord_3902798).sum := by decide
  have hdescent : baseEnd_3902798 < baseStart_3902798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902948 : List Nat := [2, 3, 1, 1, 1, 1, 1, 12]
def baseStart_3902948 : Nat := 118140960795 + 3902948 * 2 ^ 59
def prefixEnd_3902948 : Nat := 4983230072969 + 3 ^ 40 * 3902948 * 2
def baseEnd_3902948 : Nat := 148450984704022291237087

theorem tailTrace_3902948 : CollatzResearch.WordTrace tailWord_3902948 prefixEnd_3902948 148450984704022291237087 := by
  unfold tailWord_3902948
  simp only [CollatzResearch.WordTrace]
  refine ⟨71176104132146720647562749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94901472176195627530083665 71176104132146720647562749)
  ·
    refine ⟨26691039049555020242836031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71176104132146720647562749 26691039049555020242836031)
    ·
      refine ⟨40036558574332530364254047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26691039049555020242836031 40036558574332530364254047)
      ·
        refine ⟨60054837861498795546381071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40036558574332530364254047 60054837861498795546381071)
        ·
          refine ⟨90082256792248193319571607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60054837861498795546381071 90082256792248193319571607)
          ·
            refine ⟨135123385188372289979357411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90082256792248193319571607 135123385188372289979357411)
            ·
              refine ⟨202685077782558434969036117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135123385188372289979357411 202685077782558434969036117)
              ·
                refine ⟨148450984704022291237087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 202685077782558434969036117 148450984704022291237087)
                ·
                  rfl

theorem cell22_3902948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 12].length) (baseStart_3902948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902948 prefixEnd_3902948 := by exact prefixLift 3902948
  have htrace : WordTrace (prefixWord ++ tailWord_3902948) baseStart_3902948 baseEnd_3902948 := by
    simpa [prefixWord, tailWord_3902948, baseEnd_3902948] using wordTrace_append hprefix tailTrace_3902948
  have hstable : (prefixWord ++ tailWord_3902948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902948).length < 2 ^ (prefixWord ++ tailWord_3902948).sum := by decide
  have hdescent : baseEnd_3902948 < baseStart_3902948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902954 : List Nat := [3, 1, 3, 1, 4, 1, 2, 3, 4]
def baseStart_3902954 : Nat := 118140960795 + 3902954 * 2 ^ 59
def prefixEnd_3902954 : Nat := 4983230072969 + 3 ^ 40 * 3902954 * 2
def baseEnd_3902954 : Nat := 445353638752939535161255

theorem tailTrace_3902954 : CollatzResearch.WordTrace tailWord_3902954 prefixEnd_3902954 445353638752939535161255 := by
  unfold tailWord_3902954
  simp only [CollatzResearch.WordTrace]
  refine ⟨35588106775567926079960979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94901618068181136213229277 35588106775567926079960979)
  ·
    refine ⟨53382160163351889119941469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35588106775567926079960979 53382160163351889119941469)
    ·
      refine ⟨20018310061256958419978051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53382160163351889119941469 20018310061256958419978051)
      ·
        refine ⟨30027465091885437629967077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20018310061256958419978051 30027465091885437629967077)
        ·
          refine ⟨5630149704728519555618827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30027465091885437629967077 5630149704728519555618827)
          ·
            refine ⟨8445224557092779333428241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5630149704728519555618827 8445224557092779333428241)
            ·
              refine ⟨6333918417819584500071181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8445224557092779333428241 6333918417819584500071181)
              ·
                refine ⟨2375219406682344187526693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6333918417819584500071181 2375219406682344187526693)
                ·
                  refine ⟨445353638752939535161255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2375219406682344187526693 445353638752939535161255)
                  ·
                    rfl

theorem cell22_3902954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_3902954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902954 prefixEnd_3902954 := by exact prefixLift 3902954
  have htrace : WordTrace (prefixWord ++ tailWord_3902954) baseStart_3902954 baseEnd_3902954 := by
    simpa [prefixWord, tailWord_3902954, baseEnd_3902954] using wordTrace_append hprefix tailTrace_3902954
  have hstable : (prefixWord ++ tailWord_3902954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902954).length < 2 ^ (prefixWord ++ tailWord_3902954).sum := by decide
  have hdescent : baseEnd_3902954 < baseStart_3902954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902997 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 3, 3]
def baseStart_3902997 : Nat := 118140960795 + 3902997 * 2 ^ 59
def prefixEnd_3902997 : Nat := 4983230072969 + 3 ^ 40 * 3902997 * 2
def baseEnd_3902997 : Nat := 1336075636037580826658633

theorem tailTrace_3902997 : CollatzResearch.WordTrace tailWord_3902997 prefixEnd_3902997 1336075636037580826658633 := by
  unfold tailWord_3902997
  simp only [CollatzResearch.WordTrace]
  refine ⟨142353995441115922663659245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94902663627410615109106163 142353995441115922663659245)
  ·
    refine ⟨53382748290418470998872217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142353995441115922663659245 53382748290418470998872217)
    ·
      refine ⟨40037061217813853249154163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53382748290418470998872217 40037061217813853249154163)
      ·
        refine ⟨60055591826720779873731245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40037061217813853249154163 60055591826720779873731245)
        ·
          refine ⟨22520846935020292452649217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60055591826720779873731245 22520846935020292452649217)
          ·
            refine ⟨16890635201265219339486913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22520846935020292452649217 16890635201265219339486913)
            ·
              refine ⟨12667976400948914504615185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16890635201265219339486913 12667976400948914504615185)
              ·
                refine ⟨9500982300711685878461389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12667976400948914504615185 9500982300711685878461389)
                ·
                  refine ⟨3562868362766882204423021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9500982300711685878461389 3562868362766882204423021)
                  ·
                    refine ⟨1336075636037580826658633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3562868362766882204423021 1336075636037580826658633)
                    ·
                      rfl

theorem cell22_3902997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_3902997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3902997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3902997 prefixEnd_3902997 := by exact prefixLift 3902997
  have htrace : WordTrace (prefixWord ++ tailWord_3902997) baseStart_3902997 baseEnd_3902997 := by
    simpa [prefixWord, tailWord_3902997, baseEnd_3902997] using wordTrace_append hprefix tailTrace_3902997
  have hstable : (prefixWord ++ tailWord_3902997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902997).length < 2 ^ (prefixWord ++ tailWord_3902997).sum := by decide
  have hdescent : baseEnd_3902997 < baseStart_3902997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903010 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 7]
def baseStart_3903010 : Nat := 118140960795 + 3903010 * 2 ^ 59
def prefixEnd_3903010 : Nat := 4983230072969 + 3 ^ 40 * 3903010 * 2
def baseEnd_3903010 : Nat := 445360028734417708694531

theorem tailTrace_3903010 : CollatzResearch.WordTrace tailWord_3903010 prefixEnd_3903010 445360028734417708694531 := by
  unfold tailWord_3903010
  simp only [CollatzResearch.WordTrace]
  refine ⟨35588617397517206470970621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94902979726712550589254989 35588617397517206470970621)
  ·
    refine ⟨13345731524068952426613983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35588617397517206470970621 13345731524068952426613983)
    ·
      refine ⟨20018597286103428639920975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13345731524068952426613983 20018597286103428639920975)
      ·
        refine ⟨30027895929155142959881463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20018597286103428639920975 30027895929155142959881463)
        ·
          refine ⟨45041843893732714439822195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30027895929155142959881463 45041843893732714439822195)
          ·
            refine ⟨67562765840599071659733293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45041843893732714439822195 67562765840599071659733293)
            ·
              refine ⟨25336037190224651872399985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67562765840599071659733293 25336037190224651872399985)
              ·
                refine ⟨19002027892668488904299989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25336037190224651872399985 19002027892668488904299989)
                ·
                  refine ⟨445360028734417708694531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19002027892668488904299989 445360028734417708694531)
                  ·
                    rfl

theorem cell22_3903010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_3903010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903010 prefixEnd_3903010 := by exact prefixLift 3903010
  have htrace : WordTrace (prefixWord ++ tailWord_3903010) baseStart_3903010 baseEnd_3903010 := by
    simpa [prefixWord, tailWord_3903010, baseEnd_3903010] using wordTrace_append hprefix tailTrace_3903010
  have hstable : (prefixWord ++ tailWord_3903010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903010).length < 2 ^ (prefixWord ++ tailWord_3903010).sum := by decide
  have hdescent : baseEnd_3903010 < baseStart_3903010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903031 : List Nat := [1, 1, 3, 1, 2, 5, 3, 2, 1, 3]
def baseStart_3903031 : Nat := 118140960795 + 3903031 * 2 ^ 59
def prefixEnd_3903031 : Nat := 4983230072969 + 3 ^ 40 * 3903031 * 2
def baseEnd_3903031 : Nat := 1336087274932416071308529

theorem tailTrace_3903031 : CollatzResearch.WordTrace tailWord_3903031 prefixEnd_3903031 1336087274932416071308529 := by
  unfold tailWord_3903031
  simp only [CollatzResearch.WordTrace]
  refine ⟨142355235522992746470396947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94903490348661830980264631 142355235522992746470396947)
  ·
    refine ⟨213532853284489119705595421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142355235522992746470396947 213532853284489119705595421)
    ·
      refine ⟨80074819981683419889598283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213532853284489119705595421 80074819981683419889598283)
      ·
        refine ⟨120112229972525129834397425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80074819981683419889598283 120112229972525129834397425)
        ·
          refine ⟨90084172479393847375798069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120112229972525129834397425 90084172479393847375798069)
          ·
            refine ⟨8445391169943173191481069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90084172479393847375798069 8445391169943173191481069)
            ·
              refine ⟨3167021688728689946805401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8445391169943173191481069 3167021688728689946805401)
              ·
                refine ⟨2375266266546517460104051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3167021688728689946805401 2375266266546517460104051)
                ·
                  refine ⟨3562899399819776190156077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375266266546517460104051 3562899399819776190156077)
                  ·
                    refine ⟨1336087274932416071308529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3562899399819776190156077 1336087274932416071308529)
                    ·
                      rfl

theorem cell22_3903031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_3903031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903031 prefixEnd_3903031 := by exact prefixLift 3903031
  have htrace : WordTrace (prefixWord ++ tailWord_3903031) baseStart_3903031 baseEnd_3903031 := by
    simpa [prefixWord, tailWord_3903031, baseEnd_3903031] using wordTrace_append hprefix tailTrace_3903031
  have hstable : (prefixWord ++ tailWord_3903031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903031).length < 2 ^ (prefixWord ++ tailWord_3903031).sum := by decide
  have hdescent : baseEnd_3903031 < baseStart_3903031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903040 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 3, 4]
def baseStart_3903040 : Nat := 118140960795 + 3903040 * 2 ^ 59
def prefixEnd_3903040 : Nat := 4983230072969 + 3 ^ 40 * 3903040 * 2
def baseEnd_3903040 : Nat := 1336090355816343047833501

theorem tailTrace_3903040 : CollatzResearch.WordTrace tailWord_3903040 prefixEnd_3903040 1336090355816343047833501 := by
  unfold tailWord_3903040
  simp only [CollatzResearch.WordTrace]
  refine ⟨71177781889980070503737287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94903709186640094004983049 71177781889980070503737287)
  ·
    refine ⟨106766672834970105755605931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71177781889980070503737287 106766672834970105755605931)
    ·
      refine ⟨160150009252455158633408897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106766672834970105755605931 160150009252455158633408897)
      ·
        refine ⟨120112506939341368975056673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160150009252455158633408897 120112506939341368975056673)
        ·
          refine ⟨90084380204506026731292505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120112506939341368975056673 90084380204506026731292505)
          ·
            refine ⟨67563285153379520048469379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90084380204506026731292505 67563285153379520048469379)
            ·
              refine ⟨101344927730069280072704069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67563285153379520048469379 101344927730069280072704069)
              ·
                refine ⟨19002173949387990013632013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101344927730069280072704069 19002173949387990013632013)
                ·
                  refine ⟨7125815231020496255112005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19002173949387990013632013 7125815231020496255112005)
                  ·
                    refine ⟨1336090355816343047833501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7125815231020496255112005 1336090355816343047833501)
                    ·
                      rfl

theorem cell22_3903040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_3903040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903040 prefixEnd_3903040 := by exact prefixLift 3903040
  have htrace : WordTrace (prefixWord ++ tailWord_3903040) baseStart_3903040 baseEnd_3903040 := by
    simpa [prefixWord, tailWord_3903040, baseEnd_3903040] using wordTrace_append hprefix tailTrace_3903040
  have hstable : (prefixWord ++ tailWord_3903040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903040).length < 2 ^ (prefixWord ++ tailWord_3903040).sum := by decide
  have hdescent : baseEnd_3903040 < baseStart_3903040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903072 : List Nat := [2, 1, 1, 3, 2, 1, 1, 7, 4]
def baseStart_3903072 : Nat := 118140960795 + 3903072 * 2 ^ 59
def prefixEnd_3903072 : Nat := 4983230072969 + 3 ^ 40 * 3903072 * 2
def baseEnd_3903072 : Nat := 445367103356768543677801

theorem tailTrace_3903072 : CollatzResearch.WordTrace tailWord_3903072 prefixEnd_3903072 445367103356768543677801 := by
  unfold tailWord_3903072
  simp only [CollatzResearch.WordTrace]
  refine ⟨71178365457922105236319735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94904487277229473648426313 71178365457922105236319735)
  ·
    refine ⟨106767548186883157854479603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71178365457922105236319735 106767548186883157854479603)
    ·
      refine ⟨160151322280324736781719405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106767548186883157854479603 160151322280324736781719405)
      ·
        refine ⟨60056745855121776293144777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160151322280324736781719405 60056745855121776293144777)
        ·
          refine ⟨45042559391341332219858583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60056745855121776293144777 45042559391341332219858583)
          ·
            refine ⟨67563839087011998329787875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45042559391341332219858583 67563839087011998329787875)
            ·
              refine ⟨101345758630517997494681813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67563839087011998329787875 101345758630517997494681813)
              ·
                refine ⟨2375291217902765566281605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101345758630517997494681813 2375291217902765566281605)
                ·
                  refine ⟨445367103356768543677801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2375291217902765566281605 445367103356768543677801)
                  ·
                    rfl

theorem cell22_3903072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 4].length) (baseStart_3903072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903072 prefixEnd_3903072 := by exact prefixLift 3903072
  have htrace : WordTrace (prefixWord ++ tailWord_3903072) baseStart_3903072 baseEnd_3903072 := by
    simpa [prefixWord, tailWord_3903072, baseEnd_3903072] using wordTrace_append hprefix tailTrace_3903072
  have hstable : (prefixWord ++ tailWord_3903072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903072).length < 2 ^ (prefixWord ++ tailWord_3903072).sum := by decide
  have hdescent : baseEnd_3903072 < baseStart_3903072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903258 : List Nat := [3, 1, 1, 3, 2, 4, 2, 2, 4]
def baseStart_3903258 : Nat := 118140960795 + 3903258 * 2 ^ 59
def prefixEnd_3903258 : Nat := 4983230072969 + 3 ^ 40 * 3903258 * 2
def baseEnd_3903258 : Nat := 445388327223821048627611

theorem tailTrace_3903258 : CollatzResearch.WordTrace tailWord_3903258 prefixEnd_3903258 445388327223821048627611 := by
  unfold tailWord_3903258
  simp only [CollatzResearch.WordTrace]
  refine ⟨35590878723292591059727607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94909009928780242825940285 35590878723292591059727607)
  ·
    refine ⟨53386318084938886589591411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35590878723292591059727607 53386318084938886589591411)
    ·
      refine ⟨80079477127408329884387117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53386318084938886589591411 80079477127408329884387117)
      ·
        refine ⟨30029803922778123706645169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80079477127408329884387117 30029803922778123706645169)
        ·
          refine ⟨22522352942083592779983877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30029803922778123706645169 22522352942083592779983877)
          ·
            refine ⟨4222941176640673646246977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22522352942083592779983877 4222941176640673646246977)
            ·
              refine ⟨3167205882480505234685233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4222941176640673646246977 3167205882480505234685233)
              ·
                refine ⟨2375404411860378926013925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3167205882480505234685233 2375404411860378926013925)
                ·
                  refine ⟨445388327223821048627611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2375404411860378926013925 445388327223821048627611)
                  ·
                    rfl

theorem cell22_3903258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_3903258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903258 prefixEnd_3903258 := by exact prefixLift 3903258
  have htrace : WordTrace (prefixWord ++ tailWord_3903258) baseStart_3903258 baseEnd_3903258 := by
    simpa [prefixWord, tailWord_3903258, baseEnd_3903258] using wordTrace_append hprefix tailTrace_3903258
  have hstable : (prefixWord ++ tailWord_3903258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903258).length < 2 ^ (prefixWord ++ tailWord_3903258).sum := by decide
  have hdescent : baseEnd_3903258 < baseStart_3903258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903269 : List Nat := [1, 3, 1, 2, 3, 4, 1, 7]
def baseStart_3903269 : Nat := 118140960795 + 3903269 * 2 ^ 59
def prefixEnd_3903269 : Nat := 4983230072969 + 3 ^ 40 * 3903269 * 2
def baseEnd_3903269 : Nat := 148463194132918087095311

theorem tailTrace_3903269 : CollatzResearch.WordTrace tailWord_3903269 prefixEnd_3903269 148463194132918087095311 := by
  unfold tailWord_3903269
  simp only [CollatzResearch.WordTrace]
  refine ⟨142363916096130513117560861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94909277397420342078373907 142363916096130513117560861)
  ·
    refine ⟨53386468536048942419085323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142363916096130513117560861 53386468536048942419085323)
    ·
      refine ⟨80079702804073413628627985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53386468536048942419085323 80079702804073413628627985)
      ·
        refine ⟨60059777103055060221470989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80079702804073413628627985 60059777103055060221470989)
        ·
          refine ⟨22522416413645647583051621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60059777103055060221470989 22522416413645647583051621)
          ·
            refine ⟨4222953077558558921822179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22522416413645647583051621 4222953077558558921822179)
            ·
              refine ⟨6334429616337838382733269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4222953077558558921822179 6334429616337838382733269)
              ·
                refine ⟨148463194132918087095311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6334429616337838382733269 148463194132918087095311)
                ·
                  rfl

theorem cell22_3903269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 7].length) (baseStart_3903269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903269 prefixEnd_3903269 := by exact prefixLift 3903269
  have htrace : WordTrace (prefixWord ++ tailWord_3903269) baseStart_3903269 baseEnd_3903269 := by
    simpa [prefixWord, tailWord_3903269, baseEnd_3903269] using wordTrace_append hprefix tailTrace_3903269
  have hstable : (prefixWord ++ tailWord_3903269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903269).length < 2 ^ (prefixWord ++ tailWord_3903269).sum := by decide
  have hdescent : baseEnd_3903269 < baseStart_3903269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903314 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 7]
def baseStart_3903314 : Nat := 118140960795 + 3903314 * 2 ^ 59
def prefixEnd_3903314 : Nat := 4983230072969 + 3 ^ 40 * 3903314 * 2
def baseEnd_3903314 : Nat := 445394717205299222160887

theorem tailTrace_3903314 : CollatzResearch.WordTrace tailWord_3903314 prefixEnd_3903314 445394717205299222160887 := by
  unfold tailWord_3903314
  simp only [CollatzResearch.WordTrace]
  refine ⟨35591389345241871450737249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94910371587311657201965997 35591389345241871450737249)
  ·
    refine ⟨26693542008931403588052937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35591389345241871450737249 26693542008931403588052937)
    ·
      refine ⟨20020156506698552691039703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26693542008931403588052937 20020156506698552691039703)
      ·
        refine ⟨30030234760047829036559555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20020156506698552691039703 30030234760047829036559555)
        ·
          refine ⟨45045352140071743554839333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30030234760047829036559555 45045352140071743554839333)
          ·
            refine ⟨8446003526263451916532375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45045352140071743554839333 8446003526263451916532375)
            ·
              refine ⟨12669005289395177874798563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8446003526263451916532375 12669005289395177874798563)
              ·
                refine ⟨19003507934092766812197845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12669005289395177874798563 19003507934092766812197845)
                ·
                  refine ⟨445394717205299222160887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19003507934092766812197845 445394717205299222160887)
                  ·
                    rfl

theorem cell22_3903314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_3903314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903314 prefixEnd_3903314 := by exact prefixLift 3903314
  have htrace : WordTrace (prefixWord ++ tailWord_3903314) baseStart_3903314 baseEnd_3903314 := by
    simpa [prefixWord, tailWord_3903314, baseEnd_3903314] using wordTrace_append hprefix tailTrace_3903314
  have hstable : (prefixWord ++ tailWord_3903314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903314).length < 2 ^ (prefixWord ++ tailWord_3903314).sum := by decide
  have hdescent : baseEnd_3903314 < baseStart_3903314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903412 : List Nat := [2, 5, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3903412 : Nat := 118140960795 + 3903412 * 2 ^ 59
def prefixEnd_3903412 : Nat := 4983230072969 + 3 ^ 40 * 3903412 * 2
def baseEnd_3903412 : Nat := 1336217699018658077532361

theorem tailTrace_3903412 : CollatzResearch.WordTrace tailWord_3903412 prefixEnd_3903412 1336217699018658077532361 := by
  unfold tailWord_3903412
  simp only [CollatzResearch.WordTrace]
  refine ⟨71184565867306224270008245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94912754489741632360010993 71184565867306224270008245)
  ·
    refine ⟨6673553050059958525313273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71184565867306224270008245 6673553050059958525313273)
    ·
      refine ⟨5005164787544968893984955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6673553050059958525313273 5005164787544968893984955)
      ·
        refine ⟨7507747181317453340977433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5005164787544968893984955 7507747181317453340977433)
        ·
          refine ⟨5630810385988090005733075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7507747181317453340977433 5630810385988090005733075)
          ·
            refine ⟨8446215578982135008599613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5630810385988090005733075 8446215578982135008599613)
            ·
              refine ⟨3167330842118300628224855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8446215578982135008599613 3167330842118300628224855)
              ·
                refine ⟨4750996263177450942337283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3167330842118300628224855 4750996263177450942337283)
                ·
                  refine ⟨7126494394766176413505925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4750996263177450942337283 7126494394766176413505925)
                  ·
                    refine ⟨1336217699018658077532361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7126494394766176413505925 1336217699018658077532361)
                    ·
                      rfl

theorem cell22_3903412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3903412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903412 prefixEnd_3903412 := by exact prefixLift 3903412
  have htrace : WordTrace (prefixWord ++ tailWord_3903412) baseStart_3903412 baseEnd_3903412 := by
    simpa [prefixWord, tailWord_3903412, baseEnd_3903412] using wordTrace_append hprefix tailTrace_3903412
  have hstable : (prefixWord ++ tailWord_3903412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903412).length < 2 ^ (prefixWord ++ tailWord_3903412).sum := by decide
  have hdescent : baseEnd_3903412 < baseStart_3903412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903434 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_3903434 : Nat := 118140960795 + 3903434 * 2 ^ 59
def prefixEnd_3903434 : Nat := 4983230072969 + 3 ^ 40 * 3903434 * 2
def baseEnd_3903434 : Nat := 1336225230068257353482293

theorem tailTrace_3903434 : CollatzResearch.WordTrace tailWord_3903434 prefixEnd_3903434 1336225230068257353482293 := by
  unfold tailWord_3903434
  simp only [CollatzResearch.WordTrace]
  refine ⟨35592483535133186574329339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94913289427021830864878237 35592483535133186574329339)
  ·
    refine ⟨53388725302699779861494009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35592483535133186574329339 53388725302699779861494009)
    ·
      refine ⟨40041543977024834896120507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53388725302699779861494009 40041543977024834896120507)
      ·
        refine ⟨60062315965537252344180761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40041543977024834896120507 60062315965537252344180761)
        ·
          refine ⟨45046736974152939258135571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60062315965537252344180761 45046736974152939258135571)
          ·
            refine ⟨67570105461229408887203357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45046736974152939258135571 67570105461229408887203357)
            ·
              refine ⟨25338789547961028332701259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67570105461229408887203357 25338789547961028332701259)
              ·
                refine ⟨38008184321941542499051889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25338789547961028332701259 38008184321941542499051889)
                ·
                  refine ⟨28506138241456156874288917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38008184321941542499051889 28506138241456156874288917)
                  ·
                    refine ⟨1336225230068257353482293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28506138241456156874288917 1336225230068257353482293)
                    ·
                      rfl

theorem cell22_3903434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_3903434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903434 prefixEnd_3903434 := by exact prefixLift 3903434
  have htrace : WordTrace (prefixWord ++ tailWord_3903434) baseStart_3903434 baseEnd_3903434 := by
    simpa [prefixWord, tailWord_3903434, baseEnd_3903434] using wordTrace_append hprefix tailTrace_3903434
  have hstable : (prefixWord ++ tailWord_3903434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903434).length < 2 ^ (prefixWord ++ tailWord_3903434).sum := by decide
  have hdescent : baseEnd_3903434 < baseStart_3903434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903464 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 3, 7]
def baseStart_3903464 : Nat := 118140960795 + 3903464 * 2 ^ 59
def prefixEnd_3903464 : Nat := 4983230072969 + 3 ^ 40 * 3903464 * 2
def baseEnd_3903464 : Nat := 1336235499681347275232201

theorem tailTrace_3903464 : CollatzResearch.WordTrace tailWord_3903464 prefixEnd_3903464 1336235499681347275232201 := by
  unfold tailWord_3903464
  simp only [CollatzResearch.WordTrace]
  refine ⟨71185514165212030710454723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94914018886949374280606297 71185514165212030710454723)
  ·
    refine ⟨106778271247818046065682085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71185514165212030710454723 106778271247818046065682085)
    ·
      refine ⟨20020925858965883637315391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106778271247818046065682085 20020925858965883637315391)
      ·
        refine ⟨30031388788448825455973087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20020925858965883637315391 30031388788448825455973087)
        ·
          refine ⟨45047083182673238183959631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30031388788448825455973087 45047083182673238183959631)
          ·
            refine ⟨67570624774009857275939447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45047083182673238183959631 67570624774009857275939447)
            ·
              refine ⟨101355937161014785913909171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67570624774009857275939447 101355937161014785913909171)
              ·
                refine ⟨152033905741522178870863757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101355937161014785913909171 152033905741522178870863757)
                ·
                  refine ⟨57012714653070817076573909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152033905741522178870863757 57012714653070817076573909)
                  ·
                    refine ⟨1336235499681347275232201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57012714653070817076573909 1336235499681347275232201)
                    ·
                      rfl

theorem cell22_3903464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_3903464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903464 prefixEnd_3903464 := by exact prefixLift 3903464
  have htrace : WordTrace (prefixWord ++ tailWord_3903464) baseStart_3903464 baseEnd_3903464 := by
    simpa [prefixWord, tailWord_3903464, baseEnd_3903464] using wordTrace_append hprefix tailTrace_3903464
  have hstable : (prefixWord ++ tailWord_3903464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903464).length < 2 ^ (prefixWord ++ tailWord_3903464).sum := by decide
  have hdescent : baseEnd_3903464 < baseStart_3903464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903470 : List Nat := [4, 1, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_3903470 : Nat := 118140960795 + 3903470 * 2 ^ 59
def prefixEnd_3903470 : Nat := 4983230072969 + 3 ^ 40 * 3903470 * 2
def baseEnd_3903470 : Nat := 1336237553603965259582183

theorem tailTrace_3903470 : CollatzResearch.WordTrace tailWord_3903470 prefixEnd_3903470 1336237553603965259582183 := by
  unfold tailWord_3903470
  simp only [CollatzResearch.WordTrace]
  refine ⟨17796405896050290555703483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94914164778934882963751909 17796405896050290555703483)
  ·
    refine ⟨26694608844075435833555225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17796405896050290555703483 26694608844075435833555225)
    ·
      refine ⟨20020956633056576875166419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26694608844075435833555225 20020956633056576875166419)
      ·
        refine ⟨30031434949584865312749629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20020956633056576875166419 30031434949584865312749629)
        ·
          refine ⟨11261788106094324492281111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30031434949584865312749629 11261788106094324492281111)
          ·
            refine ⟨16892682159141486738421667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11261788106094324492281111 16892682159141486738421667)
            ·
              refine ⟨25339023238712230107632501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16892682159141486738421667 25339023238712230107632501)
              ·
                refine ⟨2375533428629271572590547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25339023238712230107632501 2375533428629271572590547)
                ·
                  refine ⟨3563300142943907358885821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375533428629271572590547 3563300142943907358885821)
                  ·
                    refine ⟨1336237553603965259582183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3563300142943907358885821 1336237553603965259582183)
                    ·
                      rfl

theorem cell22_3903470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_3903470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903470 prefixEnd_3903470 := by exact prefixLift 3903470
  have htrace : WordTrace (prefixWord ++ tailWord_3903470) baseStart_3903470 baseEnd_3903470 := by
    simpa [prefixWord, tailWord_3903470, baseEnd_3903470] using wordTrace_append hprefix tailTrace_3903470
  have hstable : (prefixWord ++ tailWord_3903470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903470).length < 2 ^ (prefixWord ++ tailWord_3903470).sum := by decide
  have hdescent : baseEnd_3903470 < baseStart_3903470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903539 : List Nat := [1, 1, 1, 2, 4, 1, 12]
def baseStart_3903539 : Nat := 118140960795 + 3903539 * 2 ^ 59
def prefixEnd_3903539 : Nat := 4983230072969 + 3 ^ 40 * 3903539 * 2
def baseEnd_3903539 : Nat := 49491154582002669615073

theorem tailTrace_3903539 : CollatzResearch.WordTrace tailWord_3903539 prefixEnd_3903539 49491154582002669615073 := by
  unfold tailWord_3903539
  simp only [CollatzResearch.WordTrace]
  refine ⟨142373763805152349229889671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94915842536768232819926447 142373763805152349229889671)
  ·
    refine ⟨213560645707728523844834507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142373763805152349229889671 213560645707728523844834507)
    ·
      refine ⟨320340968561592785767251761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213560645707728523844834507 320340968561592785767251761)
      ·
        refine ⟨240255726421194589325438821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320340968561592785767251761 240255726421194589325438821)
        ·
          refine ⟨45047948703973985498519779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240255726421194589325438821 45047948703973985498519779)
          ·
            refine ⟨67571923055960978247779669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45047948703973985498519779 67571923055960978247779669)
            ·
              refine ⟨49491154582002669615073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 67571923055960978247779669 49491154582002669615073)
              ·
                rfl

theorem cell22_3903539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 12].length) (baseStart_3903539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903539 prefixEnd_3903539 := by exact prefixLift 3903539
  have htrace : WordTrace (prefixWord ++ tailWord_3903539) baseStart_3903539 baseEnd_3903539 := by
    simpa [prefixWord, tailWord_3903539, baseEnd_3903539] using wordTrace_append hprefix tailTrace_3903539
  have hstable : (prefixWord ++ tailWord_3903539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903539).length < 2 ^ (prefixWord ++ tailWord_3903539).sum := by decide
  have hdescent : baseEnd_3903539 < baseStart_3903539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903541 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3903541 : Nat := 118140960795 + 3903541 * 2 ^ 59
def prefixEnd_3903541 : Nat := 4983230072969 + 3 ^ 40 * 3903541 * 2
def baseEnd_3903541 : Nat := 1336261858354944741056965

theorem tailTrace_3903541 : CollatzResearch.WordTrace tailWord_3903541 prefixEnd_3903541 1336261858354944741056965 := by
  unfold tailWord_3903541
  simp only [CollatzResearch.WordTrace]
  refine ⟨142373836751145103571462477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94915891167430069047641651 142373836751145103571462477)
  ·
    refine ⟨53390188781679413839298429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142373836751145103571462477 53390188781679413839298429)
    ·
      refine ⟨20021320793129780189736911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53390188781679413839298429 20021320793129780189736911)
      ·
        refine ⟨30031981189694670284605367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20021320793129780189736911 30031981189694670284605367)
        ·
          refine ⟨45047971784542005426908051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30031981189694670284605367 45047971784542005426908051)
          ·
            refine ⟨67571957676813008140362077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45047971784542005426908051 67571957676813008140362077)
            ·
              refine ⟨25339484128804878052635779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67571957676813008140362077 25339484128804878052635779)
              ·
                refine ⟨38009226193207317078953669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25339484128804878052635779 38009226193207317078953669)
                ·
                  refine ⟨7126729911226371952303813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38009226193207317078953669 7126729911226371952303813)
                  ·
                    refine ⟨1336261858354944741056965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7126729911226371952303813 1336261858354944741056965)
                    ·
                      rfl

theorem cell22_3903541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3903541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903541 prefixEnd_3903541 := by exact prefixLift 3903541
  have htrace : WordTrace (prefixWord ++ tailWord_3903541) baseStart_3903541 baseEnd_3903541 := by
    simpa [prefixWord, tailWord_3903541, baseEnd_3903541] using wordTrace_append hprefix tailTrace_3903541
  have hstable : (prefixWord ++ tailWord_3903541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903541).length < 2 ^ (prefixWord ++ tailWord_3903541).sum := by decide
  have hdescent : baseEnd_3903541 < baseStart_3903541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903545 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 6]
def baseStart_3903545 : Nat := 118140960795 + 3903545 * 2 ^ 59
def prefixEnd_3903545 : Nat := 4983230072969 + 3 ^ 40 * 3903545 * 2
def baseEnd_3903545 : Nat := 445421075878896687985651

theorem tailTrace_3903545 : CollatzResearch.WordTrace tailWord_3903545 prefixEnd_3903545 445421075878896687985651 := by
  unfold tailWord_3903545
  simp only [CollatzResearch.WordTrace]
  refine ⟨142373982643130612254608089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94915988428753741503072059 142373982643130612254608089)
  ·
    refine ⟨106780486982347959190956067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142373982643130612254608089 106780486982347959190956067)
    ·
      refine ⟨160170730473521938786434101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106780486982347959190956067 160170730473521938786434101)
      ·
        refine ⟨15016005981892681761228197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160170730473521938786434101 15016005981892681761228197)
        ·
          refine ⟨2815501121604877830230287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15016005981892681761228197 2815501121604877830230287)
          ·
            refine ⟨4223251682407316745345431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815501121604877830230287 4223251682407316745345431)
            ·
              refine ⟨6334877523610975118018147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223251682407316745345431 6334877523610975118018147)
              ·
                refine ⟨9502316285416462677027221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6334877523610975118018147 9502316285416462677027221)
                ·
                  refine ⟨445421075878896687985651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9502316285416462677027221 445421075878896687985651)
                  ·
                    rfl

theorem cell22_3903545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 6].length) (baseStart_3903545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903545 prefixEnd_3903545 := by exact prefixLift 3903545
  have htrace : WordTrace (prefixWord ++ tailWord_3903545) baseStart_3903545 baseEnd_3903545 := by
    simpa [prefixWord, tailWord_3903545, baseEnd_3903545] using wordTrace_append hprefix tailTrace_3903545
  have hstable : (prefixWord ++ tailWord_3903545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903545).length < 2 ^ (prefixWord ++ tailWord_3903545).sum := by decide
  have hdescent : baseEnd_3903545 < baseStart_3903545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903652 : List Nat := [2, 3, 1, 2, 5, 1, 1, 2, 5]
def baseStart_3903652 : Nat := 118140960795 + 3903652 * 2 ^ 59
def prefixEnd_3903652 : Nat := 4983230072969 + 3 ^ 40 * 3903652 * 2
def baseEnd_3903652 : Nat := 445433285307792483843875

theorem tailTrace_3903652 : CollatzResearch.WordTrace tailWord_3903652 prefixEnd_3903652 445433285307792483843875 := by
  unfold tailWord_3903652
  simp only [CollatzResearch.WordTrace]
  refine ⟨71188942626871484764376605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94918590169161979685835473 71188942626871484764376605)
  ·
    refine ⟨26695853485076806786641227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71188942626871484764376605 26695853485076806786641227)
    ·
      refine ⟨40043780227615210179961841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26695853485076806786641227 40043780227615210179961841)
      ·
        refine ⟨30032835170711407634971381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40043780227615210179961841 30032835170711407634971381)
        ·
          refine ⟨2815578297254194465778567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30032835170711407634971381 2815578297254194465778567)
          ·
            refine ⟨4223367445881291698667851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815578297254194465778567 4223367445881291698667851)
            ·
              refine ⟨6335051168821937548001777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223367445881291698667851 6335051168821937548001777)
              ·
                refine ⟨4751288376616453161001333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6335051168821937548001777 4751288376616453161001333)
                ·
                  refine ⟨445433285307792483843875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4751288376616453161001333 445433285307792483843875)
                  ·
                    rfl

theorem cell22_3903652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_3903652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903652 prefixEnd_3903652 := by exact prefixLift 3903652
  have htrace : WordTrace (prefixWord ++ tailWord_3903652) baseStart_3903652 baseEnd_3903652 := by
    simpa [prefixWord, tailWord_3903652, baseEnd_3903652] using wordTrace_append hprefix tailTrace_3903652
  have hstable : (prefixWord ++ tailWord_3903652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903652).length < 2 ^ (prefixWord ++ tailWord_3903652).sum := by decide
  have hdescent : baseEnd_3903652 < baseStart_3903652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903691 : List Nat := [1, 1, 1, 1, 3, 2, 5, 8]
def baseStart_3903691 : Nat := 118140960795 + 3903691 * 2 ^ 59
def prefixEnd_3903691 : Nat := 4983230072969 + 3 ^ 40 * 3903691 * 2
def baseEnd_3903691 : Nat := 148479245157821594422945

theorem tailTrace_3903691 : CollatzResearch.WordTrace tailWord_3903691 prefixEnd_3903691 148479245157821594422945 := by
  unfold tailWord_3903691
  simp only [CollatzResearch.WordTrace]
  refine ⟨142379307700601679189422927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94919538467067786126281951 142379307700601679189422927)
  ·
    refine ⟨213568961550902518784134391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142379307700601679189422927 213568961550902518784134391)
    ·
      refine ⟨320353442326353778176201587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213568961550902518784134391 320353442326353778176201587)
      ·
        refine ⟨480530163489530667264302381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320353442326353778176201587 480530163489530667264302381)
        ·
          refine ⟨180198811308574000224113393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480530163489530667264302381 180198811308574000224113393)
          ·
            refine ⟨135149108481430500168085045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180198811308574000224113393 135149108481430500168085045)
            ·
              refine ⟨12670228920134109390757973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135149108481430500168085045 12670228920134109390757973)
              ·
                refine ⟨148479245157821594422945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12670228920134109390757973 148479245157821594422945)
                ·
                  rfl

theorem cell22_3903691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 8].length) (baseStart_3903691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903691 prefixEnd_3903691 := by exact prefixLift 3903691
  have htrace : WordTrace (prefixWord ++ tailWord_3903691) baseStart_3903691 baseEnd_3903691 := by
    simpa [prefixWord, tailWord_3903691, baseEnd_3903691] using wordTrace_append hprefix tailTrace_3903691
  have hstable : (prefixWord ++ tailWord_3903691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903691).length < 2 ^ (prefixWord ++ tailWord_3903691).sum := by decide
  have hdescent : baseEnd_3903691 < baseStart_3903691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903721 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 1, 8]
def baseStart_3903721 : Nat := 118140960795 + 3903721 * 2 ^ 59
def prefixEnd_3903721 : Nat := 4983230072969 + 3 ^ 40 * 3903721 * 2
def baseEnd_3903721 : Nat := 1336323476033484271556413

theorem tailTrace_3903721 : CollatzResearch.WordTrace tailWord_3903721 prefixEnd_3903721 1336323476033484271556413 := by
  unfold tailWord_3903721
  simp only [CollatzResearch.WordTrace]
  refine ⟨142380401890492994313015017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94920267926995329542010011 142380401890492994313015017)
  ·
    refine ⟨106785301417869745734761263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142380401890492994313015017 106785301417869745734761263)
    ·
      refine ⟨160177952126804618602141895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106785301417869745734761263 160177952126804618602141895)
      ·
        refine ⟨240266928190206927903212843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160177952126804618602141895 240266928190206927903212843)
        ·
          refine ⟨360400392285310391854819265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240266928190206927903212843 360400392285310391854819265)
          ·
            refine ⟨270300294213982793891114449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360400392285310391854819265 270300294213982793891114449)
            ·
              refine ⟨202725220660487095418335837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270300294213982793891114449 202725220660487095418335837)
              ·
                refine ⟨76021957747682660781875939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202725220660487095418335837 76021957747682660781875939)
                ·
                  refine ⟨114032936621523991172813909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76021957747682660781875939 114032936621523991172813909)
                  ·
                    refine ⟨1336323476033484271556413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114032936621523991172813909 1336323476033484271556413)
                    ·
                      rfl

theorem cell22_3903721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_3903721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903721 prefixEnd_3903721 := by exact prefixLift 3903721
  have htrace : WordTrace (prefixWord ++ tailWord_3903721) baseStart_3903721 baseEnd_3903721 := by
    simpa [prefixWord, tailWord_3903721, baseEnd_3903721] using wordTrace_append hprefix tailTrace_3903721
  have hstable : (prefixWord ++ tailWord_3903721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903721).length < 2 ^ (prefixWord ++ tailWord_3903721).sum := by decide
  have hdescent : baseEnd_3903721 < baseStart_3903721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903725 : List Nat := [1, 5, 1, 2, 3, 1, 2, 7]
def baseStart_3903725 : Nat := 118140960795 + 3903725 * 2 ^ 59
def prefixEnd_3903725 : Nat := 4983230072969 + 3 ^ 40 * 3903725 * 2
def baseEnd_3903725 : Nat := 148480538368358843828489

theorem tailTrace_3903725 : CollatzResearch.WordTrace tailWord_3903725 prefixEnd_3903725 148480538368358843828489 := by
  unfold tailWord_3903725
  simp only [CollatzResearch.WordTrace]
  refine ⟨142380547782478502996160629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94920365188319001997440419 142380547782478502996160629)
  ·
    refine ⟨13348176354607359655890059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142380547782478502996160629 13348176354607359655890059)
    ·
      refine ⟨20022264531911039483835089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13348176354607359655890059 20022264531911039483835089)
      ·
        refine ⟨15016698398933279612876317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20022264531911039483835089 15016698398933279612876317)
        ·
          refine ⟨5631261899599979854828619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15016698398933279612876317 5631261899599979854828619)
          ·
            refine ⟨8446892849399969782242929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631261899599979854828619 8446892849399969782242929)
            ·
              refine ⟨6335169637049977336682197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8446892849399969782242929 6335169637049977336682197)
              ·
                refine ⟨148480538368358843828489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6335169637049977336682197 148480538368358843828489)
                ·
                  rfl

theorem cell22_3903725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 7].length) (baseStart_3903725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903725 prefixEnd_3903725 := by exact prefixLift 3903725
  have htrace : WordTrace (prefixWord ++ tailWord_3903725) baseStart_3903725 baseEnd_3903725 := by
    simpa [prefixWord, tailWord_3903725, baseEnd_3903725] using wordTrace_append hprefix tailTrace_3903725
  have hstable : (prefixWord ++ tailWord_3903725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903725).length < 2 ^ (prefixWord ++ tailWord_3903725).sum := by decide
  have hdescent : baseEnd_3903725 < baseStart_3903725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903768 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 2, 5]
def baseStart_3903768 : Nat := 118140960795 + 3903768 * 2 ^ 59
def prefixEnd_3903768 : Nat := 4983230072969 + 3 ^ 40 * 3903768 * 2
def baseEnd_3903768 : Nat := 1336339565093991815631269

theorem tailTrace_3903768 : CollatzResearch.WordTrace tailWord_3903768 prefixEnd_3903768 1336339565093991815631269 := by
  unfold tailWord_3903768
  simp only [CollatzResearch.WordTrace]
  refine ⟨71191058060661360669987979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94921410747548480893317305 71191058060661360669987979)
  ·
    refine ⟨106786587090992041004981969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71191058060661360669987979 106786587090992041004981969)
    ·
      refine ⟨80089940318244030753736477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106786587090992041004981969 80089940318244030753736477)
      ·
        refine ⟨30033727619341511532651179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80089940318244030753736477 30033727619341511532651179)
        ·
          refine ⟨45050591429012267298976769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30033727619341511532651179 45050591429012267298976769)
          ·
            refine ⟨33787943571759200474232577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45050591429012267298976769 33787943571759200474232577)
            ·
              refine ⟨25340957678819400355674433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33787943571759200474232577 25340957678819400355674433)
              ·
                refine ⟨19005718259114550266755825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25340957678819400355674433 19005718259114550266755825)
                ·
                  refine ⟨14254288694335912700066869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19005718259114550266755825 14254288694335912700066869)
                  ·
                    refine ⟨1336339565093991815631269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14254288694335912700066869 1336339565093991815631269)
                    ·
                      rfl

theorem cell22_3903768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_3903768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903768 prefixEnd_3903768 := by exact prefixLift 3903768
  have htrace : WordTrace (prefixWord ++ tailWord_3903768) baseStart_3903768 baseEnd_3903768 := by
    simpa [prefixWord, tailWord_3903768, baseEnd_3903768] using wordTrace_append hprefix tailTrace_3903768
  have hstable : (prefixWord ++ tailWord_3903768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903768).length < 2 ^ (prefixWord ++ tailWord_3903768).sum := by decide
  have hdescent : baseEnd_3903768 < baseStart_3903768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903843 : List Nat := [1, 1, 1, 5, 2, 1, 2, 9]
def baseStart_3903843 : Nat := 118140960795 + 3903843 * 2 ^ 59
def prefixEnd_3903843 : Nat := 4983230072969 + 3 ^ 40 * 3903843 * 2
def baseEnd_3903843 : Nat := 148485026569635180000671

theorem tailTrace_3903843 : CollatzResearch.WordTrace tailWord_3903843 prefixEnd_3903843 148485026569635180000671 := by
  unfold tailWord_3903843
  simp only [CollatzResearch.WordTrace]
  refine ⟨142384851596051009148956183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94923234397367339432637455 142384851596051009148956183)
  ·
    refine ⟨213577277394076513723434275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142384851596051009148956183 213577277394076513723434275)
    ·
      refine ⟨320365916091114770585151413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213577277394076513723434275 320365916091114770585151413)
      ·
        refine ⟨30034304633542009742357945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320365916091114770585151413 30034304633542009742357945)
        ·
          refine ⟨22525728475156507306768459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30034304633542009742357945 22525728475156507306768459)
          ·
            refine ⟨33788592712734760960152689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22525728475156507306768459 33788592712734760960152689)
            ·
              refine ⟨25341444534551070720114517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33788592712734760960152689 25341444534551070720114517)
              ·
                refine ⟨148485026569635180000671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25341444534551070720114517 148485026569635180000671)
                ·
                  rfl

theorem cell22_3903843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 9].length) (baseStart_3903843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903843 prefixEnd_3903843 := by exact prefixLift 3903843
  have htrace : WordTrace (prefixWord ++ tailWord_3903843) baseStart_3903843 baseEnd_3903843 := by
    simpa [prefixWord, tailWord_3903843, baseEnd_3903843] using wordTrace_append hprefix tailTrace_3903843
  have hstable : (prefixWord ++ tailWord_3903843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903843).length < 2 ^ (prefixWord ++ tailWord_3903843).sum := by decide
  have hdescent : baseEnd_3903843 < baseStart_3903843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903847 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 1, 5]
def baseStart_3903847 : Nat := 118140960795 + 3903847 * 2 ^ 59
def prefixEnd_3903847 : Nat := 4983230072969 + 3 ^ 40 * 3903847 * 2
def baseEnd_3903847 : Nat := 1336366608408461942906027

theorem tailTrace_3903847 : CollatzResearch.WordTrace tailWord_3903847 prefixEnd_3903847 1336366608408461942906027 := by
  unfold tailWord_3903847
  simp only [CollatzResearch.WordTrace]
  refine ⟨142384997488036517832101795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94923331658691011888067863 142384997488036517832101795)
  ·
    refine ⟨213577496232054776748152693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142384997488036517832101795 213577496232054776748152693)
    ·
      refine ⟨20022890271755135320139315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213577496232054776748152693 20022890271755135320139315)
      ·
        refine ⟨30034335407632702980208973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20022890271755135320139315 30034335407632702980208973)
        ·
          refine ⟨11262875777862263617578365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30034335407632702980208973 11262875777862263617578365)
          ·
            refine ⟨4223578416698348856591887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11262875777862263617578365 4223578416698348856591887)
            ·
              refine ⟨6335367625047523284887831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223578416698348856591887 6335367625047523284887831)
              ·
                refine ⟨9503051437571284927331747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6335367625047523284887831 9503051437571284927331747)
                ·
                  refine ⟨14254577156356927390997621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9503051437571284927331747 14254577156356927390997621)
                  ·
                    refine ⟨1336366608408461942906027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14254577156356927390997621 1336366608408461942906027)
                    ·
                      rfl

theorem cell22_3903847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_3903847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903847 prefixEnd_3903847 := by exact prefixLift 3903847
  have htrace : WordTrace (prefixWord ++ tailWord_3903847) baseStart_3903847 baseEnd_3903847 := by
    simpa [prefixWord, tailWord_3903847, baseEnd_3903847] using wordTrace_append hprefix tailTrace_3903847
  have hstable : (prefixWord ++ tailWord_3903847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903847).length < 2 ^ (prefixWord ++ tailWord_3903847).sum := by decide
  have hdescent : baseEnd_3903847 < baseStart_3903847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903950 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_3903950 : Nat := 118140960795 + 3903950 * 2 ^ 59
def prefixEnd_3903950 : Nat := 4983230072969 + 3 ^ 40 * 3903950 * 2
def baseEnd_3903950 : Nat := 445467289137801335860237

theorem tailTrace_3903950 : CollatzResearch.WordTrace tailWord_3903950 prefixEnd_3903950 445467289137801335860237 := by
  unfold tailWord_3903950
  simp only [CollatzResearch.WordTrace]
  refine ⟨17798594275832920802887663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94925836137775577615400869 17798594275832920802887663)
  ·
    refine ⟨26697891413749381204331495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17798594275832920802887663 26697891413749381204331495)
    ·
      refine ⟨40046837120624071806497243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26697891413749381204331495 40046837120624071806497243)
      ·
        refine ⟨60070255680936107709745865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40046837120624071806497243 60070255680936107709745865)
        ·
          refine ⟨45052691760702080782309399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60070255680936107709745865 45052691760702080782309399)
          ·
            refine ⟨67579037641053121173464099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45052691760702080782309399 67579037641053121173464099)
            ·
              refine ⟨101368556461579681760196149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67579037641053121173464099 101368556461579681760196149)
              ·
                refine ⟨9503302168273095165018389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101368556461579681760196149 9503302168273095165018389)
                ·
                  refine ⟨445467289137801335860237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9503302168273095165018389 445467289137801335860237)
                  ·
                    rfl

theorem cell22_3903950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_3903950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903950 prefixEnd_3903950 := by exact prefixLift 3903950
  have htrace : WordTrace (prefixWord ++ tailWord_3903950) baseStart_3903950 baseEnd_3903950 := by
    simpa [prefixWord, tailWord_3903950, baseEnd_3903950] using wordTrace_append hprefix tailTrace_3903950
  have hstable : (prefixWord ++ tailWord_3903950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903950).length < 2 ^ (prefixWord ++ tailWord_3903950).sum := by decide
  have hdescent : baseEnd_3903950 < baseStart_3903950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903954 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_3903954 : Nat := 118140960795 + 3903954 * 2 ^ 59
def prefixEnd_3903954 : Nat := 4983230072969 + 3 ^ 40 * 3903954 * 2
def baseEnd_3903954 : Nat := 1336403236695149330480699

theorem tailTrace_3903954 : CollatzResearch.WordTrace tailWord_3903954 prefixEnd_3903954 1336403236695149330480699 := by
  unfold tailWord_3903954
  simp only [CollatzResearch.WordTrace]
  refine ⟨35597225024662218776561729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94925933399099250070831277 35597225024662218776561729)
  ·
    refine ⟨26697918768496664082421297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35597225024662218776561729 26697918768496664082421297)
    ·
      refine ⟨20023439076372498061815973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26697918768496664082421297 20023439076372498061815973)
      ·
        refine ⟨3754394826819843386590495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20023439076372498061815973 3754394826819843386590495)
        ·
          refine ⟨5631592240229765079885743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754394826819843386590495 5631592240229765079885743)
          ·
            refine ⟨8447388360344647619828615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631592240229765079885743 8447388360344647619828615)
            ·
              refine ⟨12671082540516971429742923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8447388360344647619828615 12671082540516971429742923)
              ·
                refine ⟨19006623810775457144614385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12671082540516971429742923 19006623810775457144614385)
                ·
                  refine ⟨14254967858081592858460789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19006623810775457144614385 14254967858081592858460789)
                  ·
                    refine ⟨1336403236695149330480699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14254967858081592858460789 1336403236695149330480699)
                    ·
                      rfl

theorem cell22_3903954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_3903954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903954 prefixEnd_3903954 := by exact prefixLift 3903954
  have htrace : WordTrace (prefixWord ++ tailWord_3903954) baseStart_3903954 baseEnd_3903954 := by
    simpa [prefixWord, tailWord_3903954, baseEnd_3903954] using wordTrace_append hprefix tailTrace_3903954
  have hstable : (prefixWord ++ tailWord_3903954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903954).length < 2 ^ (prefixWord ++ tailWord_3903954).sum := by decide
  have hdescent : baseEnd_3903954 < baseStart_3903954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903980 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_3903980 : Nat := 118140960795 + 3903980 * 2 ^ 59
def prefixEnd_3903980 : Nat := 4983230072969 + 3 ^ 40 * 3903980 * 2
def baseEnd_3903980 : Nat := 1336412137026493929330619

theorem tailTrace_3903980 : CollatzResearch.WordTrace tailWord_3903980 prefixEnd_3903980 1336412137026493929330619 := by
  unfold tailWord_3903980
  simp only [CollatzResearch.WordTrace]
  refine ⟨71194924198277340773346697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94926565597703121031128929 71194924198277340773346697)
  ·
    refine ⟨53396193148708005580010023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71194924198277340773346697 53396193148708005580010023)
    ·
      refine ⟨80094289723062008370015035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53396193148708005580010023 80094289723062008370015035)
      ·
        refine ⟨120141434584593012555022553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80094289723062008370015035 120141434584593012555022553)
        ·
          refine ⟨90106075938444759416266915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120141434584593012555022553 90106075938444759416266915)
          ·
            refine ⟨135159113907667139124400373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90106075938444759416266915 135159113907667139124400373)
            ·
              refine ⟨12671166928843794292912535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135159113907667139124400373 12671166928843794292912535)
              ·
                refine ⟨19006750393265691439368803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12671166928843794292912535 19006750393265691439368803)
                ·
                  refine ⟨28510125589898537159053205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19006750393265691439368803 28510125589898537159053205)
                  ·
                    refine ⟨1336412137026493929330619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28510125589898537159053205 1336412137026493929330619)
                    ·
                      rfl

theorem cell22_3903980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_3903980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903980 prefixEnd_3903980 := by exact prefixLift 3903980
  have htrace : WordTrace (prefixWord ++ tailWord_3903980) baseStart_3903980 baseEnd_3903980 := by
    simpa [prefixWord, tailWord_3903980, baseEnd_3903980] using wordTrace_append hprefix tailTrace_3903980
  have hstable : (prefixWord ++ tailWord_3903980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903980).length < 2 ^ (prefixWord ++ tailWord_3903980).sum := by decide
  have hdescent : baseEnd_3903980 < baseStart_3903980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903982 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_3903982 : Nat := 118140960795 + 3903982 * 2 ^ 59
def prefixEnd_3903982 : Nat := 4983230072969 + 3 ^ 40 * 3903982 * 2
def baseEnd_3903982 : Nat := 1336412821667366590780613

theorem tailTrace_3903982 : CollatzResearch.WordTrace tailWord_3903982 prefixEnd_3903982 1336412821667366590780613 := by
  unfold tailWord_3903982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17798740167818429486033275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94926614228364957258844133 17798740167818429486033275)
  ·
    refine ⟨26698110251727644229049913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17798740167818429486033275 26698110251727644229049913)
    ·
      refine ⟨20023582688795733171787435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26698110251727644229049913 20023582688795733171787435)
      ·
        refine ⟨30035374033193599757681153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20023582688795733171787435 30035374033193599757681153)
        ·
          refine ⟨22526530524895199818260865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30035374033193599757681153 22526530524895199818260865)
          ·
            refine ⟨16894897893671399863695649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22526530524895199818260865 16894897893671399863695649)
            ·
              refine ⟨12671173420253549897771737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16894897893671399863695649 12671173420253549897771737)
              ·
                refine ⟨9503380065190162423328803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12671173420253549897771737 9503380065190162423328803)
                ·
                  refine ⟨14255070097785243634993205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9503380065190162423328803 14255070097785243634993205)
                  ·
                    refine ⟨1336412821667366590780613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14255070097785243634993205 1336412821667366590780613)
                    ·
                      rfl

theorem cell22_3903982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_3903982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3903982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3903982 prefixEnd_3903982 := by exact prefixLift 3903982
  have htrace : WordTrace (prefixWord ++ tailWord_3903982) baseStart_3903982 baseEnd_3903982 := by
    simpa [prefixWord, tailWord_3903982, baseEnd_3903982] using wordTrace_append hprefix tailTrace_3903982
  have hstable : (prefixWord ++ tailWord_3903982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903982).length < 2 ^ (prefixWord ++ tailWord_3903982).sum := by decide
  have hdescent : baseEnd_3903982 < baseStart_3903982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904029 : List Nat := [1, 4, 2, 2, 1, 4, 2, 6]
def baseStart_3904029 : Nat := 118140960795 + 3904029 * 2 ^ 59
def prefixEnd_3904029 : Nat := 4983230072969 + 3 ^ 40 * 3904029 * 2
def baseEnd_3904029 : Nat := 148492101191986014983941

theorem tailTrace_3904029 : CollatzResearch.WordTrace tailWord_3904029 prefixEnd_3904029 148492101191986014983941 := by
  unfold tailWord_3904029
  simp only [CollatzResearch.WordTrace]
  refine ⟨142391635573377162915227141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94927757048918108610151427 142391635573377162915227141)
  ·
    refine ⟨26698431670008218046605089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142391635573377162915227141 26698431670008218046605089)
    ·
      refine ⟨20023823752506163534953817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26698431670008218046605089 20023823752506163534953817)
      ·
        refine ⟨15017867814379622651215363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20023823752506163534953817 15017867814379622651215363)
        ·
          refine ⟨22526801721569433976823045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15017867814379622651215363 22526801721569433976823045)
          ·
            refine ⟨4223775322794268870654321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22526801721569433976823045 4223775322794268870654321)
            ·
              refine ⟨3167831492095701652990741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4223775322794268870654321 3167831492095701652990741)
              ·
                refine ⟨148492101191986014983941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3167831492095701652990741 148492101191986014983941)
                ·
                  rfl

theorem cell22_3904029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 6].length) (baseStart_3904029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904029 prefixEnd_3904029 := by exact prefixLift 3904029
  have htrace : WordTrace (prefixWord ++ tailWord_3904029) baseStart_3904029 baseEnd_3904029 := by
    simpa [prefixWord, tailWord_3904029, baseEnd_3904029] using wordTrace_append hprefix tailTrace_3904029
  have hstable : (prefixWord ++ tailWord_3904029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904029).length < 2 ^ (prefixWord ++ tailWord_3904029).sum := by decide
  have hdescent : baseEnd_3904029 < baseStart_3904029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904057 : List Nat := [1, 2, 1, 5, 1, 1, 2, 4, 5]
def baseStart_3904057 : Nat := 118140960795 + 3904057 * 2 ^ 59
def prefixEnd_3904057 : Nat := 4983230072969 + 3 ^ 40 * 3904057 * 2
def baseEnd_3904057 : Nat := 445479498566697131718461

theorem tailTrace_3904057 : CollatzResearch.WordTrace tailWord_3904057 prefixEnd_3904057 445479498566697131718461 := by
  unfold tailWord_3904057
  simp only [CollatzResearch.WordTrace]
  refine ⟨142392656817275723697246425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94928437878183815798164283 142392656817275723697246425)
  ·
    refine ⟨106794492612956792772934819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142392656817275723697246425 106794492612956792772934819)
    ·
      refine ⟨160191738919435189159402229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106794492612956792772934819 160191738919435189159402229)
      ·
        refine ⟨15017975523697048983693959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160191738919435189159402229 15017975523697048983693959)
        ·
          refine ⟨22526963285545573475540939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15017975523697048983693959 22526963285545573475540939)
          ·
            refine ⟨33790444928318360213311409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22526963285545573475540939 33790444928318360213311409)
            ·
              refine ⟨25342833696238770159983557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33790444928318360213311409 25342833696238770159983557)
              ·
                refine ⟨4751781318044769404996917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25342833696238770159983557 4751781318044769404996917)
                ·
                  refine ⟨445479498566697131718461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4751781318044769404996917 445479498566697131718461)
                  ·
                    rfl

theorem cell22_3904057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_3904057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904057 prefixEnd_3904057 := by exact prefixLift 3904057
  have htrace : WordTrace (prefixWord ++ tailWord_3904057) baseStart_3904057 baseEnd_3904057 := by
    simpa [prefixWord, tailWord_3904057, baseEnd_3904057] using wordTrace_append hprefix tailTrace_3904057
  have hstable : (prefixWord ++ tailWord_3904057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904057).length < 2 ^ (prefixWord ++ tailWord_3904057).sum := by decide
  have hdescent : baseEnd_3904057 < baseStart_3904057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904061 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_3904061 : Nat := 118140960795 + 3904061 * 2 ^ 59
def prefixEnd_3904061 : Nat := 4983230072969 + 3 ^ 40 * 3904061 * 2
def baseEnd_3904061 : Nat := 1336439864981836718055371

theorem tailTrace_3904061 : CollatzResearch.WordTrace tailWord_3904061 prefixEnd_3904061 1336439864981836718055371 := by
  unfold tailWord_3904061
  simp only [CollatzResearch.WordTrace]
  refine ⟨142392802709261232380392037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94928535139507488253594691 142392802709261232380392037)
  ·
    refine ⟨26698650507986481071323507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142392802709261232380392037 26698650507986481071323507)
    ·
      refine ⟨40047975761979721606985261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26698650507986481071323507 40047975761979721606985261)
      ·
        refine ⟨15017990910742395602619473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40047975761979721606985261 15017990910742395602619473)
        ·
          refine ⟨11263493183056796701964605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15017990910742395602619473 11263493183056796701964605)
          ·
            refine ⟨4223809943646298763236727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11263493183056796701964605 4223809943646298763236727)
            ·
              refine ⟨6335714915469448144855091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223809943646298763236727 6335714915469448144855091)
              ·
                refine ⟨9503572373204172217282637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6335714915469448144855091 9503572373204172217282637)
                ·
                  refine ⟨3563839639951564581480989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9503572373204172217282637 3563839639951564581480989)
                  ·
                    refine ⟨1336439864981836718055371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3563839639951564581480989 1336439864981836718055371)
                    ·
                      rfl

theorem cell22_3904061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_3904061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904061 prefixEnd_3904061 := by exact prefixLift 3904061
  have htrace : WordTrace (prefixWord ++ tailWord_3904061) baseStart_3904061 baseEnd_3904061 := by
    simpa [prefixWord, tailWord_3904061, baseEnd_3904061] using wordTrace_append hprefix tailTrace_3904061
  have hstable : (prefixWord ++ tailWord_3904061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904061).length < 2 ^ (prefixWord ++ tailWord_3904061).sum := by decide
  have hdescent : baseEnd_3904061 < baseStart_3904061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904074 : List Nat := [3, 1, 2, 1, 1, 4, 4, 1, 5]
def baseStart_3904074 : Nat := 118140960795 + 3904074 * 2 ^ 59
def prefixEnd_3904074 : Nat := 4983230072969 + 3 ^ 40 * 3904074 * 2
def baseEnd_3904074 : Nat := 445481438382503005826777

theorem tailTrace_3904074 : CollatzResearch.WordTrace tailWord_3904074 prefixEnd_3904074 445481438382503005826777 := by
  unfold tailWord_3904074
  simp only [CollatzResearch.WordTrace]
  refine ⟨35598319214553533900153819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94928851238809423733743517 35598319214553533900153819)
  ·
    refine ⟨53397478821830300850230729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35598319214553533900153819 53397478821830300850230729)
    ·
      refine ⟨40048109116372725637673047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53397478821830300850230729 40048109116372725637673047)
      ·
        refine ⟨60072163674559088456509571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40048109116372725637673047 60072163674559088456509571)
        ·
          refine ⟨90108245511838632684764357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60072163674559088456509571 90108245511838632684764357)
          ·
            refine ⟨16895296033469743628393317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90108245511838632684764357 16895296033469743628393317)
            ·
              refine ⟨3167868006275576930323747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16895296033469743628393317 3167868006275576930323747)
              ·
                refine ⟨4751802009413365395485621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3167868006275576930323747 4751802009413365395485621)
                ·
                  refine ⟨445481438382503005826777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4751802009413365395485621 445481438382503005826777)
                  ·
                    rfl

theorem cell22_3904074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_3904074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904074 prefixEnd_3904074 := by exact prefixLift 3904074
  have htrace : WordTrace (prefixWord ++ tailWord_3904074) baseStart_3904074 baseEnd_3904074 := by
    simpa [prefixWord, tailWord_3904074, baseEnd_3904074] using wordTrace_append hprefix tailTrace_3904074
  have hstable : (prefixWord ++ tailWord_3904074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904074).length < 2 ^ (prefixWord ++ tailWord_3904074).sum := by decide
  have hdescent : baseEnd_3904074 < baseStart_3904074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904087 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 3, 4]
def baseStart_3904087 : Nat := 118140960795 + 3904087 * 2 ^ 59
def prefixEnd_3904087 : Nat := 4983230072969 + 3 ^ 40 * 3904087 * 2
def baseEnd_3904087 : Nat := 1336448765313181316905291

theorem tailTrace_3904087 : CollatzResearch.WordTrace tailWord_3904087 prefixEnd_3904087 1336448765313181316905291 := by
  unfold tailWord_3904087
  simp only [CollatzResearch.WordTrace]
  refine ⟨142393751007167038820838515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94929167338111359213892343 142393751007167038820838515)
  ·
    refine ⟨213590626510750558231257773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142393751007167038820838515 213590626510750558231257773)
    ·
      refine ⟨80096484941531459336721665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213590626510750558231257773 80096484941531459336721665)
      ·
        refine ⟨60072363706148594502541249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80096484941531459336721665 60072363706148594502541249)
        ·
          refine ⟨45054272779611445876905937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60072363706148594502541249 45054272779611445876905937)
          ·
            refine ⟨33790704584708584407679453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45054272779611445876905937 33790704584708584407679453)
            ·
              refine ⟨12671514219265719152879795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33790704584708584407679453 12671514219265719152879795)
              ·
                refine ⟨19007271328898578729319693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12671514219265719152879795 19007271328898578729319693)
                ·
                  refine ⟨7127726748336967023494885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19007271328898578729319693 7127726748336967023494885)
                  ·
                    refine ⟨1336448765313181316905291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7127726748336967023494885 1336448765313181316905291)
                    ·
                      rfl

theorem cell22_3904087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_3904087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904087 prefixEnd_3904087 := by exact prefixLift 3904087
  have htrace : WordTrace (prefixWord ++ tailWord_3904087) baseStart_3904087 baseEnd_3904087 := by
    simpa [prefixWord, tailWord_3904087, baseEnd_3904087] using wordTrace_append hprefix tailTrace_3904087
  have hstable : (prefixWord ++ tailWord_3904087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904087).length < 2 ^ (prefixWord ++ tailWord_3904087).sum := by decide
  have hdescent : baseEnd_3904087 < baseStart_3904087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904179 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 3, 3]
def baseStart_3904179 : Nat := 118140960795 + 3904179 * 2 ^ 59
def prefixEnd_3904179 : Nat := 4983230072969 + 3 ^ 40 * 3904179 * 2
def baseEnd_3904179 : Nat := 1336480258793323743605009

theorem tailTrace_3904179 : CollatzResearch.WordTrace tailWord_3904179 prefixEnd_3904179 1336480258793323743605009 := by
  unfold tailWord_3904179
  simp only [CollatzResearch.WordTrace]
  refine ⟨142397106522833738533187591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94931404348555825688791727 142397106522833738533187591)
  ·
    refine ⟨213595659784250607799781387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142397106522833738533187591 213595659784250607799781387)
    ·
      refine ⟨320393489676375911699672081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213595659784250607799781387 320393489676375911699672081)
      ·
        refine ⟨240295117257281933774754061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320393489676375911699672081 240295117257281933774754061)
        ·
          refine ⟨90110668971480725165532773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240295117257281933774754061 90110668971480725165532773)
          ·
            refine ⟨16895750432152635968537395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90110668971480725165532773 16895750432152635968537395)
            ·
              refine ⟨25343625648228953952806093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16895750432152635968537395 25343625648228953952806093)
              ·
                refine ⟨9503859618085857732302285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25343625648228953952806093 9503859618085857732302285)
                ·
                  refine ⟨3563947356782196649613357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9503859618085857732302285 3563947356782196649613357)
                  ·
                    refine ⟨1336480258793323743605009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3563947356782196649613357 1336480258793323743605009)
                    ·
                      rfl

theorem cell22_3904179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 3].length) (baseStart_3904179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904179 prefixEnd_3904179 := by exact prefixLift 3904179
  have htrace : WordTrace (prefixWord ++ tailWord_3904179) baseStart_3904179 baseEnd_3904179 := by
    simpa [prefixWord, tailWord_3904179, baseEnd_3904179] using wordTrace_append hprefix tailTrace_3904179
  have hstable : (prefixWord ++ tailWord_3904179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904179).length < 2 ^ (prefixWord ++ tailWord_3904179).sum := by decide
  have hdescent : baseEnd_3904179 < baseStart_3904179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904196 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_3904196 : Nat := 118140960795 + 3904196 * 2 ^ 59
def prefixEnd_3904196 : Nat := 4983230072969 + 3 ^ 40 * 3904196 * 2
def baseEnd_3904196 : Nat := 1336486078240741365929957

theorem tailTrace_3904196 : CollatzResearch.WordTrace tailWord_3904196 prefixEnd_3904196 1336486078240741365929957 := by
  unfold tailWord_3904196
  simp only [CollatzResearch.WordTrace]
  refine ⟨71198863281886075218278221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94931817709181433624370961 71198863281886075218278221)
  ·
    refine ⟨26699573730707278206854333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71198863281886075218278221 26699573730707278206854333)
    ·
      refine ⟨10012340149015229327570375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26699573730707278206854333 10012340149015229327570375)
      ·
        refine ⟨15018510223522843991355563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10012340149015229327570375 15018510223522843991355563)
        ·
          refine ⟨22527765335284265987033345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15018510223522843991355563 22527765335284265987033345)
          ·
            refine ⟨16895824001463199490275009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22527765335284265987033345 16895824001463199490275009)
            ·
              refine ⟨12671868001097399617706257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16895824001463199490275009 12671868001097399617706257)
              ·
                refine ⟨9503901000823049713279693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12671868001097399617706257 9503901000823049713279693)
                ·
                  refine ⟨3563962875308643642479885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9503901000823049713279693 3563962875308643642479885)
                  ·
                    refine ⟨1336486078240741365929957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3563962875308643642479885 1336486078240741365929957)
                    ·
                      rfl

theorem cell22_3904196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_3904196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904196 prefixEnd_3904196 := by exact prefixLift 3904196
  have htrace : WordTrace (prefixWord ++ tailWord_3904196) baseStart_3904196 baseEnd_3904196 := by
    simpa [prefixWord, tailWord_3904196, baseEnd_3904196] using wordTrace_append hprefix tailTrace_3904196
  have hstable : (prefixWord ++ tailWord_3904196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904196).length < 2 ^ (prefixWord ++ tailWord_3904196).sum := by decide
  have hdescent : baseEnd_3904196 < baseStart_3904196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904198 : List Nat := [6, 1, 2, 1, 2, 1, 1, 8]
def baseStart_3904198 : Nat := 118140960795 + 3904198 * 2 ^ 59
def prefixEnd_3904198 : Nat := 4983230072969 + 3 ^ 40 * 3904198 * 2
def baseEnd_3904198 : Nat := 148498529209068225264439

theorem tailTrace_3904198 : CollatzResearch.WordTrace tailWord_3904198 prefixEnd_3904198 148498529209068225264439 := by
  unfold tailWord_3904198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4449931234680153274316539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94931866339843269852086165 4449931234680153274316539)
  ·
    refine ⟨6674896852020229911474809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4449931234680153274316539 6674896852020229911474809)
    ·
      refine ⟨5006172639015172433606107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6674896852020229911474809 5006172639015172433606107)
      ·
        refine ⟨7509258958522758650409161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5006172639015172433606107 7509258958522758650409161)
        ·
          refine ⟨5631944218892068987806871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7509258958522758650409161 5631944218892068987806871)
          ·
            refine ⟨8447916328338103481710307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631944218892068987806871 8447916328338103481710307)
            ·
              refine ⟨12671874492507155222565461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8447916328338103481710307 12671874492507155222565461)
              ·
                refine ⟨148498529209068225264439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12671874492507155222565461 148498529209068225264439)
                ·
                  rfl

theorem cell22_3904198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_3904198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904198 prefixEnd_3904198 := by exact prefixLift 3904198
  have htrace : WordTrace (prefixWord ++ tailWord_3904198) baseStart_3904198 baseEnd_3904198 := by
    simpa [prefixWord, tailWord_3904198, baseEnd_3904198] using wordTrace_append hprefix tailTrace_3904198
  have hstable : (prefixWord ++ tailWord_3904198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904198).length < 2 ^ (prefixWord ++ tailWord_3904198).sum := by decide
  have hdescent : baseEnd_3904198 < baseStart_3904198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904288 : List Nat := [2, 1, 1, 5, 1, 2, 4, 2, 4]
def baseStart_3904288 : Nat := 118140960795 + 3904288 * 2 ^ 59
def prefixEnd_3904288 : Nat := 4983230072969 + 3 ^ 40 * 3904288 * 2
def baseEnd_3904288 : Nat := 445505857240294597543225

theorem tailTrace_3904288 : CollatzResearch.WordTrace tailWord_3904288 prefixEnd_3904288 445505857240294597543225 := by
  unfold tailWord_3904288
  simp only [CollatzResearch.WordTrace]
  refine ⟨71200541039719425074452759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94934054719625900099270345 71200541039719425074452759)
  ·
    refine ⟨106800811559579137611679139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71200541039719425074452759 106800811559579137611679139)
    ·
      refine ⟨160201217339368706417518709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106800811559579137611679139 160201217339368706417518709)
      ·
        refine ⟨15018864125565816226642379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160201217339368706417518709 15018864125565816226642379)
        ·
          refine ⟨22528296188348724339963569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15018864125565816226642379 22528296188348724339963569)
          ·
            refine ⟨16896222141261543254972677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22528296188348724339963569 16896222141261543254972677)
            ·
              refine ⟨3168041651486539360307377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16896222141261543254972677 3168041651486539360307377)
              ·
                refine ⟨2376031238614904520230533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3168041651486539360307377 2376031238614904520230533)
                ·
                  refine ⟨445505857240294597543225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2376031238614904520230533 445505857240294597543225)
                  ·
                    rfl

theorem cell22_3904288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 4].length) (baseStart_3904288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904288 prefixEnd_3904288 := by exact prefixLift 3904288
  have htrace : WordTrace (prefixWord ++ tailWord_3904288) baseStart_3904288 baseEnd_3904288 := by
    simpa [prefixWord, tailWord_3904288, baseEnd_3904288] using wordTrace_append hprefix tailTrace_3904288
  have hstable : (prefixWord ++ tailWord_3904288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904288).length < 2 ^ (prefixWord ++ tailWord_3904288).sum := by decide
  have hdescent : baseEnd_3904288 < baseStart_3904288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904324 : List Nat := [2, 3, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3904324 : Nat := 118140960795 + 3904324 * 2 ^ 59
def prefixEnd_3904324 : Nat := 4983230072969 + 3 ^ 40 * 3904324 * 2
def baseEnd_3904324 : Nat := 1336529895256591698729565

theorem tailTrace_3904324 : CollatzResearch.WordTrace tailWord_3904324 prefixEnd_3904324 1336529895256591698729565 := by
  unfold tailWord_3904324
  simp only [CollatzResearch.WordTrace]
  refine ⟨71201197553654214148608013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94934930071538952198144017 71201197553654214148608013)
  ·
    refine ⟨26700449082620330305728005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71201197553654214148608013 26700449082620330305728005)
    ·
      refine ⟨5006334202991311932324001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26700449082620330305728005 5006334202991311932324001)
      ·
        refine ⟨3754750652243483949243001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5006334202991311932324001 3754750652243483949243001)
        ·
          refine ⟨2816062989182612961932251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3754750652243483949243001 2816062989182612961932251)
          ·
            refine ⟨4224094483773919442898377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816062989182612961932251 4224094483773919442898377)
            ·
              refine ⟨3168070862830439582173783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4224094483773919442898377 3168070862830439582173783)
              ·
                refine ⟨4752106294245659373260675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168070862830439582173783 4752106294245659373260675)
                ·
                  refine ⟨7128159441368489059891013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752106294245659373260675 7128159441368489059891013)
                  ·
                    refine ⟨1336529895256591698729565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7128159441368489059891013 1336529895256591698729565)
                    ·
                      rfl

theorem cell22_3904324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3904324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904324 prefixEnd_3904324 := by exact prefixLift 3904324
  have htrace : WordTrace (prefixWord ++ tailWord_3904324) baseStart_3904324 baseEnd_3904324 := by
    simpa [prefixWord, tailWord_3904324, baseEnd_3904324] using wordTrace_append hprefix tailTrace_3904324
  have hstable : (prefixWord ++ tailWord_3904324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904324).length < 2 ^ (prefixWord ++ tailWord_3904324).sum := by decide
  have hdescent : baseEnd_3904324 < baseStart_3904324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904348 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3904348 : Nat := 118140960795 + 3904348 * 2 ^ 59
def prefixEnd_3904348 : Nat := 4983230072969 + 3 ^ 40 * 3904348 * 2
def baseEnd_3904348 : Nat := 1336538110947063636129491

theorem tailTrace_3904348 : CollatzResearch.WordTrace tailWord_3904348 prefixEnd_3904348 1336538110947063636129491 := by
  unfold tailWord_3904348
  simp only [CollatzResearch.WordTrace]
  refine ⟨71201635229610740198044849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94935513639480986930726465 71201635229610740198044849)
  ·
    refine ⟨53401226422208055148533637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71201635229610740198044849 53401226422208055148533637)
    ·
      refine ⟨10012729954164010340350057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53401226422208055148533637 10012729954164010340350057)
      ·
        refine ⟨7509547465623007755262543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10012729954164010340350057 7509547465623007755262543)
        ·
          refine ⟨11264321198434511632893815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7509547465623007755262543 11264321198434511632893815)
          ·
            refine ⟨16896481797651767449340723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11264321198434511632893815 16896481797651767449340723)
            ·
              refine ⟨25344722696477651174011085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16896481797651767449340723 25344722696477651174011085)
              ·
                refine ⟨9504271011179119190254157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25344722696477651174011085 9504271011179119190254157)
                ·
                  refine ⟨3564101629192169696345309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9504271011179119190254157 3564101629192169696345309)
                  ·
                    refine ⟨1336538110947063636129491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3564101629192169696345309 1336538110947063636129491)
                    ·
                      rfl

theorem cell22_3904348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3904348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904348 prefixEnd_3904348 := by exact prefixLift 3904348
  have htrace : WordTrace (prefixWord ++ tailWord_3904348) baseStart_3904348 baseEnd_3904348 := by
    simpa [prefixWord, tailWord_3904348, baseEnd_3904348] using wordTrace_append hprefix tailTrace_3904348
  have hstable : (prefixWord ++ tailWord_3904348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904348).length < 2 ^ (prefixWord ++ tailWord_3904348).sum := by decide
  have hdescent : baseEnd_3904348 < baseStart_3904348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904412 : List Nat := [2, 2, 3, 3, 3, 1, 2, 1, 5]
def baseStart_3904412 : Nat := 118140960795 + 3904412 * 2 ^ 59
def prefixEnd_3904412 : Nat := 4983230072969 + 3 ^ 40 * 3904412 * 2
def baseEnd_3904412 : Nat := 445520006484996267509765

theorem tailTrace_3904412 : CollatzResearch.WordTrace tailWord_3904412 prefixEnd_3904412 445520006484996267509765 := by
  unfold tailWord_3904412
  simp only [CollatzResearch.WordTrace]
  refine ⟨71202802365494809663209745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94937069820659746217612993 71202802365494809663209745)
  ·
    refine ⟨53402101774121107247407309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71202802365494809663209745 53402101774121107247407309)
    ·
      refine ⟨20025788165295415217777741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53402101774121107247407309 20025788165295415217777741)
      ·
        refine ⟨7509670561985780706666653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20025788165295415217777741 7509670561985780706666653)
        ·
          refine ⟨2816126460744667764999995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7509670561985780706666653 2816126460744667764999995)
          ·
            refine ⟨4224189691117001647499993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816126460744667764999995 4224189691117001647499993)
            ·
              refine ⟨3168142268337751235624995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4224189691117001647499993 3168142268337751235624995)
              ·
                refine ⟨4752213402506626853437493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168142268337751235624995 4752213402506626853437493)
                ·
                  refine ⟨445520006484996267509765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4752213402506626853437493 445520006484996267509765)
                  ·
                    rfl

theorem cell22_3904412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_3904412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904412 prefixEnd_3904412 := by exact prefixLift 3904412
  have htrace : WordTrace (prefixWord ++ tailWord_3904412) baseStart_3904412 baseEnd_3904412 := by
    simpa [prefixWord, tailWord_3904412, baseEnd_3904412] using wordTrace_append hprefix tailTrace_3904412
  have hstable : (prefixWord ++ tailWord_3904412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904412).length < 2 ^ (prefixWord ++ tailWord_3904412).sum := by decide
  have hdescent : baseEnd_3904412 < baseStart_3904412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904419 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 3, 6]
def baseStart_3904419 : Nat := 118140960795 + 3904419 * 2 ^ 59
def prefixEnd_3904419 : Nat := 4983230072969 + 3 ^ 40 * 3904419 * 2
def baseEnd_3904419 : Nat := 1336562415698043117604273

theorem tailTrace_3904419 : CollatzResearch.WordTrace tailWord_3904419 prefixEnd_3904419 1336562415698043117604273 := by
  unfold tailWord_3904419
  simp only [CollatzResearch.WordTrace]
  refine ⟨142405860041964259521924311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94937240027976173014616207 142405860041964259521924311)
  ·
    refine ⟨213608790062946389282886467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142405860041964259521924311 213608790062946389282886467)
    ·
      refine ⟨320413185094419583924329701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213608790062946389282886467 320413185094419583924329701)
      ·
        refine ⟨60077472205203671985811819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320413185094419583924329701 60077472205203671985811819)
        ·
          refine ⟨90116208307805507978717729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60077472205203671985811819 90116208307805507978717729)
          ·
            refine ⟨67587156230854130984038297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90116208307805507978717729 67587156230854130984038297)
            ·
              refine ⟨50690367173140598238028723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67587156230854130984038297 50690367173140598238028723)
              ·
                refine ⟨76035550759710897357043085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50690367173140598238028723 76035550759710897357043085)
                ·
                  refine ⟨28513331534891586508891157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76035550759710897357043085 28513331534891586508891157)
                  ·
                    refine ⟨1336562415698043117604273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28513331534891586508891157 1336562415698043117604273)
                    ·
                      rfl

theorem cell22_3904419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_3904419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904419 prefixEnd_3904419 := by exact prefixLift 3904419
  have htrace : WordTrace (prefixWord ++ tailWord_3904419) baseStart_3904419 baseEnd_3904419 := by
    simpa [prefixWord, tailWord_3904419, baseEnd_3904419] using wordTrace_append hprefix tailTrace_3904419
  have hstable : (prefixWord ++ tailWord_3904419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904419).length < 2 ^ (prefixWord ++ tailWord_3904419).sum := by decide
  have hdescent : baseEnd_3904419 < baseStart_3904419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904468 : List Nat := [2, 4, 1, 2, 1, 4, 1, 7]
def baseStart_3904468 : Nat := 118140960795 + 3904468 * 2 ^ 59
def prefixEnd_3904468 : Nat := 4983230072969 + 3 ^ 40 * 3904468 * 2
def baseEnd_3904468 : Nat := 148508798822158147014347

theorem tailTrace_3904468 : CollatzResearch.WordTrace tailWord_3904468 prefixEnd_3904468 148508798822158147014347 := by
  unfold tailWord_3904468
  simp only [CollatzResearch.WordTrace]
  refine ⟨71203823609393370445229029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94938431479191160593638705 71203823609393370445229029)
  ·
    refine ⟨13350716926761256958480443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71203823609393370445229029 13350716926761256958480443)
    ·
      refine ⟨20026075390141885437720665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13350716926761256958480443 20026075390141885437720665)
      ·
        refine ⟨15019556542606414078290499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20026075390141885437720665 15019556542606414078290499)
        ·
          refine ⟨22529334813909621117435749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15019556542606414078290499 22529334813909621117435749)
          ·
            refine ⟨4224250277608053959519203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22529334813909621117435749 4224250277608053959519203)
            ·
              refine ⟨6336375416412080939278805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4224250277608053959519203 6336375416412080939278805)
              ·
                refine ⟨148508798822158147014347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6336375416412080939278805 148508798822158147014347)
                ·
                  rfl

theorem cell22_3904468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 7].length) (baseStart_3904468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904468 prefixEnd_3904468 := by exact prefixLift 3904468
  have htrace : WordTrace (prefixWord ++ tailWord_3904468) baseStart_3904468 baseEnd_3904468 := by
    simpa [prefixWord, tailWord_3904468, baseEnd_3904468] using wordTrace_append hprefix tailTrace_3904468
  have hstable : (prefixWord ++ tailWord_3904468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904468).length < 2 ^ (prefixWord ++ tailWord_3904468).sum := by decide
  have hdescent : baseEnd_3904468 < baseStart_3904468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904483 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 3, 3]
def baseStart_3904483 : Nat := 118140960795 + 3904483 * 2 ^ 59
def prefixEnd_3904483 : Nat := 4983230072969 + 3 ^ 40 * 3904483 * 2
def baseEnd_3904483 : Nat := 1336584324205968284004077

theorem tailTrace_3904483 : CollatzResearch.WordTrace tailWord_3904483 prefixEnd_3904483 1336584324205968284004077 := by
  unfold tailWord_3904483
  simp only [CollatzResearch.WordTrace]
  refine ⟨142408194313732398452254103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94938796209154932301502735 142408194313732398452254103)
  ·
    refine ⟨213612291470598597678381155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142408194313732398452254103 213612291470598597678381155)
    ·
      refine ⟨320418437205897896517571733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213612291470598597678381155 320418437205897896517571733)
      ·
        refine ⟨15019614244026463899261175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 320418437205897896517571733 15019614244026463899261175)
        ·
          refine ⟨22529421366039695848891763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15019614244026463899261175 22529421366039695848891763)
          ·
            refine ⟨33794132049059543773337645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22529421366039695848891763 33794132049059543773337645)
            ·
              refine ⟨12672799518397328915001617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33794132049059543773337645 12672799518397328915001617)
              ·
                refine ⟨9504599638797996686251213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12672799518397328915001617 9504599638797996686251213)
                ·
                  refine ⟨3564224864549248757344205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9504599638797996686251213 3564224864549248757344205)
                  ·
                    refine ⟨1336584324205968284004077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3564224864549248757344205 1336584324205968284004077)
                    ·
                      rfl

theorem cell22_3904483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 3].length) (baseStart_3904483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904483 prefixEnd_3904483 := by exact prefixLift 3904483
  have htrace : WordTrace (prefixWord ++ tailWord_3904483) baseStart_3904483 baseEnd_3904483 := by
    simpa [prefixWord, tailWord_3904483, baseEnd_3904483] using wordTrace_append hprefix tailTrace_3904483
  have hstable : (prefixWord ++ tailWord_3904483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904483).length < 2 ^ (prefixWord ++ tailWord_3904483).sum := by decide
  have hdescent : baseEnd_3904483 < baseStart_3904483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904485 : List Nat := [1, 3, 1, 6, 1, 1, 3, 6]
def baseStart_3904485 : Nat := 118140960795 + 3904485 * 2 ^ 59
def prefixEnd_3904485 : Nat := 4983230072969 + 3 ^ 40 * 3904485 * 2
def baseEnd_3904485 : Nat := 148509445427426771717119

theorem tailTrace_3904485 : CollatzResearch.WordTrace tailWord_3904485 prefixEnd_3904485 148509445427426771717119 := by
  unfold tailWord_3904485
  simp only [CollatzResearch.WordTrace]
  refine ⟨142408267259725152793826909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94938844839816768529217939 142408267259725152793826909)
  ·
    refine ⟨53403100222396932297685091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142408267259725152793826909 53403100222396932297685091)
    ·
      refine ⟨80104650333595398446527637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53403100222396932297685091 80104650333595398446527637)
      ·
        refine ⟨3754905484387284302180983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80104650333595398446527637 3754905484387284302180983)
        ·
          refine ⟨5632358226580926453271475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754905484387284302180983 5632358226580926453271475)
          ·
            refine ⟨8448537339871389679907213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632358226580926453271475 8448537339871389679907213)
            ·
              refine ⟨3168201502451771129965205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8448537339871389679907213 3168201502451771129965205)
              ·
                refine ⟨148509445427426771717119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3168201502451771129965205 148509445427426771717119)
                ·
                  rfl

theorem cell22_3904485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 6].length) (baseStart_3904485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904485 prefixEnd_3904485 := by exact prefixLift 3904485
  have htrace : WordTrace (prefixWord ++ tailWord_3904485) baseStart_3904485 baseEnd_3904485 := by
    simpa [prefixWord, tailWord_3904485, baseEnd_3904485] using wordTrace_append hprefix tailTrace_3904485
  have hstable : (prefixWord ++ tailWord_3904485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904485).length < 2 ^ (prefixWord ++ tailWord_3904485).sum := by decide
  have hdescent : baseEnd_3904485 < baseStart_3904485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904513 : List Nat := [1, 2, 4, 1, 2, 2, 3, 2, 5]
def baseStart_3904513 : Nat := 118140960795 + 3904513 * 2 ^ 59
def prefixEnd_3904513 : Nat := 4983230072969 + 3 ^ 40 * 3904513 * 2
def baseEnd_3904513 : Nat := 445531531273019401917995

theorem tailTrace_3904513 : CollatzResearch.WordTrace tailWord_3904513 prefixEnd_3904513 445531531273019401917995 := by
  unfold tailWord_3904513
  simp only [CollatzResearch.WordTrace]
  refine ⟨142409288503623713575846193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94939525669082475717230795 142409288503623713575846193)
  ·
    refine ⟨106806966377717785181884645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142409288503623713575846193 106806966377717785181884645)
    ·
      refine ⟨20026306195822084721603371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106806966377717785181884645 20026306195822084721603371)
      ·
        refine ⟨30039459293733127082405057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20026306195822084721603371 30039459293733127082405057)
        ·
          refine ⟨22529594470299845311803793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30039459293733127082405057 22529594470299845311803793)
          ·
            refine ⟨16897195852724883983852845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22529594470299845311803793 16897195852724883983852845)
            ·
              refine ⟨6336448444771831493944817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16897195852724883983852845 6336448444771831493944817)
              ·
                refine ⟨4752336333578873620458613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6336448444771831493944817 4752336333578873620458613)
                ·
                  refine ⟨445531531273019401917995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4752336333578873620458613 445531531273019401917995)
                  ·
                    rfl

theorem cell22_3904513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_3904513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904513 prefixEnd_3904513 := by exact prefixLift 3904513
  have htrace : WordTrace (prefixWord ++ tailWord_3904513) baseStart_3904513 baseEnd_3904513 := by
    simpa [prefixWord, tailWord_3904513, baseEnd_3904513] using wordTrace_append hprefix tailTrace_3904513
  have hstable : (prefixWord ++ tailWord_3904513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904513).length < 2 ^ (prefixWord ++ tailWord_3904513).sum := by decide
  have hdescent : baseEnd_3904513 < baseStart_3904513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904543 : List Nat := [1, 1, 2, 4, 1, 3, 1, 4, 1, 4]
def baseStart_3904543 : Nat := 118140960795 + 3904543 * 2 ^ 59
def prefixEnd_3904543 : Nat := 4983230072969 + 3 ^ 40 * 3904543 * 2
def baseEnd_3904543 : Nat := 1336604863432148127503893

theorem tailTrace_3904543 : CollatzResearch.WordTrace tailWord_3904543 prefixEnd_3904543 1336604863432148127503893 := by
  unfold tailWord_3904543
  simp only [CollatzResearch.WordTrace]
  refine ⟨142410382693515028699438283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94940255129010019132958855 142410382693515028699438283)
  ·
    refine ⟨213615574040272543049157425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142410382693515028699438283 213615574040272543049157425)
    ·
      refine ⟨160211680530204407286868069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213615574040272543049157425 160211680530204407286868069)
      ·
        refine ⟨30039690099413326366287763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160211680530204407286868069 30039690099413326366287763)
        ·
          refine ⟨45059535149119989549431645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30039690099413326366287763 45059535149119989549431645)
          ·
            refine ⟨16897325680919996081036867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45059535149119989549431645 16897325680919996081036867)
            ·
              refine ⟨25345988521379994121555301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16897325680919996081036867 25345988521379994121555301)
              ·
                refine ⟨4752372847758748897791619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25345988521379994121555301 4752372847758748897791619)
                ·
                  refine ⟨7128559271638123346687429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752372847758748897791619 7128559271638123346687429)
                  ·
                    refine ⟨1336604863432148127503893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7128559271638123346687429 1336604863432148127503893)
                    ·
                      rfl

theorem cell22_3904543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_3904543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904543 prefixEnd_3904543 := by exact prefixLift 3904543
  have htrace : WordTrace (prefixWord ++ tailWord_3904543) baseStart_3904543 baseEnd_3904543 := by
    simpa [prefixWord, tailWord_3904543, baseEnd_3904543] using wordTrace_append hprefix tailTrace_3904543
  have hstable : (prefixWord ++ tailWord_3904543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904543).length < 2 ^ (prefixWord ++ tailWord_3904543).sum := by decide
  have hdescent : baseEnd_3904543 < baseStart_3904543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904556 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_3904556 : Nat := 118140960795 + 3904556 * 2 ^ 59
def prefixEnd_3904556 : Nat := 4983230072969 + 3 ^ 40 * 3904556 * 2
def baseEnd_3904556 : Nat := 1336609313597820426928853

theorem tailTrace_3904556 : CollatzResearch.WordTrace tailWord_3904556 prefixEnd_3904556 1336609313597820426928853 := by
  unfold tailWord_3904556
  simp only [CollatzResearch.WordTrace]
  refine ⟨71205428421233965959830761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94940571228311954613107681 71205428421233965959830761)
  ·
    refine ⟨53404071315925474469873071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71205428421233965959830761 53404071315925474469873071)
    ·
      refine ⟨80106106973888211704809607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53404071315925474469873071 80106106973888211704809607)
      ·
        refine ⟨120159160460832317557214411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80106106973888211704809607 120159160460832317557214411)
        ·
          refine ⟨180238740691248476335821617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120159160460832317557214411 180238740691248476335821617)
          ·
            refine ⟨135179055518436357251866213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180238740691248476335821617 135179055518436357251866213)
            ·
              refine ⟨25346072909706816984724915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135179055518436357251866213 25346072909706816984724915)
              ·
                refine ⟨38019109364560225477087373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25346072909706816984724915 38019109364560225477087373)
                ·
                  refine ⟨14257166011710084553907765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38019109364560225477087373 14257166011710084553907765)
                  ·
                    refine ⟨1336609313597820426928853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14257166011710084553907765 1336609313597820426928853)
                    ·
                      rfl

theorem cell22_3904556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_3904556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904556 prefixEnd_3904556 := by exact prefixLift 3904556
  have htrace : WordTrace (prefixWord ++ tailWord_3904556) baseStart_3904556 baseEnd_3904556 := by
    simpa [prefixWord, tailWord_3904556, baseEnd_3904556] using wordTrace_append hprefix tailTrace_3904556
  have hstable : (prefixWord ++ tailWord_3904556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904556).length < 2 ^ (prefixWord ++ tailWord_3904556).sum := by decide
  have hdescent : baseEnd_3904556 < baseStart_3904556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904586 : List Nat := [3, 1, 2, 1, 1, 2, 3, 9]
def baseStart_3904586 : Nat := 118140960795 + 3904586 * 2 ^ 59
def prefixEnd_3904586 : Nat := 4983230072969 + 3 ^ 40 * 3904586 * 2
def baseEnd_3904586 : Nat := 148513287023434483186529

theorem tailTrace_3904586 : CollatzResearch.WordTrace tailWord_3904586 prefixEnd_3904586 148513287023434483186529 := by
  unfold tailWord_3904586
  simp only [CollatzResearch.WordTrace]
  refine ⟨35602987758089811760813403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94941300688239498028835741 35602987758089811760813403)
  ·
    refine ⟨53404481637134717641220105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35602987758089811760813403 53404481637134717641220105)
    ·
      refine ⟨40053361227851038230915079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53404481637134717641220105 40053361227851038230915079)
      ·
        refine ⟨60080041841776557346372619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40053361227851038230915079 60080041841776557346372619)
        ·
          refine ⟨90120062762664836019558929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60080041841776557346372619 90120062762664836019558929)
          ·
            refine ⟨67590047071998627014669197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90120062762664836019558929 67590047071998627014669197)
            ·
              refine ⟨25346267651999485130500949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67590047071998627014669197 25346267651999485130500949)
              ·
                refine ⟨148513287023434483186529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25346267651999485130500949 148513287023434483186529)
                ·
                  rfl

theorem cell22_3904586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_3904586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904586 prefixEnd_3904586 := by exact prefixLift 3904586
  have htrace : WordTrace (prefixWord ++ tailWord_3904586) baseStart_3904586 baseEnd_3904586 := by
    simpa [prefixWord, tailWord_3904586, baseEnd_3904586] using wordTrace_append hprefix tailTrace_3904586
  have hstable : (prefixWord ++ tailWord_3904586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904586).length < 2 ^ (prefixWord ++ tailWord_3904586).sum := by decide
  have hdescent : baseEnd_3904586 < baseStart_3904586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904590 : List Nat := [4, 1, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_3904590 : Nat := 118140960795 + 3904590 * 2 ^ 59
def prefixEnd_3904590 : Nat := 4983230072969 + 3 ^ 40 * 3904590 * 2
def baseEnd_3904590 : Nat := 1336620952492655671578749

theorem tailTrace_3904590 : CollatzResearch.WordTrace tailWord_3904590 prefixEnd_3904590 1336620952492655671578749 := by
  unfold tailWord_3904590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17801512115543094465799903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94941397949563170484266149 17801512115543094465799903)
  ·
    refine ⟨26702268173314641698699855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17801512115543094465799903 26702268173314641698699855)
    ·
      refine ⟨40053402259971962548049783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26702268173314641698699855 40053402259971962548049783)
      ·
        refine ⟨60080103389957943822074675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40053402259971962548049783 60080103389957943822074675)
        ·
          refine ⟨90120155084936915733112013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60080103389957943822074675 90120155084936915733112013)
          ·
            refine ⟨33795058156851343399917005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90120155084936915733112013 33795058156851343399917005)
            ·
              refine ⟨12673146808819253774968877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33795058156851343399917005 12673146808819253774968877)
              ·
                refine ⟨4752430053307220165613329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12673146808819253774968877 4752430053307220165613329)
                ·
                  refine ⟨3564322539980415124209997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4752430053307220165613329 3564322539980415124209997)
                  ·
                    refine ⟨1336620952492655671578749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3564322539980415124209997 1336620952492655671578749)
                    ·
                      rfl

theorem cell22_3904590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_3904590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904590 prefixEnd_3904590 := by exact prefixLift 3904590
  have htrace : WordTrace (prefixWord ++ tailWord_3904590) baseStart_3904590 baseEnd_3904590 := by
    simpa [prefixWord, tailWord_3904590, baseEnd_3904590] using wordTrace_append hprefix tailTrace_3904590
  have hstable : (prefixWord ++ tailWord_3904590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904590).length < 2 ^ (prefixWord ++ tailWord_3904590).sum := by decide
  have hdescent : baseEnd_3904590 < baseStart_3904590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904682 : List Nat := [3, 1, 5, 1, 1, 1, 3, 2, 5]
def baseStart_3904682 : Nat := 118140960795 + 3904682 * 2 ^ 59
def prefixEnd_3904682 : Nat := 4983230072969 + 3 ^ 40 * 3904682 * 2
def baseEnd_3904682 : Nat := 445550815324266032759489

theorem tailTrace_3904682 : CollatzResearch.WordTrace tailWord_3904682 prefixEnd_3904682 445550815324266032759489 := by
  unfold tailWord_3904682
  simp only [CollatzResearch.WordTrace]
  refine ⟨35603863110002863859687075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94943634960007636959165533 35603863110002863859687075)
  ·
    refine ⟨53405794665004295789530613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35603863110002863859687075 53405794665004295789530613)
    ·
      refine ⟨5006793249844152730268495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53405794665004295789530613 5006793249844152730268495)
      ·
        refine ⟨7510189874766229095402743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5006793249844152730268495 7510189874766229095402743)
        ·
          refine ⟨11265284812149343643104115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7510189874766229095402743 11265284812149343643104115)
          ·
            refine ⟨16897927218224015464656173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11265284812149343643104115 16897927218224015464656173)
            ·
              refine ⟨6336722706834005799246065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16897927218224015464656173 6336722706834005799246065)
              ·
                refine ⟨4752542030125504349434549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6336722706834005799246065 4752542030125504349434549)
                ·
                  refine ⟨445550815324266032759489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4752542030125504349434549 445550815324266032759489)
                  ·
                    rfl

theorem cell22_3904682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_3904682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904682 prefixEnd_3904682 := by exact prefixLift 3904682
  have htrace : WordTrace (prefixWord ++ tailWord_3904682) baseStart_3904682 baseEnd_3904682 := by
    simpa [prefixWord, tailWord_3904682, baseEnd_3904682] using wordTrace_append hprefix tailTrace_3904682
  have hstable : (prefixWord ++ tailWord_3904682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904682).length < 2 ^ (prefixWord ++ tailWord_3904682).sum := by decide
  have hdescent : baseEnd_3904682 < baseStart_3904682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904804 : List Nat := [2, 3, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_3904804 : Nat := 118140960795 + 3904804 * 2 ^ 59
def prefixEnd_3904804 : Nat := 4983230072969 + 3 ^ 40 * 3904804 * 2
def baseEnd_3904804 : Nat := 1336694209066030446728093

theorem tailTrace_3904804 : CollatzResearch.WordTrace tailWord_3904804 prefixEnd_3904804 1336694209066030446728093 := by
  unfold tailWord_3904804
  simp only [CollatzResearch.WordTrace]
  refine ⟨71209951072784735137344733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94946601430379646849792977 71209951072784735137344733)
  ·
    refine ⟨26703731652294275676504275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71209951072784735137344733 26703731652294275676504275)
    ·
      refine ⟨40055597478441413514756413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26703731652294275676504275 40055597478441413514756413)
      ·
        refine ⟨15020849054415530068033655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40055597478441413514756413 15020849054415530068033655)
        ·
          refine ⟨22531273581623295102050483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15020849054415530068033655 22531273581623295102050483)
          ·
            refine ⟨33796910372434942653075725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22531273581623295102050483 33796910372434942653075725)
            ·
              refine ⟨12673841389663103494903397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33796910372434942653075725 12673841389663103494903397)
              ·
                refine ⟨2376345260561831905294387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12673841389663103494903397 2376345260561831905294387)
                ·
                  refine ⟨3564517890842747857941581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376345260561831905294387 3564517890842747857941581)
                  ·
                    refine ⟨1336694209066030446728093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3564517890842747857941581 1336694209066030446728093)
                    ·
                      rfl

theorem cell22_3904804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_3904804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904804 prefixEnd_3904804 := by exact prefixLift 3904804
  have htrace : WordTrace (prefixWord ++ tailWord_3904804) baseStart_3904804 baseEnd_3904804 := by
    simpa [prefixWord, tailWord_3904804, baseEnd_3904804] using wordTrace_append hprefix tailTrace_3904804
  have hstable : (prefixWord ++ tailWord_3904804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904804).length < 2 ^ (prefixWord ++ tailWord_3904804).sum := by decide
  have hdescent : baseEnd_3904804 < baseStart_3904804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904843 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 2, 9]
def baseStart_3904843 : Nat := 118140960795 + 3904843 * 2 ^ 59
def prefixEnd_3904843 : Nat := 4983230072969 + 3 ^ 40 * 3904843 * 2
def baseEnd_3904843 : Nat := 1336707559563047345002973

theorem tailTrace_3904843 : CollatzResearch.WordTrace tailWord_3904843 prefixEnd_3904843 1336707559563047345002973 := by
  unfold tailWord_3904843
  simp only [CollatzResearch.WordTrace]
  refine ⟨142421324592428179935359183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94947549728285453290239455 142421324592428179935359183)
  ·
    refine ⟨213631986888642269903038775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142421324592428179935359183 213631986888642269903038775)
    ·
      refine ⟨320447980332963404854558163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213631986888642269903038775 320447980332963404854558163)
      ·
        refine ⟨480671970499445107281837245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320447980332963404854558163 480671970499445107281837245)
        ·
          refine ⟨180251988937291915230688967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480671970499445107281837245 180251988937291915230688967)
          ·
            refine ⟨270377983405937872846033451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180251988937291915230688967 270377983405937872846033451)
            ·
              refine ⟨405566975108906809269050177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270377983405937872846033451 405566975108906809269050177)
              ·
                refine ⟨304175231331680106951787633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405566975108906809269050177 304175231331680106951787633)
                ·
                  refine ⟨228131423498760080213840725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304175231331680106951787633 228131423498760080213840725)
                  ·
                    refine ⟨1336707559563047345002973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 228131423498760080213840725 1336707559563047345002973)
                    ·
                      rfl

theorem cell22_3904843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_3904843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904843 prefixEnd_3904843 := by exact prefixLift 3904843
  have htrace : WordTrace (prefixWord ++ tailWord_3904843) baseStart_3904843 baseEnd_3904843 := by
    simpa [prefixWord, tailWord_3904843, baseEnd_3904843] using wordTrace_append hprefix tailTrace_3904843
  have hstable : (prefixWord ++ tailWord_3904843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904843).length < 2 ^ (prefixWord ++ tailWord_3904843).sum := by decide
  have hdescent : baseEnd_3904843 < baseStart_3904843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904877 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_3904877 : Nat := 118140960795 + 3904877 * 2 ^ 59
def prefixEnd_3904877 : Nat := 4983230072969 + 3 ^ 40 * 3904877 * 2
def baseEnd_3904877 : Nat := 1336719198457882589652869

theorem tailTrace_3904877 : CollatzResearch.WordTrace tailWord_3904877 prefixEnd_3904877 1336719198457882589652869 := by
  unfold tailWord_3904877
  simp only [CollatzResearch.WordTrace]
  refine ⟨142422564674305003742096885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94948376449536669161397923 142422564674305003742096885)
  ·
    refine ⟨13352115438216094100821583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142422564674305003742096885 13352115438216094100821583)
    ·
      refine ⟨20028173157324141151232375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13352115438216094100821583 20028173157324141151232375)
      ·
        refine ⟨30042259735986211726848563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20028173157324141151232375 30042259735986211726848563)
        ·
          refine ⟨45063389603979317590272845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30042259735986211726848563 45063389603979317590272845)
          ·
            refine ⟨16898771101492244096352317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45063389603979317590272845 16898771101492244096352317)
            ·
              refine ⟨6337039163059591536132119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16898771101492244096352317 6337039163059591536132119)
              ·
                refine ⟨9505558744589387304198179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6337039163059591536132119 9505558744589387304198179)
                ·
                  refine ⟨14258338116884080956297269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9505558744589387304198179 14258338116884080956297269)
                  ·
                    refine ⟨1336719198457882589652869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14258338116884080956297269 1336719198457882589652869)
                    ·
                      rfl

theorem cell22_3904877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_3904877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904877 prefixEnd_3904877 := by exact prefixLift 3904877
  have htrace : WordTrace (prefixWord ++ tailWord_3904877) baseStart_3904877 baseEnd_3904877 := by
    simpa [prefixWord, tailWord_3904877, baseEnd_3904877] using wordTrace_append hprefix tailTrace_3904877
  have hstable : (prefixWord ++ tailWord_3904877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904877).length < 2 ^ (prefixWord ++ tailWord_3904877).sum := by decide
  have hdescent : baseEnd_3904877 < baseStart_3904877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904924 : List Nat := [2, 2, 3, 4, 1, 1, 2, 7]
def baseStart_3904924 : Nat := 118140960795 + 3904924 * 2 ^ 59
def prefixEnd_3904924 : Nat := 4983230072969 + 3 ^ 40 * 3904924 * 2
def baseEnd_3904924 : Nat := 148526143057598903747525

theorem tailTrace_3904924 : CollatzResearch.WordTrace tailWord_3904924 prefixEnd_3904924 148526143057598903747525 := by
  unfold tailWord_3904924
  simp only [CollatzResearch.WordTrace]
  refine ⟨71212139452567365384528913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94949519270089820512705217 71212139452567365384528913)
  ·
    refine ⟨53409104589425524038396685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71212139452567365384528913 53409104589425524038396685)
    ·
      refine ⟨20028414221034571514398757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53409104589425524038396685 20028414221034571514398757)
      ·
        refine ⟨3755327666443982158949767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20028414221034571514398757 3755327666443982158949767)
        ·
          refine ⟨5632991499665973238424651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755327666443982158949767 5632991499665973238424651)
          ·
            refine ⟨8449487249498959857636977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632991499665973238424651 8449487249498959857636977)
            ·
              refine ⟨6337115437124219893227733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8449487249498959857636977 6337115437124219893227733)
              ·
                refine ⟨148526143057598903747525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6337115437124219893227733 148526143057598903747525)
                ·
                  rfl

theorem cell22_3904924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 7].length) (baseStart_3904924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904924 prefixEnd_3904924 := by exact prefixLift 3904924
  have htrace : WordTrace (prefixWord ++ tailWord_3904924) baseStart_3904924 baseEnd_3904924 := by
    simpa [prefixWord, tailWord_3904924, baseEnd_3904924] using wordTrace_append hprefix tailTrace_3904924
  have hstable : (prefixWord ++ tailWord_3904924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904924).length < 2 ^ (prefixWord ++ tailWord_3904924).sum := by decide
  have hdescent : baseEnd_3904924 < baseStart_3904924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904962 : List Nat := [3, 5, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3904962 : Nat := 118140960795 + 3904962 * 2 ^ 59
def prefixEnd_3904962 : Nat := 4983230072969 + 3 ^ 40 * 3904962 * 2
def baseEnd_3904962 : Nat := 1336748295694970701277609

theorem tailTrace_3904962 : CollatzResearch.WordTrace tailWord_3904962 prefixEnd_3904962 1336748295694970701277609 := by
  unfold tailWord_3904962
  simp only [CollatzResearch.WordTrace]
  refine ⟨35606416219749265814735285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94950443252664708839294093 35606416219749265814735285)
  ·
    refine ⟨3338101520601493670131433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35606416219749265814735285 3338101520601493670131433)
    ·
      refine ⟨2503576140451120252598575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3338101520601493670131433 2503576140451120252598575)
      ·
        refine ⟨3755364210676680378897863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503576140451120252598575 3755364210676680378897863)
        ·
          refine ⟨5633046316015020568346795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755364210676680378897863 5633046316015020568346795)
          ·
            refine ⟨8449569474022530852520193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633046316015020568346795 8449569474022530852520193)
            ·
              refine ⟨6337177105516898139390145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8449569474022530852520193 6337177105516898139390145)
              ·
                refine ⟨4752882829137673604542609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6337177105516898139390145 4752882829137673604542609)
                ·
                  refine ⟨3564662121853255203406957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4752882829137673604542609 3564662121853255203406957)
                  ·
                    refine ⟨1336748295694970701277609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3564662121853255203406957 1336748295694970701277609)
                    ·
                      rfl

theorem cell22_3904962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3904962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904962 prefixEnd_3904962 := by exact prefixLift 3904962
  have htrace : WordTrace (prefixWord ++ tailWord_3904962) baseStart_3904962 baseEnd_3904962 := by
    simpa [prefixWord, tailWord_3904962, baseEnd_3904962] using wordTrace_append hprefix tailTrace_3904962
  have hstable : (prefixWord ++ tailWord_3904962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904962).length < 2 ^ (prefixWord ++ tailWord_3904962).sum := by decide
  have hdescent : baseEnd_3904962 < baseStart_3904962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904997 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 8]
def baseStart_3904997 : Nat := 118140960795 + 3904997 * 2 ^ 59
def prefixEnd_3904997 : Nat := 4983230072969 + 3 ^ 40 * 3904997 * 2
def baseEnd_3904997 : Nat := 445586758970080758884167

theorem tailTrace_3904997 : CollatzResearch.WordTrace tailWord_3904997 prefixEnd_3904997 445586758970080758884167 := by
  unfold tailWord_3904997
  simp only [CollatzResearch.WordTrace]
  refine ⟨142426941433870264236465245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94951294289246842824310163 142426941433870264236465245)
  ·
    refine ⟨53410103037701349088674467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142426941433870264236465245 53410103037701349088674467)
    ·
      refine ⟨80115154556552023633011701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53410103037701349088674467 80115154556552023633011701)
      ·
        refine ⟨7510795739676752215594847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80115154556552023633011701 7510795739676752215594847)
        ·
          refine ⟨11266193609515128323392271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7510795739676752215594847 11266193609515128323392271)
          ·
            refine ⟨16899290414272692485088407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11266193609515128323392271 16899290414272692485088407)
            ·
              refine ⟨25348935621409038727632611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16899290414272692485088407 25348935621409038727632611)
              ·
                refine ⟨38023403432113558091448917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25348935621409038727632611 38023403432113558091448917)
                ·
                  refine ⟨445586758970080758884167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38023403432113558091448917 445586758970080758884167)
                  ·
                    rfl

theorem cell22_3904997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_3904997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3904997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3904997 prefixEnd_3904997 := by exact prefixLift 3904997
  have htrace : WordTrace (prefixWord ++ tailWord_3904997) baseStart_3904997 baseEnd_3904997 := by
    simpa [prefixWord, tailWord_3904997, baseEnd_3904997] using wordTrace_append hprefix tailTrace_3904997
  have hstable : (prefixWord ++ tailWord_3904997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904997).length < 2 ^ (prefixWord ++ tailWord_3904997).sum := by decide
  have hdescent : baseEnd_3904997 < baseStart_3904997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905016 : List Nat := [2, 1, 2, 1, 1, 7, 2, 1, 1, 4]
def baseStart_3905016 : Nat := 118140960795 + 3905016 * 2 ^ 59
def prefixEnd_3905016 : Nat := 4983230072969 + 3 ^ 40 * 3905016 * 2
def baseEnd_3905016 : Nat := 1336766780998532560427443

theorem tailTrace_3905016 : CollatzResearch.WordTrace tailWord_3905016 prefixEnd_3905016 1336766780998532560427443 := by
  unfold tailWord_3905016
  simp only [CollatzResearch.WordTrace]
  refine ⟨71213817210400715240703451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94951756280534286987604601 71213817210400715240703451)
  ·
    refine ⟨106820725815601072861055177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71213817210400715240703451 106820725815601072861055177)
    ·
      refine ⟨80115544361700804645791383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106820725815601072861055177 80115544361700804645791383)
      ·
        refine ⟨120173316542551206968687075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80115544361700804645791383 120173316542551206968687075)
        ·
          refine ⟨180259974813826810453030613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120173316542551206968687075 180259974813826810453030613)
          ·
            refine ⟨4224843159699065869992905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 180259974813826810453030613 4224843159699065869992905)
            ·
              refine ⟨3168632369774299402494679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4224843159699065869992905 3168632369774299402494679)
              ·
                refine ⟨4752948554661449103742019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168632369774299402494679 4752948554661449103742019)
                ·
                  refine ⟨7129422831992173655613029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752948554661449103742019 7129422831992173655613029)
                  ·
                    refine ⟨1336766780998532560427443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7129422831992173655613029 1336766780998532560427443)
                    ·
                      rfl

theorem cell22_3905016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_3905016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905016 prefixEnd_3905016 := by exact prefixLift 3905016
  have htrace : WordTrace (prefixWord ++ tailWord_3905016) baseStart_3905016 baseEnd_3905016 := by
    simpa [prefixWord, tailWord_3905016, baseEnd_3905016] using wordTrace_append hprefix tailTrace_3905016
  have hstable : (prefixWord ++ tailWord_3905016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905016).length < 2 ^ (prefixWord ++ tailWord_3905016).sum := by decide
  have hdescent : baseEnd_3905016 < baseStart_3905016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905087 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 7]
def baseStart_3905087 : Nat := 118140960795 + 3905087 * 2 ^ 59
def prefixEnd_3905087 : Nat := 4983230072969 + 3 ^ 40 * 3905087 * 2
def baseEnd_3905087 : Nat := 445597028583170680634075

theorem tailTrace_3905087 : CollatzResearch.WordTrace tailWord_3905087 prefixEnd_3905087 445597028583170680634075 := by
  unfold tailWord_3905087
  simp only [CollatzResearch.WordTrace]
  refine ⟨142430224003544209607241515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94953482669029473071494343 142430224003544209607241515)
  ·
    refine ⟨213645336005316314410862273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142430224003544209607241515 213645336005316314410862273)
    ·
      refine ⟨160234002003987235808146705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213645336005316314410862273 160234002003987235808146705)
      ·
        refine ⟨120175501502990426856110029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160234002003987235808146705 120175501502990426856110029)
        ·
          refine ⟨45065813063621410071041261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120175501502990426856110029 45065813063621410071041261)
          ·
            refine ⟨16899679898858028776640473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45065813063621410071041261 16899679898858028776640473)
            ·
              refine ⟨12674759924143521582480355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16899679898858028776640473 12674759924143521582480355)
              ·
                refine ⟨19012139886215282373720533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12674759924143521582480355 19012139886215282373720533)
                ·
                  refine ⟨445597028583170680634075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19012139886215282373720533 445597028583170680634075)
                  ·
                    rfl

theorem cell22_3905087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 7].length) (baseStart_3905087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905087 prefixEnd_3905087 := by exact prefixLift 3905087
  have htrace : WordTrace (prefixWord ++ tailWord_3905087) baseStart_3905087 baseEnd_3905087 := by
    simpa [prefixWord, tailWord_3905087, baseEnd_3905087] using wordTrace_append hprefix tailTrace_3905087
  have hstable : (prefixWord ++ tailWord_3905087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905087).length < 2 ^ (prefixWord ++ tailWord_3905087).sum := by decide
  have hdescent : baseEnd_3905087 < baseStart_3905087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905102 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_3905102 : Nat := 118140960795 + 3905102 * 2 ^ 59
def prefixEnd_3905102 : Nat := 4983230072969 + 3 ^ 40 * 3905102 * 2
def baseEnd_3905102 : Nat := 1336796220556057002777179

theorem tailTrace_3905102 : CollatzResearch.WordTrace tailWord_3905102 prefixEnd_3905102 1336796220556057002777179 := by
  unfold tailWord_3905102
  simp only [CollatzResearch.WordTrace]
  refine ⟨17803846387311233396129695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94953847398993244779358373 17803846387311233396129695)
  ·
    refine ⟨26705769580966850094194543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17803846387311233396129695 26705769580966850094194543)
    ·
      refine ⟨40058654371450275141291815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26705769580966850094194543 40058654371450275141291815)
      ·
        refine ⟨60087981557175412711937723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40058654371450275141291815 60087981557175412711937723)
        ·
          refine ⟨90131972335763119067906585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60087981557175412711937723 90131972335763119067906585)
          ·
            refine ⟨67598979251822339300929939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90131972335763119067906585 67598979251822339300929939)
            ·
              refine ⟨101398468877733508951394909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67598979251822339300929939 101398468877733508951394909)
              ·
                refine ⟨38024425829150065856773091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101398468877733508951394909 38024425829150065856773091)
                ·
                  refine ⟨57036638743725098785159637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38024425829150065856773091 57036638743725098785159637)
                  ·
                    refine ⟨1336796220556057002777179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57036638743725098785159637 1336796220556057002777179)
                    ·
                      rfl

theorem cell22_3905102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_3905102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905102 prefixEnd_3905102 := by exact prefixLift 3905102
  have htrace : WordTrace (prefixWord ++ tailWord_3905102) baseStart_3905102 baseEnd_3905102 := by
    simpa [prefixWord, tailWord_3905102, baseEnd_3905102] using wordTrace_append hprefix tailTrace_3905102
  have hstable : (prefixWord ++ tailWord_3905102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905102).length < 2 ^ (prefixWord ++ tailWord_3905102).sum := by decide
  have hdescent : baseEnd_3905102 < baseStart_3905102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905142 : List Nat := [5, 1, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_3905142 : Nat := 118140960795 + 3905142 * 2 ^ 59
def prefixEnd_3905142 : Nat := 4983230072969 + 3 ^ 40 * 3905142 * 2
def baseEnd_3905142 : Nat := 1336809913373510231777057

theorem tailTrace_3905142 : CollatzResearch.WordTrace tailWord_3905142 prefixEnd_3905142 1336809913373510231777057 := by
  unfold tailWord_3905142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8902014376146559625030855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94954820012229969333662453 8902014376146559625030855)
  ·
    refine ⟨13353021564219839437546283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8902014376146559625030855 13353021564219839437546283)
    ·
      refine ⟨20029532346329759156319425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13353021564219839437546283 20029532346329759156319425)
      ·
        refine ⟨15022149259747319367239569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20029532346329759156319425 15022149259747319367239569)
        ·
          refine ⟨11266611944810489525429677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15022149259747319367239569 11266611944810489525429677)
          ·
            refine ⟨4224979479303933572036129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11266611944810489525429677 4224979479303933572036129)
            ·
              refine ⟨3168734609477950179027097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4224979479303933572036129 3168734609477950179027097)
              ·
                refine ⟨2376550957108462634270323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3168734609477950179027097 2376550957108462634270323)
                ·
                  refine ⟨3564826435662693951405485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376550957108462634270323 3564826435662693951405485)
                  ·
                    refine ⟨1336809913373510231777057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3564826435662693951405485 1336809913373510231777057)
                    ·
                      rfl

theorem cell22_3905142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_3905142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905142 prefixEnd_3905142 := by exact prefixLift 3905142
  have htrace : WordTrace (prefixWord ++ tailWord_3905142) baseStart_3905142 baseEnd_3905142 := by
    simpa [prefixWord, tailWord_3905142, baseEnd_3905142] using wordTrace_append hprefix tailTrace_3905142
  have hstable : (prefixWord ++ tailWord_3905142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905142).length < 2 ^ (prefixWord ++ tailWord_3905142).sum := by decide
  have hdescent : baseEnd_3905142 < baseStart_3905142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905147 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 3, 5]
def baseStart_3905147 : Nat := 118140960795 + 3905147 * 2 ^ 59
def prefixEnd_3905147 : Nat := 4983230072969 + 3 ^ 40 * 3905147 * 2
def baseEnd_3905147 : Nat := 1336811624975691885402041

theorem tailTrace_3905147 : CollatzResearch.WordTrace tailWord_3905147 prefixEnd_3905147 1336811624975691885402041 := by
  unfold tailWord_3905147
  simp only [CollatzResearch.WordTrace]
  refine ⟨142432412383326839854425695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94954941588884559902950463 142432412383326839854425695)
  ·
    refine ⟨213648618574990259781638543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142432412383326839854425695 213648618574990259781638543)
    ·
      refine ⟨320472927862485389672457815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213648618574990259781638543 320472927862485389672457815)
      ·
        refine ⟨480709391793728084508686723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320472927862485389672457815 480709391793728084508686723)
        ·
          refine ⟨721064087690592126763030085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480709391793728084508686723 721064087690592126763030085)
          ·
            refine ⟨135199516441986023768068141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 721064087690592126763030085 135199516441986023768068141)
            ·
              refine ⟨50699818665744758913025553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135199516441986023768068141 50699818665744758913025553)
              ·
                refine ⟨38024863999308569184769165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50699818665744758913025553 38024863999308569184769165)
                ·
                  refine ⟨14259323999740713444288437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38024863999308569184769165 14259323999740713444288437)
                  ·
                    refine ⟨1336811624975691885402041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14259323999740713444288437 1336811624975691885402041)
                    ·
                      rfl

theorem cell22_3905147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_3905147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905147 prefixEnd_3905147 := by exact prefixLift 3905147
  have htrace : WordTrace (prefixWord ++ tailWord_3905147) baseStart_3905147 baseEnd_3905147 := by
    simpa [prefixWord, tailWord_3905147, baseEnd_3905147] using wordTrace_append hprefix tailTrace_3905147
  have hstable : (prefixWord ++ tailWord_3905147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905147).length < 2 ^ (prefixWord ++ tailWord_3905147).sum := by decide
  have hdescent : baseEnd_3905147 < baseStart_3905147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905164 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_3905164 : Nat := 118140960795 + 3905164 * 2 ^ 59
def prefixEnd_3905164 : Nat := 4983230072969 + 3 ^ 40 * 3905164 * 2
def baseEnd_3905164 : Nat := 1336817444423109507726989

theorem tailTrace_3905164 : CollatzResearch.WordTrace tailWord_3905164 prefixEnd_3905164 1336817444423109507726989 := by
  unfold tailWord_3905164
  simp only [CollatzResearch.WordTrace]
  refine ⟨71216516212132625878897273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94955354949510167838529697 71216516212132625878897273)
  ·
    refine ⟨53412387159099469409172955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71216516212132625878897273 53412387159099469409172955)
    ·
      refine ⟨80118580738649204113759433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53412387159099469409172955 80118580738649204113759433)
      ·
        refine ⟨60088935553986903085319575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80118580738649204113759433 60088935553986903085319575)
        ·
          refine ⟨90133403330980354627979363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60088935553986903085319575 90133403330980354627979363)
          ·
            refine ⟨135200104996470531941969045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90133403330980354627979363 135200104996470531941969045)
            ·
              refine ⟨6337504921709556184779799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135200104996470531941969045 6337504921709556184779799)
              ·
                refine ⟨9506257382564334277169699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6337504921709556184779799 9506257382564334277169699)
                ·
                  refine ⟨14259386073846501415754549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9506257382564334277169699 14259386073846501415754549)
                  ·
                    refine ⟨1336817444423109507726989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14259386073846501415754549 1336817444423109507726989)
                    ·
                      rfl

theorem cell22_3905164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_3905164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905164 prefixEnd_3905164 := by exact prefixLift 3905164
  have htrace : WordTrace (prefixWord ++ tailWord_3905164) baseStart_3905164 baseEnd_3905164 := by
    simpa [prefixWord, tailWord_3905164, baseEnd_3905164] using wordTrace_append hprefix tailTrace_3905164
  have hstable : (prefixWord ++ tailWord_3905164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905164).length < 2 ^ (prefixWord ++ tailWord_3905164).sum := by decide
  have hdescent : baseEnd_3905164 < baseStart_3905164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905228 : List Nat := [2, 2, 1, 5, 2, 2, 2, 6]
def baseStart_3905228 : Nat := 118140960795 + 3905228 * 2 ^ 59
def prefixEnd_3905228 : Nat := 4983230072969 + 3 ^ 40 * 3905228 * 2
def baseEnd_3905228 : Nat := 148537705881226074902977

theorem tailTrace_3905228 : CollatzResearch.WordTrace tailWord_3905228 prefixEnd_3905228 148537705881226074902977 := by
  unfold tailWord_3905228
  simp only [CollatzResearch.WordTrace]
  refine ⟨71217683348016695344062169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94956911130688927125416225 71217683348016695344062169)
  ·
    refine ⟨53413262511012521508046627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71217683348016695344062169 53413262511012521508046627)
    ·
      refine ⟨80119893766518782262069941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53413262511012521508046627 80119893766518782262069941)
      ·
        refine ⟨7511240040611135837069057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80119893766518782262069941 7511240040611135837069057)
        ·
          refine ⟨5633430030458351877801793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7511240040611135837069057 5633430030458351877801793)
          ·
            refine ⟨4225072522843763908351345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5633430030458351877801793 4225072522843763908351345)
            ·
              refine ⟨3168804392132822931263509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4225072522843763908351345 3168804392132822931263509)
              ·
                refine ⟨148537705881226074902977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3168804392132822931263509 148537705881226074902977)
                ·
                  rfl

theorem cell22_3905228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 6].length) (baseStart_3905228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905228 prefixEnd_3905228 := by exact prefixLift 3905228
  have htrace : WordTrace (prefixWord ++ tailWord_3905228) baseStart_3905228 baseEnd_3905228 := by
    simpa [prefixWord, tailWord_3905228, baseEnd_3905228] using wordTrace_append hprefix tailTrace_3905228
  have hstable : (prefixWord ++ tailWord_3905228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905228).length < 2 ^ (prefixWord ++ tailWord_3905228).sum := by decide
  have hdescent : baseEnd_3905228 < baseStart_3905228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
