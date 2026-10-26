import V185TrunkScan22Chunk390

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3487703 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 1, 7]
def baseStart_3487703 : Nat := 118140960795 + 3487703 * 2 ^ 59
def prefixEnd_3487703 : Nat := 4983230072969 + 3 ^ 40 * 3487703 * 2
def baseEnd_3487703 : Nat := 1193912012752048719781901

theorem tailTrace_3487703 : CollatzResearch.WordTrace tailWord_3487703 prefixEnd_3487703 1193912012752048719781901 := by
  unfold tailWord_3487703
  simp only [CollatzResearch.WordTrace]
  refine ⟨127206978883655158095211763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84804652589103438730141175 127206978883655158095211763)
  ·
    refine ⟨190810468325482737142817645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127206978883655158095211763 190810468325482737142817645)
    ·
      refine ⟨71553925622056026428556617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190810468325482737142817645 71553925622056026428556617)
      ·
        refine ⟨53665444216542019821417463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71553925622056026428556617 53665444216542019821417463)
        ·
          refine ⟨80498166324813029732126195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53665444216542019821417463 80498166324813029732126195)
          ·
            refine ⟨120747249487219544598189293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80498166324813029732126195 120747249487219544598189293)
            ·
              refine ⟨45280218557707329224320985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120747249487219544598189293 45280218557707329224320985)
              ·
                refine ⟨33960163918280496918240739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45280218557707329224320985 33960163918280496918240739)
                ·
                  refine ⟨50940245877420745377361109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33960163918280496918240739 50940245877420745377361109)
                  ·
                    refine ⟨1193912012752048719781901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50940245877420745377361109 1193912012752048719781901)
                    ·
                      rfl

theorem cell22_3487703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_3487703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487703 prefixEnd_3487703 := by exact prefixLift 3487703
  have htrace : WordTrace (prefixWord ++ tailWord_3487703) baseStart_3487703 baseEnd_3487703 := by
    simpa [prefixWord, tailWord_3487703, baseEnd_3487703] using wordTrace_append hprefix tailTrace_3487703
  have hstable : (prefixWord ++ tailWord_3487703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487703).length < 2 ^ (prefixWord ++ tailWord_3487703).sum := by decide
  have hdescent : baseEnd_3487703 < baseStart_3487703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487752 : List Nat := [2, 1, 3, 2, 1, 2, 4, 2, 1, 4]
def baseStart_3487752 : Nat := 118140960795 + 3487752 * 2 ^ 59
def prefixEnd_3487752 : Nat := 4983230072969 + 3 ^ 40 * 3487752 * 2
def baseEnd_3487752 : Nat := 1193928786453428925306751

theorem tailTrace_3487752 : CollatzResearch.WordTrace tailWord_3487752 prefixEnd_3487752 1193928786453428925306751 := by
  unfold tailWord_3487752
  simp only [CollatzResearch.WordTrace]
  refine ⟨63604383030238819731872755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84805844040318426309163673 63604383030238819731872755)
  ·
    refine ⟨95406574545358229597809133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63604383030238819731872755 95406574545358229597809133)
    ·
      refine ⟨35777465454509336099178425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95406574545358229597809133 35777465454509336099178425)
      ·
        refine ⟨26833099090882002074383819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35777465454509336099178425 26833099090882002074383819)
        ·
          refine ⟨40249648636323003111575729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26833099090882002074383819 40249648636323003111575729)
          ·
            refine ⟨30187236477242252333681797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40249648636323003111575729 30187236477242252333681797)
            ·
              refine ⟨5660106839482922312565337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30187236477242252333681797 5660106839482922312565337)
              ·
                refine ⟨4245080129612191734424003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5660106839482922312565337 4245080129612191734424003)
                ·
                  refine ⟨6367620194418287601636005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4245080129612191734424003 6367620194418287601636005)
                  ·
                    refine ⟨1193928786453428925306751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6367620194418287601636005 1193928786453428925306751)
                    ·
                      rfl

theorem cell22_3487752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_3487752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487752 prefixEnd_3487752 := by exact prefixLift 3487752
  have htrace : WordTrace (prefixWord ++ tailWord_3487752) baseStart_3487752 baseEnd_3487752 := by
    simpa [prefixWord, tailWord_3487752, baseEnd_3487752] using wordTrace_append hprefix tailTrace_3487752
  have hstable : (prefixWord ++ tailWord_3487752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487752).length < 2 ^ (prefixWord ++ tailWord_3487752).sum := by decide
  have hdescent : baseEnd_3487752 < baseStart_3487752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487799 : List Nat := [1, 1, 3, 1, 2, 2, 6, 1, 2, 3]
def baseStart_3487799 : Nat := 118140960795 + 3487799 * 2 ^ 59
def prefixEnd_3487799 : Nat := 4983230072969 + 3 ^ 40 * 3487799 * 2
def baseEnd_3487799 : Nat := 1193944875513936469381607

theorem tailTrace_3487799 : CollatzResearch.WordTrace tailWord_3487799 prefixEnd_3487799 1193944875513936469381607 := by
  unfold tailWord_3487799
  simp only [CollatzResearch.WordTrace]
  refine ⟨127210480291307366490706451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84806986860871577660470967 127210480291307366490706451)
  ·
    refine ⟨190815720436961049736059677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127210480291307366490706451 190815720436961049736059677)
    ·
      refine ⟨71555895163860393651022379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190815720436961049736059677 71555895163860393651022379)
      ·
        refine ⟨107333842745790590476533569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71555895163860393651022379 107333842745790590476533569)
        ·
          refine ⟨80500382059342942857400177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107333842745790590476533569 80500382059342942857400177)
          ·
            refine ⟨60375286544507207143050133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80500382059342942857400177 60375286544507207143050133)
            ·
              refine ⟨2830091556773775334830475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60375286544507207143050133 2830091556773775334830475)
              ·
                refine ⟨4245137335160663002245713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830091556773775334830475 4245137335160663002245713)
                ·
                  refine ⟨3183853001370497251684285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4245137335160663002245713 3183853001370497251684285)
                  ·
                    refine ⟨1193944875513936469381607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3183853001370497251684285 1193944875513936469381607)
                    ·
                      rfl

theorem cell22_3487799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_3487799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487799 prefixEnd_3487799 := by exact prefixLift 3487799
  have htrace : WordTrace (prefixWord ++ tailWord_3487799) baseStart_3487799 baseEnd_3487799 := by
    simpa [prefixWord, tailWord_3487799, baseEnd_3487799] using wordTrace_append hprefix tailTrace_3487799
  have hstable : (prefixWord ++ tailWord_3487799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487799).length < 2 ^ (prefixWord ++ tailWord_3487799).sum := by decide
  have hdescent : baseEnd_3487799 < baseStart_3487799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487855 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 1, 7]
def baseStart_3487855 : Nat := 118140960795 + 3487855 * 2 ^ 59
def prefixEnd_3487855 : Nat := 4983230072969 + 3 ^ 40 * 3487855 * 2
def baseEnd_3487855 : Nat := 1193964045458370989981435

theorem tailTrace_3487855 : CollatzResearch.WordTrace tailWord_3487855 prefixEnd_3487855 1193964045458370989981435 := by
  unfold tailWord_3487855
  simp only [CollatzResearch.WordTrace]
  refine ⟨127212522779104488054745019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84808348519402992036496679 127212522779104488054745019)
  ·
    refine ⟨190818784168656732082117529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127212522779104488054745019 190818784168656732082117529)
    ·
      refine ⟨143114088126492549061588147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190818784168656732082117529 143114088126492549061588147)
      ·
        refine ⟨214671132189738823592382221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143114088126492549061588147 214671132189738823592382221)
        ·
          refine ⟨80501674571152058847143333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214671132189738823592382221 80501674571152058847143333)
          ·
            refine ⟨15094063982091011033839375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80501674571152058847143333 15094063982091011033839375)
            ·
              refine ⟨22641095973136516550759063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15094063982091011033839375 22641095973136516550759063)
              ·
                refine ⟨33961643959704774826138595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22641095973136516550759063 33961643959704774826138595)
                ·
                  refine ⟨50942465939557162239207893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33961643959704774826138595 50942465939557162239207893)
                  ·
                    refine ⟨1193964045458370989981435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50942465939557162239207893 1193964045458370989981435)
                    ·
                      rfl

theorem cell22_3487855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_3487855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487855 prefixEnd_3487855 := by exact prefixLift 3487855
  have htrace : WordTrace (prefixWord ++ tailWord_3487855) baseStart_3487855 baseEnd_3487855 := by
    simpa [prefixWord, tailWord_3487855, baseEnd_3487855] using wordTrace_append hprefix tailTrace_3487855
  have hstable : (prefixWord ++ tailWord_3487855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487855).length < 2 ^ (prefixWord ++ tailWord_3487855).sum := by decide
  have hdescent : baseEnd_3487855 < baseStart_3487855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487921 : List Nat := [1, 2, 2, 5, 2, 1, 2, 2, 1, 4]
def baseStart_3487921 : Nat := 118140960795 + 3487921 * 2 ^ 59
def prefixEnd_3487921 : Nat := 4983230072969 + 3 ^ 40 * 3487921 * 2
def baseEnd_3487921 : Nat := 1193986638607168817831233

theorem tailTrace_3487921 : CollatzResearch.WordTrace tailWord_3487921 prefixEnd_3487921 1193986638607168817831233 := by
  unfold tailWord_3487921
  simp only [CollatzResearch.WordTrace]
  refine ⟨127214929996865381326647617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84809953331243587551098411 127214929996865381326647617)
  ·
    refine ⟨95411197497649035994985713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127214929996865381326647617 95411197497649035994985713)
    ·
      refine ⟨71558398123236776996239285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95411197497649035994985713 71558398123236776996239285)
      ·
        refine ⟨6708599824053447843397433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71558398123236776996239285 6708599824053447843397433)
        ·
          refine ⟨5031449868040085882548075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6708599824053447843397433 5031449868040085882548075)
          ·
            refine ⟨7547174802060128823822113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5031449868040085882548075 7547174802060128823822113)
            ·
              refine ⟨5660381101545096617866585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7547174802060128823822113 5660381101545096617866585)
              ·
                refine ⟨4245285826158822463399939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5660381101545096617866585 4245285826158822463399939)
                ·
                  refine ⟨6367928739238233695099909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4245285826158822463399939 6367928739238233695099909)
                  ·
                    refine ⟨1193986638607168817831233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6367928739238233695099909 1193986638607168817831233)
                    ·
                      rfl

theorem cell22_3487921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_3487921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487921 prefixEnd_3487921 := by exact prefixLift 3487921
  have htrace : WordTrace (prefixWord ++ tailWord_3487921) baseStart_3487921 baseEnd_3487921 := by
    simpa [prefixWord, tailWord_3487921, baseEnd_3487921] using wordTrace_append hprefix tailTrace_3487921
  have hstable : (prefixWord ++ tailWord_3487921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487921).length < 2 ^ (prefixWord ++ tailWord_3487921).sum := by decide
  have hdescent : baseEnd_3487921 < baseStart_3487921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487936 : List Nat := [2, 1, 1, 2, 5, 3, 1, 3, 4]
def baseStart_3487936 : Nat := 118140960795 + 3487936 * 2 ^ 59
def prefixEnd_3487936 : Nat := 4983230072969 + 3 ^ 40 * 3487936 * 2
def baseEnd_3487936 : Nat := 397997257804571259568729

theorem tailTrace_3487936 : CollatzResearch.WordTrace tailWord_3487936 prefixEnd_3487936 397997257804571259568729 := by
  unfold tailWord_3487936
  simp only [CollatzResearch.WordTrace]
  refine ⟨63607738545905519444221831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84810318061207359258962441 63607738545905519444221831)
  ·
    refine ⟨95411607818858279166332747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63607738545905519444221831 95411607818858279166332747)
    ·
      refine ⟨143117411728287418749499121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95411607818858279166332747 143117411728287418749499121)
      ·
        refine ⟨107338058796215564062124341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143117411728287418749499121 107338058796215564062124341)
        ·
          refine ⟨10062943012145209130824157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107338058796215564062124341 10062943012145209130824157)
          ·
            refine ⟨3773603629554453424059059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10062943012145209130824157 3773603629554453424059059)
            ·
              refine ⟨5660405444331680136088589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3773603629554453424059059 5660405444331680136088589)
              ·
                refine ⟨2122652041624380051033221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5660405444331680136088589 2122652041624380051033221)
                ·
                  refine ⟨397997257804571259568729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2122652041624380051033221 397997257804571259568729)
                  ·
                    rfl

theorem cell22_3487936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 4].length) (baseStart_3487936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487936 prefixEnd_3487936 := by exact prefixLift 3487936
  have htrace : WordTrace (prefixWord ++ tailWord_3487936) baseStart_3487936 baseEnd_3487936 := by
    simpa [prefixWord, tailWord_3487936, baseEnd_3487936] using wordTrace_append hprefix tailTrace_3487936
  have hstable : (prefixWord ++ tailWord_3487936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487936).length < 2 ^ (prefixWord ++ tailWord_3487936).sum := by decide
  have hdescent : baseEnd_3487936 < baseStart_3487936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487938 : List Nat := [3, 5, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3487938 : Nat := 118140960795 + 3487938 * 2 ^ 59
def prefixEnd_3487938 : Nat := 4983230072969 + 3 ^ 40 * 3487938 * 2
def baseEnd_3487938 : Nat := 1193992458054586440156181

theorem tailTrace_3487938 : CollatzResearch.WordTrace tailWord_3487938 prefixEnd_3487938 1193992458054586440156181 := by
  unfold tailWord_3487938
  simp only [CollatzResearch.WordTrace]
  refine ⟨31803887509450948307504117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84810366691869195486677645 31803887509450948307504117)
  ·
    refine ⟨2981614454011026403828511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31803887509450948307504117 2981614454011026403828511)
    ·
      refine ⟨4472421681016539605742767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2981614454011026403828511 4472421681016539605742767)
      ·
        refine ⟨6708632521524809408614151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4472421681016539605742767 6708632521524809408614151)
        ·
          refine ⟨10062948782287214112921227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6708632521524809408614151 10062948782287214112921227)
          ·
            refine ⟨15094423173430821169381841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10062948782287214112921227 15094423173430821169381841)
            ·
              refine ⟨11320817380073115877036381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15094423173430821169381841 11320817380073115877036381)
              ·
                refine ⟨4245306517527418453888643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11320817380073115877036381 4245306517527418453888643)
                ·
                  refine ⟨6367959776291127680832965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4245306517527418453888643 6367959776291127680832965)
                  ·
                    refine ⟨1193992458054586440156181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6367959776291127680832965 1193992458054586440156181)
                    ·
                      rfl

theorem cell22_3487938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3487938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487938 prefixEnd_3487938 := by exact prefixLift 3487938
  have htrace : WordTrace (prefixWord ++ tailWord_3487938) baseStart_3487938 baseEnd_3487938 := by
    simpa [prefixWord, tailWord_3487938, baseEnd_3487938] using wordTrace_append hprefix tailTrace_3487938
  have hstable : (prefixWord ++ tailWord_3487938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487938).length < 2 ^ (prefixWord ++ tailWord_3487938).sum := by decide
  have hdescent : baseEnd_3487938 < baseStart_3487938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488009 : List Nat := [1, 2, 1, 1, 3, 5, 2, 2, 5]
def baseStart_3488009 : Nat := 118140960795 + 3488009 * 2 ^ 59
def prefixEnd_3488009 : Nat := 4983230072969 + 3 ^ 40 * 3488009 * 2
def baseEnd_3488009 : Nat := 398005587601855307210321

theorem tailTrace_3488009 : CollatzResearch.WordTrace tailWord_3488009 prefixEnd_3488009 398005587601855307210321 := by
  unfold tailWord_3488009
  simp only [CollatzResearch.WordTrace]
  refine ⟨127218139620546572355851081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84812093080364381570567387 127218139620546572355851081)
  ·
    refine ⟨95413604715409929266888311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127218139620546572355851081 95413604715409929266888311)
    ·
      refine ⟨143120407073114893900332467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95413604715409929266888311 143120407073114893900332467)
      ·
        refine ⟨214680610609672340850498701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143120407073114893900332467 214680610609672340850498701)
        ·
          refine ⟨80505228978627127818937013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214680610609672340850498701 80505228978627127818937013)
          ·
            refine ⟨7547365216746293233025345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80505228978627127818937013 7547365216746293233025345)
            ·
              refine ⟨5660523912559719924769009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7547365216746293233025345 5660523912559719924769009)
              ·
                refine ⟨4245392934419789943576757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5660523912559719924769009 4245392934419789943576757)
                ·
                  refine ⟨398005587601855307210321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4245392934419789943576757 398005587601855307210321)
                  ·
                    rfl

theorem cell22_3488009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_3488009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488009 prefixEnd_3488009 := by exact prefixLift 3488009
  have htrace : WordTrace (prefixWord ++ tailWord_3488009) baseStart_3488009 baseEnd_3488009 := by
    simpa [prefixWord, tailWord_3488009, baseEnd_3488009] using wordTrace_append hprefix tailTrace_3488009
  have hstable : (prefixWord ++ tailWord_3488009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488009).length < 2 ^ (prefixWord ++ tailWord_3488009).sum := by decide
  have hdescent : baseEnd_3488009 < baseStart_3488009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488056 : List Nat := [2, 1, 2, 1, 3, 1, 6, 1, 1, 4]
def baseStart_3488056 : Nat := 118140960795 + 3488056 * 2 ^ 59
def prefixEnd_3488056 : Nat := 4983230072969 + 3 ^ 40 * 3488056 * 2
def baseEnd_3488056 : Nat := 1194032851866073465705819

theorem tailTrace_3488056 : CollatzResearch.WordTrace tailWord_3488056 prefixEnd_3488056 1194032851866073465705819 := by
  unfold tailWord_3488056
  simp only [CollatzResearch.WordTrace]
  refine ⟨63609926925688149691406011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84813235900917532921874681 63609926925688149691406011)
  ·
    refine ⟨95414890388532224537109017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63609926925688149691406011 95414890388532224537109017)
    ·
      refine ⟨71561167791399168402831763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95414890388532224537109017 71561167791399168402831763)
      ·
        refine ⟨107341751687098752604247645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71561167791399168402831763 107341751687098752604247645)
        ·
          refine ⟨40253156882662032226592867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107341751687098752604247645 40253156882662032226592867)
          ·
            refine ⟨60379735323993048339889301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40253156882662032226592867 60379735323993048339889301)
            ·
              refine ⟨2830300093312174140932311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60379735323993048339889301 2830300093312174140932311)
              ·
                refine ⟨4245450139968261211398467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830300093312174140932311 4245450139968261211398467)
                ·
                  refine ⟨6368175209952391817097701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4245450139968261211398467 6368175209952391817097701)
                  ·
                    refine ⟨1194032851866073465705819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6368175209952391817097701 1194032851866073465705819)
                    ·
                      rfl

theorem cell22_3488056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_3488056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488056 prefixEnd_3488056 := by exact prefixLift 3488056
  have htrace : WordTrace (prefixWord ++ tailWord_3488056) baseStart_3488056 baseEnd_3488056 := by
    simpa [prefixWord, tailWord_3488056, baseEnd_3488056] using wordTrace_append hprefix tailTrace_3488056
  have hstable : (prefixWord ++ tailWord_3488056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488056).length < 2 ^ (prefixWord ++ tailWord_3488056).sum := by decide
  have hdescent : baseEnd_3488056 < baseStart_3488056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488084 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3488084 : Nat := 118140960795 + 3488084 * 2 ^ 59
def prefixEnd_3488084 : Nat := 4983230072969 + 3 ^ 40 * 3488084 * 2
def baseEnd_3488084 : Nat := 1194042436838290726005733

theorem tailTrace_3488084 : CollatzResearch.WordTrace tailWord_3488084 prefixEnd_3488084 1194042436838290726005733 := by
  unfold tailWord_3488084
  simp only [CollatzResearch.WordTrace]
  refine ⟨63610437547637430082415653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84813916730183240109887537 63610437547637430082415653)
  ·
    refine ⟨11926957040182018140452935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63610437547637430082415653 11926957040182018140452935)
    ·
      refine ⟨17890435560273027210679403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11926957040182018140452935 17890435560273027210679403)
      ·
        refine ⟨26835653340409540816019105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17890435560273027210679403 26835653340409540816019105)
        ·
          refine ⟨20126740005307155612014329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26835653340409540816019105 20126740005307155612014329)
          ·
            refine ⟨15095055003980366709010747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20126740005307155612014329 15095055003980366709010747)
            ·
              refine ⟨22642582505970550063516121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15095055003980366709010747 22642582505970550063516121)
              ·
                refine ⟨16981936879477912547637091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22642582505970550063516121 16981936879477912547637091)
                ·
                  refine ⟨25472905319216868821455637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16981936879477912547637091 25472905319216868821455637)
                  ·
                    refine ⟨1194042436838290726005733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25472905319216868821455637 1194042436838290726005733)
                    ·
                      rfl

theorem cell22_3488084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3488084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488084 prefixEnd_3488084 := by exact prefixLift 3488084
  have htrace : WordTrace (prefixWord ++ tailWord_3488084) baseStart_3488084 baseEnd_3488084 := by
    simpa [prefixWord, tailWord_3488084, baseEnd_3488084] using wordTrace_append hprefix tailTrace_3488084
  have hstable : (prefixWord ++ tailWord_3488084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488084).length < 2 ^ (prefixWord ++ tailWord_3488084).sum := by decide
  have hdescent : baseEnd_3488084 < baseStart_3488084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488221 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_3488221 : Nat := 118140960795 + 3488221 * 2 ^ 59
def prefixEnd_3488221 : Nat := 4983230072969 + 3 ^ 40 * 3488221 * 2
def baseEnd_3488221 : Nat := 1194089334738068035330313

theorem tailTrace_3488221 : CollatzResearch.WordTrace tailWord_3488221 prefixEnd_3488221 1194089334738068035330313 := by
  unfold tailWord_3488221
  simp only [CollatzResearch.WordTrace]
  refine ⟨127225871895778532562568517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84817247930519021708379011 127225871895778532562568517)
  ·
    refine ⟨23854850980458474855481597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127225871895778532562568517 23854850980458474855481597)
    ·
      refine ⟨8945569117671928070805599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23854850980458474855481597 8945569117671928070805599)
      ·
        refine ⟨13418353676507892106208399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8945569117671928070805599 13418353676507892106208399)
        ·
          refine ⟨20127530514761838159312599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13418353676507892106208399 20127530514761838159312599)
          ·
            refine ⟨30191295772142757238968899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20127530514761838159312599 30191295772142757238968899)
            ·
              refine ⟨45286943658214135858453349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30191295772142757238968899 45286943658214135858453349)
              ·
                refine ⟨8491301935915150473460003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45286943658214135858453349 8491301935915150473460003)
                ·
                  refine ⟨12736952903872725710190005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8491301935915150473460003 12736952903872725710190005)
                  ·
                    refine ⟨1194089334738068035330313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12736952903872725710190005 1194089334738068035330313)
                    ·
                      rfl

theorem cell22_3488221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_3488221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488221 prefixEnd_3488221 := by exact prefixLift 3488221
  have htrace : WordTrace (prefixWord ++ tailWord_3488221) baseStart_3488221 baseEnd_3488221 := by
    simpa [prefixWord, tailWord_3488221, baseEnd_3488221] using wordTrace_append hprefix tailTrace_3488221
  have hstable : (prefixWord ++ tailWord_3488221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488221).length < 2 ^ (prefixWord ++ tailWord_3488221).sum := by decide
  have hdescent : baseEnd_3488221 < baseStart_3488221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488223 : List Nat := [1, 1, 2, 3, 3, 3, 2, 3, 4]
def baseStart_3488223 : Nat := 118140960795 + 3488223 * 2 ^ 59
def prefixEnd_3488223 : Nat := 4983230072969 + 3 ^ 40 * 3488223 * 2
def baseEnd_3488223 : Nat := 398030006459646898926769

theorem tailTrace_3488223 : CollatzResearch.WordTrace tailWord_3488223 prefixEnd_3488223 398030006459646898926769 := by
  unfold tailWord_3488223
  simp only [CollatzResearch.WordTrace]
  refine ⟨127225944841771286904141323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84817296561180857936094215 127225944841771286904141323)
  ·
    refine ⟨190838917262656930356211985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127225944841771286904141323 190838917262656930356211985)
    ·
      refine ⟨143129187946992697767158989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190838917262656930356211985 143129187946992697767158989)
      ·
        refine ⟨53673445480122261662684621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143129187946992697767158989 53673445480122261662684621)
        ·
          refine ⟨20127542055045848123506733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53673445480122261662684621 20127542055045848123506733)
          ·
            refine ⟨7547828270642193046315025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20127542055045848123506733 7547828270642193046315025)
            ·
              refine ⟨5660871202981644784736269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7547828270642193046315025 5660871202981644784736269)
              ·
                refine ⟨2122826701118116794276101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5660871202981644784736269 2122826701118116794276101)
                ·
                  refine ⟨398030006459646898926769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2122826701118116794276101 398030006459646898926769)
                  ·
                    rfl

theorem cell22_3488223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 4].length) (baseStart_3488223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488223 prefixEnd_3488223 := by exact prefixLift 3488223
  have htrace : WordTrace (prefixWord ++ tailWord_3488223) baseStart_3488223 baseEnd_3488223 := by
    simpa [prefixWord, tailWord_3488223, baseEnd_3488223] using wordTrace_append hprefix tailTrace_3488223
  have hstable : (prefixWord ++ tailWord_3488223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488223).length < 2 ^ (prefixWord ++ tailWord_3488223).sum := by decide
  have hdescent : baseEnd_3488223 < baseStart_3488223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488238 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_3488238 : Nat := 118140960795 + 3488238 * 2 ^ 59
def prefixEnd_3488238 : Nat := 4983230072969 + 3 ^ 40 * 3488238 * 2
def baseEnd_3488238 : Nat := 1194095154185485657655261

theorem tailTrace_3488238 : CollatzResearch.WordTrace tailWord_3488238 prefixEnd_3488238 1194095154185485657655261 := by
  unfold tailWord_3488238
  simp only [CollatzResearch.WordTrace]
  refine ⟨15903311492089618058242171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84817661291144629643958245 15903311492089618058242171)
  ·
    refine ⟨23854967238134427087363257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15903311492089618058242171 23854967238134427087363257)
    ·
      refine ⟨17891225428600820315522443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23854967238134427087363257 17891225428600820315522443)
      ·
        refine ⟨26836838142901230473283665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17891225428600820315522443 26836838142901230473283665)
        ·
          refine ⟨20127628607175922854962749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26836838142901230473283665 20127628607175922854962749)
          ·
            refine ⟨7547860727690971070611031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20127628607175922854962749 7547860727690971070611031)
            ·
              refine ⟨11321791091536456605916547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7547860727690971070611031 11321791091536456605916547)
              ·
                refine ⟨16982686637304684908874821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11321791091536456605916547 16982686637304684908874821)
                ·
                  refine ⟨3184253744494628420414029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16982686637304684908874821 3184253744494628420414029)
                  ·
                    refine ⟨1194095154185485657655261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3184253744494628420414029 1194095154185485657655261)
                    ·
                      rfl

theorem cell22_3488238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_3488238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488238 prefixEnd_3488238 := by exact prefixLift 3488238
  have htrace : WordTrace (prefixWord ++ tailWord_3488238) baseStart_3488238 baseEnd_3488238 := by
    simpa [prefixWord, tailWord_3488238, baseEnd_3488238] using wordTrace_append hprefix tailTrace_3488238
  have hstable : (prefixWord ++ tailWord_3488238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488238).length < 2 ^ (prefixWord ++ tailWord_3488238).sum := by decide
  have hdescent : baseEnd_3488238 < baseStart_3488238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488268 : List Nat := [2, 2, 1, 2, 4, 3, 2, 6]
def baseStart_3488268 : Nat := 118140960795 + 3488268 * 2 ^ 59
def prefixEnd_3488268 : Nat := 4983230072969 + 3 ^ 40 * 3488268 * 2
def baseEnd_3488268 : Nat := 132678380422063953267241

theorem tailTrace_3488268 : CollatzResearch.WordTrace tailWord_3488268 prefixEnd_3488268 132678380422063953267241 := by
  unfold tailWord_3488268
  simp only [CollatzResearch.WordTrace]
  refine ⟨63613793063304129794764729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84818390751072173059686305 63613793063304129794764729)
  ·
    refine ⟨47710344797478097346073547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63613793063304129794764729 47710344797478097346073547)
    ·
      refine ⟨71565517196217146019110321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47710344797478097346073547 71565517196217146019110321)
      ·
        refine ⟨53674137897162859514332741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71565517196217146019110321 53674137897162859514332741)
        ·
          refine ⟨10063900855718036158937389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53674137897162859514332741 10063900855718036158937389)
          ·
            refine ⟨3773962820894263559601521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10063900855718036158937389 3773962820894263559601521)
            ·
              refine ⟨2830472115670697669701141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3773962820894263559601521 2830472115670697669701141)
              ·
                refine ⟨132678380422063953267241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2830472115670697669701141 132678380422063953267241)
                ·
                  rfl

theorem cell22_3488268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 6].length) (baseStart_3488268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488268 prefixEnd_3488268 := by exact prefixLift 3488268
  have htrace : WordTrace (prefixWord ++ tailWord_3488268) baseStart_3488268 baseEnd_3488268 := by
    simpa [prefixWord, tailWord_3488268, baseEnd_3488268] using wordTrace_append hprefix tailTrace_3488268
  have hstable : (prefixWord ++ tailWord_3488268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488268).length < 2 ^ (prefixWord ++ tailWord_3488268).sum := by decide
  have hdescent : baseEnd_3488268 < baseStart_3488268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488356 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_3488356 : Nat := 118140960795 + 3488356 * 2 ^ 59
def prefixEnd_3488356 : Nat := 4983230072969 + 3 ^ 40 * 3488356 * 2
def baseEnd_3488356 : Nat := 1194135547996972683204899

theorem tailTrace_3488356 : CollatzResearch.WordTrace tailWord_3488356 prefixEnd_3488356 1194135547996972683204899 := by
  unfold tailWord_3488356
  simp only [CollatzResearch.WordTrace]
  refine ⟨63615397875144725309366461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84820530500192967079155281 63615397875144725309366461)
  ·
    refine ⟨23855774203179271991012423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63615397875144725309366461 23855774203179271991012423)
    ·
      refine ⟨35783661304768907986518635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23855774203179271991012423 35783661304768907986518635)
      ·
        refine ⟨53675491957153361979777953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35783661304768907986518635 53675491957153361979777953)
        ·
          refine ⟨40256618967865021484833465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53675491957153361979777953 40256618967865021484833465)
          ·
            refine ⟨30192464225898766113625099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40256618967865021484833465 30192464225898766113625099)
            ·
              refine ⟨45288696338848149170437649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30192464225898766113625099 45288696338848149170437649)
              ·
                refine ⟨33966522254136111877828237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45288696338848149170437649 33966522254136111877828237)
                ·
                  refine ⟨12737445845301041954185589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33966522254136111877828237 12737445845301041954185589)
                  ·
                    refine ⟨1194135547996972683204899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12737445845301041954185589 1194135547996972683204899)
                    ·
                      rfl

theorem cell22_3488356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_3488356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488356 prefixEnd_3488356 := by exact prefixLift 3488356
  have htrace : WordTrace (prefixWord ++ tailWord_3488356) baseStart_3488356 baseEnd_3488356 := by
    simpa [prefixWord, tailWord_3488356, baseEnd_3488356] using wordTrace_append hprefix tailTrace_3488356
  have hstable : (prefixWord ++ tailWord_3488356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488356).length < 2 ^ (prefixWord ++ tailWord_3488356).sum := by decide
  have hdescent : baseEnd_3488356 < baseStart_3488356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488388 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_3488388 : Nat := 118140960795 + 3488388 * 2 ^ 59
def prefixEnd_3488388 : Nat := 4983230072969 + 3 ^ 40 * 3488388 * 2
def baseEnd_3488388 : Nat := 1194146502250935266404801

theorem tailTrace_3488388 : CollatzResearch.WordTrace tailWord_3488388 prefixEnd_3488388 1194146502250935266404801 := by
  unfold tailWord_3488388
  simp only [CollatzResearch.WordTrace]
  refine ⟨63615981443086760041948909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84821308590782346722598545 63615981443086760041948909)
  ·
    refine ⟨23855993041157535015730841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63615981443086760041948909 23855993041157535015730841)
    ·
      refine ⟨17891994780868151261798131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23855993041157535015730841 17891994780868151261798131)
      ·
        refine ⟨26837992171302226892697197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17891994780868151261798131 26837992171302226892697197)
        ·
          refine ⟨10064247064238335084761449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26837992171302226892697197 10064247064238335084761449)
          ·
            refine ⟨7548185298178751313571087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10064247064238335084761449 7548185298178751313571087)
            ·
              refine ⟨11322277947268126970356631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7548185298178751313571087 11322277947268126970356631)
              ·
                refine ⟨16983416920902190455534947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11322277947268126970356631 16983416920902190455534947)
                ·
                  refine ⟨25475125381353285683302421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16983416920902190455534947 25475125381353285683302421)
                  ·
                    refine ⟨1194146502250935266404801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25475125381353285683302421 1194146502250935266404801)
                    ·
                      rfl

theorem cell22_3488388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_3488388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488388 prefixEnd_3488388 := by exact prefixLift 3488388
  have htrace : WordTrace (prefixWord ++ tailWord_3488388) baseStart_3488388 baseEnd_3488388 := by
    simpa [prefixWord, tailWord_3488388, baseEnd_3488388] using wordTrace_append hprefix tailTrace_3488388
  have hstable : (prefixWord ++ tailWord_3488388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488388).length < 2 ^ (prefixWord ++ tailWord_3488388).sum := by decide
  have hdescent : baseEnd_3488388 < baseStart_3488388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488394 : List Nat := [3, 1, 2, 3, 4, 1, 2, 1, 1, 4]
def baseStart_3488394 : Nat := 118140960795 + 3488394 * 2 ^ 59
def prefixEnd_3488394 : Nat := 4983230072969 + 3 ^ 40 * 3488394 * 2
def baseEnd_3488394 : Nat := 1194148556173553250754783

theorem tailTrace_3488394 : CollatzResearch.WordTrace tailWord_3488394 prefixEnd_3488394 1194148556173553250754783 := by
  unfold tailWord_3488394
  simp only [CollatzResearch.WordTrace]
  refine ⟨31808045431037945777154059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84821454482767855405744157 31808045431037945777154059)
  ·
    refine ⟨47712068146556918665731089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31808045431037945777154059 47712068146556918665731089)
    ·
      refine ⟨35784051109917688999298317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47712068146556918665731089 35784051109917688999298317)
      ·
        refine ⟨13419019166219133374736869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35784051109917688999298317 13419019166219133374736869)
        ·
          refine ⟨2516066093666087507763163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13419019166219133374736869 2516066093666087507763163)
          ·
            refine ⟨3774099140499131261644745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516066093666087507763163 3774099140499131261644745)
            ·
              refine ⟨2830574355374348446233559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3774099140499131261644745 2830574355374348446233559)
              ·
                refine ⟨4245861533061522669350339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830574355374348446233559 4245861533061522669350339)
                ·
                  refine ⟨6368792299592284004025509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4245861533061522669350339 6368792299592284004025509)
                  ·
                    refine ⟨1194148556173553250754783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6368792299592284004025509 1194148556173553250754783)
                    ·
                      rfl

theorem cell22_3488394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_3488394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488394 prefixEnd_3488394 := by exact prefixLift 3488394
  have htrace : WordTrace (prefixWord ++ tailWord_3488394) baseStart_3488394 baseEnd_3488394 := by
    simpa [prefixWord, tailWord_3488394, baseEnd_3488394] using wordTrace_append hprefix tailTrace_3488394
  have hstable : (prefixWord ++ tailWord_3488394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488394).length < 2 ^ (prefixWord ++ tailWord_3488394).sum := by decide
  have hdescent : baseEnd_3488394 < baseStart_3488394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488454 : List Nat := [6, 1, 2, 1, 3, 1, 8]
def baseStart_3488454 : Nat := 118140960795 + 3488454 * 2 ^ 59
def prefixEnd_3488454 : Nat := 4983230072969 + 3 ^ 40 * 3488454 * 2
def baseEnd_3488454 : Nat := 44228485014804929416837

theorem tailTrace_3488454 : CollatzResearch.WordTrace tailWord_3488454 prefixEnd_3488454 44228485014804929416837 := by
  unfold tailWord_3488454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976074065747950417368763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84822913402622942237200277 3976074065747950417368763)
  ·
    refine ⟨5964111098621925626053145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3976074065747950417368763 5964111098621925626053145)
    ·
      refine ⟨4473083323966444219539859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5964111098621925626053145 4473083323966444219539859)
      ·
        refine ⟨6709624985949666329309789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473083323966444219539859 6709624985949666329309789)
        ·
          refine ⟨2516109369731124873491171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6709624985949666329309789 2516109369731124873491171)
          ·
            refine ⟨3774164054596687310236757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516109369731124873491171 3774164054596687310236757)
            ·
              refine ⟨44228485014804929416837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3774164054596687310236757 44228485014804929416837)
              ·
                rfl

theorem cell22_3488454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 8].length) (baseStart_3488454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488454 prefixEnd_3488454 := by exact prefixLift 3488454
  have htrace : WordTrace (prefixWord ++ tailWord_3488454) baseStart_3488454 baseEnd_3488454 := by
    simpa [prefixWord, tailWord_3488454, baseEnd_3488454] using wordTrace_append hprefix tailTrace_3488454
  have hstable : (prefixWord ++ tailWord_3488454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488454).length < 2 ^ (prefixWord ++ tailWord_3488454).sum := by decide
  have hdescent : baseEnd_3488454 < baseStart_3488454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488469 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 3, 3]
def baseStart_3488469 : Nat := 118140960795 + 3488469 * 2 ^ 59
def prefixEnd_3488469 : Nat := 4983230072969 + 3 ^ 40 * 3488469 * 2
def baseEnd_3488469 : Nat := 1194174230206278055129553

theorem tailTrace_3488469 : CollatzResearch.WordTrace tailWord_3488469 prefixEnd_3488469 1194174230206278055129553 := by
  unfold tailWord_3488469
  simp only [CollatzResearch.WordTrace]
  refine ⟨127234917198880070917596461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84823278132586713945064307 127234917198880070917596461)
  ·
    refine ⟨47713093949580026594098673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127234917198880070917596461 47713093949580026594098673)
    ·
      refine ⟨35784820462185019945574005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47713093949580026594098673 35784820462185019945574005)
      ·
        refine ⟨3354826918329845619897563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35784820462185019945574005 3354826918329845619897563)
        ·
          refine ⟨5032240377494768429846345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354826918329845619897563 5032240377494768429846345)
          ·
            refine ⟨3774180283121076322384759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5032240377494768429846345 3774180283121076322384759)
            ·
              refine ⟨5661270424681614483577139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774180283121076322384759 5661270424681614483577139)
              ·
                refine ⟨8491905637022421725365709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5661270424681614483577139 8491905637022421725365709)
                ·
                  refine ⟨3184464613883408147012141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8491905637022421725365709 3184464613883408147012141)
                  ·
                    refine ⟨1194174230206278055129553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3184464613883408147012141 1194174230206278055129553)
                    ·
                      rfl

theorem cell22_3488469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_3488469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488469 prefixEnd_3488469 := by exact prefixLift 3488469
  have htrace : WordTrace (prefixWord ++ tailWord_3488469) baseStart_3488469 baseEnd_3488469 := by
    simpa [prefixWord, tailWord_3488469, baseEnd_3488469] using wordTrace_append hprefix tailTrace_3488469
  have hstable : (prefixWord ++ tailWord_3488469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488469).length < 2 ^ (prefixWord ++ tailWord_3488469).sum := by decide
  have hdescent : baseEnd_3488469 < baseStart_3488469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488493 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3488493 : Nat := 118140960795 + 3488493 * 2 ^ 59
def prefixEnd_3488493 : Nat := 4983230072969 + 3 ^ 40 * 3488493 * 2
def baseEnd_3488493 : Nat := 398060815298916664176493

theorem tailTrace_3488493 : CollatzResearch.WordTrace tailWord_3488493 prefixEnd_3488493 398060815298916664176493 := by
  unfold tailWord_3488493
  simp only [CollatzResearch.WordTrace]
  refine ⟨127235792550793123016470133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84823861700528748677646755 127235792550793123016470133)
  ·
    refine ⟨11928355551636855282794075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127235792550793123016470133 11928355551636855282794075)
    ·
      refine ⟨17892533327455282924191113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11928355551636855282794075 17892533327455282924191113)
      ·
        refine ⟨13419399995591462193143335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17892533327455282924191113 13419399995591462193143335)
        ·
          refine ⟨20129099993387193289715003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13419399995591462193143335 20129099993387193289715003)
          ·
            refine ⟨30193649990080789934572505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20129099993387193289715003 30193649990080789934572505)
            ·
              refine ⟨22645237492560592450929379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30193649990080789934572505 22645237492560592450929379)
              ·
                refine ⟨33967856238840888676394069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22645237492560592450929379 33967856238840888676394069)
                ·
                  refine ⟨398060815298916664176493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33967856238840888676394069 398060815298916664176493)
                  ·
                    rfl

theorem cell22_3488493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3488493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488493 prefixEnd_3488493 := by exact prefixLift 3488493
  have htrace : WordTrace (prefixWord ++ tailWord_3488493) baseStart_3488493 baseEnd_3488493 := by
    simpa [prefixWord, tailWord_3488493, baseEnd_3488493] using wordTrace_append hprefix tailTrace_3488493
  have hstable : (prefixWord ++ tailWord_3488493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488493).length < 2 ^ (prefixWord ++ tailWord_3488493).sum := by decide
  have hdescent : baseEnd_3488493 < baseStart_3488493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488495 : List Nat := [1, 1, 2, 1, 5, 2, 3, 2, 1, 4]
def baseStart_3488495 : Nat := 118140960795 + 3488495 * 2 ^ 59
def prefixEnd_3488495 : Nat := 4983230072969 + 3 ^ 40 * 3488495 * 2
def baseEnd_3488495 : Nat := 1194183130537622653979473

theorem tailTrace_3488495 : CollatzResearch.WordTrace tailWord_3488495 prefixEnd_3488495 1194183130537622653979473 := by
  unfold tailWord_3488495
  simp only [CollatzResearch.WordTrace]
  refine ⟨127235865496785877358042939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84823910331190584905361959 127235865496785877358042939)
  ·
    refine ⟨190853798245178816037064409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127235865496785877358042939 190853798245178816037064409)
    ·
      refine ⟨143140348683884112027798307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190853798245178816037064409 143140348683884112027798307)
      ·
        refine ⟨214710523025826168041697461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143140348683884112027798307 214710523025826168041697461)
        ·
          refine ⟨20129111533671203253909137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214710523025826168041697461 20129111533671203253909137)
          ·
            refine ⟨15096833650253402440431853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20129111533671203253909137 15096833650253402440431853)
            ·
              refine ⟨5661312618845025915161945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15096833650253402440431853 5661312618845025915161945)
              ·
                refine ⟨4245984464133769436371459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5661312618845025915161945 4245984464133769436371459)
                ·
                  refine ⟨6368976696200654154557189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4245984464133769436371459 6368976696200654154557189)
                  ·
                    refine ⟨1194183130537622653979473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6368976696200654154557189 1194183130537622653979473)
                    ·
                      rfl

theorem cell22_3488495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_3488495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488495 prefixEnd_3488495 := by exact prefixLift 3488495
  have htrace : WordTrace (prefixWord ++ tailWord_3488495) baseStart_3488495 baseEnd_3488495 := by
    simpa [prefixWord, tailWord_3488495, baseEnd_3488495] using wordTrace_append hprefix tailTrace_3488495
  have hstable : (prefixWord ++ tailWord_3488495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488495).length < 2 ^ (prefixWord ++ tailWord_3488495).sum := by decide
  have hdescent : baseEnd_3488495 < baseStart_3488495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488508 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_3488508 : Nat := 118140960795 + 3488508 * 2 ^ 59
def prefixEnd_3488508 : Nat := 4983230072969 + 3 ^ 40 * 3488508 * 2
def baseEnd_3488508 : Nat := 1194187580703294953404433

theorem tailTrace_3488508 : CollatzResearch.WordTrace tailWord_3488508 prefixEnd_3488508 1194187580703294953404433 := by
  unfold tailWord_3488508
  simp only [CollatzResearch.WordTrace]
  refine ⟨63618169822869390289133089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84824226430492520385510785 63618169822869390289133089)
  ·
    refine ⟨47713627367152042716849817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63618169822869390289133089 47713627367152042716849817)
    ·
      refine ⟨35785220525364032037637363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47713627367152042716849817 35785220525364032037637363)
      ·
        refine ⟨53677830788046048056456045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35785220525364032037637363 53677830788046048056456045)
        ·
          refine ⟨20129186545517268021171017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53677830788046048056456045 20129186545517268021171017)
          ·
            refine ⟨15096889909137951015878263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20129186545517268021171017 15096889909137951015878263)
            ·
              refine ⟨22645334863706926523817395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15096889909137951015878263 22645334863706926523817395)
              ·
                refine ⟨33968002295560389785726093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22645334863706926523817395 33968002295560389785726093)
                ·
                  refine ⟨12738000860835146169647285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33968002295560389785726093 12738000860835146169647285)
                  ·
                    refine ⟨1194187580703294953404433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12738000860835146169647285 1194187580703294953404433)
                    ·
                      rfl

theorem cell22_3488508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_3488508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488508 prefixEnd_3488508 := by exact prefixLift 3488508
  have htrace : WordTrace (prefixWord ++ tailWord_3488508) baseStart_3488508 baseEnd_3488508 := by
    simpa [prefixWord, tailWord_3488508, baseEnd_3488508] using wordTrace_append hprefix tailTrace_3488508
  have hstable : (prefixWord ++ tailWord_3488508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488508).length < 2 ^ (prefixWord ++ tailWord_3488508).sum := by decide
  have hdescent : baseEnd_3488508 < baseStart_3488508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488638 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3488638 : Nat := 118140960795 + 3488638 * 2 ^ 59
def prefixEnd_3488638 : Nat := 4983230072969 + 3 ^ 40 * 3488638 * 2
def baseEnd_3488638 : Nat := 1194232082360017947654035

theorem tailTrace_3488638 : CollatzResearch.WordTrace tailWord_3488638 prefixEnd_3488638 1194232082360017947654035 := by
  unfold tailWord_3488638
  simp only [CollatzResearch.WordTrace]
  refine ⟨15905135141908476597562321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84827387423511875186999045 15905135141908476597562321)
  ·
    refine ⟨11928851356431357448171741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15905135141908476597562321 11928851356431357448171741)
    ·
      refine ⟨4473319258661759043064403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11928851356431357448171741 4473319258661759043064403)
      ·
        refine ⟨6709978887992638564596605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473319258661759043064403 6709978887992638564596605)
        ·
          refine ⟨2516242082997239461723727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6709978887992638564596605 2516242082997239461723727)
          ·
            refine ⟨3774363124495859192585591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516242082997239461723727 3774363124495859192585591)
            ·
              refine ⟨5661544686743788788878387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774363124495859192585591 5661544686743788788878387)
              ·
                refine ⟨8492317030115683183317581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5661544686743788788878387 8492317030115683183317581)
                ·
                  refine ⟨3184618886293381193744093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8492317030115683183317581 3184618886293381193744093)
                  ·
                    refine ⟨1194232082360017947654035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3184618886293381193744093 1194232082360017947654035)
                    ·
                      rfl

theorem cell22_3488638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3488638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488638 prefixEnd_3488638 := by exact prefixLift 3488638
  have htrace : WordTrace (prefixWord ++ tailWord_3488638) baseStart_3488638 baseEnd_3488638 := by
    simpa [prefixWord, tailWord_3488638, baseEnd_3488638] using wordTrace_append hprefix tailTrace_3488638
  have hstable : (prefixWord ++ tailWord_3488638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488638).length < 2 ^ (prefixWord ++ tailWord_3488638).sum := by decide
  have hdescent : baseEnd_3488638 < baseStart_3488638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488645 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 6]
def baseStart_3488645 : Nat := 118140960795 + 3488645 * 2 ^ 59
def prefixEnd_3488645 : Nat := 4983230072969 + 3 ^ 40 * 3488645 * 2
def baseEnd_3488645 : Nat := 398078159534357420909671

theorem tailTrace_3488645 : CollatzResearch.WordTrace tailWord_3488645 prefixEnd_3488645 398078159534357420909671 := by
  unfold tailWord_3488645
  simp only [CollatzResearch.WordTrace]
  refine ⟨127241336446242452976003389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84827557630828301984002259 127241336446242452976003389)
  ·
    refine ⟨47715501167340919866001271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127241336446242452976003389 47715501167340919866001271)
    ·
      refine ⟨71573251751011379799001907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47715501167340919866001271 71573251751011379799001907)
      ·
        refine ⟨107359877626517069698502861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71573251751011379799001907 107359877626517069698502861)
        ·
          refine ⟨40259954109943901136938573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107359877626517069698502861 40259954109943901136938573)
          ·
            refine ⟨15097482791228962926351965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40259954109943901136938573 15097482791228962926351965)
            ·
              refine ⟨5661556046710861097381987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15097482791228962926351965 5661556046710861097381987)
              ·
                refine ⟨8492334070066291646072981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5661556046710861097381987 8492334070066291646072981)
                ·
                  refine ⟨398078159534357420909671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8492334070066291646072981 398078159534357420909671)
                  ·
                    rfl

theorem cell22_3488645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_3488645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488645 prefixEnd_3488645 := by exact prefixLift 3488645
  have htrace : WordTrace (prefixWord ++ tailWord_3488645) baseStart_3488645 baseEnd_3488645 := by
    simpa [prefixWord, tailWord_3488645, baseEnd_3488645] using wordTrace_append hprefix tailTrace_3488645
  have hstable : (prefixWord ++ tailWord_3488645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488645).length < 2 ^ (prefixWord ++ tailWord_3488645).sum := by decide
  have hdescent : baseEnd_3488645 < baseStart_3488645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488675 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 2, 4]
def baseStart_3488675 : Nat := 118140960795 + 3488675 * 2 ^ 59
def prefixEnd_3488675 : Nat := 4983230072969 + 3 ^ 40 * 3488675 * 2
def baseEnd_3488675 : Nat := 1194244748216162184478921

theorem tailTrace_3488675 : CollatzResearch.WordTrace tailWord_3488675 prefixEnd_3488675 1194244748216162184478921 := by
  unfold tailWord_3488675
  simp only [CollatzResearch.WordTrace]
  refine ⟨127242430636133768099595479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84828287090755845399730319 127242430636133768099595479)
  ·
    refine ⟨190863645954200652149393219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127242430636133768099595479 190863645954200652149393219)
    ·
      refine ⟨286295468931300978224089829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190863645954200652149393219 286295468931300978224089829)
      ·
        refine ⟨53680400424618933417016843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286295468931300978224089829 53680400424618933417016843)
        ·
          refine ⟨80520600636928400125525265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53680400424618933417016843 80520600636928400125525265)
          ·
            refine ⟨60390450477696300094143949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80520600636928400125525265 60390450477696300094143949)
            ·
              refine ⟨22646418929136112535303981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60390450477696300094143949 22646418929136112535303981)
              ·
                refine ⟨8492407098426042200738993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22646418929136112535303981 8492407098426042200738993)
                ·
                  refine ⟨6369305323819531650554245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8492407098426042200738993 6369305323819531650554245)
                  ·
                    refine ⟨1194244748216162184478921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6369305323819531650554245 1194244748216162184478921)
                    ·
                      rfl

theorem cell22_3488675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 4].length) (baseStart_3488675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488675 prefixEnd_3488675 := by exact prefixLift 3488675
  have htrace : WordTrace (prefixWord ++ tailWord_3488675) baseStart_3488675 baseEnd_3488675 := by
    simpa [prefixWord, tailWord_3488675, baseEnd_3488675] using wordTrace_append hprefix tailTrace_3488675
  have hstable : (prefixWord ++ tailWord_3488675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488675).length < 2 ^ (prefixWord ++ tailWord_3488675).sum := by decide
  have hdescent : baseEnd_3488675 < baseStart_3488675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488726 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_3488726 : Nat := 118140960795 + 3488726 * 2 ^ 59
def prefixEnd_3488726 : Nat := 4983230072969 + 3 ^ 40 * 3488726 * 2
def baseEnd_3488726 : Nat := 1194262206558415051453765

theorem tailTrace_3488726 : CollatzResearch.WordTrace tailWord_3488726 prefixEnd_3488726 1194262206558415051453765 := by
  unfold tailWord_3488726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7952768172434312738106377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84829527172632669206468021 7952768172434312738106377)
  ·
    refine ⟨5964576129325734553579783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7952768172434312738106377 5964576129325734553579783)
    ·
      refine ⟨8946864193988601830369675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5964576129325734553579783 8946864193988601830369675)
      ·
        refine ⟨13420296290982902745554513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8946864193988601830369675 13420296290982902745554513)
        ·
          refine ⟨10065222218237177059165885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13420296290982902745554513 10065222218237177059165885)
          ·
            refine ⟨3774458331838941397187207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10065222218237177059165885 3774458331838941397187207)
            ·
              refine ⟨5661687497758412095780811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774458331838941397187207 5661687497758412095780811)
              ·
                refine ⟨8492531246637618143671217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5661687497758412095780811 8492531246637618143671217)
                ·
                  refine ⟨6369398434978213607753413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8492531246637618143671217 6369398434978213607753413)
                  ·
                    refine ⟨1194262206558415051453765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6369398434978213607753413 1194262206558415051453765)
                    ·
                      rfl

theorem cell22_3488726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_3488726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488726 prefixEnd_3488726 := by exact prefixLift 3488726
  have htrace : WordTrace (prefixWord ++ tailWord_3488726) baseStart_3488726 baseEnd_3488726 := by
    simpa [prefixWord, tailWord_3488726, baseEnd_3488726] using wordTrace_append hprefix tailTrace_3488726
  have hstable : (prefixWord ++ tailWord_3488726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488726).length < 2 ^ (prefixWord ++ tailWord_3488726).sum := by decide
  have hdescent : baseEnd_3488726 < baseStart_3488726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488769 : List Nat := [1, 2, 4, 1, 2, 3, 3, 1, 5]
def baseStart_3488769 : Nat := 118140960795 + 3488769 * 2 ^ 59
def prefixEnd_3488769 : Nat := 4983230072969 + 3 ^ 40 * 3488769 * 2
def baseEnd_3488769 : Nat := 398092308779059090876211

theorem tailTrace_3488769 : CollatzResearch.WordTrace tailWord_3488769 prefixEnd_3488769 398092308779059090876211 := by
  unfold tailWord_3488769
  simp only [CollatzResearch.WordTrace]
  refine ⟨127245859097793222153517361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84830572731862148102344907 127245859097793222153517361)
  ·
    refine ⟨95434394323344916615138021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127245859097793222153517361 95434394323344916615138021)
    ·
      refine ⟨17893948935627171865338379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95434394323344916615138021 17893948935627171865338379)
      ·
        refine ⟨26840923403440757798007569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17893948935627171865338379 26840923403440757798007569)
        ·
          refine ⟨20130692552580568348505677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26840923403440757798007569 20130692552580568348505677)
          ·
            refine ⟨7549009707217713130689629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20130692552580568348505677 7549009707217713130689629)
            ·
              refine ⟨2830878640206642424008611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7549009707217713130689629 2830878640206642424008611)
              ·
                refine ⟨4246317960309963636012917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830878640206642424008611 4246317960309963636012917)
                ·
                  refine ⟨398092308779059090876211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4246317960309963636012917 398092308779059090876211)
                  ·
                    rfl

theorem cell22_3488769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 5].length) (baseStart_3488769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488769 prefixEnd_3488769 := by exact prefixLift 3488769
  have htrace : WordTrace (prefixWord ++ tailWord_3488769) baseStart_3488769 baseEnd_3488769 := by
    simpa [prefixWord, tailWord_3488769, baseEnd_3488769] using wordTrace_append hprefix tailTrace_3488769
  have hstable : (prefixWord ++ tailWord_3488769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488769).length < 2 ^ (prefixWord ++ tailWord_3488769).sum := by decide
  have hdescent : baseEnd_3488769 < baseStart_3488769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488812 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 4, 3]
def baseStart_3488812 : Nat := 118140960795 + 3488812 * 2 ^ 59
def prefixEnd_3488812 : Nat := 4983230072969 + 3 ^ 40 * 3488812 * 2
def baseEnd_3488812 : Nat := 1194291646115939493803501

theorem tailTrace_3488812 : CollatzResearch.WordTrace tailWord_3488812 prefixEnd_3488812 1194291646115939493803501 := by
  unfold tailWord_3488812
  simp only [CollatzResearch.WordTrace]
  refine ⟨63623713718318720248666345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84831618291091626998221793 63623713718318720248666345)
  ·
    refine ⟨47717785288739040186499759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63623713718318720248666345 47717785288739040186499759)
    ·
      refine ⟨71576677933108560279749639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47717785288739040186499759 71576677933108560279749639)
      ·
        refine ⟨107365016899662840419624459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71576677933108560279749639 107365016899662840419624459)
        ·
          refine ⟨161047525349494260629436689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107365016899662840419624459 161047525349494260629436689)
          ·
            refine ⟨120785644012120695472077517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161047525349494260629436689 120785644012120695472077517)
            ·
              refine ⟨45294616504545260802029069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120785644012120695472077517 45294616504545260802029069)
              ·
                refine ⟨16985481189204472800760901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45294616504545260802029069 16985481189204472800760901)
                ·
                  refine ⟨3184777722975838650142669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16985481189204472800760901 3184777722975838650142669)
                  ·
                    refine ⟨1194291646115939493803501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3184777722975838650142669 1194291646115939493803501)
                    ·
                      rfl

theorem cell22_3488812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_3488812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488812 prefixEnd_3488812 := by exact prefixLift 3488812
  have htrace : WordTrace (prefixWord ++ tailWord_3488812) baseStart_3488812 baseEnd_3488812 := by
    simpa [prefixWord, tailWord_3488812, baseEnd_3488812] using wordTrace_append hprefix tailTrace_3488812
  have hstable : (prefixWord ++ tailWord_3488812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488812).length < 2 ^ (prefixWord ++ tailWord_3488812).sum := by decide
  have hdescent : baseEnd_3488812 < baseStart_3488812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488833 : List Nat := [1, 2, 5, 1, 4, 1, 1, 2, 1, 4]
def baseStart_3488833 : Nat := 118140960795 + 3488833 * 2 ^ 59
def prefixEnd_3488833 : Nat := 4983230072969 + 3 ^ 40 * 3488833 * 2
def baseEnd_3488833 : Nat := 1194298834845102439028437

theorem tailTrace_3488833 : CollatzResearch.WordTrace tailWord_3488833 prefixEnd_3488833 1194298834845102439028437 := by
  unfold tailWord_3488833
  simp only [CollatzResearch.WordTrace]
  refine ⟨127248193369561361083847153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84832128913040907389231435 127248193369561361083847153)
  ·
    refine ⟨95436145027171020812885365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127248193369561361083847153 95436145027171020812885365)
    ·
      refine ⟨8947138596297283201208003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95436145027171020812885365 8947138596297283201208003)
      ·
        refine ⟨13420707894445924801812005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8947138596297283201208003 13420707894445924801812005)
        ·
          refine ⟨2516382730208610900339751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13420707894445924801812005 2516382730208610900339751)
          ·
            refine ⟨3774574095312916350509627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516382730208610900339751 3774574095312916350509627)
            ·
              refine ⟨5661861142969374525764441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774574095312916350509627 5661861142969374525764441)
              ·
                refine ⟨4246395857227030894323331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5661861142969374525764441 4246395857227030894323331)
                ·
                  refine ⟨6369593785840546341484997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246395857227030894323331 6369593785840546341484997)
                  ·
                    refine ⟨1194298834845102439028437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6369593785840546341484997 1194298834845102439028437)
                    ·
                      rfl

theorem cell22_3488833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_3488833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488833 prefixEnd_3488833 := by exact prefixLift 3488833
  have htrace : WordTrace (prefixWord ++ tailWord_3488833) baseStart_3488833 baseEnd_3488833 := by
    simpa [prefixWord, tailWord_3488833, baseEnd_3488833] using wordTrace_append hprefix tailTrace_3488833
  have hstable : (prefixWord ++ tailWord_3488833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488833).length < 2 ^ (prefixWord ++ tailWord_3488833).sum := by decide
  have hdescent : baseEnd_3488833 < baseStart_3488833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488857 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 7, 3]
def baseStart_3488857 : Nat := 118140960795 + 3488857 * 2 ^ 59
def prefixEnd_3488857 : Nat := 4983230072969 + 3 ^ 40 * 3488857 * 2
def baseEnd_3488857 : Nat := 1194307050535574376428363

theorem tailTrace_3488857 : CollatzResearch.WordTrace tailWord_3488857 prefixEnd_3488857 1194307050535574376428363 := by
  unfold tailWord_3488857
  simp only [CollatzResearch.WordTrace]
  refine ⟨127249068721474413182720825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84832712480982942121813883 127249068721474413182720825)
  ·
    refine ⟨95436801541105809887040619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127249068721474413182720825 95436801541105809887040619)
    ·
      refine ⟨143155202311658714830560929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95436801541105809887040619 143155202311658714830560929)
      ·
        refine ⟨107366401733744036122920697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143155202311658714830560929 107366401733744036122920697)
        ·
          refine ⟨80524801300308027092190523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107366401733744036122920697 80524801300308027092190523)
          ·
            refine ⟨120787201950462040638285785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80524801300308027092190523 120787201950462040638285785)
            ·
              refine ⟨90590401462846530478714339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120787201950462040638285785 90590401462846530478714339)
              ·
                refine ⟨135885602194269795718071509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90590401462846530478714339 135885602194269795718071509)
                ·
                  refine ⟨3184818801428198337142301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 135885602194269795718071509 3184818801428198337142301)
                  ·
                    refine ⟨1194307050535574376428363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3184818801428198337142301 1194307050535574376428363)
                    ·
                      rfl

theorem cell22_3488857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 3].length) (baseStart_3488857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488857 prefixEnd_3488857 := by exact prefixLift 3488857
  have htrace : WordTrace (prefixWord ++ tailWord_3488857) baseStart_3488857 baseEnd_3488857 := by
    simpa [prefixWord, tailWord_3488857, baseEnd_3488857] using wordTrace_append hprefix tailTrace_3488857
  have hstable : (prefixWord ++ tailWord_3488857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488857).length < 2 ^ (prefixWord ++ tailWord_3488857).sum := by decide
  have hdescent : baseEnd_3488857 < baseStart_3488857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488887 : List Nat := [1, 1, 3, 1, 1, 4, 1, 5, 5]
def baseStart_3488887 : Nat := 118140960795 + 3488887 * 2 ^ 59
def prefixEnd_3488887 : Nat := 4983230072969 + 3 ^ 40 * 3488887 * 2
def baseEnd_3488887 : Nat := 398105773382888099392757

theorem tailTrace_3488887 : CollatzResearch.WordTrace tailWord_3488887 prefixEnd_3488887 398105773382888099392757 := by
  unfold tailWord_3488887
  simp only [CollatzResearch.WordTrace]
  refine ⟨127250162911365728306312915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84833441940910485537541943 127250162911365728306312915)
  ·
    refine ⟨190875244367048592459469373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127250162911365728306312915 190875244367048592459469373)
    ·
      refine ⟨71578216637643222172301015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190875244367048592459469373 71578216637643222172301015)
      ·
        refine ⟨107367324956464833258451523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71578216637643222172301015 107367324956464833258451523)
        ·
          refine ⟨161050987434697249887677285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107367324956464833258451523 161050987434697249887677285)
          ·
            refine ⟨30197060144005734353939491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161050987434697249887677285 30197060144005734353939491)
            ·
              refine ⟨45295590216008601530909237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30197060144005734353939491 45295590216008601530909237)
              ·
                refine ⟨4246461582750806393522741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45295590216008601530909237 4246461582750806393522741)
                ·
                  refine ⟨398105773382888099392757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4246461582750806393522741 398105773382888099392757)
                  ·
                    rfl

theorem cell22_3488887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 5].length) (baseStart_3488887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488887 prefixEnd_3488887 := by exact prefixLift 3488887
  have htrace : WordTrace (prefixWord ++ tailWord_3488887) baseStart_3488887 baseEnd_3488887 := by
    simpa [prefixWord, tailWord_3488887, baseEnd_3488887] using wordTrace_append hprefix tailTrace_3488887
  have hstable : (prefixWord ++ tailWord_3488887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488887).length < 2 ^ (prefixWord ++ tailWord_3488887).sum := by decide
  have hdescent : baseEnd_3488887 < baseStart_3488887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488917 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3488917 : Nat := 118140960795 + 3488917 * 2 ^ 59
def prefixEnd_3488917 : Nat := 4983230072969 + 3 ^ 40 * 3488917 * 2
def baseEnd_3488917 : Nat := 1194327589761754219928179

theorem tailTrace_3488917 : CollatzResearch.WordTrace tailWord_3488917 prefixEnd_3488917 1194327589761754219928179 := by
  unfold tailWord_3488917
  simp only [CollatzResearch.WordTrace]
  refine ⟨127251257101257043429905005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84834171400838028953270003 127251257101257043429905005)
  ·
    refine ⟨47719221412971391286214377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127251257101257043429905005 47719221412971391286214377)
    ·
      refine ⟨35789416059728543464660783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47719221412971391286214377 35789416059728543464660783)
      ·
        refine ⟨53684124089592815196991175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35789416059728543464660783 53684124089592815196991175)
        ·
          refine ⟨80526186134389222795486763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53684124089592815196991175 80526186134389222795486763)
          ·
            refine ⟨120789279201583834193230145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80526186134389222795486763 120789279201583834193230145)
            ·
              refine ⟨90591959401187875644922609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120789279201583834193230145 90591959401187875644922609)
              ·
                refine ⟨67943969550890906733691957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90591959401187875644922609 67943969550890906733691957)
                ·
                  refine ⟨6369747145396022506283621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67943969550890906733691957 6369747145396022506283621)
                  ·
                    refine ⟨1194327589761754219928179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6369747145396022506283621 1194327589761754219928179)
                    ·
                      rfl

theorem cell22_3488917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3488917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488917 prefixEnd_3488917 := by exact prefixLift 3488917
  have htrace : WordTrace (prefixWord ++ tailWord_3488917) baseStart_3488917 baseEnd_3488917 := by
    simpa [prefixWord, tailWord_3488917, baseEnd_3488917] using wordTrace_append hprefix tailTrace_3488917
  have hstable : (prefixWord ++ tailWord_3488917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488917).length < 2 ^ (prefixWord ++ tailWord_3488917).sum := by decide
  have hdescent : baseEnd_3488917 < baseStart_3488917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488938 : List Nat := [3, 1, 5, 1, 1, 2, 3, 1, 5]
def baseStart_3488938 : Nat := 118140960795 + 3488938 * 2 ^ 59
def prefixEnd_3488938 : Nat := 4983230072969 + 3 ^ 40 * 3488938 * 2
def baseEnd_3488938 : Nat := 398111592830305721717705

theorem tailTrace_3488938 : CollatzResearch.WordTrace tailWord_3488938 prefixEnd_3488938 398111592830305721717705 := by
  unfold tailWord_3488938
  simp only [CollatzResearch.WordTrace]
  refine ⟨31813005758545241004104867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84834682022787309344279645 31813005758545241004104867)
  ·
    refine ⟨47719508637817861506157301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31813005758545241004104867 47719508637817861506157301)
    ·
      refine ⟨4473703934795424516202247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47719508637817861506157301 4473703934795424516202247)
      ·
        refine ⟨6710555902193136774303371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473703934795424516202247 6710555902193136774303371)
        ·
          refine ⟨10065833853289705161455057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710555902193136774303371 10065833853289705161455057)
          ·
            refine ⟨7549375389967278871091293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10065833853289705161455057 7549375389967278871091293)
            ·
              refine ⟨2831015771237729576659235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7549375389967278871091293 2831015771237729576659235)
              ·
                refine ⟨4246523656856594364988853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831015771237729576659235 4246523656856594364988853)
                ·
                  refine ⟨398111592830305721717705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4246523656856594364988853 398111592830305721717705)
                  ·
                    rfl

theorem cell22_3488938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_3488938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488938 prefixEnd_3488938 := by exact prefixLift 3488938
  have htrace : WordTrace (prefixWord ++ tailWord_3488938) baseStart_3488938 baseEnd_3488938 := by
    simpa [prefixWord, tailWord_3488938, baseEnd_3488938] using wordTrace_append hprefix tailTrace_3488938
  have hstable : (prefixWord ++ tailWord_3488938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488938).length < 2 ^ (prefixWord ++ tailWord_3488938).sum := by decide
  have hdescent : baseEnd_3488938 < baseStart_3488938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488981 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 4, 3]
def baseStart_3488981 : Nat := 118140960795 + 3488981 * 2 ^ 59
def prefixEnd_3488981 : Nat := 4983230072969 + 3 ^ 40 * 3488981 * 2
def baseEnd_3488981 : Nat := 1194349498269679386327983

theorem tailTrace_3488981 : CollatzResearch.WordTrace tailWord_3488981 prefixEnd_3488981 1194349498269679386327983 := by
  unfold tailWord_3488981
  simp only [CollatzResearch.WordTrace]
  refine ⟨127253591373025182360234797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84835727582016788240156531 127253591373025182360234797)
  ·
    refine ⟨47720096764884443385088049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127253591373025182360234797 47720096764884443385088049)
    ·
      refine ⟨35790072573663332538816037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47720096764884443385088049 35790072573663332538816037)
      ·
        refine ⟨6710638607561874851028007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35790072573663332538816037 6710638607561874851028007)
        ·
          refine ⟨10065957911342812276542011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710638607561874851028007 10065957911342812276542011)
          ·
            refine ⟨15098936867014218414813017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10065957911342812276542011 15098936867014218414813017)
            ·
              refine ⟨11324202650260663811109763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15098936867014218414813017 11324202650260663811109763)
              ·
                refine ⟨16986303975390995716664645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11324202650260663811109763 16986303975390995716664645)
                ·
                  refine ⟨3184931995385811696874621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16986303975390995716664645 3184931995385811696874621)
                  ·
                    refine ⟨1194349498269679386327983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3184931995385811696874621 1194349498269679386327983)
                    ·
                      rfl

theorem cell22_3488981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_3488981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3488981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3488981 prefixEnd_3488981 := by exact prefixLift 3488981
  have htrace : WordTrace (prefixWord ++ tailWord_3488981) baseStart_3488981 baseEnd_3488981 := by
    simpa [prefixWord, tailWord_3488981, baseEnd_3488981] using wordTrace_append hprefix tailTrace_3488981
  have hstable : (prefixWord ++ tailWord_3488981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488981).length < 2 ^ (prefixWord ++ tailWord_3488981).sum := by decide
  have hdescent : baseEnd_3488981 < baseStart_3488981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489009 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 5, 3]
def baseStart_3489009 : Nat := 118140960795 + 3489009 * 2 ^ 59
def prefixEnd_3489009 : Nat := 4983230072969 + 3 ^ 40 * 3489009 * 2
def baseEnd_3489009 : Nat := 1194359083241896646627897

theorem tailTrace_3489009 : CollatzResearch.WordTrace tailWord_3489009 prefixEnd_3489009 1194359083241896646627897 := by
  unfold tailWord_3489009
  simp only [CollatzResearch.WordTrace]
  refine ⟨127254612616923743142254081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84836408411282495428169387 127254612616923743142254081)
  ·
    refine ⟨95440959462692807356690561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127254612616923743142254081 95440959462692807356690561)
    ·
      refine ⟨71580719597019605517517921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95440959462692807356690561 71580719597019605517517921)
      ·
        refine ⟨53685539697764704138138441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71580719597019605517517921 53685539697764704138138441)
        ·
          refine ⟨40264154773323528103603831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53685539697764704138138441 40264154773323528103603831)
          ·
            refine ⟨60396232159985292155405747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40264154773323528103603831 60396232159985292155405747)
            ·
              refine ⟨90594348239977938233108621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60396232159985292155405747 90594348239977938233108621)
              ·
                refine ⟨33972880589991726837415733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90594348239977938233108621 33972880589991726837415733)
                ·
                  refine ⟨3184957555311724391007725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33972880589991726837415733 3184957555311724391007725)
                  ·
                    refine ⟨1194359083241896646627897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3184957555311724391007725 1194359083241896646627897)
                    ·
                      rfl

theorem cell22_3489009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_3489009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489009 prefixEnd_3489009 := by exact prefixLift 3489009
  have htrace : WordTrace (prefixWord ++ tailWord_3489009) baseStart_3489009 baseEnd_3489009 := by
    simpa [prefixWord, tailWord_3489009, baseEnd_3489009] using wordTrace_append hprefix tailTrace_3489009
  have hstable : (prefixWord ++ tailWord_3489009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489009).length < 2 ^ (prefixWord ++ tailWord_3489009).sum := by decide
  have hdescent : baseEnd_3489009 < baseStart_3489009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489114 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_3489114 : Nat := 118140960795 + 3489114 * 2 ^ 59
def prefixEnd_3489114 : Nat := 4983230072969 + 3 ^ 40 * 3489114 * 2
def baseEnd_3489114 : Nat := 1194395026887711372752575

theorem tailTrace_3489114 : CollatzResearch.WordTrace tailWord_3489114 prefixEnd_3489114 1194395026887711372752575 := by
  unfold tailWord_3489114
  simp only [CollatzResearch.WordTrace]
  refine ⟨31814610570385836518706599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84838961521028897383217597 31814610570385836518706599)
  ·
    refine ⟨47721915855578754778059899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31814610570385836518706599 47721915855578754778059899)
    ·
      refine ⟨71582873783368132167089849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47721915855578754778059899 71582873783368132167089849)
      ·
        refine ⟨53687155337526099125317387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71582873783368132167089849 53687155337526099125317387)
        ·
          refine ⟨80530733006289148687976081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53687155337526099125317387 80530733006289148687976081)
          ·
            refine ⟨60398049754716861515982061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80530733006289148687976081 60398049754716861515982061)
            ·
              refine ⟨22649268658018823068493273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60398049754716861515982061 22649268658018823068493273)
              ·
                refine ⟨16986951493514117301369955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22649268658018823068493273 16986951493514117301369955)
                ·
                  refine ⟨25480427240271175952054933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16986951493514117301369955 25480427240271175952054933)
                  ·
                    refine ⟨1194395026887711372752575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25480427240271175952054933 1194395026887711372752575)
                    ·
                      rfl

theorem cell22_3489114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_3489114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489114 prefixEnd_3489114 := by exact prefixLift 3489114
  have htrace : WordTrace (prefixWord ++ tailWord_3489114) baseStart_3489114 baseEnd_3489114 := by
    simpa [prefixWord, tailWord_3489114, baseEnd_3489114] using wordTrace_append hprefix tailTrace_3489114
  have hstable : (prefixWord ++ tailWord_3489114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489114).length < 2 ^ (prefixWord ++ tailWord_3489114).sum := by decide
  have hdescent : baseEnd_3489114 < baseStart_3489114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489189 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_3489189 : Nat := 118140960795 + 3489189 * 2 ^ 59
def prefixEnd_3489189 : Nat := 4983230072969 + 3 ^ 40 * 3489189 * 2
def baseEnd_3489189 : Nat := 1194420700920436177127345

theorem tailTrace_3489189 : CollatzResearch.WordTrace tailWord_3489189 prefixEnd_3489189 1194420700920436177127345 := by
  unfold tailWord_3489189
  simp only [CollatzResearch.WordTrace]
  refine ⟨127261177756271633883806621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84840785170847755922537747 127261177756271633883806621)
  ·
    refine ⟨47722941658601862706427483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127261177756271633883806621 47722941658601862706427483)
    ·
      refine ⟨71584412487902794059641225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47722941658601862706427483 71584412487902794059641225)
      ·
        refine ⟨53688309365927095544730919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71584412487902794059641225 53688309365927095544730919)
        ·
          refine ⟨80532464048890643317096379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53688309365927095544730919 80532464048890643317096379)
          ·
            refine ⟨120798696073335964975644569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80532464048890643317096379 120798696073335964975644569)
            ·
              refine ⟨90599022055001973731733427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120798696073335964975644569 90599022055001973731733427)
              ·
                refine ⟨135898533082502960597600141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90599022055001973731733427 135898533082502960597600141)
                ·
                  refine ⟨50961949905938610224100053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135898533082502960597600141 50961949905938610224100053)
                  ·
                    refine ⟨1194420700920436177127345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50961949905938610224100053 1194420700920436177127345)
                    ·
                      rfl

theorem cell22_3489189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_3489189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489189 prefixEnd_3489189 := by exact prefixLift 3489189
  have htrace : WordTrace (prefixWord ++ tailWord_3489189) baseStart_3489189 baseEnd_3489189 := by
    simpa [prefixWord, tailWord_3489189, baseEnd_3489189] using wordTrace_append hprefix tailTrace_3489189
  have hstable : (prefixWord ++ tailWord_3489189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489189).length < 2 ^ (prefixWord ++ tailWord_3489189).sum := by decide
  have hdescent : baseEnd_3489189 < baseStart_3489189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489212 : List Nat := [2, 2, 2, 4, 2, 1, 1, 4, 1, 3]
def baseStart_3489212 : Nat := 118140960795 + 3489212 * 2 ^ 59
def prefixEnd_3489212 : Nat := 4983230072969 + 3 ^ 40 * 3489212 * 2
def baseEnd_3489212 : Nat := 1194428574290471783802275

theorem tailTrace_3489212 : CollatzResearch.WordTrace tailWord_3489212 prefixEnd_3489212 1194428574290471783802275 := by
  unfold tailWord_3489212
  simp only [CollatzResearch.WordTrace]
  refine ⟨63631008317594154405946945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84841344423458872541262593 63631008317594154405946945)
  ·
    refine ⟨47723256238195615804460209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63631008317594154405946945 47723256238195615804460209)
    ·
      refine ⟨35792442178646711853345157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47723256238195615804460209 35792442178646711853345157)
      ·
        refine ⟨6711082908496258472502217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35792442178646711853345157 6711082908496258472502217)
        ·
          refine ⟨5033312181372193854376663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6711082908496258472502217 5033312181372193854376663)
          ·
            refine ⟨7549968272058290781564995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5033312181372193854376663 7549968272058290781564995)
            ·
              refine ⟨11324952408087436172347493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7549968272058290781564995 11324952408087436172347493)
              ·
                refine ⟨2123428576516394282315155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11324952408087436172347493 2123428576516394282315155)
                ·
                  refine ⟨3185142864774591423472733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2123428576516394282315155 3185142864774591423472733)
                  ·
                    refine ⟨1194428574290471783802275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3185142864774591423472733 1194428574290471783802275)
                    ·
                      rfl

theorem cell22_3489212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_3489212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489212 prefixEnd_3489212 := by exact prefixLift 3489212
  have htrace : WordTrace (prefixWord ++ tailWord_3489212) baseStart_3489212 baseEnd_3489212 := by
    simpa [prefixWord, tailWord_3489212, baseEnd_3489212] using wordTrace_append hprefix tailTrace_3489212
  have hstable : (prefixWord ++ tailWord_3489212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489212).length < 2 ^ (prefixWord ++ tailWord_3489212).sum := by decide
  have hdescent : baseEnd_3489212 < baseStart_3489212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489255 : List Nat := [1, 1, 5, 2, 1, 2, 4, 1, 1, 4]
def baseStart_3489255 : Nat := 118140960795 + 3489255 * 2 ^ 59
def prefixEnd_3489255 : Nat := 4983230072969 + 3 ^ 40 * 3489255 * 2
def baseEnd_3489255 : Nat := 1194443294069234004977143

theorem tailTrace_3489255 : CollatzResearch.WordTrace tailWord_3489255 prefixEnd_3489255 1194443294069234004977143 := by
  unfold tailWord_3489255
  simp only [CollatzResearch.WordTrace]
  refine ⟨127263584974032527155709219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84842389982688351437139479 127263584974032527155709219)
  ·
    refine ⟨190895377461048790733563829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127263584974032527155709219 190895377461048790733563829)
    ·
      refine ⟨17896441636973324131271609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190895377461048790733563829 17896441636973324131271609)
      ·
        refine ⟨13422331227729993098453707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17896441636973324131271609 13422331227729993098453707)
        ·
          refine ⟨20133496841594989647680561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13422331227729993098453707 20133496841594989647680561)
          ·
            refine ⟨15100122631196242235760421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20133496841594989647680561 15100122631196242235760421)
            ·
              refine ⟨2831272993349295419205079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15100122631196242235760421 2831272993349295419205079)
              ·
                refine ⟨4246909490023943128807619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831272993349295419205079 4246909490023943128807619)
                ·
                  refine ⟨6370364235035914693211429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246909490023943128807619 6370364235035914693211429)
                  ·
                    refine ⟨1194443294069234004977143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6370364235035914693211429 1194443294069234004977143)
                    ·
                      rfl

theorem cell22_3489255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_3489255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489255 prefixEnd_3489255 := by exact prefixLift 3489255
  have htrace : WordTrace (prefixWord ++ tailWord_3489255) baseStart_3489255 baseEnd_3489255 := by
    simpa [prefixWord, tailWord_3489255, baseEnd_3489255] using wordTrace_append hprefix tailTrace_3489255
  have hstable : (prefixWord ++ tailWord_3489255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489255).length < 2 ^ (prefixWord ++ tailWord_3489255).sum := by decide
  have hdescent : baseEnd_3489255 < baseStart_3489255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489270 : List Nat := [5, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_3489270 : Nat := 118140960795 + 3489270 * 2 ^ 59
def prefixEnd_3489270 : Nat := 4983230072969 + 3 ^ 40 * 3489270 * 2
def baseEnd_3489270 : Nat := 398149476291926321950699

theorem tailTrace_3489270 : CollatzResearch.WordTrace tailWord_3489270 prefixEnd_3489270 398149476291926321950699 := by
  unfold tailWord_3489270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954008254311136544844079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84842754712652123145003509 7954008254311136544844079)
  ·
    refine ⟨11931012381466704817266119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7954008254311136544844079 11931012381466704817266119)
    ·
      refine ⟨17896518572200057225899179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11931012381466704817266119 17896518572200057225899179)
      ·
        refine ⟨26844777858300085838848769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17896518572200057225899179 26844777858300085838848769)
        ·
          refine ⟨20133583393725064379136577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26844777858300085838848769 20133583393725064379136577)
          ·
            refine ⟨15100187545293798284352433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20133583393725064379136577 15100187545293798284352433)
            ·
              refine ⟨11325140658970348713264325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15100187545293798284352433 11325140658970348713264325)
              ·
                refine ⟨2123463873556940383737061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11325140658970348713264325 2123463873556940383737061)
                ·
                  refine ⟨398149476291926321950699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2123463873556940383737061 398149476291926321950699)
                  ·
                    rfl

theorem cell22_3489270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_3489270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489270 prefixEnd_3489270 := by exact prefixLift 3489270
  have htrace : WordTrace (prefixWord ++ tailWord_3489270) baseStart_3489270 baseEnd_3489270 := by
    simpa [prefixWord, tailWord_3489270, baseEnd_3489270] using wordTrace_append hprefix tailTrace_3489270
  have hstable : (prefixWord ++ tailWord_3489270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489270).length < 2 ^ (prefixWord ++ tailWord_3489270).sum := by decide
  have hdescent : baseEnd_3489270 < baseStart_3489270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489343 : List Nat := [1, 1, 2, 2, 3, 4, 1, 3, 5]
def baseStart_3489343 : Nat := 118140960795 + 3489343 * 2 ^ 59
def prefixEnd_3489343 : Nat := 4983230072969 + 3 ^ 40 * 3489343 * 2
def baseEnd_3489343 : Nat := 398157806089210369592291

theorem tailTrace_3489343 : CollatzResearch.WordTrace tailWord_3489343 prefixEnd_3489343 398157806089210369592291 := by
  unfold tailWord_3489343
  simp only [CollatzResearch.WordTrace]
  refine ⟨127266794597713718184912683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84844529731809145456608455 127266794597713718184912683)
  ·
    refine ⟨190900191896570577277369025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127266794597713718184912683 190900191896570577277369025)
    ·
      refine ⟨143175143922427932958026769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190900191896570577277369025 143175143922427932958026769)
      ·
        refine ⟨107381357941820949718520077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143175143922427932958026769 107381357941820949718520077)
        ·
          refine ⟨40268009228182856144445029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107381357941820949718520077 40268009228182856144445029)
          ·
            refine ⟨7550251730284285527083443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40268009228182856144445029 7550251730284285527083443)
            ·
              refine ⟨11325377595426428290625165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7550251730284285527083443 11325377595426428290625165)
              ·
                refine ⟨4247016598284910608984437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11325377595426428290625165 4247016598284910608984437)
                ·
                  refine ⟨398157806089210369592291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4247016598284910608984437 398157806089210369592291)
                  ·
                    rfl

theorem cell22_3489343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 5].length) (baseStart_3489343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489343 prefixEnd_3489343 := by exact prefixLift 3489343
  have htrace : WordTrace (prefixWord ++ tailWord_3489343) baseStart_3489343 baseEnd_3489343 := by
    simpa [prefixWord, tailWord_3489343, baseEnd_3489343] using wordTrace_append hprefix tailTrace_3489343
  have hstable : (prefixWord ++ tailWord_3489343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489343).length < 2 ^ (prefixWord ++ tailWord_3489343).sum := by decide
  have hdescent : baseEnd_3489343 < baseStart_3489343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489403 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 1, 5]
def baseStart_3489403 : Nat := 118140960795 + 3489403 * 2 ^ 59
def prefixEnd_3489403 : Nat := 4983230072969 + 3 ^ 40 * 3489403 * 2
def baseEnd_3489403 : Nat := 1194493957493810952276689

theorem tailTrace_3489403 : CollatzResearch.WordTrace tailWord_3489403 prefixEnd_3489403 1194493957493810952276689 := by
  unfold tailWord_3489403
  simp only [CollatzResearch.WordTrace]
  refine ⟨127268982977496348432096863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84845988651664232288064575 127268982977496348432096863)
  ·
    refine ⟨190903474466244522648145295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127268982977496348432096863 190903474466244522648145295)
    ·
      refine ⟨286355211699366783972217943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190903474466244522648145295 286355211699366783972217943)
      ·
        refine ⟨429532817549050175958326915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286355211699366783972217943 429532817549050175958326915)
        ·
          refine ⟨644299226323575263937490373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429532817549050175958326915 644299226323575263937490373)
          ·
            refine ⟨120806104935670361988279445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 644299226323575263937490373 120806104935670361988279445)
            ·
              refine ⟨5662786168859548218200599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120806104935670361988279445 5662786168859548218200599)
              ·
                refine ⟨8494179253289322327300899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5662786168859548218200599 8494179253289322327300899)
                ·
                  refine ⟨12741268879933983490951349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8494179253289322327300899 12741268879933983490951349)
                  ·
                    refine ⟨1194493957493810952276689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12741268879933983490951349 1194493957493810952276689)
                    ·
                      rfl

theorem cell22_3489403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 5].length) (baseStart_3489403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489403 prefixEnd_3489403 := by exact prefixLift 3489403
  have htrace : WordTrace (prefixWord ++ tailWord_3489403) baseStart_3489403 baseEnd_3489403 := by
    simpa [prefixWord, tailWord_3489403, baseEnd_3489403] using wordTrace_append hprefix tailTrace_3489403
  have hstable : (prefixWord ++ tailWord_3489403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489403).length < 2 ^ (prefixWord ++ tailWord_3489403).sum := by decide
  have hdescent : baseEnd_3489403 < baseStart_3489403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489422 : List Nat := [4, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_3489422 : Nat := 118140960795 + 3489422 * 2 ^ 59
def prefixEnd_3489422 : Nat := 4983230072969 + 3 ^ 40 * 3489422 * 2
def baseEnd_3489422 : Nat := 398166820527367078683877

theorem tailTrace_3489422 : CollatzResearch.WordTrace tailWord_3489422 prefixEnd_3489422 398166820527367078683877 := by
  unfold tailWord_3489422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15908709495553439334629815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84846450642951676451359013 15908709495553439334629815)
  ·
    refine ⟨23863064243330159001944723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15908709495553439334629815 23863064243330159001944723)
    ·
      refine ⟨35794596364995238502917085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23863064243330159001944723 35794596364995238502917085)
      ·
        refine ⟨13422973636873214438593907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35794596364995238502917085 13422973636873214438593907)
        ·
          refine ⟨20134460455309821657890861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13422973636873214438593907 20134460455309821657890861)
          ·
            refine ⟨7550422670741183121709073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20134460455309821657890861 7550422670741183121709073)
            ·
              refine ⟨5662817003055887341281805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7550422670741183121709073 5662817003055887341281805)
              ·
                refine ⟨2123556376145957752980677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5662817003055887341281805 2123556376145957752980677)
                ·
                  refine ⟨398166820527367078683877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2123556376145957752980677 398166820527367078683877)
                  ·
                    rfl

theorem cell22_3489422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_3489422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489422 prefixEnd_3489422 := by exact prefixLift 3489422
  have htrace : WordTrace (prefixWord ++ tailWord_3489422) baseStart_3489422 baseEnd_3489422 := by
    simpa [prefixWord, tailWord_3489422, baseEnd_3489422] using wordTrace_append hprefix tailTrace_3489422
  have hstable : (prefixWord ++ tailWord_3489422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489422).length < 2 ^ (prefixWord ++ tailWord_3489422).sum := by decide
  have hdescent : baseEnd_3489422 < baseStart_3489422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489454 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3489454 : Nat := 118140960795 + 3489454 * 2 ^ 59
def prefixEnd_3489454 : Nat := 4983230072969 + 3 ^ 40 * 3489454 * 2
def baseEnd_3489454 : Nat := 1194511415836063819251533

theorem tailTrace_3489454 : CollatzResearch.WordTrace tailWord_3489454 prefixEnd_3489454 1194511415836063819251533 := by
  unfold tailWord_3489454
  simp only [CollatzResearch.WordTrace]
  refine ⟨15908855387538948017775427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84847228733541056094802277 15908855387538948017775427)
  ·
    refine ⟨23863283081308422026663141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15908855387538948017775427 23863283081308422026663141)
    ·
      refine ⟨4474365577745329129999339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23863283081308422026663141 4474365577745329129999339)
      ·
        refine ⟨6711548366617993694999009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474365577745329129999339 6711548366617993694999009)
        ·
          refine ⟨5033661274963495271249257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6711548366617993694999009 5033661274963495271249257)
          ·
            refine ⟨3775245956222621453436943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5033661274963495271249257 3775245956222621453436943)
            ·
              refine ⟨5662868934333932180155415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775245956222621453436943 5662868934333932180155415)
              ·
                refine ⟨8494303401500898270233123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5662868934333932180155415 8494303401500898270233123)
                ·
                  refine ⟨12741455102251347405349685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8494303401500898270233123 12741455102251347405349685)
                  ·
                    refine ⟨1194511415836063819251533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12741455102251347405349685 1194511415836063819251533)
                    ·
                      rfl

theorem cell22_3489454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3489454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489454 prefixEnd_3489454 := by exact prefixLift 3489454
  have htrace : WordTrace (prefixWord ++ tailWord_3489454) baseStart_3489454 baseEnd_3489454 := by
    simpa [prefixWord, tailWord_3489454, baseEnd_3489454] using wordTrace_append hprefix tailTrace_3489454
  have hstable : (prefixWord ++ tailWord_3489454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489454).length < 2 ^ (prefixWord ++ tailWord_3489454).sum := by decide
  have hdescent : baseEnd_3489454 < baseStart_3489454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489465 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 3, 3]
def baseStart_3489465 : Nat := 118140960795 + 3489465 * 2 ^ 59
def prefixEnd_3489465 : Nat := 4983230072969 + 3 ^ 40 * 3489465 * 2
def baseEnd_3489465 : Nat := 1194515181360863457226499

theorem tailTrace_3489465 : CollatzResearch.WordTrace tailWord_3489465 prefixEnd_3489465 1194515181360863457226499 := by
  unfold tailWord_3489465
  simp only [CollatzResearch.WordTrace]
  refine ⟨127271244303271733020853849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84847496202181155347235899 127271244303271733020853849)
  ·
    refine ⟨95453433227453799765640387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127271244303271733020853849 95453433227453799765640387)
    ·
      refine ⟨143180149841180699648460581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95453433227453799765640387 143180149841180699648460581)
      ·
        refine ⟨26846278095221381184086359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143180149841180699648460581 26846278095221381184086359)
        ·
          refine ⟨40269417142832071776129539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26846278095221381184086359 40269417142832071776129539)
          ·
            refine ⟨60404125714248107664194309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40269417142832071776129539 60404125714248107664194309)
            ·
              refine ⟨11325773571421520187036433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60404125714248107664194309 11325773571421520187036433)
              ·
                refine ⟨8494330178566140140277325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11325773571421520187036433 8494330178566140140277325)
                ·
                  refine ⟨3185373816962302552603997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8494330178566140140277325 3185373816962302552603997)
                  ·
                    refine ⟨1194515181360863457226499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3185373816962302552603997 1194515181360863457226499)
                    ·
                      rfl

theorem cell22_3489465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 3].length) (baseStart_3489465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489465 prefixEnd_3489465 := by exact prefixLift 3489465
  have htrace : WordTrace (prefixWord ++ tailWord_3489465) baseStart_3489465 baseEnd_3489465 := by
    simpa [prefixWord, tailWord_3489465, baseEnd_3489465] using wordTrace_append hprefix tailTrace_3489465
  have hstable : (prefixWord ++ tailWord_3489465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489465).length < 2 ^ (prefixWord ++ tailWord_3489465).sum := by decide
  have hdescent : baseEnd_3489465 < baseStart_3489465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489512 : List Nat := [2, 1, 4, 1, 3, 1, 4, 1, 5]
def baseStart_3489512 : Nat := 118140960795 + 3489512 * 2 ^ 59
def prefixEnd_3489512 : Nat := 4983230072969 + 3 ^ 40 * 3489512 * 2
def baseEnd_3489512 : Nat := 398177090140457000433785

theorem tailTrace_3489512 : CollatzResearch.WordTrace tailWord_3489512 prefixEnd_3489512 398177090140457000433785 := by
  unfold tailWord_3489512
  simp only [CollatzResearch.WordTrace]
  refine ⟨63636479267050730023907395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84848639022734306698543193 63636479267050730023907395)
  ·
    refine ⟨95454718900576095035861093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63636479267050730023907395 95454718900576095035861093)
    ·
      refine ⟨17897759793858017819223955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95454718900576095035861093 17897759793858017819223955)
      ·
        refine ⟨26846639690787026728835933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17897759793858017819223955 26846639690787026728835933)
        ·
          refine ⟨10067489884045135023313475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26846639690787026728835933 10067489884045135023313475)
          ·
            refine ⟨15101234826067702534970213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10067489884045135023313475 15101234826067702534970213)
            ·
              refine ⟨2831481529887694225306915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15101234826067702534970213 2831481529887694225306915)
              ·
                refine ⟨4247222294831541337960373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831481529887694225306915 4247222294831541337960373)
                ·
                  refine ⟨398177090140457000433785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4247222294831541337960373 398177090140457000433785)
                  ·
                    rfl

theorem cell22_3489512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 5].length) (baseStart_3489512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489512 prefixEnd_3489512 := by exact prefixLift 3489512
  have htrace : WordTrace (prefixWord ++ tailWord_3489512) baseStart_3489512 baseEnd_3489512 := by
    simpa [prefixWord, tailWord_3489512, baseEnd_3489512] using wordTrace_append hprefix tailTrace_3489512
  have hstable : (prefixWord ++ tailWord_3489512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489512).length < 2 ^ (prefixWord ++ tailWord_3489512).sum := by decide
  have hdescent : baseEnd_3489512 < baseStart_3489512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489523 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 6]
def baseStart_3489523 : Nat := 118140960795 + 3489523 * 2 ^ 59
def prefixEnd_3489523 : Nat := 4983230072969 + 3 ^ 40 * 3489523 * 2
def baseEnd_3489523 : Nat := 398178345315390213092107

theorem tailTrace_3489523 : CollatzResearch.WordTrace tailWord_3489523 prefixEnd_3489523 398178345315390213092107 := by
  unfold tailWord_3489523
  simp only [CollatzResearch.WordTrace]
  refine ⟨127273359737061608926465223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84848906491374405950976815 127273359737061608926465223)
  ·
    refine ⟨190910039605592413389697835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127273359737061608926465223 190910039605592413389697835)
    ·
      refine ⟨286365059408388620084546753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190910039605592413389697835 286365059408388620084546753)
      ·
        refine ⟨214773794556291465063410065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286365059408388620084546753 214773794556291465063410065)
        ·
          refine ⟨161080345917218598797557549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214773794556291465063410065 161080345917218598797557549)
          ·
            refine ⟨60405129718956974549084081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161080345917218598797557549 60405129718956974549084081)
            ·
              refine ⟨45303847289217730911813061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60405129718956974549084081 45303847289217730911813061)
              ·
                refine ⟨8494471366728324545964949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45303847289217730911813061 8494471366728324545964949)
                ·
                  refine ⟨398178345315390213092107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8494471366728324545964949 398178345315390213092107)
                  ·
                    rfl

theorem cell22_3489523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 6].length) (baseStart_3489523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489523 prefixEnd_3489523 := by exact prefixLift 3489523
  have htrace : WordTrace (prefixWord ++ tailWord_3489523) baseStart_3489523 baseEnd_3489523 := by
    simpa [prefixWord, tailWord_3489523, baseEnd_3489523] using wordTrace_append hprefix tailTrace_3489523
  have hstable : (prefixWord ++ tailWord_3489523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489523).length < 2 ^ (prefixWord ++ tailWord_3489523).sum := by decide
  have hdescent : baseEnd_3489523 < baseStart_3489523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489553 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 3, 6]
def baseStart_3489553 : Nat := 118140960795 + 3489553 * 2 ^ 59
def prefixEnd_3489553 : Nat := 4983230072969 + 3 ^ 40 * 3489553 * 2
def baseEnd_3489553 : Nat := 1194545305559260561026229

theorem tailTrace_3489553 : CollatzResearch.WordTrace tailWord_3489553 prefixEnd_3489553 1194545305559260561026229 := by
  unfold tailWord_3489553
  simp only [CollatzResearch.WordTrace]
  refine ⟨127274453926952924050057313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84849635951301949366704875 127274453926952924050057313)
  ·
    refine ⟨95455840445214693037542985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127274453926952924050057313 95455840445214693037542985)
    ·
      refine ⟨71591880333911019778157239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95455840445214693037542985 71591880333911019778157239)
      ·
        refine ⟨107387820500866529667235859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71591880333911019778157239 107387820500866529667235859)
        ·
          refine ⟨161081730751299794500853789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107387820500866529667235859 161081730751299794500853789)
          ·
            refine ⟨60405649031737422937820171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161081730751299794500853789 60405649031737422937820171)
            ·
              refine ⟨90608473547606134406730257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60405649031737422937820171 90608473547606134406730257)
              ·
                refine ⟨67956355160704600805047693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90608473547606134406730257 67956355160704600805047693)
                ·
                  refine ⟨25483633185264225301892885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67956355160704600805047693 25483633185264225301892885)
                  ·
                    refine ⟨1194545305559260561026229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25483633185264225301892885 1194545305559260561026229)
                    ·
                      rfl

theorem cell22_3489553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_3489553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489553 prefixEnd_3489553 := by exact prefixLift 3489553
  have htrace : WordTrace (prefixWord ++ tailWord_3489553) baseStart_3489553 baseEnd_3489553 := by
    simpa [prefixWord, tailWord_3489553, baseEnd_3489553] using wordTrace_append hprefix tailTrace_3489553
  have hstable : (prefixWord ++ tailWord_3489553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489553).length < 2 ^ (prefixWord ++ tailWord_3489553).sum := by decide
  have hdescent : baseEnd_3489553 < baseStart_3489553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489557 : List Nat := [1, 3, 2, 1, 2, 4, 1, 4, 4]
def baseStart_3489557 : Nat := 118140960795 + 3489557 * 2 ^ 59
def prefixEnd_3489557 : Nat := 4983230072969 + 3 ^ 40 * 3489557 * 2
def baseEnd_3489557 : Nat := 398182224947001961308739

theorem tailTrace_3489557 : CollatzResearch.WordTrace tailWord_3489557 prefixEnd_3489557 398182224947001961308739 := by
  unfold tailWord_3489557
  simp only [CollatzResearch.WordTrace]
  refine ⟨127274599818938432733202925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84849733212625621822135283 127274599818938432733202925)
  ·
    refine ⟨47727974932101912274951097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127274599818938432733202925 47727974932101912274951097)
    ·
      refine ⟨35795981199076434206213323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47727974932101912274951097 35795981199076434206213323)
      ·
        refine ⟨53693971798614651309319985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35795981199076434206213323 53693971798614651309319985)
        ·
          refine ⟨40270478848960988481989989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53693971798614651309319985 40270478848960988481989989)
          ·
            refine ⟨7550714784180185340373123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40270478848960988481989989 7550714784180185340373123)
            ·
              refine ⟨11326072176270278010559685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7550714784180185340373123 11326072176270278010559685)
              ·
                refine ⟨2123638533050677126979941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11326072176270278010559685 2123638533050677126979941)
                ·
                  refine ⟨398182224947001961308739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2123638533050677126979941 398182224947001961308739)
                  ·
                    rfl

theorem cell22_3489557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_3489557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489557 prefixEnd_3489557 := by exact prefixLift 3489557
  have htrace : WordTrace (prefixWord ++ tailWord_3489557) baseStart_3489557 baseEnd_3489557 := by
    simpa [prefixWord, tailWord_3489557, baseEnd_3489557] using wordTrace_append hprefix tailTrace_3489557
  have hstable : (prefixWord ++ tailWord_3489557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489557).length < 2 ^ (prefixWord ++ tailWord_3489557).sum := by decide
  have hdescent : baseEnd_3489557 < baseStart_3489557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489570 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_3489570 : Nat := 118140960795 + 3489570 * 2 ^ 59
def prefixEnd_3489570 : Nat := 4983230072969 + 3 ^ 40 * 3489570 * 2
def baseEnd_3489570 : Nat := 1194551125006678183351177

theorem tailTrace_3489570 : CollatzResearch.WordTrace tailWord_3489570 prefixEnd_3489570 1194551125006678183351177 := by
  unfold tailWord_3489570
  simp only [CollatzResearch.WordTrace]
  refine ⟨31818768491972833988356541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84850049311927557302284109 31818768491972833988356541)
  ·
    refine ⟨11932038184489812745633703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31818768491972833988356541 11932038184489812745633703)
    ·
      refine ⟨17898057276734719118450555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11932038184489812745633703 17898057276734719118450555)
      ·
        refine ⟨26847085915102078677675833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17898057276734719118450555 26847085915102078677675833)
        ·
          refine ⟨20135314436326559008256875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26847085915102078677675833 20135314436326559008256875)
          ·
            refine ⟨30202971654489838512385313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20135314436326559008256875 30202971654489838512385313)
            ·
              refine ⟨22652228740867378884288985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30202971654489838512385313 22652228740867378884288985)
              ·
                refine ⟨16989171555650534163216739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22652228740867378884288985 16989171555650534163216739)
                ·
                  refine ⟨25483757333475801244825109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16989171555650534163216739 25483757333475801244825109)
                  ·
                    refine ⟨1194551125006678183351177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25483757333475801244825109 1194551125006678183351177)
                    ·
                      rfl

theorem cell22_3489570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_3489570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489570 prefixEnd_3489570 := by exact prefixLift 3489570
  have htrace : WordTrace (prefixWord ++ tailWord_3489570) baseStart_3489570 baseEnd_3489570 := by
    simpa [prefixWord, tailWord_3489570, baseEnd_3489570] using wordTrace_append hprefix tailTrace_3489570
  have hstable : (prefixWord ++ tailWord_3489570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489570).length < 2 ^ (prefixWord ++ tailWord_3489570).sum := by decide
  have hdescent : baseEnd_3489570 < baseStart_3489570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489572 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_3489572 : Nat := 118140960795 + 3489572 * 2 ^ 59
def prefixEnd_3489572 : Nat := 4983230072969 + 3 ^ 40 * 3489572 * 2
def baseEnd_3489572 : Nat := 1194551809647550844801171

theorem tailTrace_3489572 : CollatzResearch.WordTrace tailWord_3489572 prefixEnd_3489572 1194551809647550844801171 := by
  unfold tailWord_3489572
  simp only [CollatzResearch.WordTrace]
  refine ⟨63637573456942045147499485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84850097942589393529999313 63637573456942045147499485)
  ·
    refine ⟨23864090046353266930312307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63637573456942045147499485 23864090046353266930312307)
    ·
      refine ⟨35796135069529900395468461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23864090046353266930312307 35796135069529900395468461)
      ·
        refine ⟨13423550651073712648300673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35796135069529900395468461 13423550651073712648300673)
        ·
          refine ⟨10067662988305284486225505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13423550651073712648300673 10067662988305284486225505)
          ·
            refine ⟨7550747241228963364669129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10067662988305284486225505 7550747241228963364669129)
            ·
              refine ⟨5663060430921722523501847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7550747241228963364669129 5663060430921722523501847)
              ·
                refine ⟨8494590646382583785252771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5663060430921722523501847 8494590646382583785252771)
                ·
                  refine ⟨12741885969573875677879157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8494590646382583785252771 12741885969573875677879157)
                  ·
                    refine ⟨1194551809647550844801171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12741885969573875677879157 1194551809647550844801171)
                    ·
                      rfl

theorem cell22_3489572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_3489572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489572 prefixEnd_3489572 := by exact prefixLift 3489572
  have htrace : WordTrace (prefixWord ++ tailWord_3489572) baseStart_3489572 baseEnd_3489572 := by
    simpa [prefixWord, tailWord_3489572, baseEnd_3489572] using wordTrace_append hprefix tailTrace_3489572
  have hstable : (prefixWord ++ tailWord_3489572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489572).length < 2 ^ (prefixWord ++ tailWord_3489572).sum := by decide
  have hdescent : baseEnd_3489572 < baseStart_3489572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489583 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 2, 7]
def baseStart_3489583 : Nat := 118140960795 + 3489583 * 2 ^ 59
def prefixEnd_3489583 : Nat := 4983230072969 + 3 ^ 40 * 3489583 * 2
def baseEnd_3489583 : Nat := 1194555575172350482776137

theorem tailTrace_3489583 : CollatzResearch.WordTrace tailWord_3489583 prefixEnd_3489583 1194555575172350482776137 := by
  unfold tailWord_3489583
  simp only [CollatzResearch.WordTrace]
  refine ⟨127275548116844239173649403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84850365411229492782432935 127275548116844239173649403)
  ·
    refine ⟨190913322175266358760474105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127275548116844239173649403 190913322175266358760474105)
    ·
      refine ⟨143184991631449769070355579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190913322175266358760474105 143184991631449769070355579)
      ·
        refine ⟨214777487447174653605533369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143184991631449769070355579 214777487447174653605533369)
        ·
          refine ⟨161083115585380990204150027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214777487447174653605533369 161083115585380990204150027)
          ·
            refine ⟨241624673378071485306225041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161083115585380990204150027 241624673378071485306225041)
            ·
              refine ⟨181218505033553613979668781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241624673378071485306225041 181218505033553613979668781)
              ·
                refine ⟨67956939387582605242375793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181218505033553613979668781 67956939387582605242375793)
                ·
                  refine ⟨50967704540686953931781845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67956939387582605242375793 50967704540686953931781845)
                  ·
                    refine ⟨1194555575172350482776137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50967704540686953931781845 1194555575172350482776137)
                    ·
                      rfl

theorem cell22_3489583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_3489583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489583 prefixEnd_3489583 := by exact prefixLift 3489583
  have htrace : WordTrace (prefixWord ++ tailWord_3489583) baseStart_3489583 baseEnd_3489583 := by
    simpa [prefixWord, tailWord_3489583, baseEnd_3489583] using wordTrace_append hprefix tailTrace_3489583
  have hstable : (prefixWord ++ tailWord_3489583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489583).length < 2 ^ (prefixWord ++ tailWord_3489583).sum := by decide
  have hdescent : baseEnd_3489583 < baseStart_3489583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489593 : List Nat := [1, 2, 1, 7, 2, 1, 2, 1, 1, 4]
def baseStart_3489593 : Nat := 118140960795 + 3489593 * 2 ^ 59
def prefixEnd_3489593 : Nat := 4983230072969 + 3 ^ 40 * 3489593 * 2
def baseEnd_3489593 : Nat := 1194558998376713790026107

theorem tailTrace_3489593 : CollatzResearch.WordTrace tailWord_3489593 prefixEnd_3489593 1194558998376713790026107 := by
  unfold tailWord_3489593
  simp only [CollatzResearch.WordTrace]
  refine ⟨127275912846808010881513433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84850608564538673921008955 127275912846808010881513433)
  ·
    refine ⟨95456934635106008161135075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127275912846808010881513433 95456934635106008161135075)
    ·
      refine ⟨143185401952659012241702613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95456934635106008161135075 143185401952659012241702613)
      ·
        refine ⟨3355907858265445599414905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 143185401952659012241702613 3355907858265445599414905)
        ·
          refine ⟨2516930893699084199561179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3355907858265445599414905 2516930893699084199561179)
          ·
            refine ⟨3775396340548626299341769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516930893699084199561179 3775396340548626299341769)
            ·
              refine ⟨2831547255411469724506327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3775396340548626299341769 2831547255411469724506327)
              ·
                refine ⟨4247320883117204586759491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831547255411469724506327 4247320883117204586759491)
                ·
                  refine ⟨6370981324675806880139237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247320883117204586759491 6370981324675806880139237)
                  ·
                    refine ⟨1194558998376713790026107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6370981324675806880139237 1194558998376713790026107)
                    ·
                      rfl

theorem cell22_3489593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 1, 4].length) (baseStart_3489593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489593 prefixEnd_3489593 := by exact prefixLift 3489593
  have htrace : WordTrace (prefixWord ++ tailWord_3489593) baseStart_3489593 baseEnd_3489593 := by
    simpa [prefixWord, tailWord_3489593, baseEnd_3489593] using wordTrace_append hprefix tailTrace_3489593
  have hstable : (prefixWord ++ tailWord_3489593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489593).length < 2 ^ (prefixWord ++ tailWord_3489593).sum := by decide
  have hdescent : baseEnd_3489593 < baseStart_3489593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489606 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_3489606 : Nat := 118140960795 + 3489606 * 2 ^ 59
def prefixEnd_3489606 : Nat := 4983230072969 + 3 ^ 40 * 3489606 * 2
def baseEnd_3489606 : Nat := 1194563448542386089451067

theorem tailTrace_3489606 : CollatzResearch.WordTrace tailWord_3489606 prefixEnd_3489606 1194563448542386089451067 := by
  unfold tailWord_3489606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3977387093617528565679271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84850924663840609401157781 3977387093617528565679271)
  ·
    refine ⟨5966080640426292848518907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3977387093617528565679271 5966080640426292848518907)
    ·
      refine ⟨8949120960639439272778361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5966080640426292848518907 8949120960639439272778361)
      ·
        refine ⟨6711840720479579454583771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8949120960639439272778361 6711840720479579454583771)
        ·
          refine ⟨10067761080719369181875657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6711840720479579454583771 10067761080719369181875657)
          ·
            refine ⟨7550820810539526886406743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10067761080719369181875657 7550820810539526886406743)
            ·
              refine ⟨11326231215809290329610115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7550820810539526886406743 11326231215809290329610115)
              ·
                refine ⟨16989346823713935494415173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11326231215809290329610115 16989346823713935494415173)
                ·
                  refine ⟨3185502529446362905202845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16989346823713935494415173 3185502529446362905202845)
                  ·
                    refine ⟨1194563448542386089451067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3185502529446362905202845 1194563448542386089451067)
                    ·
                      rfl

theorem cell22_3489606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_3489606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489606 prefixEnd_3489606 := by exact prefixLift 3489606
  have htrace : WordTrace (prefixWord ++ tailWord_3489606) baseStart_3489606 baseEnd_3489606 := by
    simpa [prefixWord, tailWord_3489606, baseEnd_3489606] using wordTrace_append hprefix tailTrace_3489606
  have hstable : (prefixWord ++ tailWord_3489606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489606).length < 2 ^ (prefixWord ++ tailWord_3489606).sum := by decide
  have hdescent : baseEnd_3489606 < baseStart_3489606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489617 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 3, 3]
def baseStart_3489617 : Nat := 118140960795 + 3489617 * 2 ^ 59
def prefixEnd_3489617 : Nat := 4983230072969 + 3 ^ 40 * 3489617 * 2
def baseEnd_3489617 : Nat := 1194567214067185727426033

theorem tailTrace_3489617 : CollatzResearch.WordTrace tailWord_3489617 prefixEnd_3489617 1194567214067185727426033 := by
  unfold tailWord_3489617
  simp only [CollatzResearch.WordTrace]
  refine ⟨127276788198721062980387105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84851192132480708653591403 127276788198721062980387105)
  ·
    refine ⟨95457591149040797235290329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127276788198721062980387105 95457591149040797235290329)
    ·
      refine ⟨71593193361780597926467747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95457591149040797235290329 71593193361780597926467747)
      ·
        refine ⟨107389790042670896889701621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71593193361780597926467747 107389790042670896889701621)
        ·
          refine ⟨10067792816500396583409527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107389790042670896889701621 10067792816500396583409527)
          ·
            refine ⟨15101689224750594875114291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10067792816500396583409527 15101689224750594875114291)
            ·
              refine ⟨22652533837125892312671437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15101689224750594875114291 22652533837125892312671437)
              ·
                refine ⟨8494700188922209617251789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22652533837125892312671437 8494700188922209617251789)
                ·
                  refine ⟨3185512570845828606469421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8494700188922209617251789 3185512570845828606469421)
                  ·
                    refine ⟨1194567214067185727426033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3185512570845828606469421 1194567214067185727426033)
                    ·
                      rfl

theorem cell22_3489617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_3489617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489617 prefixEnd_3489617 := by exact prefixLift 3489617
  have htrace : WordTrace (prefixWord ++ tailWord_3489617) baseStart_3489617 baseEnd_3489617 := by
    simpa [prefixWord, tailWord_3489617, baseEnd_3489617] using wordTrace_append hprefix tailTrace_3489617
  have hstable : (prefixWord ++ tailWord_3489617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489617).length < 2 ^ (prefixWord ++ tailWord_3489617).sum := by decide
  have hdescent : baseEnd_3489617 < baseStart_3489617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489634 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_3489634 : Nat := 118140960795 + 3489634 * 2 ^ 59
def prefixEnd_3489634 : Nat := 4983230072969 + 3 ^ 40 * 3489634 * 2
def baseEnd_3489634 : Nat := 1194573033514603349750981

theorem tailTrace_3489634 : CollatzResearch.WordTrace tailWord_3489634 prefixEnd_3489634 1194573033514603349750981 := by
  unfold tailWord_3489634
  simp only [CollatzResearch.WordTrace]
  refine ⟨31819352059914868720938989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84851605493106316589170637 31819352059914868720938989)
  ·
    refine ⟨11932257022468075770352121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31819352059914868720938989 11932257022468075770352121)
    ·
      refine ⟨8949192766851056827764091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11932257022468075770352121 8949192766851056827764091)
      ·
        refine ⟨13423789150276585241646137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8949192766851056827764091 13423789150276585241646137)
        ·
          refine ⟨10067841862707438931234603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13423789150276585241646137 10067841862707438931234603)
          ·
            refine ⟨15101762794061158396851905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10067841862707438931234603 15101762794061158396851905)
            ·
              refine ⟨11326322095545868797638929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15101762794061158396851905 11326322095545868797638929)
              ·
                refine ⟨8494741571659401598229197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11326322095545868797638929 8494741571659401598229197)
                ·
                  refine ⟨3185528089372275599335949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8494741571659401598229197 3185528089372275599335949)
                  ·
                    refine ⟨1194573033514603349750981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3185528089372275599335949 1194573033514603349750981)
                    ·
                      rfl

theorem cell22_3489634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_3489634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489634 prefixEnd_3489634 := by exact prefixLift 3489634
  have htrace : WordTrace (prefixWord ++ tailWord_3489634) baseStart_3489634 baseEnd_3489634 := by
    simpa [prefixWord, tailWord_3489634, baseEnd_3489634] using wordTrace_append hprefix tailTrace_3489634
  have hstable : (prefixWord ++ tailWord_3489634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489634).length < 2 ^ (prefixWord ++ tailWord_3489634).sum := by decide
  have hdescent : baseEnd_3489634 < baseStart_3489634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489645 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_3489645 : Nat := 118140960795 + 3489645 * 2 ^ 59
def prefixEnd_3489645 : Nat := 4983230072969 + 3 ^ 40 * 3489645 * 2
def baseEnd_3489645 : Nat := 1194576799039402987725947

theorem tailTrace_3489645 : CollatzResearch.WordTrace tailWord_3489645 prefixEnd_3489645 1194576799039402987725947 := by
  unfold tailWord_3489645
  simp only [CollatzResearch.WordTrace]
  refine ⟨127277809442619623762406389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84851872961746415841604259 127277809442619623762406389)
  ·
    refine ⟨11932294635245589727725599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127277809442619623762406389 11932294635245589727725599)
    ·
      refine ⟨17898441952868384591588399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11932294635245589727725599 17898441952868384591588399)
      ·
        refine ⟨26847662929302576887382599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17898441952868384591588399 26847662929302576887382599)
        ·
          refine ⟨40271494393953865331073899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26847662929302576887382599 40271494393953865331073899)
          ·
            refine ⟨60407241590930797996610849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40271494393953865331073899 60407241590930797996610849)
            ·
              refine ⟨45305431193198098497458137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60407241590930797996610849 45305431193198098497458137)
              ·
                refine ⟨33979073394898573873093603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45305431193198098497458137 33979073394898573873093603)
                ·
                  refine ⟨50968610092347860809640405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33979073394898573873093603 50968610092347860809640405)
                  ·
                    refine ⟨1194576799039402987725947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50968610092347860809640405 1194576799039402987725947)
                    ·
                      rfl

theorem cell22_3489645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_3489645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489645 prefixEnd_3489645 := by exact prefixLift 3489645
  have htrace : WordTrace (prefixWord ++ tailWord_3489645) baseStart_3489645 baseEnd_3489645 := by
    simpa [prefixWord, tailWord_3489645, baseEnd_3489645] using wordTrace_append hprefix tailTrace_3489645
  have hstable : (prefixWord ++ tailWord_3489645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489645).length < 2 ^ (prefixWord ++ tailWord_3489645).sum := by decide
  have hdescent : baseEnd_3489645 < baseStart_3489645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489660 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_3489660 : Nat := 118140960795 + 3489660 * 2 ^ 59
def prefixEnd_3489660 : Nat := 4983230072969 + 3 ^ 40 * 3489660 * 2
def baseEnd_3489660 : Nat := 1194581933845947948600901

theorem tailTrace_3489660 : CollatzResearch.WordTrace tailWord_3489660 prefixEnd_3489660 1194581933845947948600901 := by
  unfold tailWord_3489660
  simp only [CollatzResearch.WordTrace]
  refine ⟨63639178268782640662101217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84852237691710187549468289 63639178268782640662101217)
  ·
    refine ⟨47729383701586980496575913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63639178268782640662101217 47729383701586980496575913)
    ·
      refine ⟨35797037776190235372431935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47729383701586980496575913 35797037776190235372431935)
      ·
        refine ⟨53695556664285353058647903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35797037776190235372431935 53695556664285353058647903)
        ·
          refine ⟨80543334996428029587971855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53695556664285353058647903 80543334996428029587971855)
          ·
            refine ⟨120815002494642044381957783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80543334996428029587971855 120815002494642044381957783)
            ·
              refine ⟨181222503741963066572936675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120815002494642044381957783 181222503741963066572936675)
              ·
                refine ⟨271833755612944599859405013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181222503741963066572936675 271833755612944599859405013)
                ·
                  refine ⟨6371103647178389059204805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 271833755612944599859405013 6371103647178389059204805)
                  ·
                    refine ⟨1194581933845947948600901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6371103647178389059204805 1194581933845947948600901)
                    ·
                      rfl

theorem cell22_3489660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_3489660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489660 prefixEnd_3489660 := by exact prefixLift 3489660
  have htrace : WordTrace (prefixWord ++ tailWord_3489660) baseStart_3489660 baseEnd_3489660 := by
    simpa [prefixWord, tailWord_3489660, baseEnd_3489660] using wordTrace_append hprefix tailTrace_3489660
  have hstable : (prefixWord ++ tailWord_3489660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489660).length < 2 ^ (prefixWord ++ tailWord_3489660).sum := by decide
  have hdescent : baseEnd_3489660 < baseStart_3489660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489726 : List Nat := [4, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_3489726 : Nat := 118140960795 + 3489726 * 2 ^ 59
def prefixEnd_3489726 : Nat := 4983230072969 + 3 ^ 40 * 3489726 * 2
def baseEnd_3489726 : Nat := 398201508998248592150233

theorem tailTrace_3489726 : CollatzResearch.WordTrace tailWord_3489726 prefixEnd_3489726 398201508998248592150233 := by
  unfold tailWord_3489726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15910095469415771824513129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84853842503550783064070021 15910095469415771824513129)
  ·
    refine ⟨11932571602061828868384847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15910095469415771824513129 11932571602061828868384847)
    ·
      refine ⟨17898857403092743302577271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11932571602061828868384847 17898857403092743302577271)
      ·
        refine ⟨26848286104639114953865907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17898857403092743302577271 26848286104639114953865907)
        ·
          refine ⟨40272429156958672430798861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26848286104639114953865907 40272429156958672430798861)
          ·
            refine ⟨15102160933859502161549573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40272429156958672430798861 15102160933859502161549573)
            ·
              refine ⟨2831655175098656655290545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15102160933859502161549573 2831655175098656655290545)
              ·
                refine ⟨2123741381323992491467909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2831655175098656655290545 2123741381323992491467909)
                ·
                  refine ⟨398201508998248592150233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2123741381323992491467909 398201508998248592150233)
                  ·
                    rfl

theorem cell22_3489726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_3489726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489726 prefixEnd_3489726 := by exact prefixLift 3489726
  have htrace : WordTrace (prefixWord ++ tailWord_3489726) baseStart_3489726 baseEnd_3489726 := by
    simpa [prefixWord, tailWord_3489726, baseEnd_3489726] using wordTrace_append hprefix tailTrace_3489726
  have hstable : (prefixWord ++ tailWord_3489726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489726).length < 2 ^ (prefixWord ++ tailWord_3489726).sum := by decide
  have hdescent : baseEnd_3489726 < baseStart_3489726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489735 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 2, 7]
def baseStart_3489735 : Nat := 118140960795 + 3489735 * 2 ^ 59
def prefixEnd_3489735 : Nat := 4983230072969 + 3 ^ 40 * 3489735 * 2
def baseEnd_3489735 : Nat := 1194607607878672752975671

theorem tailTrace_3489735 : CollatzResearch.WordTrace tailWord_3489735 prefixEnd_3489735 1194607607878672752975671 := by
  unfold tailWord_3489735
  simp only [CollatzResearch.WordTrace]
  refine ⟨127281092012293569133182659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84854061341529046088788439 127281092012293569133182659)
  ·
    refine ⟨190921638018440353699773989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127281092012293569133182659 190921638018440353699773989)
    ·
      refine ⟨35797807128457566318707623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190921638018440353699773989 35797807128457566318707623)
      ·
        refine ⟨53696710692686349478061435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35797807128457566318707623 53696710692686349478061435)
        ·
          refine ⟨80545066039029524217092153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53696710692686349478061435 80545066039029524217092153)
          ·
            refine ⟨60408799529272143162819115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80545066039029524217092153 60408799529272143162819115)
            ·
              refine ⟨90613199293908214744228673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60408799529272143162819115 90613199293908214744228673)
              ·
                refine ⟨67959899470431161058171505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90613199293908214744228673 67959899470431161058171505)
                ·
                  refine ⟨50969924602823370793628629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67959899470431161058171505 50969924602823370793628629)
                  ·
                    refine ⟨1194607607878672752975671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50969924602823370793628629 1194607607878672752975671)
                    ·
                      rfl

theorem cell22_3489735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_3489735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489735 prefixEnd_3489735 := by exact prefixLift 3489735
  have htrace : WordTrace (prefixWord ++ tailWord_3489735) baseStart_3489735 baseEnd_3489735 := by
    simpa [prefixWord, tailWord_3489735, baseEnd_3489735] using wordTrace_append hprefix tailTrace_3489735
  have hstable : (prefixWord ++ tailWord_3489735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489735).length < 2 ^ (prefixWord ++ tailWord_3489735).sum := by decide
  have hdescent : baseEnd_3489735 < baseStart_3489735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489754 : List Nat := [3, 1, 1, 2, 5, 1, 3, 6]
def baseStart_3489754 : Nat := 118140960795 + 3489754 * 2 ^ 59
def prefixEnd_3489754 : Nat := 4983230072969 + 3 ^ 40 * 3489754 * 2
def baseEnd_3489754 : Nat := 132734901329662559638957

theorem tailTrace_3489754 : CollatzResearch.WordTrace tailWord_3489754 prefixEnd_3489754 132734901329662559638957 := by
  unfold tailWord_3489754
  simp only [CollatzResearch.WordTrace]
  refine ⟨31820446249806183844531079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84854523332816490252082877 31820446249806183844531079)
  ·
    refine ⟨47730669374709275766796619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31820446249806183844531079 47730669374709275766796619)
    ·
      refine ⟨71596004062063913650194929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47730669374709275766796619 71596004062063913650194929)
      ·
        refine ⟨53697003046547935237646197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71596004062063913650194929 53697003046547935237646197)
        ·
          refine ⟨5034094035613868928529331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53697003046547935237646197 5034094035613868928529331)
          ·
            refine ⟨7551141053420803392793997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5034094035613868928529331 7551141053420803392793997)
            ·
              refine ⟨2831677895032801272297749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7551141053420803392793997 2831677895032801272297749)
              ·
                refine ⟨132734901329662559638957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2831677895032801272297749 132734901329662559638957)
                ·
                  rfl

theorem cell22_3489754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_3489754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489754 prefixEnd_3489754 := by exact prefixLift 3489754
  have htrace : WordTrace (prefixWord ++ tailWord_3489754) baseStart_3489754 baseEnd_3489754 := by
    simpa [prefixWord, tailWord_3489754, baseEnd_3489754] using wordTrace_append hprefix tailTrace_3489754
  have hstable : (prefixWord ++ tailWord_3489754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489754).length < 2 ^ (prefixWord ++ tailWord_3489754).sum := by decide
  have hdescent : baseEnd_3489754 < baseStart_3489754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489797 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_3489797 : Nat := 118140960795 + 3489797 * 2 ^ 59
def prefixEnd_3489797 : Nat := 4983230072969 + 3 ^ 40 * 3489797 * 2
def baseEnd_3489797 : Nat := 1194628831745725257925481

theorem tailTrace_3489797 : CollatzResearch.WordTrace tailWord_3489797 prefixEnd_3489797 1194628831745725257925481 := by
  unfold tailWord_3489797
  simp only [CollatzResearch.WordTrace]
  refine ⟨127283353338068953721939645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84855568892045969147959763 127283353338068953721939645)
  ·
    refine ⟨47731257501775857645727367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127283353338068953721939645 47731257501775857645727367)
    ·
      refine ⟨71596886252663786468591051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47731257501775857645727367 71596886252663786468591051)
      ·
        refine ⟨107395329378995679702886577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71596886252663786468591051 107395329378995679702886577)
        ·
          refine ⟨80546497034246759777164933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107395329378995679702886577 80546497034246759777164933)
          ·
            refine ⟨15102468193921267458218425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80546497034246759777164933 15102468193921267458218425)
            ·
              refine ⟨11326851145440950593663819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15102468193921267458218425 11326851145440950593663819)
              ·
                refine ⟨16990276718161425890495729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11326851145440950593663819 16990276718161425890495729)
                ·
                  refine ⟨12742707538621069417871797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16990276718161425890495729 12742707538621069417871797)
                  ·
                    refine ⟨1194628831745725257925481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12742707538621069417871797 1194628831745725257925481)
                    ·
                      rfl

theorem cell22_3489797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_3489797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489797 prefixEnd_3489797 := by exact prefixLift 3489797
  have htrace : WordTrace (prefixWord ++ tailWord_3489797) baseStart_3489797 baseEnd_3489797 := by
    simpa [prefixWord, tailWord_3489797, baseEnd_3489797] using wordTrace_append hprefix tailTrace_3489797
  have hstable : (prefixWord ++ tailWord_3489797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489797).length < 2 ^ (prefixWord ++ tailWord_3489797).sum := by decide
  have hdescent : baseEnd_3489797 < baseStart_3489797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489805 : List Nat := [1, 7, 1, 2, 1, 2, 2, 6]
def baseStart_3489805 : Nat := 118140960795 + 3489805 * 2 ^ 59
def prefixEnd_3489805 : Nat := 4983230072969 + 3 ^ 40 * 3489805 * 2
def baseEnd_3489805 : Nat := 132736841145468433747273

theorem tailTrace_3489805 : CollatzResearch.WordTrace tailWord_3489805 prefixEnd_3489805 132736841145468433747273 := by
  unfold tailWord_3489805
  simp only [CollatzResearch.WordTrace]
  refine ⟨127283645122039971088230869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84855763414693314058820579 127283645122039971088230869)
  ·
    refine ⟨2983210432547811822380411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 127283645122039971088230869 2983210432547811822380411)
    ·
      refine ⟨4474815648821717733570617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2983210432547811822380411 4474815648821717733570617)
      ·
        refine ⟨3356111736616288300177963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4474815648821717733570617 3356111736616288300177963)
        ·
          refine ⟨5034167604924432450266945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3356111736616288300177963 5034167604924432450266945)
          ·
            refine ⟨3775625703693324337700209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5034167604924432450266945 3775625703693324337700209)
            ·
              refine ⟨2831719277769993253275157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3775625703693324337700209 2831719277769993253275157)
              ·
                refine ⟨132736841145468433747273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2831719277769993253275157 132736841145468433747273)
                ·
                  rfl

theorem cell22_3489805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 6].length) (baseStart_3489805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489805 prefixEnd_3489805 := by exact prefixLift 3489805
  have htrace : WordTrace (prefixWord ++ tailWord_3489805) baseStart_3489805 baseEnd_3489805 := by
    simpa [prefixWord, tailWord_3489805, baseEnd_3489805] using wordTrace_append hprefix tailTrace_3489805
  have hstable : (prefixWord ++ tailWord_3489805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489805).length < 2 ^ (prefixWord ++ tailWord_3489805).sum := by decide
  have hdescent : baseEnd_3489805 < baseStart_3489805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489829 : List Nat := [1, 3, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_3489829 : Nat := 118140960795 + 3489829 * 2 ^ 59
def prefixEnd_3489829 : Nat := 4983230072969 + 3 ^ 40 * 3489829 * 2
def baseEnd_3489829 : Nat := 1194639785999687841125383

theorem tailTrace_3489829 : CollatzResearch.WordTrace tailWord_3489829 prefixEnd_3489829 1194639785999687841125383 := by
  unfold tailWord_3489829
  simp only [CollatzResearch.WordTrace]
  refine ⟨127284520473953023187104541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84856346982635348791403027 127284520473953023187104541)
  ·
    refine ⟨47731695177732383695164203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127284520473953023187104541 47731695177732383695164203)
    ·
      refine ⟨71597542766598575542746305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47731695177732383695164203 71597542766598575542746305)
      ·
        refine ⟨53698157074948931657059729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71597542766598575542746305 53698157074948931657059729)
        ·
          refine ⟨40273617806211698742794797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53698157074948931657059729 40273617806211698742794797)
          ·
            refine ⟨15102606677329387028548049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40273617806211698742794797 15102606677329387028548049)
            ·
              refine ⟨11326955007997040271411037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15102606677329387028548049 11326955007997040271411037)
              ·
                refine ⟨4247608127998890101779139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11326955007997040271411037 4247608127998890101779139)
                ·
                  refine ⟨6371412191998335152668709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247608127998890101779139 6371412191998335152668709)
                  ·
                    refine ⟨1194639785999687841125383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6371412191998335152668709 1194639785999687841125383)
                    ·
                      rfl

theorem cell22_3489829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_3489829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489829 prefixEnd_3489829 := by exact prefixLift 3489829
  have htrace : WordTrace (prefixWord ++ tailWord_3489829) baseStart_3489829 baseEnd_3489829 := by
    simpa [prefixWord, tailWord_3489829, baseEnd_3489829] using wordTrace_append hprefix tailTrace_3489829
  have hstable : (prefixWord ++ tailWord_3489829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489829).length < 2 ^ (prefixWord ++ tailWord_3489829).sum := by decide
  have hdescent : baseEnd_3489829 < baseStart_3489829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489949 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_3489949 : Nat := 118140960795 + 3489949 * 2 ^ 59
def prefixEnd_3489949 : Nat := 4983230072969 + 3 ^ 40 * 3489949 * 2
def baseEnd_3489949 : Nat := 1194680864452047528125015

theorem tailTrace_3489949 : CollatzResearch.WordTrace tailWord_3489949 prefixEnd_3489949 1194680864452047528125015 := by
  unfold tailWord_3489949
  simp only [CollatzResearch.WordTrace]
  refine ⟨127288897233518283681472901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84859264822345522454315267 127288897233518283681472901)
  ·
    refine ⟨23866668231284678190276169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127288897233518283681472901 23866668231284678190276169)
    ·
      refine ⟨17900001173463508642707127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23866668231284678190276169 17900001173463508642707127)
      ·
        refine ⟨26850001760195262964060691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17900001173463508642707127 26850001760195262964060691)
        ·
          refine ⟨40275002640292894446091037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26850001760195262964060691 40275002640292894446091037)
          ·
            refine ⟨15103125990109835417284139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40275002640292894446091037 15103125990109835417284139)
            ·
              refine ⟨22654688985164753125926209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15103125990109835417284139 22654688985164753125926209)
              ·
                refine ⟨16991016738873564844444657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22654688985164753125926209 16991016738873564844444657)
                ·
                  refine ⟨12743262554155173633333493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16991016738873564844444657 12743262554155173633333493)
                  ·
                    refine ⟨1194680864452047528125015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12743262554155173633333493 1194680864452047528125015)
                    ·
                      rfl

theorem cell22_3489949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_3489949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489949 prefixEnd_3489949 := by exact prefixLift 3489949
  have htrace : WordTrace (prefixWord ++ tailWord_3489949) baseStart_3489949 baseEnd_3489949 := by
    simpa [prefixWord, tailWord_3489949, baseEnd_3489949] using wordTrace_append hprefix tailTrace_3489949
  have hstable : (prefixWord ++ tailWord_3489949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489949).length < 2 ^ (prefixWord ++ tailWord_3489949).sum := by decide
  have hdescent : baseEnd_3489949 < baseStart_3489949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489951 : List Nat := [1, 1, 2, 6, 1, 1, 3, 2, 5]
def baseStart_3489951 : Nat := 118140960795 + 3489951 * 2 ^ 59
def prefixEnd_3489951 : Nat := 4983230072969 + 3 ^ 40 * 3489951 * 2
def baseEnd_3489951 : Nat := 398227183030973396525003

theorem tailTrace_3489951 : CollatzResearch.WordTrace tailWord_3489951 prefixEnd_3489951 398227183030973396525003 := by
  unfold tailWord_3489951
  simp only [CollatzResearch.WordTrace]
  refine ⟨127288970179511038023045707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84859313453007358682030471 127288970179511038023045707)
  ·
    refine ⟨190933455269266557034568561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127288970179511038023045707 190933455269266557034568561)
    ·
      refine ⟨143200091451949917775926421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190933455269266557034568561 143200091451949917775926421)
      ·
        refine ⟨6712504286810152395746551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143200091451949917775926421 6712504286810152395746551)
        ·
          refine ⟨10068756430215228593619827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6712504286810152395746551 10068756430215228593619827)
          ·
            refine ⟨15103134645322842890429741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10068756430215228593619827 15103134645322842890429741)
            ·
              refine ⟨5663675491996066083911153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15103134645322842890429741 5663675491996066083911153)
              ·
                refine ⟨4247756618997049562933365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5663675491996066083911153 4247756618997049562933365)
                ·
                  refine ⟨398227183030973396525003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4247756618997049562933365 398227183030973396525003)
                  ·
                    rfl

theorem cell22_3489951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 5].length) (baseStart_3489951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489951 prefixEnd_3489951 := by exact prefixLift 3489951
  have htrace : WordTrace (prefixWord ++ tailWord_3489951) baseStart_3489951 baseEnd_3489951 := by
    simpa [prefixWord, tailWord_3489951, baseEnd_3489951] using wordTrace_append hprefix tailTrace_3489951
  have hstable : (prefixWord ++ tailWord_3489951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489951).length < 2 ^ (prefixWord ++ tailWord_3489951).sum := by decide
  have hdescent : baseEnd_3489951 < baseStart_3489951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489994 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_3489994 : Nat := 118140960795 + 3489994 * 2 ^ 59
def prefixEnd_3489994 : Nat := 4983230072969 + 3 ^ 40 * 3489994 * 2
def baseEnd_3489994 : Nat := 1194696268871682410749877

theorem tailTrace_3489994 : CollatzResearch.WordTrace tailWord_3489994 prefixEnd_3489994 1194696268871682410749877 := by
  unfold tailWord_3489994
  simp only [CollatzResearch.WordTrace]
  refine ⟨31822634629588814091715259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84860359012236837577907357 31822634629588814091715259)
  ·
    refine ⟨47733951944383221137572889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31822634629588814091715259 47733951944383221137572889)
    ·
      refine ⟨35800463958287415853179667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47733951944383221137572889 35800463958287415853179667)
      ·
        refine ⟨53700695937431123779769501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35800463958287415853179667 53700695937431123779769501)
        ·
          refine ⟨20137760976536671417413563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53700695937431123779769501 20137760976536671417413563)
          ·
            refine ⟨30206641464805007126120345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20137760976536671417413563 30206641464805007126120345)
            ·
              refine ⟨22654981098603755344590259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30206641464805007126120345 22654981098603755344590259)
              ·
                refine ⟨33982471647905633016885389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22654981098603755344590259 33982471647905633016885389)
                ·
                  refine ⟨12743426867964612381332021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33982471647905633016885389 12743426867964612381332021)
                  ·
                    refine ⟨1194696268871682410749877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12743426867964612381332021 1194696268871682410749877)
                    ·
                      rfl

theorem cell22_3489994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_3489994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3489994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3489994 prefixEnd_3489994 := by exact prefixLift 3489994
  have htrace : WordTrace (prefixWord ++ tailWord_3489994) baseStart_3489994 baseEnd_3489994 := by
    simpa [prefixWord, tailWord_3489994, baseEnd_3489994] using wordTrace_append hprefix tailTrace_3489994
  have hstable : (prefixWord ++ tailWord_3489994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489994).length < 2 ^ (prefixWord ++ tailWord_3489994).sum := by decide
  have hdescent : baseEnd_3489994 < baseStart_3489994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490009 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 4, 4]
def baseStart_3490009 : Nat := 118140960795 + 3490009 * 2 ^ 59
def prefixEnd_3490009 : Nat := 4983230072969 + 3 ^ 40 * 3490009 * 2
def baseEnd_3490009 : Nat := 1194701403678227371624831

theorem tailTrace_3490009 : CollatzResearch.WordTrace tailWord_3490009 prefixEnd_3490009 1194701403678227371624831 := by
  unfold tailWord_3490009
  simp only [CollatzResearch.WordTrace]
  refine ⟨127291085613300913928657081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84860723742200609285771387 127291085613300913928657081)
  ·
    refine ⟨95468314209975685446492811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127291085613300913928657081 95468314209975685446492811)
    ·
      refine ⟨143202471314963528169739217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95468314209975685446492811 143202471314963528169739217)
      ·
        refine ⟨107401853486222646127304413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143202471314963528169739217 107401853486222646127304413)
        ·
          refine ⟨40275695057333492297739155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107401853486222646127304413 40275695057333492297739155)
          ·
            refine ⟨60413542586000238446608733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40275695057333492297739155 60413542586000238446608733)
            ·
              refine ⟨22655078469750089417478275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60413542586000238446608733 22655078469750089417478275)
              ·
                refine ⟨33982617704625134126217413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22655078469750089417478275 33982617704625134126217413)
                ·
                  refine ⟨6371740819617212648665765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33982617704625134126217413 6371740819617212648665765)
                  ·
                    refine ⟨1194701403678227371624831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6371740819617212648665765 1194701403678227371624831)
                    ·
                      rfl

theorem cell22_3490009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_3490009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490009 prefixEnd_3490009 := by exact prefixLift 3490009
  have htrace : WordTrace (prefixWord ++ tailWord_3490009) baseStart_3490009 baseEnd_3490009 := by
    simpa [prefixWord, tailWord_3490009, baseEnd_3490009] using wordTrace_append hprefix tailTrace_3490009
  have hstable : (prefixWord ++ tailWord_3490009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490009).length < 2 ^ (prefixWord ++ tailWord_3490009).sum := by decide
  have hdescent : baseEnd_3490009 < baseStart_3490009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490013 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 6]
def baseStart_3490013 : Nat := 118140960795 + 3490013 * 2 ^ 59
def prefixEnd_3490013 : Nat := 4983230072969 + 3 ^ 40 * 3490013 * 2
def baseEnd_3490013 : Nat := 398234257653324231508273

theorem tailTrace_3490013 : CollatzResearch.WordTrace tailWord_3490013 prefixEnd_3490013 398234257653324231508273 := by
  unfold tailWord_3490013
  simp only [CollatzResearch.WordTrace]
  refine ⟨127291231505286422611802693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84860821003524281741201795 127291231505286422611802693)
  ·
    refine ⟨23867105907241204239713005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127291231505286422611802693 23867105907241204239713005)
    ·
      refine ⟨8950164715215451589892377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23867105907241204239713005 8950164715215451589892377)
      ·
        refine ⟨6712623536411588692419283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8950164715215451589892377 6712623536411588692419283)
        ·
          refine ⟨10068935304617383038628925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6712623536411588692419283 10068935304617383038628925)
          ·
            refine ⟨3775850739231518639485847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10068935304617383038628925 3775850739231518639485847)
            ·
              refine ⟨5663776108847277959228771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775850739231518639485847 5663776108847277959228771)
              ·
                refine ⟨8495664163270916938843157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5663776108847277959228771 8495664163270916938843157)
                ·
                  refine ⟨398234257653324231508273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8495664163270916938843157 398234257653324231508273)
                  ·
                    rfl

theorem cell22_3490013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_3490013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490013 prefixEnd_3490013 := by exact prefixLift 3490013
  have htrace : WordTrace (prefixWord ++ tailWord_3490013) baseStart_3490013 baseEnd_3490013 := by
    simpa [prefixWord, tailWord_3490013, baseEnd_3490013] using wordTrace_append hprefix tailTrace_3490013
  have hstable : (prefixWord ++ tailWord_3490013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490013).length < 2 ^ (prefixWord ++ tailWord_3490013).sum := by decide
  have hdescent : baseEnd_3490013 < baseStart_3490013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490024 : List Nat := [2, 1, 4, 1, 2, 2, 1, 9]
def baseStart_3490024 : Nat := 118140960795 + 3490024 * 2 ^ 59
def prefixEnd_3490024 : Nat := 4983230072969 + 3 ^ 40 * 3490024 * 2
def baseEnd_3490024 : Nat := 132745170942752481388865

theorem tailTrace_3490024 : CollatzResearch.WordTrace tailWord_3490024 prefixEnd_3490024 132745170942752481388865 := by
  unfold tailWord_3490024
  simp only [CollatzResearch.WordTrace]
  refine ⟨63645816354123285745226563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84861088472164380993635417 63645816354123285745226563)
  ·
    refine ⟨95468724531184928617839845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63645816354123285745226563 95468724531184928617839845)
    ·
      refine ⟨17900385849597174115844971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95468724531184928617839845 17900385849597174115844971)
      ·
        refine ⟨26850578774395761173767457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17900385849597174115844971 26850578774395761173767457)
        ·
          refine ⟨20137934080796820880325593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26850578774395761173767457 20137934080796820880325593)
          ·
            refine ⟨15103450560597615660244195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20137934080796820880325593 15103450560597615660244195)
            ·
              refine ⟨22655175840896423490366293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15103450560597615660244195 22655175840896423490366293)
              ·
                refine ⟨132745170942752481388865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22655175840896423490366293 132745170942752481388865)
                ·
                  rfl

theorem cell22_3490024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 9].length) (baseStart_3490024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490024 prefixEnd_3490024 := by exact prefixLift 3490024
  have htrace : WordTrace (prefixWord ++ tailWord_3490024) baseStart_3490024 baseEnd_3490024 := by
    simpa [prefixWord, tailWord_3490024, baseEnd_3490024] using wordTrace_append hprefix tailTrace_3490024
  have hstable : (prefixWord ++ tailWord_3490024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490024).length < 2 ^ (prefixWord ++ tailWord_3490024).sum := by decide
  have hdescent : baseEnd_3490024 < baseStart_3490024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490069 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 7]
def baseStart_3490069 : Nat := 118140960795 + 3490069 * 2 ^ 59
def prefixEnd_3490069 : Nat := 4983230072969 + 3 ^ 40 * 3490069 * 2
def baseEnd_3490069 : Nat := 398240647634802405041549

theorem tailTrace_3490069 : CollatzResearch.WordTrace tailWord_3490069 prefixEnd_3490069 398240647634802405041549 := by
  unfold tailWord_3490069
  simp only [CollatzResearch.WordTrace]
  refine ⟨127293273993083544175841261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84862182662055696117227507 127293273993083544175841261)
  ·
    refine ⟨47734977747406329065940473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127293273993083544175841261 47734977747406329065940473)
    ·
      refine ⟨35801233310554746799455355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47734977747406329065940473 35801233310554746799455355)
      ·
        refine ⟨53701849965832120199183033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35801233310554746799455355 53701849965832120199183033)
        ·
          refine ⟨40276387474374090149387275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53701849965832120199183033 40276387474374090149387275)
          ·
            refine ⟨60414581211561135224080913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40276387474374090149387275 60414581211561135224080913)
            ·
              refine ⟨45310935908670851418060685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60414581211561135224080913 45310935908670851418060685)
              ·
                refine ⟨16991600965751569281772757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45310935908670851418060685 16991600965751569281772757)
                ·
                  refine ⟨398240647634802405041549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16991600965751569281772757 398240647634802405041549)
                  ·
                    rfl

theorem cell22_3490069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_3490069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490069 prefixEnd_3490069 := by exact prefixLift 3490069
  have htrace : WordTrace (prefixWord ++ tailWord_3490069) baseStart_3490069 baseEnd_3490069 := by
    simpa [prefixWord, tailWord_3490069, baseEnd_3490069] using wordTrace_append hprefix tailTrace_3490069
  have hstable : (prefixWord ++ tailWord_3490069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490069).length < 2 ^ (prefixWord ++ tailWord_3490069).sum := by decide
  have hdescent : baseEnd_3490069 < baseStart_3490069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490090 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 3, 3]
def baseStart_3490090 : Nat := 118140960795 + 3490090 * 2 ^ 59
def prefixEnd_3490090 : Nat := 4983230072969 + 3 ^ 40 * 3490090 * 2
def baseEnd_3490090 : Nat := 1194729131633570160349583

theorem tailTrace_3490090 : CollatzResearch.WordTrace tailWord_3490090 prefixEnd_3490090 1194729131633570160349583 := by
  unfold tailWord_3490090
  simp only [CollatzResearch.WordTrace]
  refine ⟨31823509981501866190588931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84862693284004976508237149 31823509981501866190588931)
  ·
    refine ⟨47735264972252799285883397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31823509981501866190588931 47735264972252799285883397)
    ·
      refine ⟨8950362182297399866103137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47735264972252799285883397 8950362182297399866103137)
      ·
        refine ⟨6712771636723049899577353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8950362182297399866103137 6712771636723049899577353)
        ·
          refine ⟨5034578727542287424683015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6712771636723049899577353 5034578727542287424683015)
          ·
            refine ⟨7551868091313431137024523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5034578727542287424683015 7551868091313431137024523)
            ·
              refine ⟨11327802136970146705536785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7551868091313431137024523 11327802136970146705536785)
              ·
                refine ⟨8495851602727610029152589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11327802136970146705536785 8495851602727610029152589)
                ·
                  refine ⟨3185944351022853760932221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8495851602727610029152589 3185944351022853760932221)
                  ·
                    refine ⟨1194729131633570160349583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3185944351022853760932221 1194729131633570160349583)
                    ·
                      rfl

theorem cell22_3490090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_3490090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490090 prefixEnd_3490090 := by exact prefixLift 3490090
  have htrace : WordTrace (prefixWord ++ tailWord_3490090) baseStart_3490090 baseEnd_3490090 := by
    simpa [prefixWord, tailWord_3490090, baseEnd_3490090] using wordTrace_append hprefix tailTrace_3490090
  have hstable : (prefixWord ++ tailWord_3490090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490090).length < 2 ^ (prefixWord ++ tailWord_3490090).sum := by decide
  have hdescent : baseEnd_3490090 < baseStart_3490090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490161 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 2, 4]
def baseStart_3490161 : Nat := 118140960795 + 3490161 * 2 ^ 59
def prefixEnd_3490161 : Nat := 4983230072969 + 3 ^ 40 * 3490161 * 2
def baseEnd_3490161 : Nat := 1194753436384549641824365

theorem tailTrace_3490161 : CollatzResearch.WordTrace tailWord_3490161 prefixEnd_3490161 1194753436384549641824365 := by
  unfold tailWord_3490161
  simp only [CollatzResearch.WordTrace]
  refine ⟨127296629508750243888190337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84864419672500162592126891 127296629508750243888190337)
  ·
    refine ⟨95472472131562682916142753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127296629508750243888190337 95472472131562682916142753)
    ·
      refine ⟨71604354098672012187107065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95472472131562682916142753 71604354098672012187107065)
      ·
        refine ⟨53703265574004009140330299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71604354098672012187107065 53703265574004009140330299)
        ·
          refine ⟨80554898361006013710495449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53703265574004009140330299 80554898361006013710495449)
          ·
            refine ⟨60416173770754510282871587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80554898361006013710495449 60416173770754510282871587)
            ·
              refine ⟨90624260656131765424307381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60416173770754510282871587 90624260656131765424307381)
              ·
                refine ⟨8496024436512353008528817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90624260656131765424307381 8496024436512353008528817)
                ·
                  refine ⟨6372018327384264756396613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8496024436512353008528817 6372018327384264756396613)
                  ·
                    refine ⟨1194753436384549641824365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6372018327384264756396613 1194753436384549641824365)
                    ·
                      rfl

theorem cell22_3490161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_3490161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490161 prefixEnd_3490161 := by exact prefixLift 3490161
  have htrace : WordTrace (prefixWord ++ tailWord_3490161) baseStart_3490161 baseEnd_3490161 := by
    simpa [prefixWord, tailWord_3490161, baseEnd_3490161] using wordTrace_append hprefix tailTrace_3490161
  have hstable : (prefixWord ++ tailWord_3490161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490161).length < 2 ^ (prefixWord ++ tailWord_3490161).sum := by decide
  have hdescent : baseEnd_3490161 < baseStart_3490161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490165 : List Nat := [1, 3, 4, 1, 2, 1, 3, 3, 4]
def baseStart_3490165 : Nat := 118140960795 + 3490165 * 2 ^ 59
def prefixEnd_3490165 : Nat := 4983230072969 + 3 ^ 40 * 3490165 * 2
def baseEnd_3490165 : Nat := 398251601888764988241451

theorem tailTrace_3490165 : CollatzResearch.WordTrace tailWord_3490165 prefixEnd_3490165 398251601888764988241451 := by
  unfold tailWord_3490165
  simp only [CollatzResearch.WordTrace]
  refine ⟨127296775400735752571335949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84864516933823835047557299 127296775400735752571335949)
  ·
    refine ⟨47736290775275907214250981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127296775400735752571335949 47736290775275907214250981)
    ·
      refine ⟨8950554520364232602672059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47736290775275907214250981 8950554520364232602672059)
      ·
        refine ⟨13425831780546348904008089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8950554520364232602672059 13425831780546348904008089)
        ·
          refine ⟨10069373835409761678006067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13425831780546348904008089 10069373835409761678006067)
          ·
            refine ⟨15104060753114642517009101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10069373835409761678006067 15104060753114642517009101)
            ·
              refine ⟨5664022782417990943878413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15104060753114642517009101 5664022782417990943878413)
              ·
                refine ⟨2124008543406746603954405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5664022782417990943878413 2124008543406746603954405)
                ·
                  refine ⟨398251601888764988241451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2124008543406746603954405 398251601888764988241451)
                  ·
                    rfl

theorem cell22_3490165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_3490165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490165 prefixEnd_3490165 := by exact prefixLift 3490165
  have htrace : WordTrace (prefixWord ++ tailWord_3490165) baseStart_3490165 baseEnd_3490165 := by
    simpa [prefixWord, tailWord_3490165, baseEnd_3490165] using wordTrace_append hprefix tailTrace_3490165
  have hstable : (prefixWord ++ tailWord_3490165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490165).length < 2 ^ (prefixWord ++ tailWord_3490165).sum := by decide
  have hdescent : baseEnd_3490165 < baseStart_3490165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490238 : List Nat := [4, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_3490238 : Nat := 118140960795 + 3490238 * 2 ^ 59
def prefixEnd_3490238 : Nat := 4983230072969 + 3 ^ 40 * 3490238 * 2
def baseEnd_3490238 : Nat := 398259931686049035883043

theorem tailTrace_3490238 : CollatzResearch.WordTrace tailWord_3490238 prefixEnd_3490238 398259931686049035883043 := by
  unfold tailWord_3490238
  simp only [CollatzResearch.WordTrace]
  refine ⟨15912429741183910754842921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84866291952980857359162245 15912429741183910754842921)
  ·
    refine ⟨11934322305887933066132191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15912429741183910754842921 11934322305887933066132191)
    ·
      refine ⟨17901483458831899599198287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11934322305887933066132191 17901483458831899599198287)
      ·
        refine ⟨26852225188247849398797431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17901483458831899599198287 26852225188247849398797431)
        ·
          refine ⟨40278337782371774098196147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26852225188247849398797431 40278337782371774098196147)
          ·
            refine ⟨60417506673557661147294221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40278337782371774098196147 60417506673557661147294221)
            ·
              refine ⟨22656565002584122930235333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60417506673557661147294221 22656565002584122930235333)
              ·
                refine ⟨4248105937984523049419125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22656565002584122930235333 4248105937984523049419125)
                ·
                  refine ⟨398259931686049035883043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4248105937984523049419125 398259931686049035883043)
                  ·
                    rfl

theorem cell22_3490238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_3490238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490238 prefixEnd_3490238 := by exact prefixLift 3490238
  have htrace : WordTrace (prefixWord ++ tailWord_3490238) baseStart_3490238 baseEnd_3490238 := by
    simpa [prefixWord, tailWord_3490238, baseEnd_3490238] using wordTrace_append hprefix tailTrace_3490238
  have hstable : (prefixWord ++ tailWord_3490238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490238).length < 2 ^ (prefixWord ++ tailWord_3490238).sum := by decide
  have hdescent : baseEnd_3490238 < baseStart_3490238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490281 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 3, 5]
def baseStart_3490281 : Nat := 118140960795 + 3490281 * 2 ^ 59
def prefixEnd_3490281 : Nat := 4983230072969 + 3 ^ 40 * 3490281 * 2
def baseEnd_3490281 : Nat := 1194794514836909328823997

theorem tailTrace_3490281 : CollatzResearch.WordTrace tailWord_3490281 prefixEnd_3490281 1194794514836909328823997 := by
  unfold tailWord_3490281
  simp only [CollatzResearch.WordTrace]
  refine ⟨127301006268315504382558697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84867337512210336255039131 127301006268315504382558697)
  ·
    refine ⟨95475754701236628286919023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127301006268315504382558697 95475754701236628286919023)
    ·
      refine ⟨143213632051854942430378535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95475754701236628286919023 143213632051854942430378535)
      ·
        refine ⟨214820448077782413645567803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143213632051854942430378535 214820448077782413645567803)
        ·
          refine ⟨322230672116673620468351705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214820448077782413645567803 322230672116673620468351705)
          ·
            refine ⟨241673004087505215351263779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322230672116673620468351705 241673004087505215351263779)
            ·
              refine ⟨362509506131257823026895669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241673004087505215351263779 362509506131257823026895669)
              ·
                refine ⟨33985266199805420908771469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 362509506131257823026895669 33985266199805420908771469)
                ·
                  refine ⟨12744474824927032840789301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33985266199805420908771469 12744474824927032840789301)
                  ·
                    refine ⟨1194794514836909328823997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12744474824927032840789301 1194794514836909328823997)
                    ·
                      rfl

theorem cell22_3490281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_3490281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490281 prefixEnd_3490281 := by exact prefixLift 3490281
  have htrace : WordTrace (prefixWord ++ tailWord_3490281) baseStart_3490281 baseEnd_3490281 := by
    simpa [prefixWord, tailWord_3490281, baseEnd_3490281] using wordTrace_append hprefix tailTrace_3490281
  have hstable : (prefixWord ++ tailWord_3490281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490281).length < 2 ^ (prefixWord ++ tailWord_3490281).sum := by decide
  have hdescent : baseEnd_3490281 < baseStart_3490281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490315 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 1, 5]
def baseStart_3490315 : Nat := 118140960795 + 3490315 * 2 ^ 59
def prefixEnd_3490315 : Nat := 4983230072969 + 3 ^ 40 * 3490315 * 2
def baseEnd_3490315 : Nat := 1194806153731744573473893

theorem tailTrace_3490315 : CollatzResearch.WordTrace tailWord_3490315 prefixEnd_3490315 1194806153731744573473893 := by
  unfold tailWord_3490315
  simp only [CollatzResearch.WordTrace]
  refine ⟨127302246350192328189296399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84868164233461552126197599 127302246350192328189296399)
  ·
    refine ⟨190953369525288492283944599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127302246350192328189296399 190953369525288492283944599)
    ·
      refine ⟨286430054287932738425916899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190953369525288492283944599 286430054287932738425916899)
      ·
        refine ⟨429645081431899107638875349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286430054287932738425916899 429645081431899107638875349)
        ·
          refine ⟨10069806596060135335286141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 429645081431899107638875349 10069806596060135335286141)
          ·
            refine ⟨3776177473522550750732303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10069806596060135335286141 3776177473522550750732303)
            ·
              refine ⟨5664266210283826126098455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776177473522550750732303 5664266210283826126098455)
              ·
                refine ⟨8496399315425739189147683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5664266210283826126098455 8496399315425739189147683)
                ·
                  refine ⟨12744598973138608783721525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8496399315425739189147683 12744598973138608783721525)
                  ·
                    refine ⟨1194806153731744573473893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12744598973138608783721525 1194806153731744573473893)
                    ·
                      rfl

theorem cell22_3490315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 5].length) (baseStart_3490315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490315 prefixEnd_3490315 := by exact prefixLift 3490315
  have htrace : WordTrace (prefixWord ++ tailWord_3490315) baseStart_3490315 baseEnd_3490315 := by
    simpa [prefixWord, tailWord_3490315, baseEnd_3490315] using wordTrace_append hprefix tailTrace_3490315
  have hstable : (prefixWord ++ tailWord_3490315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490315).length < 2 ^ (prefixWord ++ tailWord_3490315).sum := by decide
  have hdescent : baseEnd_3490315 < baseStart_3490315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490317 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3490317 : Nat := 118140960795 + 3490317 * 2 ^ 59
def prefixEnd_3490317 : Nat := 4983230072969 + 3 ^ 40 * 3490317 * 2
def baseEnd_3490317 : Nat := 398268946124205744974629

theorem tailTrace_3490317 : CollatzResearch.WordTrace tailWord_3490317 prefixEnd_3490317 398268946124205744974629 := by
  unfold tailWord_3490317
  simp only [CollatzResearch.WordTrace]
  refine ⟨127302319296185082530869205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84868212864123388353912803 127302319296185082530869205)
  ·
    refine ⟨2983648108504337871817247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 127302319296185082530869205 2983648108504337871817247)
    ·
      refine ⟨4475472162756506807725871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2983648108504337871817247 4475472162756506807725871)
      ·
        refine ⟨6713208244134760211588807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4475472162756506807725871 6713208244134760211588807)
        ·
          refine ⟨10069812366202140317383211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6713208244134760211588807 10069812366202140317383211)
          ·
            refine ⟨15104718549303210476074817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10069812366202140317383211 15104718549303210476074817)
            ·
              refine ⟨11328538911977407857056113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15104718549303210476074817 11328538911977407857056113)
              ·
                refine ⟨8496404183983055892792085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11328538911977407857056113 8496404183983055892792085)
                ·
                  refine ⟨398268946124205744974629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8496404183983055892792085 398268946124205744974629)
                  ·
                    rfl

theorem cell22_3490317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3490317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490317 prefixEnd_3490317 := by exact prefixLift 3490317
  have htrace : WordTrace (prefixWord ++ tailWord_3490317) baseStart_3490317 baseEnd_3490317 := by
    simpa [prefixWord, tailWord_3490317, baseEnd_3490317] using wordTrace_append hprefix tailTrace_3490317
  have hstable : (prefixWord ++ tailWord_3490317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490317).length < 2 ^ (prefixWord ++ tailWord_3490317).sum := by decide
  have hdescent : baseEnd_3490317 < baseStart_3490317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490328 : List Nat := [2, 1, 2, 3, 3, 2, 1, 8]
def baseStart_3490328 : Nat := 118140960795 + 3490328 * 2 ^ 59
def prefixEnd_3490328 : Nat := 4983230072969 + 3 ^ 40 * 3490328 * 2
def baseEnd_3490328 : Nat := 132756733766379652544317

theorem tailTrace_3490328 : CollatzResearch.WordTrace tailWord_3490328 prefixEnd_3490328 132756733766379652544317 := by
  unfold tailWord_3490328
  simp only [CollatzResearch.WordTrace]
  refine ⟨63651360249572615704759819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84868480332763487606346425 63651360249572615704759819)
  ·
    refine ⟨95477040374358923557139729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63651360249572615704759819 95477040374358923557139729)
    ·
      refine ⟨71607780280769192667854797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95477040374358923557139729 71607780280769192667854797)
      ·
        refine ⟨26852917605288447250445549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71607780280769192667854797 26852917605288447250445549)
        ·
          refine ⟨10069844101983167718917081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26852917605288447250445549 10069844101983167718917081)
          ·
            refine ⟨7552383076487375789187811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10069844101983167718917081 7552383076487375789187811)
            ·
              refine ⟨11328574614731063683781717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7552383076487375789187811 11328574614731063683781717)
              ·
                refine ⟨132756733766379652544317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11328574614731063683781717 132756733766379652544317)
                ·
                  rfl

theorem cell22_3490328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 8].length) (baseStart_3490328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490328 prefixEnd_3490328 := by exact prefixLift 3490328
  have htrace : WordTrace (prefixWord ++ tailWord_3490328) baseStart_3490328 baseEnd_3490328 := by
    simpa [prefixWord, tailWord_3490328, baseEnd_3490328] using wordTrace_append hprefix tailTrace_3490328
  have hstable : (prefixWord ++ tailWord_3490328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490328).length < 2 ^ (prefixWord ++ tailWord_3490328).sum := by decide
  have hdescent : baseEnd_3490328 < baseStart_3490328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490422 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_3490422 : Nat := 118140960795 + 3490422 * 2 ^ 59
def prefixEnd_3490422 : Nat := 4983230072969 + 3 ^ 40 * 3490422 * 2
def baseEnd_3490422 : Nat := 1194842782018431961048565

theorem tailTrace_3490422 : CollatzResearch.WordTrace tailWord_3490422 prefixEnd_3490422 1194842782018431961048565 := by
  unfold tailWord_3490422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7956634310050292841465095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84870765973869790308961013 7956634310050292841465095)
  ·
    refine ⟨11934951465075439262197643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7956634310050292841465095 11934951465075439262197643)
    ·
      refine ⟨17902427197613158893296465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11934951465075439262197643 17902427197613158893296465)
      ·
        refine ⟨13426820398209869169972349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17902427197613158893296465 13426820398209869169972349)
        ·
          refine ⟨5035057649328700938739631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13426820398209869169972349 5035057649328700938739631)
          ·
            refine ⟨7552586473993051408109447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5035057649328700938739631 7552586473993051408109447)
            ·
              refine ⟨11328879710989577112164171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7552586473993051408109447 11328879710989577112164171)
              ·
                refine ⟨16993319566484365668246257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11328879710989577112164171 16993319566484365668246257)
                ·
                  refine ⟨12744989674863274251184693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16993319566484365668246257 12744989674863274251184693)
                  ·
                    refine ⟨1194842782018431961048565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12744989674863274251184693 1194842782018431961048565)
                    ·
                      rfl

theorem cell22_3490422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_3490422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490422 prefixEnd_3490422 := by exact prefixLift 3490422
  have htrace : WordTrace (prefixWord ++ tailWord_3490422) baseStart_3490422 baseEnd_3490422 := by
    simpa [prefixWord, tailWord_3490422, baseEnd_3490422] using wordTrace_append hprefix tailTrace_3490422
  have hstable : (prefixWord ++ tailWord_3490422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490422).length < 2 ^ (prefixWord ++ tailWord_3490422).sum := by decide
  have hdescent : baseEnd_3490422 < baseStart_3490422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490523 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 5, 7]
def baseStart_3490523 : Nat := 118140960795 + 3490523 * 2 ^ 59
def prefixEnd_3490523 : Nat := 4983230072969 + 3 ^ 40 * 3490523 * 2
def baseEnd_3490523 : Nat := 1194877356382501364273255

theorem tailTrace_3490523 : CollatzResearch.WordTrace tailWord_3490523 prefixEnd_3490523 1194877356382501364273255 := by
  unfold tailWord_3490523
  simp only [CollatzResearch.WordTrace]
  refine ⟨127309832733438779712868223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84873221822292519808578815 127309832733438779712868223)
  ·
    refine ⟨190964749100158169569302335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127309832733438779712868223 190964749100158169569302335)
    ·
      refine ⟨286447123650237254353953503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190964749100158169569302335 286447123650237254353953503)
      ·
        refine ⟨429670685475355881530930255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286447123650237254353953503 429670685475355881530930255)
        ·
          refine ⟨644506028213033822296395383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429670685475355881530930255 644506028213033822296395383)
          ·
            refine ⟨966759042319550733444593075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644506028213033822296395383 966759042319550733444593075)
            ·
              refine ⟨1450138563479326100166889613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966759042319550733444593075 1450138563479326100166889613)
              ·
                refine ⟨543801961304747287562583605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1450138563479326100166889613 543801961304747287562583605)
                ·
                  refine ⟨50981433872320058208992213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 543801961304747287562583605 50981433872320058208992213)
                  ·
                    refine ⟨1194877356382501364273255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50981433872320058208992213 1194877356382501364273255)
                    ·
                      rfl

theorem cell22_3490523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_3490523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490523 prefixEnd_3490523 := by exact prefixLift 3490523
  have htrace : WordTrace (prefixWord ++ tailWord_3490523) baseStart_3490523 baseEnd_3490523 := by
    simpa [prefixWord, tailWord_3490523, baseEnd_3490523] using wordTrace_append hprefix tailTrace_3490523
  have hstable : (prefixWord ++ tailWord_3490523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490523).length < 2 ^ (prefixWord ++ tailWord_3490523).sum := by decide
  have hdescent : baseEnd_3490523 < baseStart_3490523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490529 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 3, 3]
def baseStart_3490529 : Nat := 118140960795 + 3490529 * 2 ^ 59
def prefixEnd_3490529 : Nat := 4983230072969 + 3 ^ 40 * 3490529 * 2
def baseEnd_3490529 : Nat := 1194879410305119348623237

theorem tailTrace_3490529 : CollatzResearch.WordTrace tailWord_3490529 prefixEnd_3490529 1194879410305119348623237 := by
  unfold tailWord_3490529
  simp only [CollatzResearch.WordTrace]
  refine ⟨127310051571417042737586641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84873367714278028491724427 127310051571417042737586641)
  ·
    refine ⟨95482538678562782053189981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127310051571417042737586641 95482538678562782053189981)
    ·
      refine ⟨35805952004461043269946243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95482538678562782053189981 35805952004461043269946243)
      ·
        refine ⟨53708928006691564904919365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35805952004461043269946243 53708928006691564904919365)
        ·
          refine ⟨10070424001254668419672381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53708928006691564904919365 10070424001254668419672381)
          ·
            refine ⟨3776409000470500657377143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10070424001254668419672381 3776409000470500657377143)
            ·
              refine ⟨5664613500705750986065715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776409000470500657377143 5664613500705750986065715)
              ·
                refine ⟨8496920251058626479098573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5664613500705750986065715 8496920251058626479098573)
                ·
                  refine ⟨3186345094146984929661965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8496920251058626479098573 3186345094146984929661965)
                  ·
                    refine ⟨1194879410305119348623237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3186345094146984929661965 1194879410305119348623237)
                    ·
                      rfl

theorem cell22_3490529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_3490529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490529 prefixEnd_3490529 := by exact prefixLift 3490529
  have htrace : WordTrace (prefixWord ++ tailWord_3490529) baseStart_3490529 baseEnd_3490529 := by
    simpa [prefixWord, tailWord_3490529, baseEnd_3490529] using wordTrace_append hprefix tailTrace_3490529
  have hstable : (prefixWord ++ tailWord_3490529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490529).length < 2 ^ (prefixWord ++ tailWord_3490529).sum := by decide
  have hdescent : baseEnd_3490529 < baseStart_3490529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490542 : List Nat := [4, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_3490542 : Nat := 118140960795 + 3490542 * 2 ^ 59
def prefixEnd_3490542 : Nat := 4983230072969 + 3 ^ 40 * 3490542 * 2
def baseEnd_3490542 : Nat := 398294620156930549349399

theorem tailTrace_3490542 : CollatzResearch.WordTrace tailWord_3490542 prefixEnd_3490542 398294620156930549349399 := by
  unfold tailWord_3490542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15913815715046243244726235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84873683813579963971873253 15913815715046243244726235)
  ·
    refine ⟨23870723572569364867089353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15913815715046243244726235 23870723572569364867089353)
    ·
      refine ⟨17903042679427023650317015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23870723572569364867089353 17903042679427023650317015)
      ·
        refine ⟨26854564019140535475475523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17903042679427023650317015 26854564019140535475475523)
        ·
          refine ⟨40281846028710803213213285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26854564019140535475475523 40281846028710803213213285)
          ·
            refine ⟨7552846130383275602477491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40281846028710803213213285 7552846130383275602477491)
            ·
              refine ⟨11329269195574913403716237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7552846130383275602477491 11329269195574913403716237)
              ·
                refine ⟨4248475948340592526393589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11329269195574913403716237 4248475948340592526393589)
                ·
                  refine ⟨398294620156930549349399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4248475948340592526393589 398294620156930549349399)
                  ·
                    rfl

theorem cell22_3490542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_3490542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490542 prefixEnd_3490542 := by exact prefixLift 3490542
  have htrace : WordTrace (prefixWord ++ tailWord_3490542) baseStart_3490542 baseEnd_3490542 := by
    simpa [prefixWord, tailWord_3490542, baseEnd_3490542] using wordTrace_append hprefix tailTrace_3490542
  have hstable : (prefixWord ++ tailWord_3490542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490542).length < 2 ^ (prefixWord ++ tailWord_3490542).sum := by decide
  have hdescent : baseEnd_3490542 < baseStart_3490542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490621 : List Nat := [1, 4, 1, 4, 2, 1, 2, 3, 4]
def baseStart_3490621 : Nat := 118140960795 + 3490621 * 2 ^ 59
def prefixEnd_3490621 : Nat := 4983230072969 + 3 ^ 40 * 3490621 * 2
def baseEnd_3490621 : Nat := 398303634595087258440985

theorem tailTrace_3490621 : CollatzResearch.WordTrace tailWord_3490621 prefixEnd_3490621 398303634595087258440985 := by
  unfold tailWord_3490621
  simp only [CollatzResearch.WordTrace]
  refine ⟨127313407087083742449935717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84875604724722494966623811 127313407087083742449935717)
  ·
    refine ⟨23871263828828201709362947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127313407087083742449935717 23871263828828201709362947)
    ·
      refine ⟨35806895743242302564044421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23871263828828201709362947 35806895743242302564044421)
      ·
        refine ⟨6713792951857931730758329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35806895743242302564044421 6713792951857931730758329)
        ·
          refine ⟨5035344713893448798068747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6713792951857931730758329 5035344713893448798068747)
          ·
            refine ⟨7553017070840173197103121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5035344713893448798068747 7553017070840173197103121)
            ·
              refine ⟨5664762803130129897827341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7553017070840173197103121 5664762803130129897827341)
              ·
                refine ⟨2124286051173798711685253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5664762803130129897827341 2124286051173798711685253)
                ·
                  refine ⟨398303634595087258440985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2124286051173798711685253 398303634595087258440985)
                  ·
                    rfl

theorem cell22_3490621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_3490621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490621 prefixEnd_3490621 := by exact prefixLift 3490621
  have htrace : WordTrace (prefixWord ++ tailWord_3490621) baseStart_3490621 baseEnd_3490621 := by
    simpa [prefixWord, tailWord_3490621, baseEnd_3490621] using wordTrace_append hprefix tailTrace_3490621
  have hstable : (prefixWord ++ tailWord_3490621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490621).length < 2 ^ (prefixWord ++ tailWord_3490621).sum := by decide
  have hdescent : baseEnd_3490621 < baseStart_3490621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490636 : List Nat := [2, 2, 1, 3, 3, 3, 1, 2, 2, 3]
def baseStart_3490636 : Nat := 118140960795 + 3490636 * 2 ^ 59
def prefixEnd_3490636 : Nat := 4983230072969 + 3 ^ 40 * 3490636 * 2
def baseEnd_3490636 : Nat := 1194916038591806736197909

theorem tailTrace_3490636 : CollatzResearch.WordTrace tailWord_3490636 prefixEnd_3490636 1194916038591806736197909 := by
  unfold tailWord_3490636
  simp only [CollatzResearch.WordTrace]
  refine ⟨63656977091014700005865881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84875969454686266674487841 63656977091014700005865881)
  ·
    refine ⟨47742732818261025004399411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63656977091014700005865881 47742732818261025004399411)
    ·
      refine ⟨71614099227391537506599117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47742732818261025004399411 71614099227391537506599117)
      ·
        refine ⟨26855287210271826564974669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71614099227391537506599117 26855287210271826564974669)
        ·
          refine ⟨10070732703851934961865501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26855287210271826564974669 10070732703851934961865501)
          ·
            refine ⟨3776524763944475610699563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10070732703851934961865501 3776524763944475610699563)
            ·
              refine ⟨5664787145916713416049345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776524763944475610699563 5664787145916713416049345)
              ·
                refine ⟨4248590359437535062037009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5664787145916713416049345 4248590359437535062037009)
                ·
                  refine ⟨3186442769578151296527757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4248590359437535062037009 3186442769578151296527757)
                  ·
                    refine ⟨1194916038591806736197909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3186442769578151296527757 1194916038591806736197909)
                    ·
                      rfl

theorem cell22_3490636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_3490636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490636 prefixEnd_3490636 := by exact prefixLift 3490636
  have htrace : WordTrace (prefixWord ++ tailWord_3490636) baseStart_3490636 baseEnd_3490636 := by
    simpa [prefixWord, tailWord_3490636, baseEnd_3490636] using wordTrace_append hprefix tailTrace_3490636
  have hstable : (prefixWord ++ tailWord_3490636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490636).length < 2 ^ (prefixWord ++ tailWord_3490636).sum := by decide
  have hdescent : baseEnd_3490636 < baseStart_3490636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490664 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 3, 3]
def baseStart_3490664 : Nat := 118140960795 + 3490664 * 2 ^ 59
def prefixEnd_3490664 : Nat := 4983230072969 + 3 ^ 40 * 3490664 * 2
def baseEnd_3490664 : Nat := 1194925623564023996497823

theorem tailTrace_3490664 : CollatzResearch.WordTrace tailWord_3490664 prefixEnd_3490664 1194925623564023996497823 := by
  unfold tailWord_3490664
  simp only [CollatzResearch.WordTrace]
  refine ⟨63657487712963980396875523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84876650283951973862500697 63657487712963980396875523)
  ·
    refine ⟨95486231569445970595313285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63657487712963980396875523 95486231569445970595313285)
    ·
      refine ⟨17903668419271119486621241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95486231569445970595313285 17903668419271119486621241)
      ·
        refine ⟨13427751314453339614965931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17903668419271119486621241 13427751314453339614965931)
        ·
          refine ⟨20141626971680009422448897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13427751314453339614965931 20141626971680009422448897)
          ·
            refine ⟨15106220228760007066836673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20141626971680009422448897 15106220228760007066836673)
            ·
              refine ⟨11329665171570005300127505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15106220228760007066836673 11329665171570005300127505)
              ·
                refine ⟨8497248878677503975095629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11329665171570005300127505 8497248878677503975095629)
                ·
                  refine ⟨3186468329504063990660861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8497248878677503975095629 3186468329504063990660861)
                  ·
                    refine ⟨1194925623564023996497823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3186468329504063990660861 1194925623564023996497823)
                    ·
                      rfl

theorem cell22_3490664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_3490664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490664 prefixEnd_3490664 := by exact prefixLift 3490664
  have htrace : WordTrace (prefixWord ++ tailWord_3490664) baseStart_3490664 baseEnd_3490664 := by
    simpa [prefixWord, tailWord_3490664, baseEnd_3490664] using wordTrace_append hprefix tailTrace_3490664
  have hstable : (prefixWord ++ tailWord_3490664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490664).length < 2 ^ (prefixWord ++ tailWord_3490664).sum := by decide
  have hdescent : baseEnd_3490664 < baseStart_3490664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490675 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 1, 7]
def baseStart_3490675 : Nat := 118140960795 + 3490675 * 2 ^ 59
def prefixEnd_3490675 : Nat := 4983230072969 + 3 ^ 40 * 3490675 * 2
def baseEnd_3490675 : Nat := 1194929389088823634472789

theorem tailTrace_3490675 : CollatzResearch.WordTrace tailWord_3490675 prefixEnd_3490675 1194929389088823634472789 := by
  unfold tailWord_3490675
  simp only [CollatzResearch.WordTrace]
  refine ⟨127315376628888109672401479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84876917752592073114934319 127315376628888109672401479)
  ·
    refine ⟨190973064943332164508602219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127315376628888109672401479 190973064943332164508602219)
    ·
      refine ⟨286459597414998246762903329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190973064943332164508602219 286459597414998246762903329)
      ·
        refine ⟨214844698061248685072177497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286459597414998246762903329 214844698061248685072177497)
        ·
          refine ⟨161133523545936513804133123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214844698061248685072177497 161133523545936513804133123)
          ·
            refine ⟨241700285318904770706199685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161133523545936513804133123 241700285318904770706199685)
            ·
              refine ⟨45318803497294644507412441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241700285318904770706199685 45318803497294644507412441)
              ·
                refine ⟨33989102622970983380559331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45318803497294644507412441 33989102622970983380559331)
                ·
                  refine ⟨50983653934456475070838997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33989102622970983380559331 50983653934456475070838997)
                  ·
                    refine ⟨1194929389088823634472789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50983653934456475070838997 1194929389088823634472789)
                    ·
                      rfl

theorem cell22_3490675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_3490675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490675 prefixEnd_3490675 := by exact prefixLift 3490675
  have htrace : WordTrace (prefixWord ++ tailWord_3490675) baseStart_3490675 baseEnd_3490675 := by
    simpa [prefixWord, tailWord_3490675, baseEnd_3490675] using wordTrace_append hprefix tailTrace_3490675
  have hstable : (prefixWord ++ tailWord_3490675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490675).length < 2 ^ (prefixWord ++ tailWord_3490675).sum := by decide
  have hdescent : baseEnd_3490675 < baseStart_3490675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490677 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 7]
def baseStart_3490677 : Nat := 118140960795 + 3490677 * 2 ^ 59
def prefixEnd_3490677 : Nat := 4983230072969 + 3 ^ 40 * 3490677 * 2
def baseEnd_3490677 : Nat := 398310024576565431974261

theorem tailTrace_3490677 : CollatzResearch.WordTrace tailWord_3490677 prefixEnd_3490677 398310024576565431974261 := by
  unfold tailWord_3490677
  simp only [CollatzResearch.WordTrace]
  refine ⟨127315449574880864013974285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84876966383253909342649523 127315449574880864013974285)
  ·
    refine ⟨47743293590580324005240357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127315449574880864013974285 47743293590580324005240357)
    ·
      refine ⟨8951867548233810750982567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47743293590580324005240357 8951867548233810750982567)
      ·
        refine ⟨13427801322350716126473851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8951867548233810750982567 13427801322350716126473851)
        ·
          refine ⟨20141701983526074189710777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13427801322350716126473851 20141701983526074189710777)
          ·
            refine ⟨15106276487644555642283083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20141701983526074189710777 15106276487644555642283083)
            ·
              refine ⟨22659414731466833463424625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15106276487644555642283083 22659414731466833463424625)
              ·
                refine ⟨16994561048600125097568469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22659414731466833463424625 16994561048600125097568469)
                ·
                  refine ⟨398310024576565431974261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16994561048600125097568469 398310024576565431974261)
                  ·
                    rfl

theorem cell22_3490677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_3490677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490677 prefixEnd_3490677 := by exact prefixLift 3490677
  have htrace : WordTrace (prefixWord ++ tailWord_3490677) baseStart_3490677 baseEnd_3490677 := by
    simpa [prefixWord, tailWord_3490677, baseEnd_3490677] using wordTrace_append hprefix tailTrace_3490677
  have hstable : (prefixWord ++ tailWord_3490677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490677).length < 2 ^ (prefixWord ++ tailWord_3490677).sum := by decide
  have hdescent : baseEnd_3490677 < baseStart_3490677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490681 : List Nat := [1, 2, 1, 3, 2, 3, 3, 3, 1, 3]
def baseStart_3490681 : Nat := 118140960795 + 3490681 * 2 ^ 59
def prefixEnd_3490681 : Nat := 4983230072969 + 3 ^ 40 * 3490681 * 2
def baseEnd_3490681 : Nat := 1194931443011441618822771

theorem tailTrace_3490681 : CollatzResearch.WordTrace tailWord_3490681 prefixEnd_3490681 1194931443011441618822771 := by
  unfold tailWord_3490681
  simp only [CollatzResearch.WordTrace]
  refine ⟨127315595466866372697119897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84877063644577581798079931 127315595466866372697119897)
  ·
    refine ⟨95486696600149779522839923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127315595466866372697119897 95486696600149779522839923)
    ·
      refine ⟨143230044900224669284259885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95486696600149779522839923 143230044900224669284259885)
      ·
        refine ⟨53711266837584250981597457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143230044900224669284259885 53711266837584250981597457)
        ·
          refine ⟨40283450128188188236198093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53711266837584250981597457 40283450128188188236198093)
          ·
            refine ⟨15106293798070570588574285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40283450128188188236198093 15106293798070570588574285)
            ·
              refine ⟨5664860174276463970715357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15106293798070570588574285 5664860174276463970715357)
              ·
                refine ⟨2124322565353673989018259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5664860174276463970715357 2124322565353673989018259)
                ·
                  refine ⟨3186483848030510983527389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124322565353673989018259 3186483848030510983527389)
                  ·
                    refine ⟨1194931443011441618822771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3186483848030510983527389 1194931443011441618822771)
                    ·
                      rfl

theorem cell22_3490681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 1, 3].length) (baseStart_3490681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490681 prefixEnd_3490681 := by exact prefixLift 3490681
  have htrace : WordTrace (prefixWord ++ tailWord_3490681) baseStart_3490681 baseEnd_3490681 := by
    simpa [prefixWord, tailWord_3490681, baseEnd_3490681] using wordTrace_append hprefix tailTrace_3490681
  have hstable : (prefixWord ++ tailWord_3490681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490681).length < 2 ^ (prefixWord ++ tailWord_3490681).sum := by decide
  have hdescent : baseEnd_3490681 < baseStart_3490681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490741 : List Nat := [1, 3, 3, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3490741 : Nat := 118140960795 + 3490741 * 2 ^ 59
def prefixEnd_3490741 : Nat := 4983230072969 + 3 ^ 40 * 3490741 * 2
def baseEnd_3490741 : Nat := 1194951982237621462322587

theorem tailTrace_3490741 : CollatzResearch.WordTrace tailWord_3490741 prefixEnd_3490741 1194951982237621462322587 := by
  unfold tailWord_3490741
  simp only [CollatzResearch.WordTrace]
  refine ⟨127317783846649002944304077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84878522564432668629536051 127317783846649002944304077)
  ·
    refine ⟨47744168942493376104114029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127317783846649002944304077 47744168942493376104114029)
    ·
      refine ⟨17904063353435016039042761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47744168942493376104114029 17904063353435016039042761)
      ·
        refine ⟨13428047515076262029282071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17904063353435016039042761 13428047515076262029282071)
        ·
          refine ⟨20142071272614393043923107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13428047515076262029282071 20142071272614393043923107)
          ·
            refine ⟨30213106908921589565884661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20142071272614393043923107 30213106908921589565884661)
            ·
              refine ⟨2832478772711399021801687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30213106908921589565884661 2832478772711399021801687)
              ·
                refine ⟨4248718159067098532702531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2832478772711399021801687 4248718159067098532702531)
                ·
                  refine ⟨6373077238600647799053797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248718159067098532702531 6373077238600647799053797)
                  ·
                    refine ⟨1194951982237621462322587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6373077238600647799053797 1194951982237621462322587)
                    ·
                      rfl

theorem cell22_3490741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3490741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490741 prefixEnd_3490741 := by exact prefixLift 3490741
  have htrace : WordTrace (prefixWord ++ tailWord_3490741) baseStart_3490741 baseEnd_3490741 := by
    simpa [prefixWord, tailWord_3490741, baseEnd_3490741] using wordTrace_append hprefix tailTrace_3490741
  have hstable : (prefixWord ++ tailWord_3490741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490741).length < 2 ^ (prefixWord ++ tailWord_3490741).sum := by decide
  have hdescent : baseEnd_3490741 < baseStart_3490741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490767 : List Nat := [1, 1, 2, 1, 1, 6, 3, 7]
def baseStart_3490767 : Nat := 118140960795 + 3490767 * 2 ^ 59
def prefixEnd_3490767 : Nat := 4983230072969 + 3 ^ 40 * 3490767 * 2
def baseEnd_3490767 : Nat := 132773431396551784574723

theorem tailTrace_3490767 : CollatzResearch.WordTrace tailWord_3490767 prefixEnd_3490767 132773431396551784574723 := by
  unfold tailWord_3490767
  simp only [CollatzResearch.WordTrace]
  refine ⟨127318732144554809384750555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84879154763036539589833703 127318732144554809384750555)
  ·
    refine ⟨190978098216832214077125833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127318732144554809384750555 190978098216832214077125833)
    ·
      refine ⟨143233573662624160557844375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190978098216832214077125833 143233573662624160557844375)
      ·
        refine ⟨214850360493936240836766563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143233573662624160557844375 214850360493936240836766563)
        ·
          refine ⟨322275540740904361255149845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214850360493936240836766563 322275540740904361255149845)
          ·
            refine ⟨15106665972229891933835149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 322275540740904361255149845 15106665972229891933835149)
            ·
              refine ⟨5664999739586209475188181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15106665972229891933835149 5664999739586209475188181)
              ·
                refine ⟨132773431396551784574723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5664999739586209475188181 132773431396551784574723)
                ·
                  rfl

theorem cell22_3490767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 7].length) (baseStart_3490767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490767 prefixEnd_3490767 := by exact prefixLift 3490767
  have htrace : WordTrace (prefixWord ++ tailWord_3490767) baseStart_3490767 baseEnd_3490767 := by
    simpa [prefixWord, tailWord_3490767, baseEnd_3490767] using wordTrace_append hprefix tailTrace_3490767
  have hstable : (prefixWord ++ tailWord_3490767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490767).length < 2 ^ (prefixWord ++ tailWord_3490767).sum := by decide
  have hdescent : baseEnd_3490767 < baseStart_3490767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490786 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3490786 : Nat := 118140960795 + 3490786 * 2 ^ 59
def prefixEnd_3490786 : Nat := 4983230072969 + 3 ^ 40 * 3490786 * 2
def baseEnd_3490786 : Nat := 1194967386657256344947449

theorem tailTrace_3490786 : CollatzResearch.WordTrace tailWord_3490786 prefixEnd_3490786 1194967386657256344947449 := by
  unfold tailWord_3490786
  simp only [CollatzResearch.WordTrace]
  refine ⟨31829856282871493907423053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84879616754323983753128141 31829856282871493907423053)
  ·
    refine ⟨11936196106076810215283645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31829856282871493907423053 11936196106076810215283645)
    ·
      refine ⟨4476073539778803830731367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11936196106076810215283645 4476073539778803830731367)
      ·
        refine ⟨6714110309668205746097051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4476073539778803830731367 6714110309668205746097051)
        ·
          refine ⟨10071165464502308619145577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6714110309668205746097051 10071165464502308619145577)
          ·
            refine ⟨7553374098376731464359183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10071165464502308619145577 7553374098376731464359183)
            ·
              refine ⟨11330061147565097196538775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7553374098376731464359183 11330061147565097196538775)
              ·
                refine ⟨16995091721347645794808163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11330061147565097196538775 16995091721347645794808163)
                ·
                  refine ⟨25492637582021468692212245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16995091721347645794808163 25492637582021468692212245)
                  ·
                    refine ⟨1194967386657256344947449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25492637582021468692212245 1194967386657256344947449)
                    ·
                      rfl

theorem cell22_3490786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3490786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490786 prefixEnd_3490786 := by exact prefixLift 3490786
  have htrace : WordTrace (prefixWord ++ tailWord_3490786) baseStart_3490786 baseEnd_3490786 := by
    simpa [prefixWord, tailWord_3490786, baseEnd_3490786] using wordTrace_append hprefix tailTrace_3490786
  have hstable : (prefixWord ++ tailWord_3490786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490786).length < 2 ^ (prefixWord ++ tailWord_3490786).sum := by decide
  have hdescent : baseEnd_3490786 < baseStart_3490786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490850 : List Nat := [3, 3, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3490850 : Nat := 118140960795 + 3490850 * 2 ^ 59
def prefixEnd_3490850 : Nat := 4983230072969 + 3 ^ 40 * 3490850 * 2
def baseEnd_3490850 : Nat := 1194989295165181511347253

theorem tailTrace_3490850 : CollatzResearch.WordTrace tailWord_3490850 prefixEnd_3490850 1194989295165181511347253 := by
  unfold tailWord_3490850
  simp only [CollatzResearch.WordTrace]
  refine ⟨31830439850813528640005501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84881172935502743040014669 31830439850813528640005501)
  ·
    refine ⟨11936414944055073240002063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31830439850813528640005501 11936414944055073240002063)
    ·
      refine ⟨17904622416082609860003095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11936414944055073240002063 17904622416082609860003095)
      ·
        refine ⟨26856933624123914790004643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17904622416082609860003095 26856933624123914790004643)
        ·
          refine ⟨40285400436185872185006965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26856933624123914790004643 40285400436185872185006965)
          ·
            refine ⟨3776756290892425517344403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40285400436185872185006965 3776756290892425517344403)
            ·
              refine ⟨5665134436338638276016605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776756290892425517344403 5665134436338638276016605)
              ·
                refine ⟨2124425413626989353506227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5665134436338638276016605 2124425413626989353506227)
                ·
                  refine ⟨3186638120440484030259341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124425413626989353506227 3186638120440484030259341)
                  ·
                    refine ⟨1194989295165181511347253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3186638120440484030259341 1194989295165181511347253)
                    ·
                      rfl

theorem cell22_3490850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3490850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490850 prefixEnd_3490850 := by exact prefixLift 3490850
  have htrace : WordTrace (prefixWord ++ tailWord_3490850) baseStart_3490850 baseEnd_3490850 := by
    simpa [prefixWord, tailWord_3490850, baseEnd_3490850] using wordTrace_append hprefix tailTrace_3490850
  have hstable : (prefixWord ++ tailWord_3490850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490850).length < 2 ^ (prefixWord ++ tailWord_3490850).sum := by decide
  have hdescent : baseEnd_3490850 < baseStart_3490850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490859 : List Nat := [1, 1, 1, 1, 2, 1, 5, 5, 1, 4]
def baseStart_3490859 : Nat := 118140960795 + 3490859 * 2 ^ 59
def prefixEnd_3490859 : Nat := 4983230072969 + 3 ^ 40 * 3490859 * 2
def baseEnd_3490859 : Nat := 1194992376049108487872225

theorem tailTrace_3490859 : CollatzResearch.WordTrace tailWord_3490859 prefixEnd_3490859 1194992376049108487872225 := by
  unfold tailWord_3490859
  simp only [CollatzResearch.WordTrace]
  refine ⟨127322087660221509097099631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84881391773481006064733087 127322087660221509097099631)
  ·
    refine ⟨190983131490332263645649447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127322087660221509097099631 190983131490332263645649447)
    ·
      refine ⟨286474697235498395468474171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190983131490332263645649447 286474697235498395468474171)
      ·
        refine ⟨429712045853247593202711257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286474697235498395468474171 429712045853247593202711257)
        ·
          refine ⟨322284034389935694902033443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429712045853247593202711257 322284034389935694902033443)
          ·
            refine ⟨483426051584903542353050165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322284034389935694902033443 483426051584903542353050165)
            ·
              refine ⟨45321192336084707095598453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 483426051584903542353050165 45321192336084707095598453)
              ·
                refine ⟨4248861781507941290212355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45321192336084707095598453 4248861781507941290212355)
                ·
                  refine ⟨6373292672261911935318533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248861781507941290212355 6373292672261911935318533)
                  ·
                    refine ⟨1194992376049108487872225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6373292672261911935318533 1194992376049108487872225)
                    ·
                      rfl

theorem cell22_3490859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 4].length) (baseStart_3490859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490859 prefixEnd_3490859 := by exact prefixLift 3490859
  have htrace : WordTrace (prefixWord ++ tailWord_3490859) baseStart_3490859 baseEnd_3490859 := by
    simpa [prefixWord, tailWord_3490859, baseEnd_3490859] using wordTrace_append hprefix tailTrace_3490859
  have hstable : (prefixWord ++ tailWord_3490859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490859).length < 2 ^ (prefixWord ++ tailWord_3490859).sum := by decide
  have hdescent : baseEnd_3490859 < baseStart_3490859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490874 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 6]
def baseStart_3490874 : Nat := 118140960795 + 3490874 * 2 ^ 59
def prefixEnd_3490874 : Nat := 4983230072969 + 3 ^ 40 * 3490874 * 2
def baseEnd_3490874 : Nat := 398332503618551149582393

theorem tailTrace_3490874 : CollatzResearch.WordTrace tailWord_3490874 prefixEnd_3490874 398332503618551149582393 := by
  unfold tailWord_3490874
  simp only [CollatzResearch.WordTrace]
  refine ⟨31830658688791791664723919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84881756503444777772597117 31830658688791791664723919)
  ·
    refine ⟨47745988033187687497085879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31830658688791791664723919 47745988033187687497085879)
    ·
      refine ⟨71618982049781531245628819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47745988033187687497085879 71618982049781531245628819)
      ·
        refine ⟨107428473074672296868443229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71618982049781531245628819 107428473074672296868443229)
        ·
          refine ⟨40285677403002111325666211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107428473074672296868443229 40285677403002111325666211)
          ·
            refine ⟨60428516104503166988499317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40285677403002111325666211 60428516104503166988499317)
            ·
              refine ⟨5665173384797171905171811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60428516104503166988499317 5665173384797171905171811)
              ·
                refine ⟨8497760077195757857757717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5665173384797171905171811 8497760077195757857757717)
                ·
                  refine ⟨398332503618551149582393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8497760077195757857757717 398332503618551149582393)
                  ·
                    rfl

theorem cell22_3490874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_3490874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490874 prefixEnd_3490874 := by exact prefixLift 3490874
  have htrace : WordTrace (prefixWord ++ tailWord_3490874) baseStart_3490874 baseEnd_3490874 := by
    simpa [prefixWord, tailWord_3490874, baseEnd_3490874] using wordTrace_append hprefix tailTrace_3490874
  have hstable : (prefixWord ++ tailWord_3490874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490874).length < 2 ^ (prefixWord ++ tailWord_3490874).sum := by decide
  have hdescent : baseEnd_3490874 < baseStart_3490874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490889 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 6, 3]
def baseStart_3490889 : Nat := 118140960795 + 3490889 * 2 ^ 59
def prefixEnd_3490889 : Nat := 4983230072969 + 3 ^ 40 * 3490889 * 2
def baseEnd_3490889 : Nat := 1195002645662198409622133

theorem tailTrace_3490889 : CollatzResearch.WordTrace tailWord_3490889 prefixEnd_3490889 1195002645662198409622133 := by
  unfold tailWord_3490889
  simp only [CollatzResearch.WordTrace]
  refine ⟨127323181850112824220691721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84882121233408549480461147 127323181850112824220691721)
  ·
    refine ⟨95492386387584618165518791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127323181850112824220691721 95492386387584618165518791)
    ·
      refine ⟨143238579581376927248278187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95492386387584618165518791 143238579581376927248278187)
      ·
        refine ⟨214857869372065390872417281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143238579581376927248278187 214857869372065390872417281)
        ·
          refine ⟨161143402029049043154312961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214857869372065390872417281 161143402029049043154312961)
          ·
            refine ⟨120857551521786782365734721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161143402029049043154312961 120857551521786782365734721)
            ·
              refine ⟨90643163641340086774301041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120857551521786782365734721 90643163641340086774301041)
              ·
                refine ⟨67982372731005065080725781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90643163641340086774301041 67982372731005065080725781)
                ·
                  refine ⟨3186673721765862425659021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67982372731005065080725781 3186673721765862425659021)
                  ·
                    refine ⟨1195002645662198409622133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3186673721765862425659021 1195002645662198409622133)
                    ·
                      rfl

theorem cell22_3490889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 3].length) (baseStart_3490889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490889 prefixEnd_3490889 := by exact prefixLift 3490889
  have htrace : WordTrace (prefixWord ++ tailWord_3490889) baseStart_3490889 baseEnd_3490889 := by
    simpa [prefixWord, tailWord_3490889, baseEnd_3490889] using wordTrace_append hprefix tailTrace_3490889
  have hstable : (prefixWord ++ tailWord_3490889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490889).length < 2 ^ (prefixWord ++ tailWord_3490889).sum := by decide
  have hdescent : baseEnd_3490889 < baseStart_3490889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490893 : List Nat := [1, 6, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3490893 : Nat := 118140960795 + 3490893 * 2 ^ 59
def prefixEnd_3490893 : Nat := 4983230072969 + 3 ^ 40 * 3490893 * 2
def baseEnd_3490893 : Nat := 1195004014943943732522121

theorem tailTrace_3490893 : CollatzResearch.WordTrace tailWord_3490893 prefixEnd_3490893 1195004014943943732522121 := by
  unfold tailWord_3490893
  simp only [CollatzResearch.WordTrace]
  refine ⟨127323327742098332903837333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84882218494732221935891555 127323327742098332903837333)
  ·
    refine ⟨5968280987910859354867375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127323327742098332903837333 5968280987910859354867375)
    ·
      refine ⟨8952421481866289032301063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5968280987910859354867375 8952421481866289032301063)
      ·
        refine ⟨13428632222799433548451595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8952421481866289032301063 13428632222799433548451595)
        ·
          refine ⟨20142948334199150322677393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13428632222799433548451595 20142948334199150322677393)
          ·
            refine ⟨15107211250649362742008045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20142948334199150322677393 15107211250649362742008045)
            ·
              refine ⟨5665204218993511028253017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15107211250649362742008045 5665204218993511028253017)
              ·
                refine ⟨4248903164245133271189763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5665204218993511028253017 4248903164245133271189763)
                ·
                  refine ⟨6373354746367699906784645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248903164245133271189763 6373354746367699906784645)
                  ·
                    refine ⟨1195004014943943732522121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6373354746367699906784645 1195004014943943732522121)
                    ·
                      rfl

theorem cell22_3490893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3490893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490893 prefixEnd_3490893 := by exact prefixLift 3490893
  have htrace : WordTrace (prefixWord ++ tailWord_3490893) baseStart_3490893 baseEnd_3490893 := by
    simpa [prefixWord, tailWord_3490893, baseEnd_3490893] using wordTrace_append hprefix tailTrace_3490893
  have hstable : (prefixWord ++ tailWord_3490893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490893).length < 2 ^ (prefixWord ++ tailWord_3490893).sum := by decide
  have hdescent : baseEnd_3490893 < baseStart_3490893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490925 : List Nat := [1, 5, 1, 1, 2, 4, 2, 2, 4]
def baseStart_3490925 : Nat := 118140960795 + 3490925 * 2 ^ 59
def prefixEnd_3490925 : Nat := 4983230072969 + 3 ^ 40 * 3490925 * 2
def baseEnd_3490925 : Nat := 398338323065968771907341

theorem tailTrace_3490925 : CollatzResearch.WordTrace tailWord_3490925 prefixEnd_3490925 398338323065968771907341 := by
  unfold tailWord_3490925
  simp only [CollatzResearch.WordTrace]
  refine ⟨127324494877982402369002229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84882996585321601579334819 127324494877982402369002229)
  ·
    refine ⟨11936671394810850222093959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127324494877982402369002229 11936671394810850222093959)
    ·
      refine ⟨17905007092216275333140939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11936671394810850222093959 17905007092216275333140939)
      ·
        refine ⟨26857510638324412999711409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17905007092216275333140939 26857510638324412999711409)
        ·
          refine ⟨20143132978743309749783557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26857510638324412999711409 20143132978743309749783557)
          ·
            refine ⟨3776837433514370578084417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20143132978743309749783557 3776837433514370578084417)
            ·
              refine ⟨2832628075135777933563313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3776837433514370578084417 2832628075135777933563313)
              ·
                refine ⟨2124471056351833450172485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2832628075135777933563313 2124471056351833450172485)
                ·
                  refine ⟨398338323065968771907341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2124471056351833450172485 398338323065968771907341)
                  ·
                    rfl

theorem cell22_3490925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_3490925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490925 prefixEnd_3490925 := by exact prefixLift 3490925
  have htrace : WordTrace (prefixWord ++ tailWord_3490925) baseStart_3490925 baseEnd_3490925 := by
    simpa [prefixWord, tailWord_3490925, baseEnd_3490925] using wordTrace_append hprefix tailTrace_3490925
  have hstable : (prefixWord ++ tailWord_3490925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490925).length < 2 ^ (prefixWord ++ tailWord_3490925).sum := by decide
  have hdescent : baseEnd_3490925 < baseStart_3490925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490981 : List Nat := [1, 3, 1, 2, 1, 4, 3, 2, 5]
def baseStart_3490981 : Nat := 118140960795 + 3490981 * 2 ^ 59
def prefixEnd_3490981 : Nat := 4983230072969 + 3 ^ 40 * 3490981 * 2
def baseEnd_3490981 : Nat := 398344713047446945440617

theorem tailTrace_3490981 : CollatzResearch.WordTrace tailWord_3490981 prefixEnd_3490981 398344713047446945440617 := by
  unfold tailWord_3490981
  simp only [CollatzResearch.WordTrace]
  refine ⟨127326537365779523933040797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84884358243853015955360531 127326537365779523933040797)
  ·
    refine ⟨47747451512167321474890299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127326537365779523933040797 47747451512167321474890299)
    ·
      refine ⟨71621177268250982212335449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47747451512167321474890299 71621177268250982212335449)
      ·
        refine ⟨53715882951188236659251587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71621177268250982212335449 53715882951188236659251587)
        ·
          refine ⟨80573824426782354988877381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53715882951188236659251587 80573824426782354988877381)
          ·
            refine ⟨15107592080021691560414509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80573824426782354988877381 15107592080021691560414509)
            ·
              refine ⟨5665347030008134335155441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15107592080021691560414509 5665347030008134335155441)
              ·
                refine ⟨4249010272506100751366581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5665347030008134335155441 4249010272506100751366581)
                ·
                  refine ⟨398344713047446945440617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4249010272506100751366581 398344713047446945440617)
                  ·
                    rfl

theorem cell22_3490981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_3490981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3490981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3490981 prefixEnd_3490981 := by exact prefixLift 3490981
  have htrace : WordTrace (prefixWord ++ tailWord_3490981) baseStart_3490981 baseEnd_3490981 := by
    simpa [prefixWord, tailWord_3490981, baseEnd_3490981] using wordTrace_append hprefix tailTrace_3490981
  have hstable : (prefixWord ++ tailWord_3490981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490981).length < 2 ^ (prefixWord ++ tailWord_3490981).sum := by decide
  have hdescent : baseEnd_3490981 < baseStart_3490981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491073 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3491073 : Nat := 118140960795 + 3491073 * 2 ^ 59
def prefixEnd_3491073 : Nat := 4983230072969 + 3 ^ 40 * 3491073 * 2
def baseEnd_3491073 : Nat := 1195065632622483263021569

theorem tailTrace_3491073 : CollatzResearch.WordTrace tailWord_3491073 prefixEnd_3491073 1195065632622483263021569 := by
  unfold tailWord_3491073
  simp only [CollatzResearch.WordTrace]
  refine ⟨127329892881446223645389873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84886595254297482430259915 127329892881446223645389873)
  ·
    refine ⟨95497419661084667734042405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127329892881446223645389873 95497419661084667734042405)
    ·
      refine ⟨17905766186453375200132951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95497419661084667734042405 17905766186453375200132951)
      ·
        refine ⟨26858649279680062800199427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17905766186453375200132951 26858649279680062800199427)
        ·
          refine ⟨40287973919520094200299141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26858649279680062800199427 40287973919520094200299141)
          ·
            refine ⟨7553995109910017662556089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40287973919520094200299141 7553995109910017662556089)
            ·
              refine ⟨5665496332432513246917067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7553995109910017662556089 5665496332432513246917067)
              ·
                refine ⟨8498244498648769870375601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5665496332432513246917067 8498244498648769870375601)
                ·
                  refine ⟨6373683373986577402781701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8498244498648769870375601 6373683373986577402781701)
                  ·
                    refine ⟨1195065632622483263021569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6373683373986577402781701 1195065632622483263021569)
                    ·
                      rfl

theorem cell22_3491073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3491073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491073 prefixEnd_3491073 := by exact prefixLift 3491073
  have htrace : WordTrace (prefixWord ++ tailWord_3491073) baseStart_3491073 baseEnd_3491073 := by
    simpa [prefixWord, tailWord_3491073, baseEnd_3491073] using wordTrace_append hprefix tailTrace_3491073
  have hstable : (prefixWord ++ tailWord_3491073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491073).length < 2 ^ (prefixWord ++ tailWord_3491073).sum := by decide
  have hdescent : baseEnd_3491073 < baseStart_3491073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491137 : List Nat := [1, 2, 5, 2, 1, 1, 1, 5, 1, 3]
def baseStart_3491137 : Nat := 118140960795 + 3491137 * 2 ^ 59
def prefixEnd_3491137 : Nat := 4983230072969 + 3 ^ 40 * 3491137 * 2
def baseEnd_3491137 : Nat := 1195087541130408429421373

theorem tailTrace_3491137 : CollatzResearch.WordTrace tailWord_3491137 prefixEnd_3491137 1195087541130408429421373 := by
  unfold tailWord_3491137
  simp only [CollatzResearch.WordTrace]
  refine ⟨127332227153214362575719665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84888151435476241717146443 127332227153214362575719665)
  ·
    refine ⟨95499170364910771931789749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127332227153214362575719665 95499170364910771931789749)
    ·
      refine ⟨8953047221710384868605289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95499170364910771931789749 8953047221710384868605289)
      ·
        refine ⟨6714785416282788651453967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8953047221710384868605289 6714785416282788651453967)
        ·
          refine ⟨10072178124424182977180951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6714785416282788651453967 10072178124424182977180951)
          ·
            refine ⟨15108267186636274465771427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10072178124424182977180951 15108267186636274465771427)
            ·
              refine ⟨22662400779954411698657141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15108267186636274465771427 22662400779954411698657141)
              ·
                refine ⟨2124600073120726096749107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22662400779954411698657141 2124600073120726096749107)
                ·
                  refine ⟨3186900109681089145123661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124600073120726096749107 3186900109681089145123661)
                  ·
                    refine ⟨1195087541130408429421373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3186900109681089145123661 1195087541130408429421373)
                    ·
                      rfl

theorem cell22_3491137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_3491137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491137 prefixEnd_3491137 := by exact prefixLift 3491137
  have htrace : WordTrace (prefixWord ++ tailWord_3491137) baseStart_3491137 baseEnd_3491137 := by
    simpa [prefixWord, tailWord_3491137, baseEnd_3491137] using wordTrace_append hprefix tailTrace_3491137
  have hstable : (prefixWord ++ tailWord_3491137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491137).length < 2 ^ (prefixWord ++ tailWord_3491137).sum := by decide
  have hdescent : baseEnd_3491137 < baseStart_3491137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491161 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 6]
def baseStart_3491161 : Nat := 118140960795 + 3491161 * 2 ^ 59
def prefixEnd_3491161 : Nat := 4983230072969 + 3 ^ 40 * 3491161 * 2
def baseEnd_3491161 : Nat := 398365252273626788940433

theorem tailTrace_3491161 : CollatzResearch.WordTrace tailWord_3491161 prefixEnd_3491161 398365252273626788940433 := by
  unfold tailWord_3491161
  simp only [CollatzResearch.WordTrace]
  refine ⟨127333102505127414674593337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84888735003418276449728891 127333102505127414674593337)
  ·
    refine ⟨95499826878845561005945003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127333102505127414674593337 95499826878845561005945003)
    ·
      refine ⟨143249740318268341508917505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95499826878845561005945003 143249740318268341508917505)
      ·
        refine ⟨107437305238701256131688129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143249740318268341508917505 107437305238701256131688129)
        ·
          refine ⟨80577978929025942098766097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107437305238701256131688129 80577978929025942098766097)
          ·
            refine ⟨60433484196769456574074573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80577978929025942098766097 60433484196769456574074573)
            ·
              refine ⟨22662556573788546215277965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60433484196769456574074573 22662556573788546215277965)
              ·
                refine ⟨8498458715170704830729237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22662556573788546215277965 8498458715170704830729237)
                ·
                  refine ⟨398365252273626788940433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8498458715170704830729237 398365252273626788940433)
                  ·
                    rfl

theorem cell22_3491161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_3491161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491161 prefixEnd_3491161 := by exact prefixLift 3491161
  have htrace : WordTrace (prefixWord ++ tailWord_3491161) baseStart_3491161 baseEnd_3491161 := by
    simpa [prefixWord, tailWord_3491161, baseEnd_3491161] using wordTrace_append hprefix tailTrace_3491161
  have hstable : (prefixWord ++ tailWord_3491161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491161).length < 2 ^ (prefixWord ++ tailWord_3491161).sum := by decide
  have hdescent : baseEnd_3491161 < baseStart_3491161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491180 : List Nat := [2, 2, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_3491180 : Nat := 118140960795 + 3491180 * 2 ^ 59
def prefixEnd_3491180 : Nat := 4983230072969 + 3 ^ 40 * 3491180 * 2
def baseEnd_3491180 : Nat := 1195102260909170650596241

theorem tailTrace_3491180 : CollatzResearch.WordTrace tailWord_3491180 prefixEnd_3491180 1195102260909170650596241 := by
  unfold tailWord_3491180
  simp only [CollatzResearch.WordTrace]
  refine ⟨63666897746029290459767497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84889196994705720613023329 63666897746029290459767497)
  ·
    refine ⟨47750173309521967844825623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63666897746029290459767497 47750173309521967844825623)
    ·
      refine ⟨71625259964282951767238435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47750173309521967844825623 71625259964282951767238435)
      ·
        refine ⟨107437889946424427650857653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71625259964282951767238435 107437889946424427650857653)
        ·
          refine ⟨10072302182477290092267905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107437889946424427650857653 10072302182477290092267905)
          ·
            refine ⟨7554226636857967569200929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10072302182477290092267905 7554226636857967569200929)
            ·
              refine ⟨5665669977643475676900697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7554226636857967569200929 5665669977643475676900697)
              ·
                refine ⟨4249252483232606757675523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5665669977643475676900697 4249252483232606757675523)
                ·
                  refine ⟨6373878724848910136513285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4249252483232606757675523 6373878724848910136513285)
                  ·
                    refine ⟨1195102260909170650596241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6373878724848910136513285 1195102260909170650596241)
                    ·
                      rfl

theorem cell22_3491180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_3491180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491180 prefixEnd_3491180 := by exact prefixLift 3491180
  have htrace : WordTrace (prefixWord ++ tailWord_3491180) baseStart_3491180 baseEnd_3491180 := by
    simpa [prefixWord, tailWord_3491180, baseEnd_3491180] using wordTrace_append hprefix tailTrace_3491180
  have hstable : (prefixWord ++ tailWord_3491180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491180).length < 2 ^ (prefixWord ++ tailWord_3491180).sum := by decide
  have hdescent : baseEnd_3491180 < baseStart_3491180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491191 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 1, 6]
def baseStart_3491191 : Nat := 118140960795 + 3491191 * 2 ^ 59
def prefixEnd_3491191 : Nat := 4983230072969 + 3 ^ 40 * 3491191 * 2
def baseEnd_3491191 : Nat := 1195106026433970288571207

theorem tailTrace_3491191 : CollatzResearch.WordTrace tailWord_3491191 prefixEnd_3491191 1195106026433970288571207 := by
  unfold tailWord_3491191
  simp only [CollatzResearch.WordTrace]
  refine ⟨127334196695018729798185427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84889464463345819865456951 127334196695018729798185427)
  ·
    refine ⟨191001295042528094697278141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127334196695018729798185427 191001295042528094697278141)
    ·
      refine ⟨71625485640948035511479303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191001295042528094697278141 71625485640948035511479303)
      ·
        refine ⟨107438228461422053267218955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71625485640948035511479303 107438228461422053267218955)
        ·
          refine ⟨161157342692133079900828433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107438228461422053267218955 161157342692133079900828433)
          ·
            refine ⟨120868007019099809925621325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161157342692133079900828433 120868007019099809925621325)
            ·
              refine ⟨45325502632162428722107997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120868007019099809925621325 45325502632162428722107997)
              ·
                refine ⟨16997063487060910770790499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45325502632162428722107997 16997063487060910770790499)
                ·
                  refine ⟨25495595230591366156185749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16997063487060910770790499 25495595230591366156185749)
                  ·
                    refine ⟨1195106026433970288571207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25495595230591366156185749 1195106026433970288571207)
                    ·
                      rfl

theorem cell22_3491191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_3491191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491191 prefixEnd_3491191 := by exact prefixLift 3491191
  have htrace : WordTrace (prefixWord ++ tailWord_3491191) baseStart_3491191 baseEnd_3491191 := by
    simpa [prefixWord, tailWord_3491191, baseEnd_3491191] using wordTrace_append hprefix tailTrace_3491191
  have hstable : (prefixWord ++ tailWord_3491191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491191).length < 2 ^ (prefixWord ++ tailWord_3491191).sum := by decide
  have hdescent : baseEnd_3491191 < baseStart_3491191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491193 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 4, 3]
def baseStart_3491193 : Nat := 118140960795 + 3491193 * 2 ^ 59
def prefixEnd_3491193 : Nat := 4983230072969 + 3 ^ 40 * 3491193 * 2
def baseEnd_3491193 : Nat := 1195106711074842950021201

theorem tailTrace_3491193 : CollatzResearch.WordTrace tailWord_3491193 prefixEnd_3491193 1195106711074842950021201 := by
  unfold tailWord_3491193
  simp only [CollatzResearch.WordTrace]
  refine ⟨127334269641011484139758233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84889513094007656093172155 127334269641011484139758233)
  ·
    refine ⟨95500702230758613104818675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127334269641011484139758233 95500702230758613104818675)
    ·
      refine ⟨143251053346137919657228013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95500702230758613104818675 143251053346137919657228013)
      ·
        refine ⟨53719145004801719871460505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143251053346137919657228013 53719145004801719871460505)
        ·
          refine ⟨40289358753601289903595379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53719145004801719871460505 40289358753601289903595379)
          ·
            refine ⟨60434038130401934855393069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40289358753601289903595379 60434038130401934855393069)
            ·
              refine ⟨22662764298900725570772401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60434038130401934855393069 22662764298900725570772401)
              ·
                refine ⟨16997073224175544178079301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22662764298900725570772401 16997073224175544178079301)
                ·
                  refine ⟨3186951229532914533389869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16997073224175544178079301 3186951229532914533389869)
                  ·
                    refine ⟨1195106711074842950021201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3186951229532914533389869 1195106711074842950021201)
                    ·
                      rfl

theorem cell22_3491193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 3].length) (baseStart_3491193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491193 prefixEnd_3491193 := by exact prefixLift 3491193
  have htrace : WordTrace (prefixWord ++ tailWord_3491193) baseStart_3491193 baseEnd_3491193 := by
    simpa [prefixWord, tailWord_3491193, baseEnd_3491193] using wordTrace_append hprefix tailTrace_3491193
  have hstable : (prefixWord ++ tailWord_3491193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491193).length < 2 ^ (prefixWord ++ tailWord_3491193).sum := by decide
  have hdescent : baseEnd_3491193 < baseStart_3491193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491208 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 4, 4]
def baseStart_3491208 : Nat := 118140960795 + 3491208 * 2 ^ 59
def prefixEnd_3491208 : Nat := 4983230072969 + 3 ^ 40 * 3491208 * 2
def baseEnd_3491208 : Nat := 1195111845881387910896155

theorem tailTrace_3491208 : CollatzResearch.WordTrace tailWord_3491208 prefixEnd_3491208 1195111845881387910896155 := by
  unfold tailWord_3491208
  simp only [CollatzResearch.WordTrace]
  refine ⟨63667408367978570850777139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84889877823971427801036185 63667408367978570850777139)
  ·
    refine ⟨95501112551967856276165709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63667408367978570850777139 95501112551967856276165709)
    ·
      refine ⟨35812917206987946103562141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95501112551967856276165709 35812917206987946103562141)
      ·
        refine ⟨13429843952620479788835803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35812917206987946103562141 13429843952620479788835803)
        ·
          refine ⟨20144765928930719683253705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13429843952620479788835803 20144765928930719683253705)
          ·
            refine ⟨15108574446698039762440279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20144765928930719683253705 15108574446698039762440279)
            ·
              refine ⟨22662861670047059643660419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15108574446698039762440279 22662861670047059643660419)
              ·
                refine ⟨33994292505070589465490629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22662861670047059643660419 33994292505070589465490629)
                ·
                  refine ⟨6373929844700735524779493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33994292505070589465490629 6373929844700735524779493)
                  ·
                    refine ⟨1195111845881387910896155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6373929844700735524779493 1195111845881387910896155)
                    ·
                      rfl

theorem cell22_3491208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_3491208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491208 prefixEnd_3491208 := by exact prefixLift 3491208
  have htrace : WordTrace (prefixWord ++ tailWord_3491208) baseStart_3491208 baseEnd_3491208 := by
    simpa [prefixWord, tailWord_3491208, baseEnd_3491208] using wordTrace_append hprefix tailTrace_3491208
  have hstable : (prefixWord ++ tailWord_3491208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491208).length < 2 ^ (prefixWord ++ tailWord_3491208).sum := by decide
  have hdescent : baseEnd_3491208 < baseStart_3491208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491251 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 9]
def baseStart_3491251 : Nat := 118140960795 + 3491251 * 2 ^ 59
def prefixEnd_3491251 : Nat := 4983230072969 + 3 ^ 40 * 3491251 * 2
def baseEnd_3491251 : Nat := 398375521886716710690341

theorem tailTrace_3491251 : CollatzResearch.WordTrace tailWord_3491251 prefixEnd_3491251 398375521886716710690341 := by
  unfold tailWord_3491251
  simp only [CollatzResearch.WordTrace]
  refine ⟨127336385074801360045369607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84890923383200906696913071 127336385074801360045369607)
  ·
    refine ⟨191004577612202040068054411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127336385074801360045369607 191004577612202040068054411)
    ·
      refine ⟨286506866418303060102081617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191004577612202040068054411 286506866418303060102081617)
      ·
        refine ⟨214880149813727295076561213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286506866418303060102081617 214880149813727295076561213)
        ·
          refine ⟨80580056180147735653710455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214880149813727295076561213 80580056180147735653710455)
          ·
            refine ⟨120870084270221603480565683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80580056180147735653710455 120870084270221603480565683)
            ·
              refine ⟨181305126405332405220848525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120870084270221603480565683 181305126405332405220848525)
              ·
                refine ⟨67989422401999651957818197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181305126405332405220848525 67989422401999651957818197)
                ·
                  refine ⟨398375521886716710690341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67989422401999651957818197 398375521886716710690341)
                  ·
                    rfl

theorem cell22_3491251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 9].length) (baseStart_3491251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491251 prefixEnd_3491251 := by exact prefixLift 3491251
  have htrace : WordTrace (prefixWord ++ tailWord_3491251) baseStart_3491251 baseEnd_3491251 := by
    simpa [prefixWord, tailWord_3491251, baseEnd_3491251] using wordTrace_append hprefix tailTrace_3491251
  have hstable : (prefixWord ++ tailWord_3491251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491251).length < 2 ^ (prefixWord ++ tailWord_3491251).sum := by decide
  have hdescent : baseEnd_3491251 < baseStart_3491251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491272 : List Nat := [2, 1, 3, 1, 3, 1, 3, 4, 1, 3]
def baseStart_3491272 : Nat := 118140960795 + 3491272 * 2 ^ 59
def prefixEnd_3491272 : Nat := 4983230072969 + 3 ^ 40 * 3491272 * 2
def baseEnd_3491272 : Nat := 1195133754389313077295959

theorem tailTrace_3491272 : CollatzResearch.WordTrace tailWord_3491272 prefixEnd_3491272 1195133754389313077295959 := by
  unfold tailWord_3491272
  simp only [CollatzResearch.WordTrace]
  refine ⟨63668575503862640315942035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84891434005150187087922713 63668575503862640315942035)
  ·
    refine ⟨95502863255793960473913053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63668575503862640315942035 95502863255793960473913053)
    ·
      refine ⟨35813573720922735177717395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95502863255793960473913053 35813573720922735177717395)
      ·
        refine ⟨53720360581384102766576093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35813573720922735177717395 53720360581384102766576093)
        ·
          refine ⟨20145135218019038537466035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53720360581384102766576093 20145135218019038537466035)
          ·
            refine ⟨30217702827028557806199053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20145135218019038537466035 30217702827028557806199053)
            ·
              refine ⟨11331638560135709177324645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30217702827028557806199053 11331638560135709177324645)
              ·
                refine ⟨2124682230025445470748371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11331638560135709177324645 2124682230025445470748371)
                ·
                  refine ⟨3187023345038168206122557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124682230025445470748371 3187023345038168206122557)
                  ·
                    refine ⟨1195133754389313077295959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187023345038168206122557 1195133754389313077295959)
                    ·
                      rfl

theorem cell22_3491272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_3491272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491272 prefixEnd_3491272 := by exact prefixLift 3491272
  have htrace : WordTrace (prefixWord ++ tailWord_3491272) baseStart_3491272 baseEnd_3491272 := by
    simpa [prefixWord, tailWord_3491272, baseEnd_3491272] using wordTrace_append hprefix tailTrace_3491272
  have hstable : (prefixWord ++ tailWord_3491272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491272).length < 2 ^ (prefixWord ++ tailWord_3491272).sum := by decide
  have hdescent : baseEnd_3491272 < baseStart_3491272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491360 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 1, 6]
def baseStart_3491360 : Nat := 118140960795 + 3491360 * 2 ^ 59
def prefixEnd_3491360 : Nat := 4983230072969 + 3 ^ 40 * 3491360 * 2
def baseEnd_3491360 : Nat := 1195163878587710181095689

theorem tailTrace_3491360 : CollatzResearch.WordTrace tailWord_3491360 prefixEnd_3491360 1195163878587710181095689 := by
  unfold tailWord_3491360
  simp only [CollatzResearch.WordTrace]
  refine ⟨63670180315703235830543767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84893573754270981107391689 63670180315703235830543767)
  ·
    refine ⟨95505270473554853745815651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63670180315703235830543767 95505270473554853745815651)
    ·
      refine ⟨143257905710332280618723477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95505270473554853745815651 143257905710332280618723477)
      ·
        refine ⟨6715214330171825654002663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143257905710332280618723477 6715214330171825654002663)
        ·
          refine ⟨10072821495257738481003995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6715214330171825654002663 10072821495257738481003995)
          ·
            refine ⟨15109232242886607721505993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10072821495257738481003995 15109232242886607721505993)
            ·
              refine ⟨11331924182164955791129495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15109232242886607721505993 11331924182164955791129495)
              ·
                refine ⟨16997886273247433686694243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11331924182164955791129495 16997886273247433686694243)
                ·
                  refine ⟨25496829409871150530041365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16997886273247433686694243 25496829409871150530041365)
                  ·
                    refine ⟨1195163878587710181095689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25496829409871150530041365 1195163878587710181095689)
                    ·
                      rfl

theorem cell22_3491360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_3491360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491360 prefixEnd_3491360 := by exact prefixLift 3491360
  have htrace : WordTrace (prefixWord ++ tailWord_3491360) baseStart_3491360 baseEnd_3491360 := by
    simpa [prefixWord, tailWord_3491360, baseEnd_3491360] using wordTrace_append hprefix tailTrace_3491360
  have hstable : (prefixWord ++ tailWord_3491360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491360).length < 2 ^ (prefixWord ++ tailWord_3491360).sum := by decide
  have hdescent : baseEnd_3491360 < baseStart_3491360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491484 : List Nat := [2, 2, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_3491484 : Nat := 118140960795 + 3491484 * 2 ^ 59
def prefixEnd_3491484 : Nat := 4983230072969 + 3 ^ 40 * 3491484 * 2
def baseEnd_3491484 : Nat := 1195206326321815190995309

theorem tailTrace_3491484 : CollatzResearch.WordTrace tailWord_3491484 prefixEnd_3491484 1195206326321815190995309 := by
  unfold tailWord_3491484
  simp only [CollatzResearch.WordTrace]
  refine ⟨63672441641478620419300753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84896588855304827225734337 63672441641478620419300753)
  ·
    refine ⟨47754331231108965314475565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63672441641478620419300753 47754331231108965314475565)
    ·
      refine ⟨17907874211665861992928337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47754331231108965314475565 17907874211665861992928337)
      ·
        refine ⟨13430905658749396494696253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17907874211665861992928337 13430905658749396494696253)
        ·
          refine ⟨5036589622031023685511095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13430905658749396494696253 5036589622031023685511095)
          ·
            refine ⟨7554884433046535528266643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5036589622031023685511095 7554884433046535528266643)
            ·
              refine ⟨11332326649569803292399965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7554884433046535528266643 11332326649569803292399965)
              ·
                refine ⟨4249622493588676234649987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11332326649569803292399965 4249622493588676234649987)
                ·
                  refine ⟨6374433740383014351974981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4249622493588676234649987 6374433740383014351974981)
                  ·
                    refine ⟨1195206326321815190995309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6374433740383014351974981 1195206326321815190995309)
                    ·
                      rfl

theorem cell22_3491484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_3491484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491484 prefixEnd_3491484 := by exact prefixLift 3491484
  have htrace : WordTrace (prefixWord ++ tailWord_3491484) baseStart_3491484 baseEnd_3491484 := by
    simpa [prefixWord, tailWord_3491484, baseEnd_3491484] using wordTrace_append hprefix tailTrace_3491484
  have hstable : (prefixWord ++ tailWord_3491484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491484).length < 2 ^ (prefixWord ++ tailWord_3491484).sum := by decide
  have hdescent : baseEnd_3491484 < baseStart_3491484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491533 : List Nat := [1, 6, 2, 1, 1, 3, 1, 3, 4]
def baseStart_3491533 : Nat := 118140960795 + 3491533 * 2 ^ 59
def prefixEnd_3491533 : Nat := 4983230072969 + 3 ^ 40 * 3491533 * 2
def baseEnd_3491533 : Nat := 398407700007731798840053

theorem tailTrace_3491533 : CollatzResearch.WordTrace tailWord_3491533 prefixEnd_3491533 398407700007731798840053 := by
  unfold tailWord_3491533
  simp only [CollatzResearch.WordTrace]
  refine ⟨127346670459779722207135253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84897780306519814804756835 127346670459779722207135253)
  ·
    refine ⟨5969375177802174478459465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127346670459779722207135253 5969375177802174478459465)
    ·
      refine ⟨4477031383351630858844599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5969375177802174478459465 4477031383351630858844599)
      ·
        refine ⟨6715547075027446288266899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4477031383351630858844599 6715547075027446288266899)
        ·
          refine ⟨10073320612541169432400349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6715547075027446288266899 10073320612541169432400349)
          ·
            refine ⟨3777495229702938537150131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10073320612541169432400349 3777495229702938537150131)
            ·
              refine ⟨5666242844554407805725197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3777495229702938537150131 5666242844554407805725197)
              ·
                refine ⟨2124841066707902927146949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5666242844554407805725197 2124841066707902927146949)
                ·
                  refine ⟨398407700007731798840053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2124841066707902927146949 398407700007731798840053)
                  ·
                    rfl

theorem cell22_3491533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_3491533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491533 prefixEnd_3491533 := by exact prefixLift 3491533
  have htrace : WordTrace (prefixWord ++ tailWord_3491533) baseStart_3491533 baseEnd_3491533 := by
    simpa [prefixWord, tailWord_3491533, baseEnd_3491533] using wordTrace_append hprefix tailTrace_3491533
  have hstable : (prefixWord ++ tailWord_3491533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491533).length < 2 ^ (prefixWord ++ tailWord_3491533).sum := by decide
  have hdescent : baseEnd_3491533 < baseStart_3491533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491632 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 8, 3]
def baseStart_3491632 : Nat := 118140960795 + 3491632 * 2 ^ 59
def prefixEnd_3491632 : Nat := 4983230072969 + 3 ^ 40 * 3491632 * 2
def baseEnd_3491632 : Nat := 1195256989746392138294855

theorem tailTrace_3491632 : CollatzResearch.WordTrace tailWord_3491632 prefixEnd_3491632 1195256989746392138294855 := by
  unfold tailWord_3491632
  simp only [CollatzResearch.WordTrace]
  refine ⟨63675140643210531057494575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84900187524280708076659433 63675140643210531057494575)
  ·
    refine ⟨95512710964815796586241863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63675140643210531057494575 95512710964815796586241863)
    ·
      refine ⟨143269066447223694879362795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95512710964815796586241863 143269066447223694879362795)
      ·
        refine ⟨214903599670835542319044193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143269066447223694879362795 214903599670835542319044193)
        ·
          refine ⟨161177699753126656739283145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214903599670835542319044193 161177699753126656739283145)
          ·
            refine ⟨120883274814844992554462359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161177699753126656739283145 120883274814844992554462359)
            ·
              refine ⟨181324912222267488831693539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120883274814844992554462359 181324912222267488831693539)
              ·
                refine ⟨271987368333401233247540309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181324912222267488831693539 271987368333401233247540309)
                ·
                  refine ⟨3187351972657045702119613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 271987368333401233247540309 3187351972657045702119613)
                  ·
                    refine ⟨1195256989746392138294855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187351972657045702119613 1195256989746392138294855)
                    ·
                      rfl

theorem cell22_3491632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 8, 3].length) (baseStart_3491632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491632 prefixEnd_3491632 := by exact prefixLift 3491632
  have htrace : WordTrace (prefixWord ++ tailWord_3491632) baseStart_3491632 baseEnd_3491632 := by
    simpa [prefixWord, tailWord_3491632, baseEnd_3491632] using wordTrace_append hprefix tailTrace_3491632
  have hstable : (prefixWord ++ tailWord_3491632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491632).length < 2 ^ (prefixWord ++ tailWord_3491632).sum := by decide
  have hdescent : baseEnd_3491632 < baseStart_3491632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491666 : List Nat := [3, 2, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_3491666 : Nat := 118140960795 + 3491666 * 2 ^ 59
def prefixEnd_3491666 : Nat := 4983230072969 + 3 ^ 40 * 3491666 * 2
def baseEnd_3491666 : Nat := 1195268628641227382944751

theorem tailTrace_3491666 : CollatzResearch.WordTrace tailWord_3491666 prefixEnd_3491666 1195268628641227382944751 := by
  unfold tailWord_3491666
  simp only [CollatzResearch.WordTrace]
  refine ⟨31837880342074471480431713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84901014245531923947817901 31837880342074471480431713)
  ·
    refine ⟨23878410256555853610323785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31837880342074471480431713 23878410256555853610323785)
    ·
      refine ⟨17908807692416890207742839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23878410256555853610323785 17908807692416890207742839)
      ·
        refine ⟨26863211538625335311614259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17908807692416890207742839 26863211538625335311614259)
        ·
          refine ⟨40294817307938002967421389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26863211538625335311614259 40294817307938002967421389)
          ·
            refine ⟨15110556490476751112783021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40294817307938002967421389 15110556490476751112783021)
            ·
              refine ⟨5666458683928781667293633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15110556490476751112783021 5666458683928781667293633)
              ·
                refine ⟨4249844012946586250470225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5666458683928781667293633 4249844012946586250470225)
                ·
                  refine ⟨3187383009709939687852669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4249844012946586250470225 3187383009709939687852669)
                  ·
                    refine ⟨1195268628641227382944751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187383009709939687852669 1195268628641227382944751)
                    ·
                      rfl

theorem cell22_3491666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_3491666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491666 prefixEnd_3491666 := by exact prefixLift 3491666
  have htrace : WordTrace (prefixWord ++ tailWord_3491666) baseStart_3491666 baseEnd_3491666 := by
    simpa [prefixWord, tailWord_3491666, baseEnd_3491666] using wordTrace_append hprefix tailTrace_3491666
  have hstable : (prefixWord ++ tailWord_3491666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491666).length < 2 ^ (prefixWord ++ tailWord_3491666).sum := by decide
  have hdescent : baseEnd_3491666 < baseStart_3491666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491683 : List Nat := [1, 1, 1, 5, 4, 1, 3, 1, 2, 3]
def baseStart_3491683 : Nat := 118140960795 + 3491683 * 2 ^ 59
def prefixEnd_3491683 : Nat := 4983230072969 + 3 ^ 40 * 3491683 * 2
def baseEnd_3491683 : Nat := 1195274448088645005269699

theorem tailTrace_3491683 : CollatzResearch.WordTrace tailWord_3491683 prefixEnd_3491683 1195274448088645005269699 := by
  unfold tailWord_3491683
  simp only [CollatzResearch.WordTrace]
  refine ⟨127352141409236297825095703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84901427606157531883397135 127352141409236297825095703)
  ·
    refine ⟨191028212113854446737643555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127352141409236297825095703 191028212113854446737643555)
    ·
      refine ⟨286542318170781670106465333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191028212113854446737643555 286542318170781670106465333)
      ·
        refine ⟨26863342328510781572481125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 286542318170781670106465333 26863342328510781572481125)
        ·
          refine ⟨5036876686595771544840211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26863342328510781572481125 5036876686595771544840211)
          ·
            refine ⟨7555315029893657317260317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5036876686595771544840211 7555315029893657317260317)
            ·
              refine ⟨2833243136210121493972619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7555315029893657317260317 2833243136210121493972619)
              ·
                refine ⟨4249864704315182240958929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833243136210121493972619 4249864704315182240958929)
                ·
                  refine ⟨3187398528236386680719197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4249864704315182240958929 3187398528236386680719197)
                  ·
                    refine ⟨1195274448088645005269699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187398528236386680719197 1195274448088645005269699)
                    ·
                      rfl

theorem cell22_3491683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 2, 3].length) (baseStart_3491683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491683 prefixEnd_3491683 := by exact prefixLift 3491683
  have htrace : WordTrace (prefixWord ++ tailWord_3491683) baseStart_3491683 baseEnd_3491683 := by
    simpa [prefixWord, tailWord_3491683, baseEnd_3491683] using wordTrace_append hprefix tailTrace_3491683
  have hstable : (prefixWord ++ tailWord_3491683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491683).length < 2 ^ (prefixWord ++ tailWord_3491683).sum := by decide
  have hdescent : baseEnd_3491683 < baseStart_3491683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491734 : List Nat := [5, 3, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3491734 : Nat := 118140960795 + 3491734 * 2 ^ 59
def prefixEnd_3491734 : Nat := 4983230072969 + 3 ^ 40 * 3491734 * 2
def baseEnd_3491734 : Nat := 1195291906430897872244543

theorem tailTrace_3491734 : CollatzResearch.WordTrace tailWord_3491734 prefixEnd_3491734 1195291906430897872244543 := by
  unfold tailWord_3491734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7959625095753220845950141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84902667688034355690134837 7959625095753220845950141)
  ·
    refine ⟨2984859410907457817231303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7959625095753220845950141 2984859410907457817231303)
    ·
      refine ⟨4477289116361186725846955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2984859410907457817231303 4477289116361186725846955)
      ·
        refine ⟨6715933674541780088770433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4477289116361186725846955 6715933674541780088770433)
        ·
          refine ⟨5036950255906335066577825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6715933674541780088770433 5036950255906335066577825)
          ·
            refine ⟨3777712691929751299933369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5036950255906335066577825 3777712691929751299933369)
            ·
              refine ⟨2833284518947313474950027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3777712691929751299933369 2833284518947313474950027)
              ·
                refine ⟨4249926778420970212425041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833284518947313474950027 4249926778420970212425041)
                ·
                  refine ⟨3187445083815727659318781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4249926778420970212425041 3187445083815727659318781)
                  ·
                    refine ⟨1195291906430897872244543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187445083815727659318781 1195291906430897872244543)
                    ·
                      rfl

theorem cell22_3491734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3491734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491734 prefixEnd_3491734 := by exact prefixLift 3491734
  have htrace : WordTrace (prefixWord ++ tailWord_3491734) baseStart_3491734 baseEnd_3491734 := by
    simpa [prefixWord, tailWord_3491734, baseEnd_3491734] using wordTrace_append hprefix tailTrace_3491734
  have hstable : (prefixWord ++ tailWord_3491734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491734).length < 2 ^ (prefixWord ++ tailWord_3491734).sum := by decide
  have hdescent : baseEnd_3491734 < baseStart_3491734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491741 : List Nat := [1, 4, 2, 1, 2, 2, 4, 1, 5]
def baseStart_3491741 : Nat := 118140960795 + 3491741 * 2 ^ 59
def prefixEnd_3491741 : Nat := 4983230072969 + 3 ^ 40 * 3491741 * 2
def baseEnd_3491741 : Nat := 398431434224650729106507

theorem tailTrace_3491741 : CollatzResearch.WordTrace tailWord_3491741 prefixEnd_3491741 398431434224650729106507 := by
  unfold tailWord_3491741
  simp only [CollatzResearch.WordTrace]
  refine ⟨127354256843026173730707077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84902837895350782487138051 127354256843026173730707077)
  ·
    refine ⟨23878923158067407574507577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127354256843026173730707077 23878923158067407574507577)
    ·
      refine ⟨17909192368550555680880683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23878923158067407574507577 17909192368550555680880683)
      ·
        refine ⟨26863788552825833521321025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17909192368550555680880683 26863788552825833521321025)
        ·
          refine ⟨20147841414619375140990769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26863788552825833521321025 20147841414619375140990769)
          ·
            refine ⟨15110881060964531355743077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20147841414619375140990769 15110881060964531355743077)
            ·
              refine ⟨2833290198930849629201827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15110881060964531355743077 2833290198930849629201827)
              ·
                refine ⟨4249935298396274443802741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833290198930849629201827 4249935298396274443802741)
                ·
                  refine ⟨398431434224650729106507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4249935298396274443802741 398431434224650729106507)
                  ·
                    rfl

theorem cell22_3491741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_3491741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491741 prefixEnd_3491741 := by exact prefixLift 3491741
  have htrace : WordTrace (prefixWord ++ tailWord_3491741) baseStart_3491741 baseEnd_3491741 := by
    simpa [prefixWord, tailWord_3491741, baseEnd_3491741] using wordTrace_append hprefix tailTrace_3491741
  have hstable : (prefixWord ++ tailWord_3491741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491741).length < 2 ^ (prefixWord ++ tailWord_3491741).sum := by decide
  have hdescent : baseEnd_3491741 < baseStart_3491741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491801 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 1, 5]
def baseStart_3491801 : Nat := 118140960795 + 3491801 * 2 ^ 59
def prefixEnd_3491801 : Nat := 4983230072969 + 3 ^ 40 * 3491801 * 2
def baseEnd_3491801 : Nat := 1195314841900132030819337

theorem tailTrace_3491801 : CollatzResearch.WordTrace tailWord_3491801 prefixEnd_3491801 1195314841900132030819337 := by
  unfold tailWord_3491801
  simp only [CollatzResearch.WordTrace]
  refine ⟨127356445222808803977891257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84904296815205869318594171 127356445222808803977891257)
  ·
    refine ⟨95517333917106602983418443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127356445222808803977891257 95517333917106602983418443)
    ·
      refine ⟨143276000875659904475127665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95517333917106602983418443 143276000875659904475127665)
      ·
        refine ⟨107457000656744928356345749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143276000875659904475127665 107457000656744928356345749)
        ·
          refine ⟨5037046905784918516703707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107457000656744928356345749 5037046905784918516703707)
          ·
            refine ⟨7555570358677377775055561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5037046905784918516703707 7555570358677377775055561)
            ·
              refine ⟨5666677769008033331291671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7555570358677377775055561 5666677769008033331291671)
              ·
                refine ⟨8500016653512049996937507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5666677769008033331291671 8500016653512049996937507)
                ·
                  refine ⟨12750024980268074995406261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8500016653512049996937507 12750024980268074995406261)
                  ·
                    refine ⟨1195314841900132030819337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12750024980268074995406261 1195314841900132030819337)
                    ·
                      rfl

theorem cell22_3491801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_3491801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491801 prefixEnd_3491801 := by exact prefixLift 3491801
  have htrace : WordTrace (prefixWord ++ tailWord_3491801) baseStart_3491801 baseEnd_3491801 := by
    simpa [prefixWord, tailWord_3491801, baseEnd_3491801] using wordTrace_append hprefix tailTrace_3491801
  have hstable : (prefixWord ++ tailWord_3491801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491801).length < 2 ^ (prefixWord ++ tailWord_3491801).sum := by decide
  have hdescent : baseEnd_3491801 < baseStart_3491801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491859 : List Nat := [1, 1, 1, 2, 1, 4, 2, 5, 5]
def baseStart_3491859 : Nat := 118140960795 + 3491859 * 2 ^ 59
def prefixEnd_3491859 : Nat := 4983230072969 + 3 ^ 40 * 3491859 * 2
def baseEnd_3491859 : Nat := 398444898828479737623053

theorem tailTrace_3491859 : CollatzResearch.WordTrace tailWord_3491859 prefixEnd_3491859 398444898828479737623053 := by
  unfold tailWord_3491859
  simp only [CollatzResearch.WordTrace]
  refine ⟨127358560656598679883502631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84905707104399119922335087 127358560656598679883502631)
  ·
    refine ⟨191037840984898019825253947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127358560656598679883502631 191037840984898019825253947)
    ·
      refine ⟨286556761477347029737880921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191037840984898019825253947 286556761477347029737880921)
      ·
        refine ⟨214917571108010272303410691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286556761477347029737880921 214917571108010272303410691)
        ·
          refine ⟨322376356662015408455116037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214917571108010272303410691 322376356662015408455116037)
          ·
            refine ⟨60445566874127889085334257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 322376356662015408455116037 60445566874127889085334257)
            ·
              refine ⟨45334175155595916814000693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60445566874127889085334257 45334175155595916814000693)
              ·
                refine ⟨4250078920837117201312565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45334175155595916814000693 4250078920837117201312565)
                ·
                  refine ⟨398444898828479737623053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4250078920837117201312565 398444898828479737623053)
                  ·
                    rfl

theorem cell22_3491859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 5].length) (baseStart_3491859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491859 prefixEnd_3491859 := by exact prefixLift 3491859
  have htrace : WordTrace (prefixWord ++ tailWord_3491859) baseStart_3491859 baseEnd_3491859 := by
    simpa [prefixWord, tailWord_3491859, baseEnd_3491859] using wordTrace_append hprefix tailTrace_3491859
  have hstable : (prefixWord ++ tailWord_3491859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491859).length < 2 ^ (prefixWord ++ tailWord_3491859).sum := by decide
  have hdescent : baseEnd_3491859 < baseStart_3491859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491897 : List Nat := [1, 2, 1, 5, 3, 1, 3, 2, 1, 3]
def baseStart_3491897 : Nat := 118140960795 + 3491897 * 2 ^ 59
def prefixEnd_3491897 : Nat := 4983230072969 + 3 ^ 40 * 3491897 * 2
def baseEnd_3491897 : Nat := 1195347704662019780419043

theorem tailTrace_3491897 : CollatzResearch.WordTrace tailWord_3491897 prefixEnd_3491897 1195347704662019780419043 := by
  unfold tailWord_3491897
  simp only [CollatzResearch.WordTrace]
  refine ⟨127359946630461012373385945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84906631086974008248923963 127359946630461012373385945)
  ·
    refine ⟨95519959972845759280039459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127359946630461012373385945 95519959972845759280039459)
    ·
      refine ⟨143279939959268638920059189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95519959972845759280039459 143279939959268638920059189)
      ·
        refine ⟨13432494371181434898755549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143279939959268638920059189 13432494371181434898755549)
        ·
          refine ⟨5037185389193038087033331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13432494371181434898755549 5037185389193038087033331)
          ·
            refine ⟨7555778083789557130549997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5037185389193038087033331 7555778083789557130549997)
            ·
              refine ⟨2833416781421083923956249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7555778083789557130549997 2833416781421083923956249)
              ·
                refine ⟨2125062586065812942967187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2833416781421083923956249 2125062586065812942967187)
                ·
                  refine ⟨3187593879098719414450781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125062586065812942967187 3187593879098719414450781)
                  ·
                    refine ⟨1195347704662019780419043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187593879098719414450781 1195347704662019780419043)
                    ·
                      rfl

theorem cell22_3491897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 1, 3].length) (baseStart_3491897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491897 prefixEnd_3491897 := by exact prefixLift 3491897
  have htrace : WordTrace (prefixWord ++ tailWord_3491897) baseStart_3491897 baseEnd_3491897 := by
    simpa [prefixWord, tailWord_3491897, baseEnd_3491897] using wordTrace_append hprefix tailTrace_3491897
  have hstable : (prefixWord ++ tailWord_3491897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491897).length < 2 ^ (prefixWord ++ tailWord_3491897).sum := by decide
  have hdescent : baseEnd_3491897 < baseStart_3491897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491936 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 1, 5]
def baseStart_3491936 : Nat := 118140960795 + 3491936 * 2 ^ 59
def prefixEnd_3491936 : Nat := 4983230072969 + 3 ^ 40 * 3491936 * 2
def baseEnd_3491936 : Nat := 1195361055159036678693923

theorem tailTrace_3491936 : CollatzResearch.WordTrace tailWord_3491936 prefixEnd_3491936 1195361055159036678693923 := by
  unfold tailWord_3491936
  simp only [CollatzResearch.WordTrace]
  refine ⟨63680684538659861017027831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84907579384879814689370441 63680684538659861017027831)
  ·
    refine ⟨95521026807989791525541747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63680684538659861017027831 95521026807989791525541747)
    ·
      refine ⟨143281540211984687288312621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95521026807989791525541747 143281540211984687288312621)
      ·
        refine ⟨53730577579494257733117233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143281540211984687288312621 53730577579494257733117233)
        ·
          refine ⟨40297933184620693299837925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53730577579494257733117233 40297933184620693299837925)
          ·
            refine ⟨7555862472116379993719611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40297933184620693299837925 7555862472116379993719611)
            ·
              refine ⟨11333793708174569990579417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7555862472116379993719611 11333793708174569990579417)
              ·
                refine ⟨8500345281130927492934563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11333793708174569990579417 8500345281130927492934563)
                ·
                  refine ⟨12750517921696391239401845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8500345281130927492934563 12750517921696391239401845)
                  ·
                    refine ⟨1195361055159036678693923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12750517921696391239401845 1195361055159036678693923)
                    ·
                      rfl

theorem cell22_3491936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_3491936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491936 prefixEnd_3491936 := by exact prefixLift 3491936
  have htrace : WordTrace (prefixWord ++ tailWord_3491936) baseStart_3491936 baseEnd_3491936 := by
    simpa [prefixWord, tailWord_3491936, baseEnd_3491936] using wordTrace_append hprefix tailTrace_3491936
  have hstable : (prefixWord ++ tailWord_3491936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491936).length < 2 ^ (prefixWord ++ tailWord_3491936).sum := by decide
  have hdescent : baseEnd_3491936 < baseStart_3491936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491951 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 2, 4]
def baseStart_3491951 : Nat := 118140960795 + 3491951 * 2 ^ 59
def prefixEnd_3491951 : Nat := 4983230072969 + 3 ^ 40 * 3491951 * 2
def baseEnd_3491951 : Nat := 1195366189965581639568877

theorem tailTrace_3491951 : CollatzResearch.WordTrace tailWord_3491951 prefixEnd_3491951 1195366189965581639568877 := by
  unfold tailWord_3491951
  simp only [CollatzResearch.WordTrace]
  refine ⟨127361916172265379595851707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84907944114843586397234471 127361916172265379595851707)
  ·
    refine ⟨191042874258398069393777561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127361916172265379595851707 191042874258398069393777561)
    ·
      refine ⟨143282155693798552045333171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191042874258398069393777561 143282155693798552045333171)
      ·
        refine ⟨214923233540697828067999757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143282155693798552045333171 214923233540697828067999757)
        ·
          refine ⟨80596212577761685525499909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214923233540697828067999757 80596212577761685525499909)
          ·
            refine ⟨15111789858330316036031233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80596212577761685525499909 15111789858330316036031233)
            ·
              refine ⟨11333842393747737027023425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15111789858330316036031233 11333842393747737027023425)
              ·
                refine ⟨8500381795310802770267569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11333842393747737027023425 8500381795310802770267569)
                ·
                  refine ⟨6375286346483102077700677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8500381795310802770267569 6375286346483102077700677)
                  ·
                    refine ⟨1195366189965581639568877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6375286346483102077700677 1195366189965581639568877)
                    ·
                      rfl

theorem cell22_3491951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_3491951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491951 prefixEnd_3491951 := by exact prefixLift 3491951
  have htrace : WordTrace (prefixWord ++ tailWord_3491951) baseStart_3491951 baseEnd_3491951 := by
    simpa [prefixWord, tailWord_3491951, baseEnd_3491951] using wordTrace_append hprefix tailTrace_3491951
  have hstable : (prefixWord ++ tailWord_3491951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491951).length < 2 ^ (prefixWord ++ tailWord_3491951).sum := by decide
  have hdescent : baseEnd_3491951 < baseStart_3491951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491953 : List Nat := [1, 2, 2, 2, 1, 1, 6, 2, 2, 3]
def baseStart_3491953 : Nat := 118140960795 + 3491953 * 2 ^ 59
def prefixEnd_3491953 : Nat := 4983230072969 + 3 ^ 40 * 3491953 * 2
def baseEnd_3491953 : Nat := 1195366874606454301018871

theorem tailTrace_3491953 : CollatzResearch.WordTrace tailWord_3491953 prefixEnd_3491953 1195366874606454301018871 := by
  unfold tailWord_3491953
  simp only [CollatzResearch.WordTrace]
  refine ⟨127361989118258133937424513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84907992745505422624949675 127361989118258133937424513)
  ·
    refine ⟨95521491838693600453068385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127361989118258133937424513 95521491838693600453068385)
    ·
      refine ⟨71641118879020200339801289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95521491838693600453068385 71641118879020200339801289)
      ·
        refine ⟨53730839159265150254850967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71641118879020200339801289 53730839159265150254850967)
        ·
          refine ⟨80596258738897725382276451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53730839159265150254850967 80596258738897725382276451)
          ·
            refine ⟨120894388108346588073414677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80596258738897725382276451 120894388108346588073414677)
            ·
              refine ⟨5666924442578746315941313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120894388108346588073414677 5666924442578746315941313)
              ·
                refine ⟨4250193331934059736955985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5666924442578746315941313 4250193331934059736955985)
                ·
                  refine ⟨3187644998950544802716989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4250193331934059736955985 3187644998950544802716989)
                  ·
                    refine ⟨1195366874606454301018871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187644998950544802716989 1195366874606454301018871)
                    ·
                      rfl

theorem cell22_3491953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_3491953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3491953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3491953 prefixEnd_3491953 := by exact prefixLift 3491953
  have htrace : WordTrace (prefixWord ++ tailWord_3491953) baseStart_3491953 baseEnd_3491953 := by
    simpa [prefixWord, tailWord_3491953, baseEnd_3491953] using wordTrace_append hprefix tailTrace_3491953
  have hstable : (prefixWord ++ tailWord_3491953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491953).length < 2 ^ (prefixWord ++ tailWord_3491953).sum := by decide
  have hdescent : baseEnd_3491953 < baseStart_3491953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492026 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_3492026 : Nat := 118140960795 + 3492026 * 2 ^ 59
def prefixEnd_3492026 : Nat := 4983230072969 + 3 ^ 40 * 3492026 * 2
def baseEnd_3492026 : Nat := 1195391863998306443943647

theorem tailTrace_3492026 : CollatzResearch.WordTrace tailWord_3492026 prefixEnd_3492026 1195391863998306443943647 := by
  unfold tailWord_3492026
  simp only [CollatzResearch.WordTrace]
  refine ⟨31841162911748416851207983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84909767764662444936554621 31841162911748416851207983)
  ·
    refine ⟨47761744367622625276811975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31841162911748416851207983 47761744367622625276811975)
    ·
      refine ⟨71642616551433937915217963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47761744367622625276811975 71642616551433937915217963)
      ·
        refine ⟨107463924827150906872826945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71642616551433937915217963 107463924827150906872826945)
        ·
          refine ⟨80597943620363180154620209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107463924827150906872826945 80597943620363180154620209)
          ·
            refine ⟨60448457715272385115965157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80597943620363180154620209 60448457715272385115965157)
            ·
              refine ⟨11334085821613572209243467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60448457715272385115965157 11334085821613572209243467)
              ·
                refine ⟨17001128732420358313865201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11334085821613572209243467 17001128732420358313865201)
                ·
                  refine ⟨12750846549315268735398901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17001128732420358313865201 12750846549315268735398901)
                  ·
                    refine ⟨1195391863998306443943647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12750846549315268735398901 1195391863998306443943647)
                    ·
                      rfl

theorem cell22_3492026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_3492026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492026 prefixEnd_3492026 := by exact prefixLift 3492026
  have htrace : WordTrace (prefixWord ++ tailWord_3492026) baseStart_3492026 baseEnd_3492026 := by
    simpa [prefixWord, tailWord_3492026, baseEnd_3492026] using wordTrace_append hprefix tailTrace_3492026
  have hstable : (prefixWord ++ tailWord_3492026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492026).length < 2 ^ (prefixWord ++ tailWord_3492026).sum := by decide
  have hdescent : baseEnd_3492026 < baseStart_3492026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492058 : List Nat := [3, 1, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_3492058 : Nat := 118140960795 + 3492058 * 2 ^ 59
def prefixEnd_3492058 : Nat := 4983230072969 + 3 ^ 40 * 3492058 * 2
def baseEnd_3492058 : Nat := 1195402818252269027143549

theorem tailTrace_3492058 : CollatzResearch.WordTrace tailWord_3492058 prefixEnd_3492058 1195402818252269027143549 := by
  unfold tailWord_3492058
  simp only [CollatzResearch.WordTrace]
  refine ⟨31841454695719434217499207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84910545855251824579997885 31841454695719434217499207)
  ·
    refine ⟨47762182043579151326248811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31841454695719434217499207 47762182043579151326248811)
    ·
      refine ⟨71643273065368726989373217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47762182043579151326248811 71643273065368726989373217)
      ·
        refine ⟨53732454799026545242029913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71643273065368726989373217 53732454799026545242029913)
        ·
          refine ⟨40299341099269908931522435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53732454799026545242029913 40299341099269908931522435)
          ·
            refine ⟨60449011648904863397283653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40299341099269908931522435 60449011648904863397283653)
            ·
              refine ⟨11334189684169661886990685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60449011648904863397283653 11334189684169661886990685)
              ·
                refine ⟨4250321131563623207621507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11334189684169661886990685 4250321131563623207621507)
                ·
                  refine ⟨6375481697345434811432261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250321131563623207621507 6375481697345434811432261)
                  ·
                    refine ⟨1195402818252269027143549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6375481697345434811432261 1195402818252269027143549)
                    ·
                      rfl

theorem cell22_3492058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_3492058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492058 prefixEnd_3492058 := by exact prefixLift 3492058
  have htrace : WordTrace (prefixWord ++ tailWord_3492058) baseStart_3492058 baseEnd_3492058 := by
    simpa [prefixWord, tailWord_3492058, baseEnd_3492058] using wordTrace_append hprefix tailTrace_3492058
  have hstable : (prefixWord ++ tailWord_3492058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492058).length < 2 ^ (prefixWord ++ tailWord_3492058).sum := by decide
  have hdescent : baseEnd_3492058 < baseStart_3492058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492066 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3492066 : Nat := 118140960795 + 3492066 * 2 ^ 59
def prefixEnd_3492066 : Nat := 4983230072969 + 3 ^ 40 * 3492066 * 2
def baseEnd_3492066 : Nat := 1195405556815759672943525

theorem tailTrace_3492066 : CollatzResearch.WordTrace tailWord_3492066 prefixEnd_3492066 1195405556815759672943525 := by
  unfold tailWord_3492066
  simp only [CollatzResearch.WordTrace]
  refine ⟨31841527641712188559072013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84910740377899169490858701 31841527641712188559072013)
  ·
    refine ⟨11940572865642070709652005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31841527641712188559072013 11940572865642070709652005)
    ·
      refine ⟨2238857412307888258059751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11940572865642070709652005 2238857412307888258059751)
      ·
        refine ⟨3358286118461832387089627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238857412307888258059751 3358286118461832387089627)
        ·
          refine ⟨5037429177692748580634441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358286118461832387089627 5037429177692748580634441)
          ·
            refine ⟨3778071883269561435475831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5037429177692748580634441 3778071883269561435475831)
            ·
              refine ⟨5667107824904342153213747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3778071883269561435475831 5667107824904342153213747)
              ·
                refine ⟨8500661737356513229820621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5667107824904342153213747 8500661737356513229820621)
                ·
                  refine ⟨3187748151508692461182733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8500661737356513229820621 3187748151508692461182733)
                  ·
                    refine ⟨1195405556815759672943525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187748151508692461182733 1195405556815759672943525)
                    ·
                      rfl

theorem cell22_3492066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3492066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492066 prefixEnd_3492066 := by exact prefixLift 3492066
  have htrace : WordTrace (prefixWord ++ tailWord_3492066) baseStart_3492066 baseEnd_3492066 := by
    simpa [prefixWord, tailWord_3492066, baseEnd_3492066] using wordTrace_append hprefix tailTrace_3492066
  have hstable : (prefixWord ++ tailWord_3492066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492066).length < 2 ^ (prefixWord ++ tailWord_3492066).sum := by decide
  have hdescent : baseEnd_3492066 < baseStart_3492066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492122 : List Nat := [3, 1, 1, 3, 4, 1, 2, 2, 2, 3]
def baseStart_3492122 : Nat := 118140960795 + 3492122 * 2 ^ 59
def prefixEnd_3492122 : Nat := 4983230072969 + 3 ^ 40 * 3492122 * 2
def baseEnd_3492122 : Nat := 1195424726760194193543353

theorem tailTrace_3492122 : CollatzResearch.WordTrace tailWord_3492122 prefixEnd_3492122 1195424726760194193543353 := by
  unfold tailWord_3492122
  simp only [CollatzResearch.WordTrace]
  refine ⟨31842038263661468950081655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84912102036430583866884413 31842038263661468950081655)
  ·
    refine ⟨47763057395492203425122483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31842038263661468950081655 47763057395492203425122483)
    ·
      refine ⟨71644586093238305137683725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47763057395492203425122483 71644586093238305137683725)
      ·
        refine ⟨26866719784964364426631397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71644586093238305137683725 26866719784964364426631397)
        ·
          refine ⟨5037509959680818329993387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26866719784964364426631397 5037509959680818329993387)
          ·
            refine ⟨7556264939521227494990081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5037509959680818329993387 7556264939521227494990081)
            ·
              refine ⟨5667198704640920621242561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7556264939521227494990081 5667198704640920621242561)
              ·
                refine ⟨4250399028480690465931921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5667198704640920621242561 4250399028480690465931921)
                ·
                  refine ⟨3187799271360517849448941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4250399028480690465931921 3187799271360517849448941)
                  ·
                    refine ⟨1195424726760194193543353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187799271360517849448941 1195424726760194193543353)
                    ·
                      rfl

theorem cell22_3492122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_3492122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492122 prefixEnd_3492122 := by exact prefixLift 3492122
  have htrace : WordTrace (prefixWord ++ tailWord_3492122) baseStart_3492122 baseEnd_3492122 := by
    simpa [prefixWord, tailWord_3492122, baseEnd_3492122] using wordTrace_append hprefix tailTrace_3492122
  have hstable : (prefixWord ++ tailWord_3492122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492122).length < 2 ^ (prefixWord ++ tailWord_3492122).sum := by decide
  have hdescent : baseEnd_3492122 < baseStart_3492122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492131 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 1, 8]
def baseStart_3492131 : Nat := 118140960795 + 3492131 * 2 ^ 59
def prefixEnd_3492131 : Nat := 4983230072969 + 3 ^ 40 * 3492131 * 2
def baseEnd_3492131 : Nat := 1195427807644121170068325

theorem tailTrace_3492131 : CollatzResearch.WordTrace tailWord_3492131 prefixEnd_3492131 1195427807644121170068325 := by
  unfold tailWord_3492131
  simp only [CollatzResearch.WordTrace]
  refine ⟨127368481311613270337404247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84912320874408846891602831 127368481311613270337404247)
  ·
    refine ⟨191052721967419905506106371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127368481311613270337404247 191052721967419905506106371)
    ·
      refine ⟨286579082951129858259159557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191052721967419905506106371 286579082951129858259159557)
      ·
        refine ⟨53733578053336848423592417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286579082951129858259159557 53733578053336848423592417)
        ·
          refine ⟨40300183540002636317694313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53733578053336848423592417 40300183540002636317694313)
          ·
            refine ⟨30225137655001977238270735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40300183540002636317694313 30225137655001977238270735)
            ·
              refine ⟨45337706482502965857406103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30225137655001977238270735 45337706482502965857406103)
              ·
                refine ⟨68006559723754448786109155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45337706482502965857406103 68006559723754448786109155)
                ·
                  refine ⟨102009839585631673179163733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68006559723754448786109155 102009839585631673179163733)
                  ·
                    refine ⟨1195427807644121170068325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102009839585631673179163733 1195427807644121170068325)
                    ·
                      rfl

theorem cell22_3492131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_3492131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492131 prefixEnd_3492131 := by exact prefixLift 3492131
  have htrace : WordTrace (prefixWord ++ tailWord_3492131) baseStart_3492131 baseEnd_3492131 := by
    simpa [prefixWord, tailWord_3492131, baseEnd_3492131] using wordTrace_append hprefix tailTrace_3492131
  have hstable : (prefixWord ++ tailWord_3492131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492131).length < 2 ^ (prefixWord ++ tailWord_3492131).sum := by decide
  have hdescent : baseEnd_3492131 < baseStart_3492131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492167 : List Nat := [1, 1, 4, 1, 2, 2, 4, 3, 1, 3]
def baseStart_3492167 : Nat := 118140960795 + 3492167 * 2 ^ 59
def prefixEnd_3492167 : Nat := 4983230072969 + 3 ^ 40 * 3492167 * 2
def baseEnd_3492167 : Nat := 1195440131179829076168215

theorem tailTrace_3492167 : CollatzResearch.WordTrace tailWord_3492167 prefixEnd_3492167 1195440131179829076168215 := by
  unfold tailWord_3492167
  simp only [CollatzResearch.WordTrace]
  refine ⟨127369794339482848485714755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84913196226321898990476503 127369794339482848485714755)
  ·
    refine ⟨191054691509224272728572133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127369794339482848485714755 191054691509224272728572133)
    ·
      refine ⟨35822754657979551136607275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191054691509224272728572133 35822754657979551136607275)
      ·
        refine ⟨53734131986969326704910913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35822754657979551136607275 53734131986969326704910913)
        ·
          refine ⟨40300598990226995028683185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53734131986969326704910913 40300598990226995028683185)
          ·
            refine ⟨30225449242670246271512389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40300598990226995028683185 30225449242670246271512389)
            ·
              refine ⟨5667271733000671175908573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30225449242670246271512389 5667271733000671175908573)
              ·
                refine ⟨2125226899875251690965715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5667271733000671175908573 2125226899875251690965715)
                ·
                  refine ⟨3187840349812877536448573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125226899875251690965715 3187840349812877536448573)
                  ·
                    refine ⟨1195440131179829076168215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187840349812877536448573 1195440131179829076168215)
                    ·
                      rfl

theorem cell22_3492167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_3492167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492167 prefixEnd_3492167 := by exact prefixLift 3492167
  have htrace : WordTrace (prefixWord ++ tailWord_3492167) baseStart_3492167 baseEnd_3492167 := by
    simpa [prefixWord, tailWord_3492167, baseEnd_3492167] using wordTrace_append hprefix tailTrace_3492167
  have hstable : (prefixWord ++ tailWord_3492167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492167).length < 2 ^ (prefixWord ++ tailWord_3492167).sum := by decide
  have hdescent : baseEnd_3492167 < baseStart_3492167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492178 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_3492178 : Nat := 118140960795 + 3492178 * 2 ^ 59
def prefixEnd_3492178 : Nat := 4983230072969 + 3 ^ 40 * 3492178 * 2
def baseEnd_3492178 : Nat := 1195443896704628714143181

theorem tailTrace_3492178 : CollatzResearch.WordTrace tailWord_3492178 prefixEnd_3492178 1195443896704628714143181 := by
  unfold tailWord_3492178
  simp only [CollatzResearch.WordTrace]
  refine ⟨31842548885610749341091297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84913463694961998242910125 31842548885610749341091297)
  ·
    refine ⟨23881911664208062005818473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31842548885610749341091297 23881911664208062005818473)
    ·
      refine ⟨17911433748156046504363855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23881911664208062005818473 17911433748156046504363855)
      ·
        refine ⟨26867150622234069756545783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17911433748156046504363855 26867150622234069756545783)
        ·
          refine ⟨40300725933351104634818675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26867150622234069756545783 40300725933351104634818675)
          ·
            refine ⟨60451088900026656952228013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40300725933351104634818675 60451088900026656952228013)
            ·
              refine ⟨22669158337509996357085505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60451088900026656952228013 22669158337509996357085505)
              ·
                refine ⟨17001868753132497267814129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22669158337509996357085505 17001868753132497267814129)
                ·
                  refine ⟨12751401564849372950860597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17001868753132497267814129 12751401564849372950860597)
                  ·
                    refine ⟨1195443896704628714143181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12751401564849372950860597 1195443896704628714143181)
                    ·
                      rfl

theorem cell22_3492178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_3492178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492178 prefixEnd_3492178 := by exact prefixLift 3492178
  have htrace : WordTrace (prefixWord ++ tailWord_3492178) baseStart_3492178 baseEnd_3492178 := by
    simpa [prefixWord, tailWord_3492178, baseEnd_3492178] using wordTrace_append hprefix tailTrace_3492178
  have hstable : (prefixWord ++ tailWord_3492178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492178).length < 2 ^ (prefixWord ++ tailWord_3492178).sum := by decide
  have hdescent : baseEnd_3492178 < baseStart_3492178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492180 : List Nat := [2, 4, 1, 1, 2, 2, 3, 2, 5]
def baseStart_3492180 : Nat := 118140960795 + 3492180 * 2 ^ 59
def prefixEnd_3492180 : Nat := 4983230072969 + 3 ^ 40 * 3492180 * 2
def baseEnd_3492180 : Nat := 398481527115167125197725

theorem tailTrace_3492180 : CollatzResearch.WordTrace tailWord_3492180 prefixEnd_3492180 398481527115167125197725 := by
  unfold tailWord_3492180
  simp only [CollatzResearch.WordTrace]
  refine ⟨63685134244217875852968997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84913512325623834470625329 63685134244217875852968997)
  ·
    refine ⟨11940962670790851722431687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63685134244217875852968997 11940962670790851722431687)
    ·
      refine ⟨17911444006186277583647531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11940962670790851722431687 17911444006186277583647531)
      ·
        refine ⟨26867166009279416375471297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17911444006186277583647531 26867166009279416375471297)
        ·
          refine ⟨20150374506959562281603473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26867166009279416375471297 20150374506959562281603473)
          ·
            refine ⟨15112780880219671711202605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20150374506959562281603473 15112780880219671711202605)
            ·
              refine ⟨5667292830082376891700977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15112780880219671711202605 5667292830082376891700977)
              ·
                refine ⟨4250469622561782668775733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5667292830082376891700977 4250469622561782668775733)
                ·
                  refine ⟨398481527115167125197725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4250469622561782668775733 398481527115167125197725)
                  ·
                    rfl

theorem cell22_3492180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_3492180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492180 prefixEnd_3492180 := by exact prefixLift 3492180
  have htrace : WordTrace (prefixWord ++ tailWord_3492180) baseStart_3492180 baseEnd_3492180 := by
    simpa [prefixWord, tailWord_3492180, baseEnd_3492180] using wordTrace_append hprefix tailTrace_3492180
  have hstable : (prefixWord ++ tailWord_3492180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492180).length < 2 ^ (prefixWord ++ tailWord_3492180).sum := by decide
  have hdescent : baseEnd_3492180 < baseStart_3492180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492190 : List Nat := [4, 4, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3492190 : Nat := 118140960795 + 3492190 * 2 ^ 59
def prefixEnd_3492190 : Nat := 4983230072969 + 3 ^ 40 * 3492190 * 2
def baseEnd_3492190 : Nat := 1195448004549864682843145

theorem tailTrace_3492190 : CollatzResearch.WordTrace tailWord_3492190 prefixEnd_3492190 1195448004549864682843145 := by
  unfold tailWord_3492190
  simp only [CollatzResearch.WordTrace]
  refine ⟨15921329152299940426725253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84913755478933015609201349 15921329152299940426725253)
  ·
    refine ⟨2985249216056238830010985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15921329152299940426725253 2985249216056238830010985)
    ·
      refine ⟨2238936912042179122508239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2985249216056238830010985 2238936912042179122508239)
      ·
        refine ⟨3358405368063268683762359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238936912042179122508239 3358405368063268683762359)
        ·
          refine ⟨5037608052094903025643539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358405368063268683762359 5037608052094903025643539)
          ·
            refine ⟨7556412078142354538465309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5037608052094903025643539 7556412078142354538465309)
            ·
              refine ⟨2833654529303382951924491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7556412078142354538465309 2833654529303382951924491)
              ·
                refine ⟨4250481793955074427886737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833654529303382951924491 4250481793955074427886737)
                ·
                  refine ⟨3187861345466305820915053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4250481793955074427886737 3187861345466305820915053)
                  ·
                    refine ⟨1195448004549864682843145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187861345466305820915053 1195448004549864682843145)
                    ·
                      rfl

theorem cell22_3492190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3492190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492190 prefixEnd_3492190 := by exact prefixLift 3492190
  have htrace : WordTrace (prefixWord ++ tailWord_3492190) baseStart_3492190 baseEnd_3492190 := by
    simpa [prefixWord, tailWord_3492190, baseEnd_3492190] using wordTrace_append hprefix tailTrace_3492190
  have hstable : (prefixWord ++ tailWord_3492190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492190).length < 2 ^ (prefixWord ++ tailWord_3492190).sum := by decide
  have hdescent : baseEnd_3492190 < baseStart_3492190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492208 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 6]
def baseStart_3492208 : Nat := 118140960795 + 3492208 * 2 ^ 59
def prefixEnd_3492208 : Nat := 4983230072969 + 3 ^ 40 * 3492208 * 2
def baseEnd_3492208 : Nat := 398484722105906211964363

theorem tailTrace_3492208 : CollatzResearch.WordTrace tailWord_3492208 prefixEnd_3492208 398484722105906211964363 := by
  unfold tailWord_3492208
  simp only [CollatzResearch.WordTrace]
  refine ⟨63685644866167156243978639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84914193154889541658638185 63685644866167156243978639)
  ·
    refine ⟨95528467299250734365967959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63685644866167156243978639 95528467299250734365967959)
    ·
      refine ⟨143292700948876101548951939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95528467299250734365967959 143292700948876101548951939)
      ·
        refine ⟨214939051423314152323427909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143292700948876101548951939 214939051423314152323427909)
        ·
          refine ⟨40301072141871403560642733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214939051423314152323427909 40301072141871403560642733)
          ·
            refine ⟨15112902053201776335241025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40301072141871403560642733 15112902053201776335241025)
            ·
              refine ⟨11334676539901332251430769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15112902053201776335241025 11334676539901332251430769)
              ·
                refine ⟨8501007404925999188573077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11334676539901332251430769 8501007404925999188573077)
                ·
                  refine ⟨398484722105906211964363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8501007404925999188573077 398484722105906211964363)
                  ·
                    rfl

theorem cell22_3492208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_3492208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492208 prefixEnd_3492208 := by exact prefixLift 3492208
  have htrace : WordTrace (prefixWord ++ tailWord_3492208) baseStart_3492208 baseEnd_3492208 := by
    simpa [prefixWord, tailWord_3492208, baseEnd_3492208] using wordTrace_append hprefix tailTrace_3492208
  have hstable : (prefixWord ++ tailWord_3492208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492208).length < 2 ^ (prefixWord ++ tailWord_3492208).sum := by decide
  have hdescent : baseEnd_3492208 < baseStart_3492208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492210 : List Nat := [3, 2, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_3492210 : Nat := 118140960795 + 3492210 * 2 ^ 59
def prefixEnd_3492210 : Nat := 4983230072969 + 3 ^ 40 * 3492210 * 2
def baseEnd_3492210 : Nat := 1195454850958591297343083

theorem tailTrace_3492210 : CollatzResearch.WordTrace tailWord_3492210 prefixEnd_3492210 1195454850958591297343083 := by
  unfold tailWord_3492210
  simp only [CollatzResearch.WordTrace]
  refine ⟨31842840669581766707382521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84914241785551377886353389 31842840669581766707382521)
  ·
    refine ⟨23882130502186325030536891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31842840669581766707382521 23882130502186325030536891)
    ·
      refine ⟨35823195753279487545805337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23882130502186325030536891 35823195753279487545805337)
      ·
        refine ⟨26867396814959615659354003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35823195753279487545805337 26867396814959615659354003)
        ·
          refine ⟨40301095222439423489031005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26867396814959615659354003 40301095222439423489031005)
          ·
            refine ⟨15112910708414783808386627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40301095222439423489031005 15112910708414783808386627)
            ·
              refine ⟨22669366062622175712579941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15112910708414783808386627 22669366062622175712579941)
              ·
                refine ⟨4250506136741657946108739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22669366062622175712579941 4250506136741657946108739)
                ·
                  refine ⟨6375759205112486919163109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250506136741657946108739 6375759205112486919163109)
                  ·
                    refine ⟨1195454850958591297343083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6375759205112486919163109 1195454850958591297343083)
                    ·
                      rfl

theorem cell22_3492210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_3492210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492210 prefixEnd_3492210 := by exact prefixLift 3492210
  have htrace : WordTrace (prefixWord ++ tailWord_3492210) baseStart_3492210 baseEnd_3492210 := by
    simpa [prefixWord, tailWord_3492210, baseEnd_3492210] using wordTrace_append hprefix tailTrace_3492210
  have hstable : (prefixWord ++ tailWord_3492210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492210).length < 2 ^ (prefixWord ++ tailWord_3492210).sum := by decide
  have hdescent : baseEnd_3492210 < baseStart_3492210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492394 : List Nat := [3, 1, 4, 1, 1, 2, 3, 3, 4]
def baseStart_3492394 : Nat := 118140960795 + 3492394 * 2 ^ 59
def prefixEnd_3492394 : Nat := 4983230072969 + 3 ^ 40 * 3492394 * 2
def baseEnd_3492394 : Nat := 398505945972958716914173

theorem tailTrace_3492394 : CollatzResearch.WordTrace tailWord_3492394 prefixEnd_3492394 398505945972958716914173 := by
  unfold tailWord_3492394
  simp only [CollatzResearch.WordTrace]
  refine ⟨31844518427415116563557059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84918715806440310836152157 31844518427415116563557059)
  ·
    refine ⟨47766777641122674845335589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31844518427415116563557059 47766777641122674845335589)
    ·
      refine ⟨8956270807710501533500423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47766777641122674845335589 8956270807710501533500423)
      ·
        refine ⟨13434406211565752300250635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8956270807710501533500423 13434406211565752300250635)
        ·
          refine ⟨20151609317348628450375953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13434406211565752300250635 20151609317348628450375953)
          ·
            refine ⟨15113706988011471337781965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20151609317348628450375953 15113706988011471337781965)
            ·
              refine ⟨5667640120504301751668237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15113706988011471337781965 5667640120504301751668237)
              ·
                refine ⟨2125365045189113156875589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5667640120504301751668237 2125365045189113156875589)
                ·
                  refine ⟨398505945972958716914173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2125365045189113156875589 398505945972958716914173)
                  ·
                    rfl

theorem cell22_3492394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_3492394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492394 prefixEnd_3492394 := by exact prefixLift 3492394
  have htrace : WordTrace (prefixWord ++ tailWord_3492394) baseStart_3492394 baseEnd_3492394 := by
    simpa [prefixWord, tailWord_3492394, baseEnd_3492394] using wordTrace_append hprefix tailTrace_3492394
  have hstable : (prefixWord ++ tailWord_3492394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492394).length < 2 ^ (prefixWord ++ tailWord_3492394).sum := by decide
  have hdescent : baseEnd_3492394 < baseStart_3492394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492426 : List Nat := [3, 1, 2, 1, 1, 6, 2, 1, 2, 3]
def baseStart_3492426 : Nat := 118140960795 + 3492426 * 2 ^ 59
def prefixEnd_3492426 : Nat := 4983230072969 + 3 ^ 40 * 3492426 * 2
def baseEnd_3492426 : Nat := 1195528792172838733942421

theorem tailTrace_3492426 : CollatzResearch.WordTrace tailWord_3492426 prefixEnd_3492426 1195528792172838733942421 := by
  unfold tailWord_3492426
  simp only [CollatzResearch.WordTrace]
  refine ⟨31844810211386133929848283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84919493897029690479595421 31844810211386133929848283)
  ·
    refine ⟨47767215317079200894772425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31844810211386133929848283 47767215317079200894772425)
    ·
      refine ⟨35825411487809400671079319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47767215317079200894772425 35825411487809400671079319)
      ·
        refine ⟨53738117231714101006618979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35825411487809400671079319 53738117231714101006618979)
        ·
          refine ⟨80607175847571151509928469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53738117231714101006618979 80607175847571151509928469)
          ·
            refine ⟨3778461367854897727027897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80607175847571151509928469 3778461367854897727027897)
            ·
              refine ⟨2833846025891173295270923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3778461367854897727027897 2833846025891173295270923)
              ·
                refine ⟨4250769038836759942906385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833846025891173295270923 4250769038836759942906385)
                ·
                  refine ⟨3188076779127569957179789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4250769038836759942906385 3188076779127569957179789)
                  ·
                    refine ⟨1195528792172838733942421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3188076779127569957179789 1195528792172838733942421)
                    ·
                      rfl

theorem cell22_3492426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_3492426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492426 prefixEnd_3492426 := by exact prefixLift 3492426
  have htrace : WordTrace (prefixWord ++ tailWord_3492426) baseStart_3492426 baseEnd_3492426 := by
    simpa [prefixWord, tailWord_3492426, baseEnd_3492426] using wordTrace_append hprefix tailTrace_3492426
  have hstable : (prefixWord ++ tailWord_3492426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492426).length < 2 ^ (prefixWord ++ tailWord_3492426).sum := by decide
  have hdescent : baseEnd_3492426 < baseStart_3492426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492437 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 3, 3]
def baseStart_3492437 : Nat := 118140960795 + 3492437 * 2 ^ 59
def prefixEnd_3492437 : Nat := 4983230072969 + 3 ^ 40 * 3492437 * 2
def baseEnd_3492437 : Nat := 1195532557697638371917387

theorem tailTrace_3492437 : CollatzResearch.WordTrace tailWord_3492437 prefixEnd_3492437 1195532557697638371917387 := by
  unfold tailWord_3492437
  simp only [CollatzResearch.WordTrace]
  refine ⟨127379642048504684598043565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84919761365669789732029043 127379642048504684598043565)
  ·
    refine ⟨47767365768189256724266337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127379642048504684598043565 47767365768189256724266337)
    ·
      refine ⟨35825524326141942543199753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47767365768189256724266337 35825524326141942543199753)
      ·
        refine ⟨26869143244606456907399815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35825524326141942543199753 26869143244606456907399815)
        ·
          refine ⟨40303714866909685361099723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26869143244606456907399815 40303714866909685361099723)
          ·
            refine ⟨60455572300364528041649585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40303714866909685361099723 60455572300364528041649585)
            ·
              refine ⟨45341679225273396031237189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60455572300364528041649585 45341679225273396031237189)
              ·
                refine ⟨8501564854738761755856973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45341679225273396031237189 8501564854738761755856973)
                ·
                  refine ⟨3188086820527035658446365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8501564854738761755856973 3188086820527035658446365)
                  ·
                    refine ⟨1195532557697638371917387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3188086820527035658446365 1195532557697638371917387)
                    ·
                      rfl

theorem cell22_3492437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_3492437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492437 prefixEnd_3492437 := by exact prefixLift 3492437
  have htrace : WordTrace (prefixWord ++ tailWord_3492437) baseStart_3492437 baseEnd_3492437 := by
    simpa [prefixWord, tailWord_3492437, baseEnd_3492437] using wordTrace_append hprefix tailTrace_3492437
  have hstable : (prefixWord ++ tailWord_3492437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492437).length < 2 ^ (prefixWord ++ tailWord_3492437).sum := by decide
  have hdescent : baseEnd_3492437 < baseStart_3492437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492471 : List Nat := [1, 1, 3, 1, 1, 3, 6, 2, 1, 3]
def baseStart_3492471 : Nat := 118140960795 + 3492471 * 2 ^ 59
def prefixEnd_3492471 : Nat := 4983230072969 + 3 ^ 40 * 3492471 * 2
def baseEnd_3492471 : Nat := 1195544196592473616567283

theorem tailTrace_3492471 : CollatzResearch.WordTrace tailWord_3492471 prefixEnd_3492471 1195544196592473616567283 := by
  unfold tailWord_3492471
  simp only [CollatzResearch.WordTrace]
  refine ⟨127380882130381508404781267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84920588086921005603187511 127380882130381508404781267)
  ·
    refine ⟨191071323195572262607171901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127380882130381508404781267 191071323195572262607171901)
    ·
      refine ⟨71651746198339598477689463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191071323195572262607171901 71651746198339598477689463)
      ·
        refine ⟨107477619297509397716534195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71651746198339598477689463 107477619297509397716534195)
        ·
          refine ⟨161216428946264096574801293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107477619297509397716534195 161216428946264096574801293)
          ·
            refine ⟨60456160854849036215550485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161216428946264096574801293 60456160854849036215550485)
            ·
              refine ⟨2833882540071048572603929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60456160854849036215550485 2833882540071048572603929)
              ·
                refine ⟨2125411905053286429452947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2833882540071048572603929 2125411905053286429452947)
                ·
                  refine ⟨3188117857579929644179421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125411905053286429452947 3188117857579929644179421)
                  ·
                    refine ⟨1195544196592473616567283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3188117857579929644179421 1195544196592473616567283)
                    ·
                      rfl

theorem cell22_3492471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_3492471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492471 prefixEnd_3492471 := by exact prefixLift 3492471
  have htrace : WordTrace (prefixWord ++ tailWord_3492471) baseStart_3492471 baseEnd_3492471 := by
    simpa [prefixWord, tailWord_3492471, baseEnd_3492471] using wordTrace_append hprefix tailTrace_3492471
  have hstable : (prefixWord ++ tailWord_3492471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492471).length < 2 ^ (prefixWord ++ tailWord_3492471).sum := by decide
  have hdescent : baseEnd_3492471 < baseStart_3492471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492495 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 6]
def baseStart_3492495 : Nat := 118140960795 + 3492495 * 2 ^ 59
def prefixEnd_3492495 : Nat := 4983230072969 + 3 ^ 40 * 3492495 * 2
def baseEnd_3492495 : Nat := 398517470760981851322403

theorem tailTrace_3492495 : CollatzResearch.WordTrace tailWord_3492495 prefixEnd_3492495 398517470760981851322403 := by
  unfold tailWord_3492495
  simp only [CollatzResearch.WordTrace]
  refine ⟨127381757482294560503654939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84921171654863040335769959 127381757482294560503654939)
  ·
    refine ⟨191072636223441840755482409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127381757482294560503654939 191072636223441840755482409)
    ·
      refine ⟨143304477167581380566611807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191072636223441840755482409 143304477167581380566611807)
      ·
        refine ⟨214956715751372070849917711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143304477167581380566611807 214956715751372070849917711)
        ·
          refine ⟨322435073627058106274876567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214956715751372070849917711 322435073627058106274876567)
          ·
            refine ⟨483652610440587159412314851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322435073627058106274876567 483652610440587159412314851)
            ·
              refine ⟨725478915660880739118472277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483652610440587159412314851 725478915660880739118472277)
              ·
                refine ⟨8501706042900946161544597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 725478915660880739118472277 8501706042900946161544597)
                ·
                  refine ⟨398517470760981851322403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8501706042900946161544597 398517470760981851322403)
                  ·
                    rfl

theorem cell22_3492495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 6].length) (baseStart_3492495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492495 prefixEnd_3492495 := by exact prefixLift 3492495
  have htrace : WordTrace (prefixWord ++ tailWord_3492495) baseStart_3492495 baseEnd_3492495 := by
    simpa [prefixWord, tailWord_3492495, baseEnd_3492495] using wordTrace_append hprefix tailTrace_3492495
  have hstable : (prefixWord ++ tailWord_3492495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492495).length < 2 ^ (prefixWord ++ tailWord_3492495).sum := by decide
  have hdescent : baseEnd_3492495 < baseStart_3492495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492542 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3492542 : Nat := 118140960795 + 3492542 * 2 ^ 59
def prefixEnd_3492542 : Nat := 4983230072969 + 3 ^ 40 * 3492542 * 2
def baseEnd_3492542 : Nat := 1195568501343453098042065

theorem tailTrace_3492542 : CollatzResearch.WordTrace tailWord_3492542 prefixEnd_3492542 1195568501343453098042065 := by
  unfold tailWord_3492542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15922933964140535941326985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84922314475416191687077253 15922933964140535941326985)
  ·
    refine ⟨11942200473105401955995239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15922933964140535941326985 11942200473105401955995239)
    ·
      refine ⟨17913300709658102933992859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11942200473105401955995239 17913300709658102933992859)
      ·
        refine ⟨26869951064487154400989289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17913300709658102933992859 26869951064487154400989289)
        ·
          refine ⟨20152463298365365800741967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26869951064487154400989289 20152463298365365800741967)
          ·
            refine ⟨30228694947548048701112951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20152463298365365800741967 30228694947548048701112951)
            ·
              refine ⟨45343042421322073051669427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30228694947548048701112951 45343042421322073051669427)
              ·
                refine ⟨68014563631983109577504141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45343042421322073051669427 68014563631983109577504141)
                ·
                  refine ⟨25505461361993666091564053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68014563631983109577504141 25505461361993666091564053)
                  ·
                    refine ⟨1195568501343453098042065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25505461361993666091564053 1195568501343453098042065)
                    ·
                      rfl

theorem cell22_3492542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3492542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492542 prefixEnd_3492542 := by exact prefixLift 3492542
  have htrace : WordTrace (prefixWord ++ tailWord_3492542) baseStart_3492542 baseEnd_3492542 := by
    simpa [prefixWord, tailWord_3492542, baseEnd_3492542] using wordTrace_append hprefix tailTrace_3492542
  have hstable : (prefixWord ++ tailWord_3492542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492542).length < 2 ^ (prefixWord ++ tailWord_3492542).sum := by decide
  have hdescent : baseEnd_3492542 < baseStart_3492542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492544 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 1, 5]
def baseStart_3492544 : Nat := 118140960795 + 3492544 * 2 ^ 59
def prefixEnd_3492544 : Nat := 4983230072969 + 3 ^ 40 * 3492544 * 2
def baseEnd_3492544 : Nat := 1195569185984325759492059

theorem tailTrace_3492544 : CollatzResearch.WordTrace tailWord_3492544 prefixEnd_3492544 1195569185984325759492059 := by
  unfold tailWord_3492544
  simp only [CollatzResearch.WordTrace]
  refine ⟨63691772329558520936094343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84922363106078027914792457 63691772329558520936094343)
  ·
    refine ⟨95537658494337781404141515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63691772329558520936094343 95537658494337781404141515)
    ·
      refine ⟨143306487741506672106212273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95537658494337781404141515 143306487741506672106212273)
      ·
        refine ⟨107479865806130004079659205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143306487741506672106212273 107479865806130004079659205)
        ·
          refine ⟨20152474838649375764936101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107479865806130004079659205 20152474838649375764936101)
          ·
            refine ⟨3778589032246757955925519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20152474838649375764936101 3778589032246757955925519)
            ·
              refine ⟨5667883548370136933888279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3778589032246757955925519 5667883548370136933888279)
              ·
                refine ⟨8501825322555205400832419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5667883548370136933888279 8501825322555205400832419)
                ·
                  refine ⟨12752737983832808101248629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8501825322555205400832419 12752737983832808101248629)
                  ·
                    refine ⟨1195569185984325759492059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12752737983832808101248629 1195569185984325759492059)
                    ·
                      rfl

theorem cell22_3492544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 5].length) (baseStart_3492544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492544 prefixEnd_3492544 := by exact prefixLift 3492544
  have htrace : WordTrace (prefixWord ++ tailWord_3492544) baseStart_3492544 baseEnd_3492544 := by
    simpa [prefixWord, tailWord_3492544, baseEnd_3492544] using wordTrace_append hprefix tailTrace_3492544
  have hstable : (prefixWord ++ tailWord_3492544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492544).length < 2 ^ (prefixWord ++ tailWord_3492544).sum := by decide
  have hdescent : baseEnd_3492544 < baseStart_3492544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492640 : List Nat := [2, 1, 1, 5, 1, 4, 2, 2, 1, 3]
def baseStart_3492640 : Nat := 118140960795 + 3492640 * 2 ^ 59
def prefixEnd_3492640 : Nat := 4983230072969 + 3 ^ 40 * 3492640 * 2
def baseEnd_3492640 : Nat := 1195602048746213509091765

theorem tailTrace_3492640 : CollatzResearch.WordTrace tailWord_3492640 prefixEnd_3492640 1195602048746213509091765 := by
  unfold tailWord_3492640
  simp only [CollatzResearch.WordTrace]
  refine ⟨63693523033384625133841687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84924697377846166845122249 63693523033384625133841687)
  ·
    refine ⟨95540284550076937700762531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63693523033384625133841687 95540284550076937700762531)
    ·
      refine ⟨143310426825115406551143797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95540284550076937700762531 143310426825115406551143797)
      ·
        refine ⟨13435352514854569364169731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143310426825115406551143797 13435352514854569364169731)
        ·
          refine ⟨20153028772281854046254597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13435352514854569364169731 20153028772281854046254597)
          ·
            refine ⟨3778692894802847633672737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20153028772281854046254597 3778692894802847633672737)
            ·
              refine ⟨2834019671102135725254553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3778692894802847633672737 2834019671102135725254553)
              ·
                refine ⟨2125514753326601793940915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2834019671102135725254553 2125514753326601793940915)
                ·
                  refine ⟨3188272129989902690911373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125514753326601793940915 3188272129989902690911373)
                  ·
                    refine ⟨1195602048746213509091765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3188272129989902690911373 1195602048746213509091765)
                    ·
                      rfl

theorem cell22_3492640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 1, 3].length) (baseStart_3492640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492640 prefixEnd_3492640 := by exact prefixLift 3492640
  have htrace : WordTrace (prefixWord ++ tailWord_3492640) baseStart_3492640 baseEnd_3492640 := by
    simpa [prefixWord, tailWord_3492640, baseEnd_3492640] using wordTrace_append hprefix tailTrace_3492640
  have hstable : (prefixWord ++ tailWord_3492640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492640).length < 2 ^ (prefixWord ++ tailWord_3492640).sum := by decide
  have hdescent : baseEnd_3492640 < baseStart_3492640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492679 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 4, 3]
def baseStart_3492679 : Nat := 118140960795 + 3492679 * 2 ^ 59
def prefixEnd_3492679 : Nat := 4983230072969 + 3 ^ 40 * 3492679 * 2
def baseEnd_3492679 : Nat := 1195615399243230407366645

theorem tailTrace_3492679 : CollatzResearch.WordTrace tailWord_3492679 prefixEnd_3492679 1195615399243230407366645 := by
  unfold tailWord_3492679
  simp only [CollatzResearch.WordTrace]
  refine ⟨127388468513627959928353091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84925645675751973285568727 127388468513627959928353091)
  ·
    refine ⟨191082702770441939892529637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127388468513627959928353091 191082702770441939892529637)
    ·
      refine ⟨35828006769457863729849307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191082702770441939892529637 35828006769457863729849307)
      ·
        refine ⟨53742010154186795594773961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35828006769457863729849307 53742010154186795594773961)
        ·
          refine ⟨40306507615640096696080471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53742010154186795594773961 40306507615640096696080471)
          ·
            refine ⟨60459761423460145044120707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40306507615640096696080471 60459761423460145044120707)
            ·
              refine ⟨90689642135190217566181061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60459761423460145044120707 90689642135190217566181061)
              ·
                refine ⟨17004307900348165793658949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90689642135190217566181061 17004307900348165793658949)
                ·
                  refine ⟨3188307731315281086311053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17004307900348165793658949 3188307731315281086311053)
                  ·
                    refine ⟨1195615399243230407366645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3188307731315281086311053 1195615399243230407366645)
                    ·
                      rfl

theorem cell22_3492679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_3492679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492679 prefixEnd_3492679 := by exact prefixLift 3492679
  have htrace : WordTrace (prefixWord ++ tailWord_3492679) baseStart_3492679 baseEnd_3492679 := by
    simpa [prefixWord, tailWord_3492679, baseEnd_3492679] using wordTrace_append hprefix tailTrace_3492679
  have hstable : (prefixWord ++ tailWord_3492679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492679).length < 2 ^ (prefixWord ++ tailWord_3492679).sum := by decide
  have hdescent : baseEnd_3492679 < baseStart_3492679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492681 : List Nat := [1, 2, 1, 1, 2, 6, 2, 3, 4]
def baseStart_3492681 : Nat := 118140960795 + 3492681 * 2 ^ 59
def prefixEnd_3492681 : Nat := 4983230072969 + 3 ^ 40 * 3492681 * 2
def baseEnd_3492681 : Nat := 398538694628034356272213

theorem tailTrace_3492681 : CollatzResearch.WordTrace tailWord_3492681 prefixEnd_3492681 398538694628034356272213 := by
  unfold tailWord_3492681
  simp only [CollatzResearch.WordTrace]
  refine ⟨127388541459620714269925897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84925694306413809513283931 127388541459620714269925897)
  ·
    refine ⟨95541406094715535702444423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127388541459620714269925897 95541406094715535702444423)
    ·
      refine ⟨143312109142073303553666635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95541406094715535702444423 143312109142073303553666635)
      ·
        refine ⟨214968163713109955330499953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143312109142073303553666635 214968163713109955330499953)
        ·
          refine ⟨161226122784832466497874965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214968163713109955330499953 161226122784832466497874965)
          ·
            refine ⟨7557474505539021867087889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161226122784832466497874965 7557474505539021867087889)
            ·
              refine ⟨5668105879154266400315917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7557474505539021867087889 5668105879154266400315917)
              ·
                refine ⟨2125539704682849900118469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5668105879154266400315917 2125539704682849900118469)
                ·
                  refine ⟨398538694628034356272213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2125539704682849900118469 398538694628034356272213)
                  ·
                    rfl

theorem cell22_3492681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 4].length) (baseStart_3492681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492681 prefixEnd_3492681 := by exact prefixLift 3492681
  have htrace : WordTrace (prefixWord ++ tailWord_3492681) baseStart_3492681 baseEnd_3492681 := by
    simpa [prefixWord, tailWord_3492681, baseEnd_3492681] using wordTrace_append hprefix tailTrace_3492681
  have hstable : (prefixWord ++ tailWord_3492681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492681).length < 2 ^ (prefixWord ++ tailWord_3492681).sum := by decide
  have hdescent : baseEnd_3492681 < baseStart_3492681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492726 : List Nat := [5, 1, 1, 3, 1, 2, 1, 8]
def baseStart_3492726 : Nat := 118140960795 + 3492726 * 2 ^ 59
def prefixEnd_3492726 : Nat := 4983230072969 + 3 ^ 40 * 3492726 * 2
def baseEnd_3492726 : Nat := 132847943144859772382389

theorem tailTrace_3492726 : CollatzResearch.WordTrace tailWord_3492726 prefixEnd_3492726 132847943144859772382389 := by
  unfold tailWord_3492726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7961886421528605434707127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84926788496305124636876021 7961886421528605434707127)
  ·
    refine ⟨11942829632292908152060691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7961886421528605434707127 11942829632292908152060691)
    ·
      refine ⟨17914244448439362228091037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11942829632292908152060691 17914244448439362228091037)
      ·
        refine ⟨6717841668164760835534139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17914244448439362228091037 6717841668164760835534139)
        ·
          refine ⟨10076762502247141253301209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6717841668164760835534139 10076762502247141253301209)
          ·
            refine ⟨7557571876685355939975907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10076762502247141253301209 7557571876685355939975907)
            ·
              refine ⟨11336357815028033909963861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7557571876685355939975907 11336357815028033909963861)
              ·
                refine ⟨132847943144859772382389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11336357815028033909963861 132847943144859772382389)
                ·
                  rfl

theorem cell22_3492726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_3492726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492726 prefixEnd_3492726 := by exact prefixLift 3492726
  have htrace : WordTrace (prefixWord ++ tailWord_3492726) baseStart_3492726 baseEnd_3492726 := by
    simpa [prefixWord, tailWord_3492726, baseEnd_3492726] using wordTrace_append hprefix tailTrace_3492726
  have hstable : (prefixWord ++ tailWord_3492726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492726).length < 2 ^ (prefixWord ++ tailWord_3492726).sum := by decide
  have hdescent : baseEnd_3492726 < baseStart_3492726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492771 : List Nat := [1, 1, 1, 4, 1, 2, 6, 1, 5]
def baseStart_3492771 : Nat := 118140960795 + 3492771 * 2 ^ 59
def prefixEnd_3492771 : Nat := 4983230072969 + 3 ^ 40 * 3492771 * 2
def baseEnd_3492771 : Nat := 398548964241124278022121

theorem tailTrace_3492771 : CollatzResearch.WordTrace tailWord_3492771 prefixEnd_3492771 398548964241124278022121 := by
  unfold tailWord_3492771
  simp only [CollatzResearch.WordTrace]
  refine ⟨127391824029294659640702167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84927882686196439760468111 127391824029294659640702167)
  ·
    refine ⟨191087736043941989461053251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127391824029294659640702167 191087736043941989461053251)
    ·
      refine ⟨286631604065912984191579877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191087736043941989461053251 286631604065912984191579877)
      ·
        refine ⟨53743425762358684535921227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286631604065912984191579877 53743425762358684535921227)
        ·
          refine ⟨80615138643538026803881841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53743425762358684535921227 80615138643538026803881841)
          ·
            refine ⟨60461353982653520102911381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80615138643538026803881841 60461353982653520102911381)
            ·
              refine ⟨2834125967936883754823971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60461353982653520102911381 2834125967936883754823971)
              ·
                refine ⟨4251188951905325632235957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2834125967936883754823971 4251188951905325632235957)
                ·
                  refine ⟨398548964241124278022121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4251188951905325632235957 398548964241124278022121)
                  ·
                    rfl

theorem cell22_3492771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 5].length) (baseStart_3492771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492771 prefixEnd_3492771 := by exact prefixLift 3492771
  have htrace : WordTrace (prefixWord ++ tailWord_3492771) baseStart_3492771 baseEnd_3492771 := by
    simpa [prefixWord, tailWord_3492771, baseEnd_3492771] using wordTrace_append hprefix tailTrace_3492771
  have hstable : (prefixWord ++ tailWord_3492771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492771).length < 2 ^ (prefixWord ++ tailWord_3492771).sum := by decide
  have hdescent : baseEnd_3492771 < baseStart_3492771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492865 : List Nat := [1, 2, 4, 1, 2, 4, 1, 2, 2, 3]
def baseStart_3492865 : Nat := 118140960795 + 3492865 * 2 ^ 59
def prefixEnd_3492865 : Nat := 4983230072969 + 3 ^ 40 * 3492865 * 2
def baseEnd_3492865 : Nat := 1195679070844387922216075

theorem tailTrace_3492865 : CollatzResearch.WordTrace tailWord_3492865 prefixEnd_3492865 1195679070844387922216075 := by
  unfold tailWord_3492865
  simp only [CollatzResearch.WordTrace]
  refine ⟨127395252490954113694624049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84930168327302742463082699 127395252490954113694624049)
  ·
    refine ⟨95546439368215585270968037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127395252490954113694624049 95546439368215585270968037)
    ·
      refine ⟨17914957381540422238306507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95546439368215585270968037 17914957381540422238306507)
      ·
        refine ⟨26872436072310633357459761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17914957381540422238306507 26872436072310633357459761)
        ·
          refine ⟨20154327054232975018094821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26872436072310633357459761 20154327054232975018094821)
          ·
            refine ⟨3778936322668682815892779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20154327054232975018094821 3778936322668682815892779)
            ·
              refine ⟨5668404484003024223839169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3778936322668682815892779 5668404484003024223839169)
              ·
                refine ⟨4251303363002268167879377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5668404484003024223839169 4251303363002268167879377)
                ·
                  refine ⟨3188477522251701125909533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4251303363002268167879377 3188477522251701125909533)
                  ·
                    refine ⟨1195679070844387922216075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3188477522251701125909533 1195679070844387922216075)
                    ·
                      rfl

theorem cell22_3492865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_3492865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492865 prefixEnd_3492865 := by exact prefixLift 3492865
  have htrace : WordTrace (prefixWord ++ tailWord_3492865) baseStart_3492865 baseEnd_3492865 := by
    simpa [prefixWord, tailWord_3492865, baseEnd_3492865] using wordTrace_append hprefix tailTrace_3492865
  have hstable : (prefixWord ++ tailWord_3492865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492865).length < 2 ^ (prefixWord ++ tailWord_3492865).sum := by decide
  have hdescent : baseEnd_3492865 < baseStart_3492865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492936 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 3, 4]
def baseStart_3492936 : Nat := 118140960795 + 3492936 * 2 ^ 59
def prefixEnd_3492936 : Nat := 4983230072969 + 3 ^ 40 * 3492936 * 2
def baseEnd_3492936 : Nat := 1195703375595367403690857

theorem tailTrace_3492936 : CollatzResearch.WordTrace tailWord_3492936 prefixEnd_3492936 1195703375595367403690857 := by
  unfold tailWord_3492936
  simp only [CollatzResearch.WordTrace]
  refine ⟨63698921036848446410229331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84931894715797928546972441 63698921036848446410229331)
  ·
    refine ⟨95548381555272669615343997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63698921036848446410229331 95548381555272669615343997)
    ·
      refine ⟨35830643083227251105753999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95548381555272669615343997 35830643083227251105753999)
      ·
        refine ⟨53745964624840876658630999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35830643083227251105753999 53745964624840876658630999)
        ·
          refine ⟨80618946937261314987946499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53745964624840876658630999 80618946937261314987946499)
          ·
            refine ⟨120928420405891972481919749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80618946937261314987946499 120928420405891972481919749)
            ·
              refine ⟨22674078826104744840359953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120928420405891972481919749 22674078826104744840359953)
              ·
                refine ⟨17005559119578558630269965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22674078826104744840359953 17005559119578558630269965)
                ·
                  refine ⟨6377084669841959486351237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17005559119578558630269965 6377084669841959486351237)
                  ·
                    refine ⟨1195703375595367403690857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6377084669841959486351237 1195703375595367403690857)
                    ·
                      rfl

theorem cell22_3492936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_3492936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492936 prefixEnd_3492936 := by exact prefixLift 3492936
  have htrace : WordTrace (prefixWord ++ tailWord_3492936) baseStart_3492936 baseEnd_3492936 := by
    simpa [prefixWord, tailWord_3492936, baseEnd_3492936] using wordTrace_append hprefix tailTrace_3492936
  have hstable : (prefixWord ++ tailWord_3492936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492936).length < 2 ^ (prefixWord ++ tailWord_3492936).sum := by decide
  have hdescent : baseEnd_3492936 < baseStart_3492936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492985 : List Nat := [1, 2, 1, 3, 5, 1, 1, 4, 4]
def baseStart_3492985 : Nat := 118140960795 + 3492985 * 2 ^ 59
def prefixEnd_3492985 : Nat := 4983230072969 + 3 ^ 40 * 3492985 * 2
def baseEnd_3492985 : Nat := 398573383098915869738569

theorem tailTrace_3492985 : CollatzResearch.WordTrace tailWord_3492985 prefixEnd_3492985 398573383098915869738569 := by
  unfold tailWord_3492985
  simp only [CollatzResearch.WordTrace]
  refine ⟨127399629250519374188992409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84933086167012916125994939 127399629250519374188992409)
  ·
    refine ⟨95549721937889530641744307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127399629250519374188992409 95549721937889530641744307)
    ·
      refine ⟨143324582906834295962616461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95549721937889530641744307 143324582906834295962616461)
      ·
        refine ⟨53746718590062860985981173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143324582906834295962616461 53746718590062860985981173)
        ·
          refine ⟨5038754867818393217435735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53746718590062860985981173 5038754867818393217435735)
          ·
            refine ⟨7558132301727589826153603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5038754867818393217435735 7558132301727589826153603)
            ·
              refine ⟨11337198452591384739230405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7558132301727589826153603 11337198452591384739230405)
              ·
                refine ⟨2125724709860884638605701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11337198452591384739230405 2125724709860884638605701)
                ·
                  refine ⟨398573383098915869738569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2125724709860884638605701 398573383098915869738569)
                  ·
                    rfl

theorem cell22_3492985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 4].length) (baseStart_3492985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3492985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3492985 prefixEnd_3492985 := by exact prefixLift 3492985
  have htrace : WordTrace (prefixWord ++ tailWord_3492985) baseStart_3492985 baseEnd_3492985 := by
    simpa [prefixWord, tailWord_3492985, baseEnd_3492985] using wordTrace_append hprefix tailTrace_3492985
  have hstable : (prefixWord ++ tailWord_3492985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492985).length < 2 ^ (prefixWord ++ tailWord_3492985).sum := by decide
  have hdescent : baseEnd_3492985 < baseStart_3492985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493000 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 1, 5]
def baseStart_3493000 : Nat := 118140960795 + 3493000 * 2 ^ 59
def prefixEnd_3493000 : Nat := 4983230072969 + 3 ^ 40 * 3493000 * 2
def baseEnd_3493000 : Nat := 1195725284103292570090661

theorem tailTrace_3493000 : CollatzResearch.WordTrace tailWord_3493000 prefixEnd_3493000 1195725284103292570090661 := by
  unfold tailWord_3493000
  simp only [CollatzResearch.WordTrace]
  refine ⟨63700088172732515875394227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84933450896976687833858969 63700088172732515875394227)
  ·
    refine ⟨95550132259098773813091341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63700088172732515875394227 95550132259098773813091341)
    ·
      refine ⟨35831299597162040179909253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95550132259098773813091341 35831299597162040179909253)
      ·
        refine ⟨6718368674467882533732985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35831299597162040179909253 6718368674467882533732985)
        ·
          refine ⟨5038776505850911900299739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6718368674467882533732985 5038776505850911900299739)
          ·
            refine ⟨7558164758776367850449609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5038776505850911900299739 7558164758776367850449609)
            ·
              refine ⟨5668623569082275887837207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7558164758776367850449609 5668623569082275887837207)
              ·
                refine ⟨8502935353623413831755811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5668623569082275887837207 8502935353623413831755811)
                ·
                  refine ⟨12754403030435120747633717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8502935353623413831755811 12754403030435120747633717)
                  ·
                    refine ⟨1195725284103292570090661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12754403030435120747633717 1195725284103292570090661)
                    ·
                      rfl

theorem cell22_3493000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_3493000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493000 prefixEnd_3493000 := by exact prefixLift 3493000
  have htrace : WordTrace (prefixWord ++ tailWord_3493000) baseStart_3493000 baseEnd_3493000 := by
    simpa [prefixWord, tailWord_3493000, baseEnd_3493000] using wordTrace_append hprefix tailTrace_3493000
  have hstable : (prefixWord ++ tailWord_3493000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493000).length < 2 ^ (prefixWord ++ tailWord_3493000).sum := by decide
  have hdescent : baseEnd_3493000 < baseStart_3493000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493015 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 2, 4]
def baseStart_3493015 : Nat := 118140960795 + 3493015 * 2 ^ 59
def prefixEnd_3493015 : Nat := 4983230072969 + 3 ^ 40 * 3493015 * 2
def baseEnd_3493015 : Nat := 1195730418909837530965615

theorem tailTrace_3493015 : CollatzResearch.WordTrace tailWord_3493015 prefixEnd_3493015 1195730418909837530965615 := by
  unfold tailWord_3493015
  simp only [CollatzResearch.WordTrace]
  refine ⟨127400723440410689312584499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84933815626940459541722999 127400723440410689312584499)
  ·
    refine ⟨191101085160616033968876749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127400723440410689312584499 191101085160616033968876749)
    ·
      refine ⟨71662906935231012738328781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191101085160616033968876749 71662906935231012738328781)
      ·
        refine ⟨26873590100711629776873293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71662906935231012738328781 26873590100711629776873293)
        ·
          refine ⟨10077596287766861166327485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26873590100711629776873293 10077596287766861166327485)
          ·
            refine ⟨3779098607912572937372807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10077596287766861166327485 3779098607912572937372807)
            ·
              refine ⟨5668647911868859406059211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779098607912572937372807 5668647911868859406059211)
              ·
                refine ⟨8502971867803289109088817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5668647911868859406059211 8502971867803289109088817)
                ·
                  refine ⟨6377228900852466831816613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8502971867803289109088817 6377228900852466831816613)
                  ·
                    refine ⟨1195730418909837530965615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6377228900852466831816613 1195730418909837530965615)
                    ·
                      rfl

theorem cell22_3493015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_3493015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493015 prefixEnd_3493015 := by exact prefixLift 3493015
  have htrace : WordTrace (prefixWord ++ tailWord_3493015) baseStart_3493015 baseEnd_3493015 := by
    simpa [prefixWord, tailWord_3493015, baseEnd_3493015] using wordTrace_append hprefix tailTrace_3493015
  have hstable : (prefixWord ++ tailWord_3493015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493015).length < 2 ^ (prefixWord ++ tailWord_3493015).sum := by decide
  have hdescent : baseEnd_3493015 < baseStart_3493015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493034 : List Nat := [3, 1, 5, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3493034 : Nat := 118140960795 + 3493034 * 2 ^ 59
def prefixEnd_3493034 : Nat := 4983230072969 + 3 ^ 40 * 3493034 * 2
def baseEnd_3493034 : Nat := 1195736922998127814740557

theorem tailTrace_3493034 : CollatzResearch.WordTrace tailWord_3493034 prefixEnd_3493034 1195736922998127814740557 := by
  unfold tailWord_3493034
  simp only [CollatzResearch.WordTrace]
  refine ⟨31850354106835463889381539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84934277618227903705017437 31850354106835463889381539)
  ·
    refine ⟨47775531160253195834072309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31850354106835463889381539 47775531160253195834072309)
    ·
      refine ⟨4478956046273737109444279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47775531160253195834072309 4478956046273737109444279)
      ·
        refine ⟨6718434069410605664166419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4478956046273737109444279 6718434069410605664166419)
        ·
          refine ⟨10077651104115908496249629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6718434069410605664166419 10077651104115908496249629)
          ·
            refine ⟨3779119164043465686093611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10077651104115908496249629 3779119164043465686093611)
            ·
              refine ⟨5668678746065198529140417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779119164043465686093611 5668678746065198529140417)
              ·
                refine ⟨4251509059548898896855313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5668678746065198529140417 4251509059548898896855313)
                ·
                  refine ⟨3188631794661674172641485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4251509059548898896855313 3188631794661674172641485)
                  ·
                    refine ⟨1195736922998127814740557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3188631794661674172641485 1195736922998127814740557)
                    ·
                      rfl

theorem cell22_3493034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3493034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493034 prefixEnd_3493034 := by exact prefixLift 3493034
  have htrace : WordTrace (prefixWord ++ tailWord_3493034) baseStart_3493034 baseEnd_3493034 := by
    simpa [prefixWord, tailWord_3493034, baseEnd_3493034] using wordTrace_append hprefix tailTrace_3493034
  have hstable : (prefixWord ++ tailWord_3493034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493034).length < 2 ^ (prefixWord ++ tailWord_3493034).sum := by decide
  have hdescent : baseEnd_3493034 < baseStart_3493034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493122 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3493122 : Nat := 118140960795 + 3493122 * 2 ^ 59
def prefixEnd_3493122 : Nat := 4983230072969 + 3 ^ 40 * 3493122 * 2
def baseEnd_3493122 : Nat := 1195767047196524918540287

theorem tailTrace_3493122 : CollatzResearch.WordTrace tailWord_3493122 prefixEnd_3493122 1195767047196524918540287 := by
  unfold tailWord_3493122
  simp only [CollatzResearch.WordTrace]
  refine ⟨31851156512755761646682405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84936417367348697724486413 31851156512755761646682405)
  ·
    refine ⟨5972091846141705308752951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31851156512755761646682405 5972091846141705308752951)
    ·
      refine ⟨8958137769212557963129427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5972091846141705308752951 8958137769212557963129427)
      ·
        refine ⟨13437206653818836944694141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8958137769212557963129427 13437206653818836944694141)
        ·
          refine ⟨5038952495182063854260303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13437206653818836944694141 5038952495182063854260303)
          ·
            refine ⟨7558428742773095781390455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5038952495182063854260303 7558428742773095781390455)
            ·
              refine ⟨11337643114159643672085683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7558428742773095781390455 11337643114159643672085683)
              ·
                refine ⟨17006464671239465508128525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11337643114159643672085683 17006464671239465508128525)
                ·
                  refine ⟨6377424251714799565548197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17006464671239465508128525 6377424251714799565548197)
                  ·
                    refine ⟨1195767047196524918540287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6377424251714799565548197 1195767047196524918540287)
                    ·
                      rfl

theorem cell22_3493122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3493122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493122 prefixEnd_3493122 := by exact prefixLift 3493122
  have htrace : WordTrace (prefixWord ++ tailWord_3493122) baseStart_3493122 baseEnd_3493122 := by
    simpa [prefixWord, tailWord_3493122, baseEnd_3493122] using wordTrace_append hprefix tailTrace_3493122
  have hstable : (prefixWord ++ tailWord_3493122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493122).length < 2 ^ (prefixWord ++ tailWord_3493122).sum := by decide
  have hdescent : baseEnd_3493122 < baseStart_3493122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493178 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_3493178 : Nat := 118140960795 + 3493178 * 2 ^ 59
def prefixEnd_3493178 : Nat := 4983230072969 + 3 ^ 40 * 3493178 * 2
def baseEnd_3493178 : Nat := 1195786217140959439140115

theorem tailTrace_3493178 : CollatzResearch.WordTrace tailWord_3493178 prefixEnd_3493178 1195786217140959439140115 := by
  unfold tailWord_3493178
  simp only [CollatzResearch.WordTrace]
  refine ⟨31851667134705042037692047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84937779025880112100512125 31851667134705042037692047)
  ·
    refine ⟨47777500702057563056538071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31851667134705042037692047 47777500702057563056538071)
    ·
      refine ⟨71666251053086344584807107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47777500702057563056538071 71666251053086344584807107)
      ·
        refine ⟨107499376579629516877210661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71666251053086344584807107 107499376579629516877210661)
        ·
          refine ⟨20156133108680534414476999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107499376579629516877210661 20156133108680534414476999)
          ·
            refine ⟨30234199663020801621715499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20156133108680534414476999 30234199663020801621715499)
            ·
              refine ⟨45351299494531202432573249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30234199663020801621715499 45351299494531202432573249)
              ·
                refine ⟨34013474620898401824429937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45351299494531202432573249 34013474620898401824429937)
                ·
                  refine ⟨25510105965673801368322453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34013474620898401824429937 25510105965673801368322453)
                  ·
                    refine ⟨1195786217140959439140115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25510105965673801368322453 1195786217140959439140115)
                    ·
                      rfl

theorem cell22_3493178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_3493178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493178 prefixEnd_3493178 := by exact prefixLift 3493178
  have htrace : WordTrace (prefixWord ++ tailWord_3493178) baseStart_3493178 baseEnd_3493178 := by
    simpa [prefixWord, tailWord_3493178, baseEnd_3493178] using wordTrace_append hprefix tailTrace_3493178
  have hstable : (prefixWord ++ tailWord_3493178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493178).length < 2 ^ (prefixWord ++ tailWord_3493178).sum := by decide
  have hdescent : baseEnd_3493178 < baseStart_3493178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493180 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 5, 3]
def baseStart_3493180 : Nat := 118140960795 + 3493180 * 2 ^ 59
def prefixEnd_3493180 : Nat := 4983230072969 + 3 ^ 40 * 3493180 * 2
def baseEnd_3493180 : Nat := 1195786901781832100590109

theorem tailTrace_3493180 : CollatzResearch.WordTrace tailWord_3493180 prefixEnd_3493180 1195786901781832100590109 := by
  unfold tailWord_3493180
  simp only [CollatzResearch.WordTrace]
  refine ⟨63703370742406461246170497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84937827656541948328227329 63703370742406461246170497)
  ·
    refine ⟨47777528056804845934627873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63703370742406461246170497 47777528056804845934627873)
    ·
      refine ⟨35833146042603634450970905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47777528056804845934627873 35833146042603634450970905)
      ·
        refine ⟨26874859531952725838228179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35833146042603634450970905 26874859531952725838228179)
        ·
          refine ⟨40312289297929088757342269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26874859531952725838228179 40312289297929088757342269)
          ·
            refine ⟨15117108486723408284003351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40312289297929088757342269 15117108486723408284003351)
            ·
              refine ⟨22675662730085112426005027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15117108486723408284003351 22675662730085112426005027)
              ·
                refine ⟨34013494095127668639007541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22675662730085112426005027 34013494095127668639007541)
                ·
                  refine ⟨3188765071418218934906957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34013494095127668639007541 3188765071418218934906957)
                  ·
                    refine ⟨1195786901781832100590109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3188765071418218934906957 1195786901781832100590109)
                    ·
                      rfl

theorem cell22_3493180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_3493180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493180 prefixEnd_3493180 := by exact prefixLift 3493180
  have htrace : WordTrace (prefixWord ++ tailWord_3493180) baseStart_3493180 baseEnd_3493180 := by
    simpa [prefixWord, tailWord_3493180, baseEnd_3493180] using wordTrace_append hprefix tailTrace_3493180
  have hstable : (prefixWord ++ tailWord_3493180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493180).length < 2 ^ (prefixWord ++ tailWord_3493180).sum := by decide
  have hdescent : baseEnd_3493180 < baseStart_3493180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493190 : List Nat := [6, 1, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_3493190 : Nat := 118140960795 + 3493190 * 2 ^ 59
def prefixEnd_3493190 : Nat := 4983230072969 + 3 ^ 40 * 3493190 * 2
def baseEnd_3493190 : Nat := 1195790324986195407840079

theorem tailTrace_3493190 : CollatzResearch.WordTrace tailWord_3493190 prefixEnd_3493190 1195790324986195407840079 := by
  unfold tailWord_3493190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3981472069211771693756407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84938070809851129466803349 3981472069211771693756407)
  ·
    refine ⟨5972208103817657540634611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3981472069211771693756407 5972208103817657540634611)
    ·
      refine ⟨8958312155726486310951917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5972208103817657540634611 8958312155726486310951917)
      ·
        refine ⟨3359367058397432366606969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8958312155726486310951917 3359367058397432366606969)
        ·
          refine ⟨2519525293798074274955227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3359367058397432366606969 2519525293798074274955227)
          ·
            refine ⟨3779287940697111412432841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519525293798074274955227 3779287940697111412432841)
            ·
              refine ⟨2834465955522833559324631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3779287940697111412432841 2834465955522833559324631)
              ·
                refine ⟨4251698933284250338986947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2834465955522833559324631 4251698933284250338986947)
                ·
                  refine ⟨6377548399926375508480421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4251698933284250338986947 6377548399926375508480421)
                  ·
                    refine ⟨1195790324986195407840079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6377548399926375508480421 1195790324986195407840079)
                    ·
                      rfl

theorem cell22_3493190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_3493190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493190 prefixEnd_3493190 := by exact prefixLift 3493190
  have htrace : WordTrace (prefixWord ++ tailWord_3493190) baseStart_3493190 baseEnd_3493190 := by
    simpa [prefixWord, tailWord_3493190, baseEnd_3493190] using wordTrace_append hprefix tailTrace_3493190
  have hstable : (prefixWord ++ tailWord_3493190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493190).length < 2 ^ (prefixWord ++ tailWord_3493190).sum := by decide
  have hdescent : baseEnd_3493190 < baseStart_3493190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493208 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 4, 5]
def baseStart_3493208 : Nat := 118140960795 + 3493208 * 2 ^ 59
def prefixEnd_3493208 : Nat := 4983230072969 + 3 ^ 40 * 3493208 * 2
def baseEnd_3493208 : Nat := 1195796486754049360890023

theorem tailTrace_3493208 : CollatzResearch.WordTrace tailWord_3493208 prefixEnd_3493208 1195796486754049360890023 := by
  unfold tailWord_3493208
  simp only [CollatzResearch.WordTrace]
  refine ⟨63703881364355741637180139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84938508485807655516240185 63703881364355741637180139)
  ·
    refine ⟨95555822046533612455770209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63703881364355741637180139 95555822046533612455770209)
    ·
      refine ⟨71666866534900209341827657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95555822046533612455770209 71666866534900209341827657)
      ·
        refine ⟨53750149901175157006370743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71666866534900209341827657 53750149901175157006370743)
        ·
          refine ⟨80625224851762735509556115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53750149901175157006370743 80625224851762735509556115)
          ·
            refine ⟨120937837277644103264334173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80625224851762735509556115 120937837277644103264334173)
            ·
              refine ⟨45351688979116538724125315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120937837277644103264334173 45351688979116538724125315)
              ·
                refine ⟨68027533468674808086187973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45351688979116538724125315 68027533468674808086187973)
                ·
                  refine ⟨12755162525376526516160245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68027533468674808086187973 12755162525376526516160245)
                  ·
                    refine ⟨1195796486754049360890023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12755162525376526516160245 1195796486754049360890023)
                    ·
                      rfl

theorem cell22_3493208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_3493208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493208 prefixEnd_3493208 := by exact prefixLift 3493208
  have htrace : WordTrace (prefixWord ++ tailWord_3493208) baseStart_3493208 baseEnd_3493208 := by
    simpa [prefixWord, tailWord_3493208, baseEnd_3493208] using wordTrace_append hprefix tailTrace_3493208
  have hstable : (prefixWord ++ tailWord_3493208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493208).length < 2 ^ (prefixWord ++ tailWord_3493208).sum := by decide
  have hdescent : baseEnd_3493208 < baseStart_3493208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493210 : List Nat := [3, 1, 1, 2, 1, 2, 5, 2, 5]
def baseStart_3493210 : Nat := 118140960795 + 3493210 * 2 ^ 59
def prefixEnd_3493210 : Nat := 4983230072969 + 3 ^ 40 * 3493210 * 2
def baseEnd_3493210 : Nat := 398599057131640674113339

theorem tailTrace_3493210 : CollatzResearch.WordTrace tailWord_3493210 prefixEnd_3493210 398599057131640674113339 := by
  unfold tailWord_3493210
  simp only [CollatzResearch.WordTrace]
  refine ⟨31851958918676059403983271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84938557116469491743955389 31851958918676059403983271)
  ·
    refine ⟨47777938378014089105974907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31851958918676059403983271 47777938378014089105974907)
    ·
      refine ⟨71666907567021133658962361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47777938378014089105974907 71666907567021133658962361)
      ·
        refine ⟨53750180675265850244221771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71666907567021133658962361 53750180675265850244221771)
        ·
          refine ⟨80625271012898775366332657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53750180675265850244221771 80625271012898775366332657)
          ·
            refine ⟨60468953259674081524749493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80625271012898775366332657 60468953259674081524749493)
            ·
              refine ⟨5668964368094445142945265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60468953259674081524749493 5668964368094445142945265)
              ·
                refine ⟨4251723276070833857208949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5668964368094445142945265 4251723276070833857208949)
                ·
                  refine ⟨398599057131640674113339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4251723276070833857208949 398599057131640674113339)
                  ·
                    rfl

theorem cell22_3493210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_3493210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493210 prefixEnd_3493210 := by exact prefixLift 3493210
  have htrace : WordTrace (prefixWord ++ tailWord_3493210) baseStart_3493210 baseEnd_3493210 := by
    simpa [prefixWord, tailWord_3493210, baseEnd_3493210] using wordTrace_append hprefix tailTrace_3493210
  have hstable : (prefixWord ++ tailWord_3493210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493210).length < 2 ^ (prefixWord ++ tailWord_3493210).sum := by decide
  have hdescent : baseEnd_3493210 < baseStart_3493210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493278 : List Nat := [4, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_3493278 : Nat := 118140960795 + 3493278 * 2 ^ 59
def prefixEnd_3493278 : Nat := 4983230072969 + 3 ^ 40 * 3493278 * 2
def baseEnd_3493278 : Nat := 398606816394864170546603

theorem tailTrace_3493278 : CollatzResearch.WordTrace tailWord_3493278 prefixEnd_3493278 398606816394864170546603 := by
  unfold tailWord_3493278
  simp only [CollatzResearch.WordTrace]
  refine ⟨15926289479807235653676061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84940210558971923486272325 15926289479807235653676061)
  ·
    refine ⟨5972358554927713370128523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15926289479807235653676061 5972358554927713370128523)
    ·
      refine ⟨8958537832391570055192785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5972358554927713370128523 8958537832391570055192785)
      ·
        refine ⟨6718903374293677541394589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8958537832391570055192785 6718903374293677541394589)
        ·
          refine ⟨2519588765360129078022971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6718903374293677541394589 2519588765360129078022971)
          ·
            refine ⟨3779383148040193617034457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519588765360129078022971 3779383148040193617034457)
            ·
              refine ⟨2834537361030145212775843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3779383148040193617034457 2834537361030145212775843)
              ·
                refine ⟨4251806041545217819163765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2834537361030145212775843 4251806041545217819163765)
                ·
                  refine ⟨398606816394864170546603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4251806041545217819163765 398606816394864170546603)
                  ·
                    rfl

theorem cell22_3493278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_3493278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493278 prefixEnd_3493278 := by exact prefixLift 3493278
  have htrace : WordTrace (prefixWord ++ tailWord_3493278) baseStart_3493278 baseEnd_3493278 := by
    simpa [prefixWord, tailWord_3493278, baseEnd_3493278] using wordTrace_append hprefix tailTrace_3493278
  have hstable : (prefixWord ++ tailWord_3493278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493278).length < 2 ^ (prefixWord ++ tailWord_3493278).sum := by decide
  have hdescent : baseEnd_3493278 < baseStart_3493278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493334 : List Nat := [5, 2, 1, 1, 1, 4, 1, 7]
def baseStart_3493334 : Nat := 118140960795 + 3493334 * 2 ^ 59
def prefixEnd_3493334 : Nat := 4983230072969 + 3 ^ 40 * 3493334 * 2
def baseEnd_3493334 : Nat := 132871068792114114693293

theorem tailTrace_3493334 : CollatzResearch.WordTrace tailWord_3493334 prefixEnd_3493334 132871068792114114693293 := by
  unfold tailWord_3493334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7963272395390937924590441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84941572217503337862298037 7963272395390937924590441)
  ·
    refine ⟨5972454296543203443442831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7963272395390937924590441 5972454296543203443442831)
    ·
      refine ⟨8958681444814805165164247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5972454296543203443442831 8958681444814805165164247)
      ·
        refine ⟨13438022167222207747746371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8958681444814805165164247 13438022167222207747746371)
        ·
          refine ⟨20157033250833311621619557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13438022167222207747746371 20157033250833311621619557)
          ·
            refine ⟨3779443734531245929053667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20157033250833311621619557 3779443734531245929053667)
            ·
              refine ⟨5669165601796868893580501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779443734531245929053667 5669165601796868893580501)
              ·
                refine ⟨132871068792114114693293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5669165601796868893580501 132871068792114114693293)
                ·
                  rfl

theorem cell22_3493334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_3493334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493334 prefixEnd_3493334 := by exact prefixLift 3493334
  have htrace : WordTrace (prefixWord ++ tailWord_3493334) baseStart_3493334 baseEnd_3493334 := by
    simpa [prefixWord, tailWord_3493334, baseEnd_3493334] using wordTrace_append hprefix tailTrace_3493334
  have hstable : (prefixWord ++ tailWord_3493334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493334).length < 2 ^ (prefixWord ++ tailWord_3493334).sum := by decide
  have hdescent : baseEnd_3493334 < baseStart_3493334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493349 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 3, 3]
def baseStart_3493349 : Nat := 118140960795 + 3493349 * 2 ^ 59
def prefixEnd_3493349 : Nat := 4983230072969 + 3 ^ 40 * 3493349 * 2
def baseEnd_3493349 : Nat := 1195844753935571993114591

theorem tailTrace_3493349 : CollatzResearch.WordTrace tailWord_3493349 prefixEnd_3493349 1195844753935571993114591 := by
  unfold tailWord_3493349
  simp only [CollatzResearch.WordTrace]
  refine ⟨127412905421200664355243101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84941936947467109570162067 127412905421200664355243101)
  ·
    refine ⟨47779839532950249133216163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127412905421200664355243101 47779839532950249133216163)
    ·
      refine ⟨71669759299425373699824245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47779839532950249133216163 71669759299425373699824245)
      ·
        refine ⟨6719039934321128784358523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71669759299425373699824245 6719039934321128784358523)
        ·
          refine ⟨10078559901481693176537785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6719039934321128784358523 10078559901481693176537785)
          ·
            refine ⟨7558919926111269882403339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10078559901481693176537785 7558919926111269882403339)
            ·
              refine ⟨11338379889166904823605009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7558919926111269882403339 11338379889166904823605009)
              ·
                refine ⟨8503784916875178617703757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11338379889166904823605009 8503784916875178617703757)
                ·
                  refine ⟨3188919343828191981638909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8503784916875178617703757 3188919343828191981638909)
                  ·
                    refine ⟨1195844753935571993114591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3188919343828191981638909 1195844753935571993114591)
                    ·
                      rfl

theorem cell22_3493349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_3493349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493349 prefixEnd_3493349 := by exact prefixLift 3493349
  have htrace : WordTrace (prefixWord ++ tailWord_3493349) baseStart_3493349 baseEnd_3493349 := by
    simpa [prefixWord, tailWord_3493349, baseEnd_3493349] using wordTrace_append hprefix tailTrace_3493349
  have hstable : (prefixWord ++ tailWord_3493349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493349).length < 2 ^ (prefixWord ++ tailWord_3493349).sum := by decide
  have hdescent : baseEnd_3493349 < baseStart_3493349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493366 : List Nat := [5, 1, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_3493366 : Nat := 118140960795 + 3493366 * 2 ^ 59
def prefixEnd_3493366 : Nat := 4983230072969 + 3 ^ 40 * 3493366 * 2
def baseEnd_3493366 : Nat := 1195850573382989615439539

theorem tailTrace_3493366 : CollatzResearch.WordTrace tailWord_3493366 prefixEnd_3493366 1195850573382989615439539 := by
  unfold tailWord_3493366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7963345341383692266163247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84942350308092717505741301 7963345341383692266163247)
  ·
    refine ⟨11945018012075538399244871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7963345341383692266163247 11945018012075538399244871)
    ·
      refine ⟨17917527018113307598867307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11945018012075538399244871 17917527018113307598867307)
      ·
        refine ⟨26876290527169961398300961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17917527018113307598867307 26876290527169961398300961)
        ·
          refine ⟨20157217895377471048725721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26876290527169961398300961 20157217895377471048725721)
          ·
            refine ⟨15117913421533103286544291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20157217895377471048725721 15117913421533103286544291)
            ·
              refine ⟨22676870132299654929816437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15117913421533103286544291 22676870132299654929816437)
              ·
                refine ⟨2125956574903092649670291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22676870132299654929816437 2125956574903092649670291)
                ·
                  refine ⟨3188934862354638974505437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125956574903092649670291 3188934862354638974505437)
                  ·
                    refine ⟨1195850573382989615439539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3188934862354638974505437 1195850573382989615439539)
                    ·
                      rfl

theorem cell22_3493366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_3493366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493366 prefixEnd_3493366 := by exact prefixLift 3493366
  have htrace : WordTrace (prefixWord ++ tailWord_3493366) baseStart_3493366 baseEnd_3493366 := by
    simpa [prefixWord, tailWord_3493366, baseEnd_3493366] using wordTrace_append hprefix tailTrace_3493366
  have hstable : (prefixWord ++ tailWord_3493366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493366).length < 2 ^ (prefixWord ++ tailWord_3493366).sum := by decide
  have hdescent : baseEnd_3493366 < baseStart_3493366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493375 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 5, 4]
def baseStart_3493375 : Nat := 118140960795 + 3493375 * 2 ^ 59
def prefixEnd_3493375 : Nat := 4983230072969 + 3 ^ 40 * 3493375 * 2
def baseEnd_3493375 : Nat := 1195853654266916591964511

theorem tailTrace_3493375 : CollatzResearch.WordTrace tailWord_3493375 prefixEnd_3493375 1195853654266916591964511 := by
  unfold tailWord_3493375
  simp only [CollatzResearch.WordTrace]
  refine ⟨127413853719106470795689579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84942569146070980530459719 127413853719106470795689579)
  ·
    refine ⟨191120780578659706193534369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127413853719106470795689579 191120780578659706193534369)
    ·
      refine ⟨143340585433994779645150777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191120780578659706193534369 143340585433994779645150777)
      ·
        refine ⟨107505439075496084733863083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143340585433994779645150777 107505439075496084733863083)
        ·
          refine ⟨161258158613244127100794625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107505439075496084733863083 161258158613244127100794625)
          ·
            refine ⟨120943618959933095325595969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161258158613244127100794625 120943618959933095325595969)
            ·
              refine ⟨90707714219949821494196977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120943618959933095325595969 90707714219949821494196977)
              ·
                refine ⟨68030785664962366120647733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90707714219949821494196977 68030785664962366120647733)
                ·
                  refine ⟨6377886156090221823810725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68030785664962366120647733 6377886156090221823810725)
                  ·
                    refine ⟨1195853654266916591964511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6377886156090221823810725 1195853654266916591964511)
                    ·
                      rfl

theorem cell22_3493375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_3493375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493375 prefixEnd_3493375 := by exact prefixLift 3493375
  have htrace : WordTrace (prefixWord ++ tailWord_3493375) baseStart_3493375 baseEnd_3493375 := by
    simpa [prefixWord, tailWord_3493375, baseEnd_3493375] using wordTrace_append hprefix tailTrace_3493375
  have hstable : (prefixWord ++ tailWord_3493375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493375).length < 2 ^ (prefixWord ++ tailWord_3493375).sum := by decide
  have hdescent : baseEnd_3493375 < baseStart_3493375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493409 : List Nat := [1, 2, 3, 2, 2, 3, 2, 2, 1, 4]
def baseStart_3493409 : Nat := 118140960795 + 3493409 * 2 ^ 59
def prefixEnd_3493409 : Nat := 4983230072969 + 3 ^ 40 * 3493409 * 2
def baseEnd_3493409 : Nat := 1195865293161751836614407

theorem tailTrace_3493409 : CollatzResearch.WordTrace tailWord_3493409 prefixEnd_3493409 1195865293161751836614407 := by
  unfold tailWord_3493409
  simp only [CollatzResearch.WordTrace]
  refine ⟨127415093800983294602427281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84943395867322196401618187 127415093800983294602427281)
  ·
    refine ⟨95561320350737470951820461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127415093800983294602427281 95561320350737470951820461)
    ·
      refine ⟨35835495131526551606932673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95561320350737470951820461 35835495131526551606932673)
      ·
        refine ⟨26876621348644913705199505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35835495131526551606932673 26876621348644913705199505)
        ·
          refine ⟨20157466011483685278899629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26876621348644913705199505 20157466011483685278899629)
          ·
            refine ⟨7559049754306381979587361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20157466011483685278899629 7559049754306381979587361)
            ·
              refine ⟨5669287315729786484690521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7559049754306381979587361 5669287315729786484690521)
              ·
                refine ⟨4251965486797339863517891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5669287315729786484690521 4251965486797339863517891)
                ·
                  refine ⟨6377948230196009795276837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4251965486797339863517891 6377948230196009795276837)
                  ·
                    refine ⟨1195865293161751836614407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6377948230196009795276837 1195865293161751836614407)
                    ·
                      rfl

theorem cell22_3493409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_3493409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493409 prefixEnd_3493409 := by exact prefixLift 3493409
  have htrace : WordTrace (prefixWord ++ tailWord_3493409) baseStart_3493409 baseEnd_3493409 := by
    simpa [prefixWord, tailWord_3493409, baseEnd_3493409] using wordTrace_append hprefix tailTrace_3493409
  have hstable : (prefixWord ++ tailWord_3493409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493409).length < 2 ^ (prefixWord ++ tailWord_3493409).sum := by decide
  have hdescent : baseEnd_3493409 < baseStart_3493409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493441 : List Nat := [1, 2, 5, 1, 1, 1, 5, 2, 4]
def baseStart_3493441 : Nat := 118140960795 + 3493441 * 2 ^ 59
def prefixEnd_3493441 : Nat := 4983230072969 + 3 ^ 40 * 3493441 * 2
def baseEnd_3493441 : Nat := 398625415805238139938103

theorem tailTrace_3493441 : CollatzResearch.WordTrace tailWord_3493441 prefixEnd_3493441 398625415805238139938103 := by
  unfold tailWord_3493441
  simp only [CollatzResearch.WordTrace]
  refine ⟨127416260936867364067592177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84944173957911576045061451 127416260936867364067592177)
  ·
    refine ⟨95562195702650523050694133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127416260936867364067592177 95562195702650523050694133)
    ·
      refine ⟨8958955847123486536002575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95562195702650523050694133 8958955847123486536002575)
      ·
        refine ⟨13438433770685229804003863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8958955847123486536002575 13438433770685229804003863)
        ·
          refine ⟨20157650656027844706005795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13438433770685229804003863 20157650656027844706005795)
          ·
            refine ⟨30236475984041767059008693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20157650656027844706005795 30236475984041767059008693)
            ·
              refine ⟨2834669623503915661782065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30236475984041767059008693 2834669623503915661782065)
              ·
                refine ⟨2126002217627936746336549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2834669623503915661782065 2126002217627936746336549)
                ·
                  refine ⟨398625415805238139938103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2126002217627936746336549 398625415805238139938103)
                  ·
                    rfl

theorem cell22_3493441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 4].length) (baseStart_3493441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493441 prefixEnd_3493441 := by exact prefixLift 3493441
  have htrace : WordTrace (prefixWord ++ tailWord_3493441) baseStart_3493441 baseEnd_3493441 := by
    simpa [prefixWord, tailWord_3493441, baseEnd_3493441] using wordTrace_append hprefix tailTrace_3493441
  have hstable : (prefixWord ++ tailWord_3493441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493441).length < 2 ^ (prefixWord ++ tailWord_3493441).sum := by decide
  have hdescent : baseEnd_3493441 < baseStart_3493441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493452 : List Nat := [2, 2, 1, 3, 1, 4, 2, 7]
def baseStart_3493452 : Nat := 118140960795 + 3493452 * 2 ^ 59
def prefixEnd_3493452 : Nat := 4983230072969 + 3 ^ 40 * 3493452 * 2
def baseEnd_3493452 : Nat := 132875556993390450865475

theorem tailTrace_3493452 : CollatzResearch.WordTrace tailWord_3493452 prefixEnd_3493452 132875556993390450865475 := by
  unfold tailWord_3493452
  simp only [CollatzResearch.WordTrace]
  refine ⟨63708331069913756473121305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84944441426551675297495073 63708331069913756473121305)
  ·
    refine ⟨47781248302435317354840979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63708331069913756473121305 47781248302435317354840979)
    ·
      refine ⟨71671872453652976032261469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47781248302435317354840979 71671872453652976032261469)
      ·
        refine ⟨26876952170119866012098051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71671872453652976032261469 26876952170119866012098051)
        ·
          refine ⟨40315428255179799018147077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26876952170119866012098051 40315428255179799018147077)
          ·
            refine ⟨7559142797846212315902577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40315428255179799018147077 7559142797846212315902577)
            ·
              refine ⟨5669357098384659236926933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7559142797846212315902577 5669357098384659236926933)
              ·
                refine ⟨132875556993390450865475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5669357098384659236926933 132875556993390450865475)
                ·
                  rfl

theorem cell22_3493452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 7].length) (baseStart_3493452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493452 prefixEnd_3493452 := by exact prefixLift 3493452
  have htrace : WordTrace (prefixWord ++ tailWord_3493452) baseStart_3493452 baseEnd_3493452 := by
    simpa [prefixWord, tailWord_3493452, baseEnd_3493452] using wordTrace_append hprefix tailTrace_3493452
  have hstable : (prefixWord ++ tailWord_3493452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493452).length < 2 ^ (prefixWord ++ tailWord_3493452).sum := by decide
  have hdescent : baseEnd_3493452 < baseStart_3493452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493514 : List Nat := [3, 1, 2, 3, 2, 1, 2, 3, 5]
def baseStart_3493514 : Nat := 118140960795 + 3493514 * 2 ^ 59
def prefixEnd_3493514 : Nat := 4983230072969 + 3 ^ 40 * 3493514 * 2
def baseEnd_3493514 : Nat := 398633745602522187579695

theorem tailTrace_3493514 : CollatzResearch.WordTrace tailWord_3493514 prefixEnd_3493514 398633745602522187579695 := by
  unfold tailWord_3493514
  simp only [CollatzResearch.WordTrace]
  refine ⟨31854730866400724383749899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84945948977068598356666397 31854730866400724383749899)
  ·
    refine ⟨47782096299601086575624849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31854730866400724383749899 47782096299601086575624849)
    ·
      refine ⟨35836572224700814931718637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47782096299601086575624849 35836572224700814931718637)
      ·
        refine ⟨13438714584262805599394489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35836572224700814931718637 13438714584262805599394489)
        ·
          refine ⟨10079035938197104199545867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13438714584262805599394489 10079035938197104199545867)
          ·
            refine ⟨15118553907295656299318801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10079035938197104199545867 15118553907295656299318801)
            ·
              refine ⟨11338915430471742224489101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15118553907295656299318801 11338915430471742224489101)
              ·
                refine ⟨4252093286426903334183413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11338915430471742224489101 4252093286426903334183413)
                ·
                  refine ⟨398633745602522187579695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4252093286426903334183413 398633745602522187579695)
                  ·
                    rfl

theorem cell22_3493514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_3493514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493514 prefixEnd_3493514 := by exact prefixLift 3493514
  have htrace : WordTrace (prefixWord ++ tailWord_3493514) baseStart_3493514 baseEnd_3493514 := by
    simpa [prefixWord, tailWord_3493514, baseEnd_3493514] using wordTrace_append hprefix tailTrace_3493514
  have hstable : (prefixWord ++ tailWord_3493514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493514).length < 2 ^ (prefixWord ++ tailWord_3493514).sum := by decide
  have hdescent : baseEnd_3493514 < baseStart_3493514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493535 : List Nat := [1, 1, 2, 7, 1, 1, 2, 3, 1, 3]
def baseStart_3493535 : Nat := 118140960795 + 3493535 * 2 ^ 59
def prefixEnd_3493535 : Nat := 4983230072969 + 3 ^ 40 * 3493535 * 2
def baseEnd_3493535 : Nat := 1195908425536729507964021

theorem tailTrace_3493535 : CollatzResearch.WordTrace tailWord_3493535 prefixEnd_3493535 1195908425536729507964021 := by
  unfold tailWord_3493535
  simp only [CollatzResearch.WordTrace]
  refine ⟨127419689398526818121514059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84946459599017878747676039 127419689398526818121514059)
  ·
    refine ⟨191129534097790227182271089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127419689398526818121514059 191129534097790227182271089)
    ·
      refine ⟨143347150573342670386703317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191129534097790227182271089 143347150573342670386703317)
      ·
        refine ⟨3359698841562718837188359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 143347150573342670386703317 3359698841562718837188359)
        ·
          refine ⟨5039548262344078255782539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3359698841562718837188359 5039548262344078255782539)
          ·
            refine ⟨7559322393516117383673809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5039548262344078255782539 7559322393516117383673809)
            ·
              refine ⟨5669491795137088037755357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7559322393516117383673809 5669491795137088037755357)
              ·
                refine ⟨2126059423176408014158259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5669491795137088037755357 2126059423176408014158259)
                ·
                  refine ⟨3189089134764612021237389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126059423176408014158259 3189089134764612021237389)
                  ·
                    refine ⟨1195908425536729507964021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3189089134764612021237389 1195908425536729507964021)
                    ·
                      rfl

theorem cell22_3493535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 1, 3].length) (baseStart_3493535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493535 prefixEnd_3493535 := by exact prefixLift 3493535
  have htrace : WordTrace (prefixWord ++ tailWord_3493535) baseStart_3493535 baseEnd_3493535 := by
    simpa [prefixWord, tailWord_3493535, baseEnd_3493535] using wordTrace_append hprefix tailTrace_3493535
  have hstable : (prefixWord ++ tailWord_3493535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493535).length < 2 ^ (prefixWord ++ tailWord_3493535).sum := by decide
  have hdescent : baseEnd_3493535 < baseStart_3493535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493559 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 6]
def baseStart_3493559 : Nat := 118140960795 + 3493559 * 2 ^ 59
def prefixEnd_3493559 : Nat := 4983230072969 + 3 ^ 40 * 3493559 * 2
def baseEnd_3493559 : Nat := 398638880409067148454649

theorem tailTrace_3493559 : CollatzResearch.WordTrace tailWord_3493559 prefixEnd_3493559 398638880409067148454649 := by
  unfold tailWord_3493559
  simp only [CollatzResearch.WordTrace]
  refine ⟨127420564750439870220387731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84947043166959913480258487 127420564750439870220387731)
  ·
    refine ⟨191130847125659805330581597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127420564750439870220387731 191130847125659805330581597)
    ·
      refine ⟨71674067672122426998968099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191130847125659805330581597 71674067672122426998968099)
      ·
        refine ⟨107511101508183640498452149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71674067672122426998968099 107511101508183640498452149)
        ·
          refine ⟨10079165766392216296729889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107511101508183640498452149 10079165766392216296729889)
          ·
            refine ⟨7559374324794162222547417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10079165766392216296729889 7559374324794162222547417)
            ·
              refine ⟨5669530743595621666910563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7559374324794162222547417 5669530743595621666910563)
              ·
                refine ⟨8504296115393432500365845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5669530743595621666910563 8504296115393432500365845)
                ·
                  refine ⟨398638880409067148454649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8504296115393432500365845 398638880409067148454649)
                  ·
                    rfl

theorem cell22_3493559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 6].length) (baseStart_3493559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493559 prefixEnd_3493559 := by exact prefixLift 3493559
  have htrace : WordTrace (prefixWord ++ tailWord_3493559) baseStart_3493559 baseEnd_3493559 := by
    simpa [prefixWord, tailWord_3493559, baseEnd_3493559] using wordTrace_append hprefix tailTrace_3493559
  have hstable : (prefixWord ++ tailWord_3493559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493559).length < 2 ^ (prefixWord ++ tailWord_3493559).sum := by decide
  have hdescent : baseEnd_3493559 < baseStart_3493559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493647 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 3, 7]
def baseStart_3493647 : Nat := 118140960795 + 3493647 * 2 ^ 59
def prefixEnd_3493647 : Nat := 4983230072969 + 3 ^ 40 * 3493647 * 2
def baseEnd_3493647 : Nat := 1195946765425598549163677

theorem tailTrace_3493647 : CollatzResearch.WordTrace tailWord_3493647 prefixEnd_3493647 1195946765425598549163677 := by
  unfold tailWord_3493647
  simp only [CollatzResearch.WordTrace]
  refine ⟨127423774374121061249591195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84949182916080707499727463 127423774374121061249591195)
  ·
    refine ⟨191135661561181591874386793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127423774374121061249591195 191135661561181591874386793)
    ·
      refine ⟨143351746170886193905790095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191135661561181591874386793 143351746170886193905790095)
      ·
        refine ⟨215027619256329290858685143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143351746170886193905790095 215027619256329290858685143)
        ·
          refine ⟨322541428884493936288027715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215027619256329290858685143 322541428884493936288027715)
          ·
            refine ⟨483812143326740904432041573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322541428884493936288027715 483812143326740904432041573)
            ·
              refine ⟨90714776873763919581007795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 483812143326740904432041573 90714776873763919581007795)
              ·
                refine ⟨136072165310645879371511693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90714776873763919581007795 136072165310645879371511693)
                ·
                  refine ⟨51027061991492204764316885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136072165310645879371511693 51027061991492204764316885)
                  ·
                    refine ⟨1195946765425598549163677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51027061991492204764316885 1195946765425598549163677)
                    ·
                      rfl

theorem cell22_3493647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_3493647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493647 prefixEnd_3493647 := by exact prefixLift 3493647
  have htrace : WordTrace (prefixWord ++ tailWord_3493647) baseStart_3493647 baseEnd_3493647 := by
    simpa [prefixWord, tailWord_3493647, baseEnd_3493647] using wordTrace_append hprefix tailTrace_3493647
  have hstable : (prefixWord ++ tailWord_3493647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493647).length < 2 ^ (prefixWord ++ tailWord_3493647).sum := by decide
  have hdescent : baseEnd_3493647 < baseStart_3493647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493664 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 2, 5]
def baseStart_3493664 : Nat := 118140960795 + 3493664 * 2 ^ 59
def prefixEnd_3493664 : Nat := 4983230072969 + 3 ^ 40 * 3493664 * 2
def baseEnd_3493664 : Nat := 1195952584873016171488625

theorem tailTrace_3493664 : CollatzResearch.WordTrace tailWord_3493664 prefixEnd_3493664 1195952584873016171488625 := by
  unfold tailWord_3493664
  simp only [CollatzResearch.WordTrace]
  refine ⟨63712197207529736576480023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84949596276706315435306697 63712197207529736576480023)
  ·
    refine ⟨95568295811294604864720035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63712197207529736576480023 95568295811294604864720035)
    ·
      refine ⟨143352443716941907297080053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95568295811294604864720035 143352443716941907297080053)
      ·
        refine ⟨13439291598463303809101255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143352443716941907297080053 13439291598463303809101255)
        ·
          refine ⟨20158937397694955713651883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13439291598463303809101255 20158937397694955713651883)
          ·
            refine ⟨30238406096542433570477825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20158937397694955713651883 30238406096542433570477825)
            ·
              refine ⟨22678804572406825177858369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30238406096542433570477825 22678804572406825177858369)
              ·
                refine ⟨17009103429305118883393777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22678804572406825177858369 17009103429305118883393777)
                ·
                  refine ⟨12756827571978839162545333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17009103429305118883393777 12756827571978839162545333)
                  ·
                    refine ⟨1195952584873016171488625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12756827571978839162545333 1195952584873016171488625)
                    ·
                      rfl

theorem cell22_3493664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_3493664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493664 prefixEnd_3493664 := by exact prefixLift 3493664
  have htrace : WordTrace (prefixWord ++ tailWord_3493664) baseStart_3493664 baseEnd_3493664 := by
    simpa [prefixWord, tailWord_3493664, baseEnd_3493664] using wordTrace_append hprefix tailTrace_3493664
  have hstable : (prefixWord ++ tailWord_3493664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493664).length < 2 ^ (prefixWord ++ tailWord_3493664).sum := by decide
  have hdescent : baseEnd_3493664 < baseStart_3493664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493666 : List Nat := [3, 3, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3493666 : Nat := 118140960795 + 3493666 * 2 ^ 59
def prefixEnd_3493666 : Nat := 4983230072969 + 3 ^ 40 * 3493666 * 2
def baseEnd_3493666 : Nat := 398651089837962944312873

theorem tailTrace_3493666 : CollatzResearch.WordTrace tailWord_3493666 prefixEnd_3493666 398651089837962944312873 := by
  unfold tailWord_3493666
  simp only [CollatzResearch.WordTrace]
  refine ⟨31856116840263056873633213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84949644907368151663021901 31856116840263056873633213)
  ·
    refine ⟨11946043815098646327612455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31856116840263056873633213 11946043815098646327612455)
    ·
      refine ⟨17919065722647969491418683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11946043815098646327612455 17919065722647969491418683)
      ·
        refine ⟨26878598583971954237128025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17919065722647969491418683 26878598583971954237128025)
        ·
          refine ⟨20158948937978965677846019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26878598583971954237128025 20158948937978965677846019)
          ·
            refine ⟨30238423406968448516769029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20158948937978965677846019 30238423406968448516769029)
            ·
              refine ⟨5669704388806584096894193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30238423406968448516769029 5669704388806584096894193)
              ·
                refine ⟨4252278291604938072670645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5669704388806584096894193 4252278291604938072670645)
                ·
                  refine ⟨398651089837962944312873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4252278291604938072670645 398651089837962944312873)
                  ·
                    rfl

theorem cell22_3493666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3493666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493666 prefixEnd_3493666 := by exact prefixLift 3493666
  have htrace : WordTrace (prefixWord ++ tailWord_3493666) baseStart_3493666 baseEnd_3493666 := by
    simpa [prefixWord, tailWord_3493666, baseEnd_3493666] using wordTrace_append hprefix tailTrace_3493666
  have hstable : (prefixWord ++ tailWord_3493666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493666).length < 2 ^ (prefixWord ++ tailWord_3493666).sum := by decide
  have hdescent : baseEnd_3493666 < baseStart_3493666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493713 : List Nat := [1, 2, 2, 1, 5, 1, 4, 1, 1, 4]
def baseStart_3493713 : Nat := 118140960795 + 3493713 * 2 ^ 59
def prefixEnd_3493713 : Nat := 4983230072969 + 3 ^ 40 * 3493713 * 2
def baseEnd_3493713 : Nat := 1195969358574396377013475

theorem tailTrace_3493713 : CollatzResearch.WordTrace tailWord_3493713 prefixEnd_3493713 1195969358574396377013475 := by
  unfold tailWord_3493713
  simp only [CollatzResearch.WordTrace]
  refine ⟨127426181591881954521493793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84950787727921303014329195 127426181591881954521493793)
  ·
    refine ⟨95569636193911465891120345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127426181591881954521493793 95569636193911465891120345)
    ·
      refine ⟨71677227145433599418340259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95569636193911465891120345 71677227145433599418340259)
      ·
        refine ⟨107515840718150399127510389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71677227145433599418340259 107515840718150399127510389)
        ·
          refine ⟨10079610067326599918204099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107515840718150399127510389 10079610067326599918204099)
          ·
            refine ⟨15119415100989899877306149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10079610067326599918204099 15119415100989899877306149)
            ·
              refine ⟨2834890331435606226994903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15119415100989899877306149 2834890331435606226994903)
              ·
                refine ⟨4252335497153409340492355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2834890331435606226994903 4252335497153409340492355)
                ·
                  refine ⟨6378503245730114010738533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4252335497153409340492355 6378503245730114010738533)
                  ·
                    refine ⟨1195969358574396377013475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6378503245730114010738533 1195969358574396377013475)
                    ·
                      rfl

theorem cell22_3493713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_3493713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493713 prefixEnd_3493713 := by exact prefixLift 3493713
  have htrace : WordTrace (prefixWord ++ tailWord_3493713) baseStart_3493713 baseEnd_3493713 := by
    simpa [prefixWord, tailWord_3493713, baseEnd_3493713] using wordTrace_append hprefix tailTrace_3493713
  have hstable : (prefixWord ++ tailWord_3493713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493713).length < 2 ^ (prefixWord ++ tailWord_3493713).sum := by decide
  have hdescent : baseEnd_3493713 < baseStart_3493713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493758 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3493758 : Nat := 118140960795 + 3493758 * 2 ^ 59
def prefixEnd_3493758 : Nat := 4983230072969 + 3 ^ 40 * 3493758 * 2
def baseEnd_3493758 : Nat := 1195984762994031259638337

theorem tailTrace_3493758 : CollatzResearch.WordTrace tailWord_3493758 prefixEnd_3493758 1195984762994031259638337 := by
  unfold tailWord_3493758
  simp only [CollatzResearch.WordTrace]
  refine ⟨15928477859589865900860241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84951881917812618137921285 15928477859589865900860241)
  ·
    refine ⟨11946358394692399425645181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15928477859589865900860241 11946358394692399425645181)
    ·
      refine ⟨4479884398009649784616943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11946358394692399425645181 4479884398009649784616943)
      ·
        refine ⟨6719826597014474676925415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4479884398009649784616943 6719826597014474676925415)
        ·
          refine ⟨10079739895521712015388123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6719826597014474676925415 10079739895521712015388123)
          ·
            refine ⟨15119609843282568023082185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10079739895521712015388123 15119609843282568023082185)
            ·
              refine ⟨11339707382461926017311639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15119609843282568023082185 11339707382461926017311639)
              ·
                refine ⟨17009561073692889025967459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11339707382461926017311639 17009561073692889025967459)
                ·
                  refine ⟨25514341610539333538951189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17009561073692889025967459 25514341610539333538951189)
                  ·
                    refine ⟨1195984762994031259638337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25514341610539333538951189 1195984762994031259638337)
                    ·
                      rfl

theorem cell22_3493758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3493758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493758 prefixEnd_3493758 := by exact prefixLift 3493758
  have htrace : WordTrace (prefixWord ++ tailWord_3493758) baseStart_3493758 baseEnd_3493758 := by
    simpa [prefixWord, tailWord_3493758, baseEnd_3493758] using wordTrace_append hprefix tailTrace_3493758
  have hstable : (prefixWord ++ tailWord_3493758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493758).length < 2 ^ (prefixWord ++ tailWord_3493758).sum := by decide
  have hdescent : baseEnd_3493758 < baseStart_3493758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493790 : List Nat := [4, 3, 1, 3, 1, 1, 2, 7]
def baseStart_3493790 : Nat := 118140960795 + 3493790 * 2 ^ 59
def prefixEnd_3493790 : Nat := 4983230072969 + 3 ^ 40 * 3493790 * 2
def baseEnd_3493790 : Nat := 132888413027554871426471

theorem tailTrace_3493790 : CollatzResearch.WordTrace tailWord_3493790 prefixEnd_3493790 132888413027554871426471 := by
  unfold tailWord_3493790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15928623751575374584005853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84952660008401997781364549 15928623751575374584005853)
  ·
    refine ⟨5973233906840765469002195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15928623751575374584005853 5973233906840765469002195)
    ·
      refine ⟨8959850860261148203503293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5973233906840765469002195 8959850860261148203503293)
      ·
        refine ⟨3359944072597930576313735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8959850860261148203503293 3359944072597930576313735)
        ·
          refine ⟨5039916108896895864470603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3359944072597930576313735 5039916108896895864470603)
          ·
            refine ⟨7559874163345343796705905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5039916108896895864470603 7559874163345343796705905)
            ·
              refine ⟨5669905622509007847529429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7559874163345343796705905 5669905622509007847529429)
              ·
                refine ⟨132888413027554871426471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5669905622509007847529429 132888413027554871426471)
                ·
                  rfl

theorem cell22_3493790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_3493790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493790 prefixEnd_3493790 := by exact prefixLift 3493790
  have htrace : WordTrace (prefixWord ++ tailWord_3493790) baseStart_3493790 baseEnd_3493790 := by
    simpa [prefixWord, tailWord_3493790, baseEnd_3493790] using wordTrace_append hprefix tailTrace_3493790
  have hstable : (prefixWord ++ tailWord_3493790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493790).length < 2 ^ (prefixWord ++ tailWord_3493790).sum := by decide
  have hdescent : baseEnd_3493790 < baseStart_3493790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493794 : List Nat := [3, 3, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_3493794 : Nat := 118140960795 + 3493794 * 2 ^ 59
def prefixEnd_3493794 : Nat := 4983230072969 + 3 ^ 40 * 3493794 * 2
def baseEnd_3493794 : Nat := 1195997086529739165738227

theorem tailTrace_3493794 : CollatzResearch.WordTrace tailWord_3493794 prefixEnd_3493794 1195997086529739165738227 := by
  unfold tailWord_3493794
  simp only [CollatzResearch.WordTrace]
  refine ⟨31857283976147126338798109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84952757269725670236794957 31857283976147126338798109)
  ·
    refine ⟨11946481491055172377049291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31857283976147126338798109 11946481491055172377049291)
    ·
      refine ⟨17919722236582758565573937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11946481491055172377049291 17919722236582758565573937)
      ·
        refine ⟨13439791677437068924180453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17919722236582758565573937 13439791677437068924180453)
        ·
          refine ⟨2519960939519450423283835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13439791677437068924180453 2519960939519450423283835)
          ·
            refine ⟨3779941409279175634925753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519960939519450423283835 3779941409279175634925753)
            ·
              refine ⟨2834956056959381726194315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3779941409279175634925753 2834956056959381726194315)
              ·
                refine ⟨4252434085439072589291473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2834956056959381726194315 4252434085439072589291473)
                ·
                  refine ⟨3189325564079304441968605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4252434085439072589291473 3189325564079304441968605)
                  ·
                    refine ⟨1195997086529739165738227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3189325564079304441968605 1195997086529739165738227)
                    ·
                      rfl

theorem cell22_3493794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_3493794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493794 prefixEnd_3493794 := by exact prefixLift 3493794
  have htrace : WordTrace (prefixWord ++ tailWord_3493794) baseStart_3493794 baseEnd_3493794 := by
    simpa [prefixWord, tailWord_3493794, baseEnd_3493794] using wordTrace_append hprefix tailTrace_3493794
  have hstable : (prefixWord ++ tailWord_3493794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493794).length < 2 ^ (prefixWord ++ tailWord_3493794).sum := by decide
  have hdescent : baseEnd_3493794 < baseStart_3493794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493829 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 10]
def baseStart_3493829 : Nat := 118140960795 + 3493829 * 2 ^ 59
def prefixEnd_3493829 : Nat := 4983230072969 + 3 ^ 40 * 3493829 * 2
def baseEnd_3493829 : Nat := 398669689248336913704373

theorem tailTrace_3493829 : CollatzResearch.WordTrace tailWord_3493829 prefixEnd_3493829 398669689248336913704373 := by
  unfold tailWord_3493829
  simp only [CollatzResearch.WordTrace]
  refine ⟨127430412459461706332716541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84953608306307804221811027 127430412459461706332716541)
  ·
    refine ⟨47786404672298139874768703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127430412459461706332716541 47786404672298139874768703)
    ·
      refine ⟨71679607008447209812153055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47786404672298139874768703 71679607008447209812153055)
      ·
        refine ⟨107519410512670814718229583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71679607008447209812153055 107519410512670814718229583)
        ·
          refine ⟨161279115769006222077344375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107519410512670814718229583 161279115769006222077344375)
          ·
            refine ⟨241918673653509333116016563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161279115769006222077344375 241918673653509333116016563)
            ·
              refine ⟨362878010480263999674024845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241918673653509333116016563 362878010480263999674024845)
              ·
                refine ⟨136079253930098999877759317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362878010480263999674024845 136079253930098999877759317)
                ·
                  refine ⟨398669689248336913704373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 136079253930098999877759317 398669689248336913704373)
                  ·
                    rfl

theorem cell22_3493829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_3493829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493829 prefixEnd_3493829 := by exact prefixLift 3493829
  have htrace : WordTrace (prefixWord ++ tailWord_3493829) baseStart_3493829 baseEnd_3493829 := by
    simpa [prefixWord, tailWord_3493829, baseEnd_3493829] using wordTrace_append hprefix tailTrace_3493829
  have hstable : (prefixWord ++ tailWord_3493829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493829).length < 2 ^ (prefixWord ++ tailWord_3493829).sum := by decide
  have hdescent : baseEnd_3493829 < baseStart_3493829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493863 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 6]
def baseStart_3493863 : Nat := 118140960795 + 3493863 * 2 ^ 59
def prefixEnd_3493863 : Nat := 4983230072969 + 3 ^ 40 * 3493863 * 2
def baseEnd_3493863 : Nat := 398673568879948661921005

theorem tailTrace_3493863 : CollatzResearch.WordTrace tailWord_3493863 prefixEnd_3493863 398673568879948661921005 := by
  unfold tailWord_3493863
  simp only [CollatzResearch.WordTrace]
  refine ⟨127431652541338530139454243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84954435027559020092969495 127431652541338530139454243)
  ·
    refine ⟨191147478812007795209181365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127431652541338530139454243 191147478812007795209181365)
    ·
      refine ⟨17920076138625730800860753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191147478812007795209181365 17920076138625730800860753)
      ·
        refine ⟨13440057103969298100645565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17920076138625730800860753 13440057103969298100645565)
        ·
          refine ⟨5040021413988486787742087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13440057103969298100645565 5040021413988486787742087)
          ·
            refine ⟨7560032120982730181613131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5040021413988486787742087 7560032120982730181613131)
            ·
              refine ⟨11340048181474095272419697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7560032120982730181613131 11340048181474095272419697)
              ·
                refine ⟨8505036136105571454314773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11340048181474095272419697 8505036136105571454314773)
                ·
                  refine ⟨398673568879948661921005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8505036136105571454314773 398673568879948661921005)
                  ·
                    rfl

theorem cell22_3493863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 6].length) (baseStart_3493863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493863 prefixEnd_3493863 := by exact prefixLift 3493863
  have htrace : WordTrace (prefixWord ++ tailWord_3493863) baseStart_3493863 baseEnd_3493863 := by
    simpa [prefixWord, tailWord_3493863, baseEnd_3493863] using wordTrace_append hprefix tailTrace_3493863
  have hstable : (prefixWord ++ tailWord_3493863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493863).length < 2 ^ (prefixWord ++ tailWord_3493863).sum := by decide
  have hdescent : baseEnd_3493863 < baseStart_3493863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493895 : List Nat := [1, 1, 4, 3, 1, 2, 3, 2, 2, 3]
def baseStart_3493895 : Nat := 118140960795 + 3493895 * 2 ^ 59
def prefixEnd_3493895 : Nat := 4983230072969 + 3 ^ 40 * 3493895 * 2
def baseEnd_3493895 : Nat := 1196031660893808568962917

theorem tailTrace_3493895 : CollatzResearch.WordTrace tailWord_3493895 prefixEnd_3493895 1196031660893808568962917 := by
  unfold tailWord_3493895
  simp only [CollatzResearch.WordTrace]
  refine ⟨127432819677222599604619139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84955213118148399736412759 127432819677222599604619139)
  ·
    refine ⟨191149229515833899406928709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127432819677222599604619139 191149229515833899406928709)
    ·
      refine ⟨35840480534218856138799133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191149229515833899406928709 35840480534218856138799133)
      ·
        refine ⟨13440180200332071052049675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35840480534218856138799133 13440180200332071052049675)
        ·
          refine ⟨20160270300498106578074513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13440180200332071052049675 20160270300498106578074513)
          ·
            refine ⟨15120202725373579933555885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20160270300498106578074513 15120202725373579933555885)
            ·
              refine ⟨5670076022015092475083457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15120202725373579933555885 5670076022015092475083457)
              ·
                refine ⟨4252557016511319356312593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5670076022015092475083457 4252557016511319356312593)
                ·
                  refine ⟨3189417762383489517234445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4252557016511319356312593 3189417762383489517234445)
                  ·
                    refine ⟨1196031660893808568962917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3189417762383489517234445 1196031660893808568962917)
                    ·
                      rfl

theorem cell22_3493895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_3493895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493895 prefixEnd_3493895 := by exact prefixLift 3493895
  have htrace : WordTrace (prefixWord ++ tailWord_3493895) baseStart_3493895 baseEnd_3493895 := by
    simpa [prefixWord, tailWord_3493895, baseEnd_3493895] using wordTrace_append hprefix tailTrace_3493895
  have hstable : (prefixWord ++ tailWord_3493895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493895).length < 2 ^ (prefixWord ++ tailWord_3493895).sum := by decide
  have hdescent : baseEnd_3493895 < baseStart_3493895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493923 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 3, 3]
def baseStart_3493923 : Nat := 118140960795 + 3493923 * 2 ^ 59
def prefixEnd_3493923 : Nat := 4983230072969 + 3 ^ 40 * 3493923 * 2
def baseEnd_3493923 : Nat := 1196041245866025829262831

theorem tailTrace_3493923 : CollatzResearch.WordTrace tailWord_3493923 prefixEnd_3493923 1196041245866025829262831 := by
  unfold tailWord_3493923
  simp only [CollatzResearch.WordTrace]
  refine ⟨127433840921121160386638423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84955893947414106924425615 127433840921121160386638423)
  ·
    refine ⟨191150761381681740579957635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127433840921121160386638423 191150761381681740579957635)
    ·
      refine ⟨286726142072522610869936453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191150761381681740579957635 286726142072522610869936453)
      ·
        refine ⟨53761151638597989538113085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286726142072522610869936453 53761151638597989538113085)
        ·
          refine ⟨20160431864474246076792407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53761151638597989538113085 20160431864474246076792407)
          ·
            refine ⟨30240647796711369115188611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20160431864474246076792407 30240647796711369115188611)
            ·
              refine ⟨45360971695067053672782917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30240647796711369115188611 45360971695067053672782917)
              ·
                refine ⟨8505182192825072563646797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45360971695067053672782917 8505182192825072563646797)
                ·
                  refine ⟨3189443322309402211367549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8505182192825072563646797 3189443322309402211367549)
                  ·
                    refine ⟨1196041245866025829262831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3189443322309402211367549 1196041245866025829262831)
                    ·
                      rfl

theorem cell22_3493923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 3].length) (baseStart_3493923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493923 prefixEnd_3493923 := by exact prefixLift 3493923
  have htrace : WordTrace (prefixWord ++ tailWord_3493923) baseStart_3493923 baseEnd_3493923 := by
    simpa [prefixWord, tailWord_3493923, baseEnd_3493923] using wordTrace_append hprefix tailTrace_3493923
  have hstable : (prefixWord ++ tailWord_3493923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493923).length < 2 ^ (prefixWord ++ tailWord_3493923).sum := by decide
  have hdescent : baseEnd_3493923 < baseStart_3493923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493936 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 7]
def baseStart_3493936 : Nat := 118140960795 + 3493936 * 2 ^ 59
def prefixEnd_3493936 : Nat := 4983230072969 + 3 ^ 40 * 3493936 * 2
def baseEnd_3493936 : Nat := 398681898677232709562597

theorem tailTrace_3493936 : CollatzResearch.WordTrace tailWord_3493936 prefixEnd_3493936 398681898677232709562597 := by
  unfold tailWord_3493936
  simp only [CollatzResearch.WordTrace]
  refine ⟨63717157535037031803430831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84956210046716042404574441 63717157535037031803430831)
  ·
    refine ⟨95575736302555547705146247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63717157535037031803430831 95575736302555547705146247)
    ·
      refine ⟨143363604453833321557719371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95575736302555547705146247 143363604453833321557719371)
      ·
        refine ⟨215045406680749982336579057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143363604453833321557719371 215045406680749982336579057)
        ·
          refine ⟨161284055010562486752434293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215045406680749982336579057 161284055010562486752434293)
          ·
            refine ⟨15120380157240233133040715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161284055010562486752434293 15120380157240233133040715)
            ·
              refine ⟨22680570235860349699561073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15120380157240233133040715 22680570235860349699561073)
              ·
                refine ⟨17010427676895262274670805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22680570235860349699561073 17010427676895262274670805)
                ·
                  refine ⟨398681898677232709562597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17010427676895262274670805 398681898677232709562597)
                  ·
                    rfl

theorem cell22_3493936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_3493936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493936 prefixEnd_3493936 := by exact prefixLift 3493936
  have htrace : WordTrace (prefixWord ++ tailWord_3493936) baseStart_3493936 baseEnd_3493936 := by
    simpa [prefixWord, tailWord_3493936, baseEnd_3493936] using wordTrace_append hprefix tailTrace_3493936
  have hstable : (prefixWord ++ tailWord_3493936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493936).length < 2 ^ (prefixWord ++ tailWord_3493936).sum := by decide
  have hdescent : baseEnd_3493936 < baseStart_3493936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493951 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 4, 5]
def baseStart_3493951 : Nat := 118140960795 + 3493951 * 2 ^ 59
def prefixEnd_3493951 : Nat := 4983230072969 + 3 ^ 40 * 3493951 * 2
def baseEnd_3493951 : Nat := 1196050830838243089562745

theorem tailTrace_3493951 : CollatzResearch.WordTrace tailWord_3493951 prefixEnd_3493951 1196050830838243089562745 := by
  unfold tailWord_3493951
  simp only [CollatzResearch.WordTrace]
  refine ⟨127434862165019721168657707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84956574776679814112438471 127434862165019721168657707)
  ·
    refine ⟨191152293247529581752986561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127434862165019721168657707 191152293247529581752986561)
    ·
      refine ⟨143364219935647186314739921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191152293247529581752986561 143364219935647186314739921)
      ·
        refine ⟨107523164951735389736054941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143364219935647186314739921 107523164951735389736054941)
        ·
          refine ⟨40321186856900771151020603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107523164951735389736054941 40321186856900771151020603)
          ·
            refine ⟨60481780285351156726530905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40321186856900771151020603 60481780285351156726530905)
            ·
              refine ⟨45361335214013367544898179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60481780285351156726530905 45361335214013367544898179)
              ·
                refine ⟨68042002821020051317347269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45361335214013367544898179 68042002821020051317347269)
                ·
                  refine ⟨12757875528941259622002613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68042002821020051317347269 12757875528941259622002613)
                  ·
                    refine ⟨1196050830838243089562745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12757875528941259622002613 1196050830838243089562745)
                    ·
                      rfl

theorem cell22_3493951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_3493951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493951 prefixEnd_3493951 := by exact prefixLift 3493951
  have htrace : WordTrace (prefixWord ++ tailWord_3493951) baseStart_3493951 baseEnd_3493951 := by
    simpa [prefixWord, tailWord_3493951, baseEnd_3493951] using wordTrace_append hprefix tailTrace_3493951
  have hstable : (prefixWord ++ tailWord_3493951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493951).length < 2 ^ (prefixWord ++ tailWord_3493951).sum := by decide
  have hdescent : baseEnd_3493951 < baseStart_3493951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493953 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 7]
def baseStart_3493953 : Nat := 118140960795 + 3493953 * 2 ^ 59
def prefixEnd_3493953 : Nat := 4983230072969 + 3 ^ 40 * 3493953 * 2
def baseEnd_3493953 : Nat := 398683838493038583670913

theorem tailTrace_3493953 : CollatzResearch.WordTrace tailWord_3493953 prefixEnd_3493953 398683838493038583670913 := by
  unfold tailWord_3493953
  simp only [CollatzResearch.WordTrace]
  refine ⟨127434935111012475510230513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84956623407341650340153675 127434935111012475510230513)
  ·
    refine ⟨95576201333259356632672885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127434935111012475510230513 95576201333259356632672885)
    ·
      refine ⟨8960268874993064684313083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95576201333259356632672885 8960268874993064684313083)
      ·
        refine ⟨13440403312489597026469625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8960268874993064684313083 13440403312489597026469625)
        ·
          refine ⟨10080302484367197769852219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13440403312489597026469625 10080302484367197769852219)
          ·
            refine ⟨15120453726550796654778329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10080302484367197769852219 15120453726550796654778329)
            ·
              refine ⟨11340340294913097491083747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15120453726550796654778329 11340340294913097491083747)
              ·
                refine ⟨17010510442369646236625621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11340340294913097491083747 17010510442369646236625621)
                ·
                  refine ⟨398683838493038583670913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17010510442369646236625621 398683838493038583670913)
                  ·
                    rfl

theorem cell22_3493953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_3493953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493953 prefixEnd_3493953 := by exact prefixLift 3493953
  have htrace : WordTrace (prefixWord ++ tailWord_3493953) baseStart_3493953 baseEnd_3493953 := by
    simpa [prefixWord, tailWord_3493953, baseEnd_3493953] using wordTrace_append hprefix tailTrace_3493953
  have hstable : (prefixWord ++ tailWord_3493953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493953).length < 2 ^ (prefixWord ++ tailWord_3493953).sum := by decide
  have hdescent : baseEnd_3493953 < baseStart_3493953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493970 : List Nat := [3, 2, 2, 1, 4, 1, 1, 3, 5]
def baseStart_3493970 : Nat := 118140960795 + 3493970 * 2 ^ 59
def prefixEnd_3493970 : Nat := 4983230072969 + 3 ^ 40 * 3493970 * 2
def baseEnd_3493970 : Nat := 398685778308844457779229

theorem tailTrace_3493970 : CollatzResearch.WordTrace tailWord_3493970 prefixEnd_3493970 398685778308844457779229 := by
  unfold tailWord_3493970
  simp only [CollatzResearch.WordTrace]
  refine ⟨31858888787987721853399841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84957036767967258275732909 31858888787987721853399841)
  ·
    refine ⟨23894166590990791390049881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31858888787987721853399841 23894166590990791390049881)
    ·
      refine ⟨17920624943243093542537411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23894166590990791390049881 17920624943243093542537411)
      ·
        refine ⟨26880937414864640313806117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17920624943243093542537411 26880937414864640313806117)
        ·
          refine ⟨5040175765287120058838647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26880937414864640313806117 5040175765287120058838647)
          ·
            refine ⟨7560263647930680088257971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5040175765287120058838647 7560263647930680088257971)
            ·
              refine ⟨11340395471896020132386957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7560263647930680088257971 11340395471896020132386957)
              ·
                refine ⟨4252648301961007549645109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11340395471896020132386957 4252648301961007549645109)
                ·
                  refine ⟨398685778308844457779229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4252648301961007549645109 398685778308844457779229)
                  ·
                    rfl

theorem cell22_3493970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_3493970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493970 prefixEnd_3493970 := by exact prefixLift 3493970
  have htrace : WordTrace (prefixWord ++ tailWord_3493970) baseStart_3493970 baseEnd_3493970 := by
    simpa [prefixWord, tailWord_3493970, baseEnd_3493970] using wordTrace_append hprefix tailTrace_3493970
  have hstable : (prefixWord ++ tailWord_3493970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493970).length < 2 ^ (prefixWord ++ tailWord_3493970).sum := by decide
  have hdescent : baseEnd_3493970 < baseStart_3493970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493983 : List Nat := [1, 1, 2, 3, 1, 1, 2, 6, 1, 4]
def baseStart_3493983 : Nat := 118140960795 + 3493983 * 2 ^ 59
def prefixEnd_3493983 : Nat := 4983230072969 + 3 ^ 40 * 3493983 * 2
def baseEnd_3493983 : Nat := 1196061785092205672762647

theorem tailTrace_3493983 : CollatzResearch.WordTrace tailWord_3493983 prefixEnd_3493983 1196061785092205672762647 := by
  unfold tailWord_3493983
  simp only [CollatzResearch.WordTrace]
  refine ⟨127436029300903790633822603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84957352867269193755881735 127436029300903790633822603)
  ·
    refine ⟨191154043951355685950733905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127436029300903790633822603 191154043951355685950733905)
    ·
      refine ⟨143365532963516764463050429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191154043951355685950733905 143365532963516764463050429)
      ·
        refine ⟨53762074861318786673643911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143365532963516764463050429 53762074861318786673643911)
        ·
          refine ⟨80643112291978180010465867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53762074861318786673643911 80643112291978180010465867)
          ·
            refine ⟨120964668437967270015698801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80643112291978180010465867 120964668437967270015698801)
            ·
              refine ⟨90723501328475452511774101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120964668437967270015698801 90723501328475452511774101)
              ·
                refine ⟨4252664124772286836489411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90723501328475452511774101 4252664124772286836489411)
                ·
                  refine ⟨6378996187158430254734117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4252664124772286836489411 6378996187158430254734117)
                  ·
                    refine ⟨1196061785092205672762647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6378996187158430254734117 1196061785092205672762647)
                    ·
                      rfl

theorem cell22_3493983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_3493983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3493983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3493983 prefixEnd_3493983 := by exact prefixLift 3493983
  have htrace : WordTrace (prefixWord ++ tailWord_3493983) baseStart_3493983 baseEnd_3493983 := by
    simpa [prefixWord, tailWord_3493983, baseEnd_3493983] using wordTrace_append hprefix tailTrace_3493983
  have hstable : (prefixWord ++ tailWord_3493983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493983).length < 2 ^ (prefixWord ++ tailWord_3493983).sum := by decide
  have hdescent : baseEnd_3493983 < baseStart_3493983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494011 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 5, 6]
def baseStart_3494011 : Nat := 118140960795 + 3494011 * 2 ^ 59
def prefixEnd_3494011 : Nat := 4983230072969 + 3 ^ 40 * 3494011 * 2
def baseEnd_3494011 : Nat := 1196071370064422933062561

theorem tailTrace_3494011 : CollatzResearch.WordTrace tailWord_3494011 prefixEnd_3494011 1196071370064422933062561 := by
  unfold tailWord_3494011
  simp only [CollatzResearch.WordTrace]
  refine ⟨127437050544802351415841887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84958033696534900943894591 127437050544802351415841887)
  ·
    refine ⟨191155575817203527123762831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127437050544802351415841887 191155575817203527123762831)
    ·
      refine ⟨286733363725805290685644247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191155575817203527123762831 286733363725805290685644247)
      ·
        refine ⟨430100045588707936028466371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286733363725805290685644247 430100045588707936028466371)
        ·
          refine ⟨645150068383061904042699557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430100045588707936028466371 645150068383061904042699557)
          ·
            refine ⟨120965637821824107008006167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 645150068383061904042699557 120965637821824107008006167)
            ·
              refine ⟨181448456732736160512009251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120965637821824107008006167 181448456732736160512009251)
              ·
                refine ⟨272172685099104240768013877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181448456732736160512009251 272172685099104240768013877)
                ·
                  refine ⟨25516189228041022572001301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272172685099104240768013877 25516189228041022572001301)
                  ·
                    refine ⟨1196071370064422933062561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25516189228041022572001301 1196071370064422933062561)
                    ·
                      rfl

theorem cell22_3494011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_3494011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494011 prefixEnd_3494011 := by exact prefixLift 3494011
  have htrace : WordTrace (prefixWord ++ tailWord_3494011) baseStart_3494011 baseEnd_3494011 := by
    simpa [prefixWord, tailWord_3494011, baseEnd_3494011] using wordTrace_append hprefix tailTrace_3494011
  have hstable : (prefixWord ++ tailWord_3494011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494011).length < 2 ^ (prefixWord ++ tailWord_3494011).sum := by decide
  have hdescent : baseEnd_3494011 < baseStart_3494011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494045 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_3494045 : Nat := 118140960795 + 3494045 * 2 ^ 59
def prefixEnd_3494045 : Nat := 4983230072969 + 3 ^ 40 * 3494045 * 2
def baseEnd_3494045 : Nat := 1196083008959258177712457

theorem tailTrace_3494045 : CollatzResearch.WordTrace tailWord_3494045 prefixEnd_3494045 1196083008959258177712457 := by
  unfold tailWord_3494045
  simp only [CollatzResearch.WordTrace]
  refine ⟨127438290626679175222579589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84958860417786116815053059 127438290626679175222579589)
  ·
    refine ⟨23894679492502345354233673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127438290626679175222579589 23894679492502345354233673)
    ·
      refine ⟨17921009619376759015675255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23894679492502345354233673 17921009619376759015675255)
      ·
        refine ⟨26881514429065138523512883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17921009619376759015675255 26881514429065138523512883)
        ·
          refine ⟨40322271643597707785269325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26881514429065138523512883 40322271643597707785269325)
          ·
            refine ⟨15120851866349140419475997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40322271643597707785269325 15120851866349140419475997)
            ·
              refine ⟨5670319449880927657303499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15120851866349140419475997 5670319449880927657303499)
              ·
                refine ⟨8505479174821391485955249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5670319449880927657303499 8505479174821391485955249)
                ·
                  refine ⟨6379109381116043614466437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8505479174821391485955249 6379109381116043614466437)
                  ·
                    refine ⟨1196083008959258177712457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6379109381116043614466437 1196083008959258177712457)
                    ·
                      rfl

theorem cell22_3494045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_3494045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494045 prefixEnd_3494045 := by exact prefixLift 3494045
  have htrace : WordTrace (prefixWord ++ tailWord_3494045) baseStart_3494045 baseEnd_3494045 := by
    simpa [prefixWord, tailWord_3494045, baseEnd_3494045] using wordTrace_append hprefix tailTrace_3494045
  have hstable : (prefixWord ++ tailWord_3494045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494045).length < 2 ^ (prefixWord ++ tailWord_3494045).sum := by decide
  have hdescent : baseEnd_3494045 < baseStart_3494045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494075 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 3, 3]
def baseStart_3494075 : Nat := 118140960795 + 3494075 * 2 ^ 59
def prefixEnd_3494075 : Nat := 4983230072969 + 3 ^ 40 * 3494075 * 2
def baseEnd_3494075 : Nat := 1196093278572348099462365

theorem tailTrace_3494075 : CollatzResearch.WordTrace tailWord_3494075 prefixEnd_3494075 1196093278572348099462365 := by
  unfold tailWord_3494075
  simp only [CollatzResearch.WordTrace]
  refine ⟨127439384816570490346171679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84959589877713660230781119 127439384816570490346171679)
  ·
    refine ⟨191159077224855735519257519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127439384816570490346171679 191159077224855735519257519)
    ·
      refine ⟨286738615837283603278886279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191159077224855735519257519 286738615837283603278886279)
      ·
        refine ⟨430107923755925404918329419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286738615837283603278886279 430107923755925404918329419)
        ·
          refine ⟨645161885633888107377494129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430107923755925404918329419 645161885633888107377494129)
          ·
            refine ⟨483871414225416080533120597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645161885633888107377494129 483871414225416080533120597)
            ·
              refine ⟨5670368135454094693747507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 483871414225416080533120597 5670368135454094693747507)
              ·
                refine ⟨8505552203181142040621261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5670368135454094693747507 8505552203181142040621261)
                ·
                  refine ⟨3189582076192928265232973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8505552203181142040621261 3189582076192928265232973)
                  ·
                    refine ⟨1196093278572348099462365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3189582076192928265232973 1196093278572348099462365)
                    ·
                      rfl

theorem cell22_3494075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 3].length) (baseStart_3494075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494075 prefixEnd_3494075 := by exact prefixLift 3494075
  have htrace : WordTrace (prefixWord ++ tailWord_3494075) baseStart_3494075 baseEnd_3494075 := by
    simpa [prefixWord, tailWord_3494075, baseEnd_3494075] using wordTrace_append hprefix tailTrace_3494075
  have hstable : (prefixWord ++ tailWord_3494075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494075).length < 2 ^ (prefixWord ++ tailWord_3494075).sum := by decide
  have hdescent : baseEnd_3494075 < baseStart_3494075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494081 : List Nat := [1, 2, 6, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3494081 : Nat := 118140960795 + 3494081 * 2 ^ 59
def prefixEnd_3494081 : Nat := 4983230072969 + 3 ^ 40 * 3494081 * 2
def baseEnd_3494081 : Nat := 1196095332494966083812347

theorem tailTrace_3494081 : CollatzResearch.WordTrace tailWord_3494081 prefixEnd_3494081 1196095332494966083812347 := by
  unfold tailWord_3494081
  simp only [CollatzResearch.WordTrace]
  refine ⟨127439603654548753370890097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84959735769699168913926731 127439603654548753370890097)
  ·
    refine ⟨95579702740911565028167573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127439603654548753370890097 95579702740911565028167573)
    ·
      refine ⟨4480298565980229610695355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95579702740911565028167573 4480298565980229610695355)
      ·
        refine ⟨6720447848970344416043033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4480298565980229610695355 6720447848970344416043033)
        ·
          refine ⟨5040335886727758312032275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6720447848970344416043033 5040335886727758312032275)
          ·
            refine ⟨7560503830091637468048413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5040335886727758312032275 7560503830091637468048413)
            ·
              refine ⟨2835188936284364050518155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7560503830091637468048413 2835188936284364050518155)
              ·
                refine ⟨4252783404426546075777233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835188936284364050518155 4252783404426546075777233)
                ·
                  refine ⟨3189587553319909556832925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4252783404426546075777233 3189587553319909556832925)
                  ·
                    refine ⟨1196095332494966083812347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3189587553319909556832925 1196095332494966083812347)
                    ·
                      rfl

theorem cell22_3494081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3494081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494081 prefixEnd_3494081 := by exact prefixLift 3494081
  have htrace : WordTrace (prefixWord ++ tailWord_3494081) baseStart_3494081 baseEnd_3494081 := by
    simpa [prefixWord, tailWord_3494081, baseEnd_3494081] using wordTrace_append hprefix tailTrace_3494081
  have hstable : (prefixWord ++ tailWord_3494081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494081).length < 2 ^ (prefixWord ++ tailWord_3494081).sum := by decide
  have hdescent : baseEnd_3494081 < baseStart_3494081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494152 : List Nat := [2, 1, 3, 2, 3, 1, 3, 2, 1, 4]
def baseStart_3494152 : Nat := 118140960795 + 3494152 * 2 ^ 59
def prefixEnd_3494152 : Nat := 4983230072969 + 3 ^ 40 * 3494152 * 2
def baseEnd_3494152 : Nat := 1196119637245945565287129

theorem tailTrace_3494152 : CollatzResearch.WordTrace tailWord_3494152 prefixEnd_3494152 1196119637245945565287129 := by
  unfold tailWord_3494152
  simp only [CollatzResearch.WordTrace]
  refine ⟨63721096618645766248362355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84961462158194354997816473 63721096618645766248362355)
  ·
    refine ⟨95581644927968649372543533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63721096618645766248362355 95581644927968649372543533)
    ·
      refine ⟨35843116847988243514703825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95581644927968649372543533 35843116847988243514703825)
      ·
        refine ⟨26882337635991182636027869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35843116847988243514703825 26882337635991182636027869)
        ·
          refine ⟨10080876613496693488510451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26882337635991182636027869 10080876613496693488510451)
          ·
            refine ⟨15121314920245040232765677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10080876613496693488510451 15121314920245040232765677)
            ·
              refine ⟨5670493095091890087287129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15121314920245040232765677 5670493095091890087287129)
              ·
                refine ⟨4252869821318917565465347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5670493095091890087287129 4252869821318917565465347)
                ·
                  refine ⟨6379304731978376348198021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4252869821318917565465347 6379304731978376348198021)
                  ·
                    refine ⟨1196119637245945565287129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6379304731978376348198021 1196119637245945565287129)
                    ·
                      rfl

theorem cell22_3494152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_3494152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494152 prefixEnd_3494152 := by exact prefixLift 3494152
  have htrace : WordTrace (prefixWord ++ tailWord_3494152) baseStart_3494152 baseEnd_3494152 := by
    simpa [prefixWord, tailWord_3494152, baseEnd_3494152] using wordTrace_append hprefix tailTrace_3494152
  have hstable : (prefixWord ++ tailWord_3494152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494152).length < 2 ^ (prefixWord ++ tailWord_3494152).sum := by decide
  have hdescent : baseEnd_3494152 < baseStart_3494152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494163 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 1, 6]
def baseStart_3494163 : Nat := 118140960795 + 3494163 * 2 ^ 59
def prefixEnd_3494163 : Nat := 4983230072969 + 3 ^ 40 * 3494163 * 2
def baseEnd_3494163 : Nat := 1196123402770745203262095

theorem tailTrace_3494163 : CollatzResearch.WordTrace tailWord_3494163 prefixEnd_3494163 1196123402770745203262095 := by
  unfold tailWord_3494163
  simp only [CollatzResearch.WordTrace]
  refine ⟨127442594440251681375375143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84961729626834454250250095 127442594440251681375375143)
  ·
    refine ⟨191163891660377522063062715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127442594440251681375375143 191163891660377522063062715)
    ·
      refine ⟨286745837490566283094594073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191163891660377522063062715 286745837490566283094594073)
      ·
        refine ⟨215059378117924712320945555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286745837490566283094594073 215059378117924712320945555)
        ·
          refine ⟨322589067176887068481418333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215059378117924712320945555 322589067176887068481418333)
          ·
            refine ⟨120970900191332650680531875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322589067176887068481418333 120970900191332650680531875)
            ·
              refine ⟨181456350286998976020797813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120970900191332650680531875 181456350286998976020797813)
              ·
                refine ⟨17011532839406154001949795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181456350286998976020797813 17011532839406154001949795)
                ·
                  refine ⟨25517299259109231002924693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17011532839406154001949795 25517299259109231002924693)
                  ·
                    refine ⟨1196123402770745203262095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25517299259109231002924693 1196123402770745203262095)
                    ·
                      rfl

theorem cell22_3494163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_3494163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494163 prefixEnd_3494163 := by exact prefixLift 3494163
  have htrace : WordTrace (prefixWord ++ tailWord_3494163) baseStart_3494163 baseEnd_3494163 := by
    simpa [prefixWord, tailWord_3494163, baseEnd_3494163] using wordTrace_append hprefix tailTrace_3494163
  have hstable : (prefixWord ++ tailWord_3494163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494163).length < 2 ^ (prefixWord ++ tailWord_3494163).sum := by decide
  have hdescent : baseEnd_3494163 < baseStart_3494163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494165 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 6, 3]
def baseStart_3494165 : Nat := 118140960795 + 3494165 * 2 ^ 59
def prefixEnd_3494165 : Nat := 4983230072969 + 3 ^ 40 * 3494165 * 2
def baseEnd_3494165 : Nat := 1196124087411617864712089

theorem tailTrace_3494165 : CollatzResearch.WordTrace tailWord_3494165 prefixEnd_3494165 1196124087411617864712089 := by
  unfold tailWord_3494165
  simp only [CollatzResearch.WordTrace]
  refine ⟨127442667386244435716947949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84961778257496290477965299 127442667386244435716947949)
  ·
    refine ⟨47791000269841663393855481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127442667386244435716947949 47791000269841663393855481)
    ·
      refine ⟨35843250202381247545391611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47791000269841663393855481 35843250202381247545391611)
      ·
        refine ⟨53764875303571871318087417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35843250202381247545391611 53764875303571871318087417)
        ·
          refine ⟨40323656477678903488565563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53764875303571871318087417 40323656477678903488565563)
          ·
            refine ⟨60485484716518355232848345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40323656477678903488565563 60485484716518355232848345)
            ·
              refine ⟨45364113537388766424636259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60485484716518355232848345 45364113537388766424636259)
              ·
                refine ⟨68046170306083149636954389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45364113537388766424636259 68046170306083149636954389)
                ·
                  refine ⟨3189664233097647639232237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68046170306083149636954389 3189664233097647639232237)
                  ·
                    refine ⟨1196124087411617864712089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3189664233097647639232237 1196124087411617864712089)
                    ·
                      rfl

theorem cell22_3494165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_3494165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494165 prefixEnd_3494165 := by exact prefixLift 3494165
  have htrace : WordTrace (prefixWord ++ tailWord_3494165) baseStart_3494165 baseEnd_3494165 := by
    simpa [prefixWord, tailWord_3494165, baseEnd_3494165] using wordTrace_append hprefix tailTrace_3494165
  have hstable : (prefixWord ++ tailWord_3494165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494165).length < 2 ^ (prefixWord ++ tailWord_3494165).sum := by decide
  have hdescent : baseEnd_3494165 < baseStart_3494165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494184 : List Nat := [2, 1, 5, 1, 3, 1, 1, 4, 4]
def baseStart_3494184 : Nat := 118140960795 + 3494184 * 2 ^ 59
def prefixEnd_3494184 : Nat := 4983230072969 + 3 ^ 40 * 3494184 * 2
def baseEnd_3494184 : Nat := 398710197166636049495677

theorem tailTrace_3494184 : CollatzResearch.WordTrace tailWord_3494184 prefixEnd_3494184 398710197166636049495677 := by
  unfold tailWord_3494184
  simp only [CollatzResearch.WordTrace]
  refine ⟨63721680186587800980944803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84962240248783734641259737 63721680186587800980944803)
  ·
    refine ⟨95582520279881701471417205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63721680186587800980944803 95582520279881701471417205)
    ·
      refine ⟨8960861276238909512945363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95582520279881701471417205 8960861276238909512945363)
      ·
        refine ⟨13441291914358364269418045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8960861276238909512945363 13441291914358364269418045)
        ·
          refine ⟨5040484467884386601031767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13441291914358364269418045 5040484467884386601031767)
          ·
            refine ⟨7560726701826579901547651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5040484467884386601031767 7560726701826579901547651)
            ·
              refine ⟨11341090052739869852321477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7560726701826579901547651 11341090052739869852321477)
              ·
                refine ⟨2126454384888725597310277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11341090052739869852321477 2126454384888725597310277)
                ·
                  refine ⟨398710197166636049495677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2126454384888725597310277 398710197166636049495677)
                  ·
                    rfl

theorem cell22_3494184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 4].length) (baseStart_3494184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494184 prefixEnd_3494184 := by exact prefixLift 3494184
  have htrace : WordTrace (prefixWord ++ tailWord_3494184) baseStart_3494184 baseEnd_3494184 := by
    simpa [prefixWord, tailWord_3494184, baseEnd_3494184] using wordTrace_append hprefix tailTrace_3494184
  have hstable : (prefixWord ++ tailWord_3494184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494184).length < 2 ^ (prefixWord ++ tailWord_3494184).sum := by decide
  have hdescent : baseEnd_3494184 < baseStart_3494184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494244 : List Nat := [2, 3, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_3494244 : Nat := 118140960795 + 3494244 * 2 ^ 59
def prefixEnd_3494244 : Nat := 4983230072969 + 3 ^ 40 * 3494244 * 2
def baseEnd_3494244 : Nat := 1196151130726087991986847

theorem tailTrace_3494244 : CollatzResearch.WordTrace tailWord_3494244 prefixEnd_3494244 1196151130726087991986847 := by
  unfold tailWord_3494244
  simp only [CollatzResearch.WordTrace]
  refine ⟨63722774376479116104536893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84963699168638821472715857 63722774376479116104536893)
  ·
    refine ⟨23896040391179668539201335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63722774376479116104536893 23896040391179668539201335)
    ·
      refine ⟨35844060586769502808802003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23896040391179668539201335 35844060586769502808802003)
      ·
        refine ⟨53766090880154254213203005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35844060586769502808802003 53766090880154254213203005)
        ·
          refine ⟨20162284080057845329951127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53766090880154254213203005 20162284080057845329951127)
          ·
            refine ⟨30243426120086767994926691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20162284080057845329951127 30243426120086767994926691)
            ·
              refine ⟨45365139180130151992390037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30243426120086767994926691 45365139180130151992390037)
              ·
                refine ⟨2126490899068600874643283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45365139180130151992390037 2126490899068600874643283)
                ·
                  refine ⟨3189736348602901311964925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126490899068600874643283 3189736348602901311964925)
                  ·
                    refine ⟨1196151130726087991986847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3189736348602901311964925 1196151130726087991986847)
                    ·
                      rfl

theorem cell22_3494244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_3494244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494244 prefixEnd_3494244 := by exact prefixLift 3494244
  have htrace : WordTrace (prefixWord ++ tailWord_3494244) baseStart_3494244 baseEnd_3494244 := by
    simpa [prefixWord, tailWord_3494244, baseEnd_3494244] using wordTrace_append hprefix tailTrace_3494244
  have hstable : (prefixWord ++ tailWord_3494244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494244).length < 2 ^ (prefixWord ++ tailWord_3494244).sum := by decide
  have hdescent : baseEnd_3494244 < baseStart_3494244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494413 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3494413 : Nat := 118140960795 + 3494413 * 2 ^ 59
def prefixEnd_3494413 : Nat := 4983230072969 + 3 ^ 40 * 3494413 * 2
def baseEnd_3494413 : Nat := 1196208982879827884511329

theorem tailTrace_3494413 : CollatzResearch.WordTrace tailWord_3494413 prefixEnd_3494413 1196208982879827884511329 := by
  unfold tailWord_3494413
  simp only [CollatzResearch.WordTrace]
  refine ⟨127451712689345974071975893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84967808459563982714650595 127451712689345974071975893)
  ·
    refine ⟨2987149516156546267311935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 127451712689345974071975893 2987149516156546267311935)
    ·
      refine ⟨4480724274234819400967903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2987149516156546267311935 4480724274234819400967903)
      ·
        refine ⟨6721086411352229101451855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4480724274234819400967903 6721086411352229101451855)
        ·
          refine ⟨10081629617028343652177783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6721086411352229101451855 10081629617028343652177783)
          ·
            refine ⟨15122444425542515478266675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10081629617028343652177783 15122444425542515478266675)
            ·
              refine ⟨22683666638313773217400013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15122444425542515478266675 22683666638313773217400013)
              ·
                refine ⟨8506374989367664956525005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22683666638313773217400013 8506374989367664956525005)
                ·
                  refine ⟨3189890621012874358696877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8506374989367664956525005 3189890621012874358696877)
                  ·
                    refine ⟨1196208982879827884511329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3189890621012874358696877 1196208982879827884511329)
                    ·
                      rfl

theorem cell22_3494413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3494413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494413 prefixEnd_3494413 := by exact prefixLift 3494413
  have htrace : WordTrace (prefixWord ++ tailWord_3494413) baseStart_3494413 baseEnd_3494413 := by
    simpa [prefixWord, tailWord_3494413, baseEnd_3494413] using wordTrace_append hprefix tailTrace_3494413
  have hstable : (prefixWord ++ tailWord_3494413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494413).length < 2 ^ (prefixWord ++ tailWord_3494413).sum := by decide
  have hdescent : baseEnd_3494413 < baseStart_3494413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494437 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 6]
def baseStart_3494437 : Nat := 118140960795 + 3494437 * 2 ^ 59
def prefixEnd_3494437 : Nat := 4983230072969 + 3 ^ 40 * 3494437 * 2
def baseEnd_3494437 : Nat := 398739066190099940637085

theorem tailTrace_3494437 : CollatzResearch.WordTrace tailWord_3494437 prefixEnd_3494437 398739066190099940637085 := by
  unfold tailWord_3494437
  simp only [CollatzResearch.WordTrace]
  refine ⟨127452588041259026170849565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84968392027506017447233043 127452588041259026170849565)
  ·
    refine ⟨47794720515472134814068587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127452588041259026170849565 47794720515472134814068587)
    ·
      refine ⟨71692080773208202221102881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47794720515472134814068587 71692080773208202221102881)
      ·
        refine ⟨53769060579906151665827161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71692080773208202221102881 53769060579906151665827161)
        ·
          refine ⟨40326795434929613749370371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53769060579906151665827161 40326795434929613749370371)
          ·
            refine ⟨60490193152394420624055557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40326795434929613749370371 60490193152394420624055557)
            ·
              refine ⟨11341911216073953867010417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60490193152394420624055557 11341911216073953867010417)
              ·
                refine ⟨8506433412055465400257813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11341911216073953867010417 8506433412055465400257813)
                ·
                  refine ⟨398739066190099940637085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8506433412055465400257813 398739066190099940637085)
                  ·
                    rfl

theorem cell22_3494437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_3494437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494437 prefixEnd_3494437 := by exact prefixLift 3494437
  have htrace : WordTrace (prefixWord ++ tailWord_3494437) baseStart_3494437 baseEnd_3494437 := by
    simpa [prefixWord, tailWord_3494437, baseEnd_3494437] using wordTrace_append hprefix tailTrace_3494437
  have hstable : (prefixWord ++ tailWord_3494437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494437).length < 2 ^ (prefixWord ++ tailWord_3494437).sum := by decide
  have hdescent : baseEnd_3494437 < baseStart_3494437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494469 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 4, 3]
def baseStart_3494469 : Nat := 118140960795 + 3494469 * 2 ^ 59
def prefixEnd_3494469 : Nat := 4983230072969 + 3 ^ 40 * 3494469 * 2
def baseEnd_3494469 : Nat := 1196228152824262405111157

theorem tailTrace_3494469 : CollatzResearch.WordTrace tailWord_3494469 prefixEnd_3494469 1196228152824262405111157 := by
  unfold tailWord_3494469
  simp only [CollatzResearch.WordTrace]
  refine ⟨127453755177143095636014461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84969170118095397090676307 127453755177143095636014461)
  ·
    refine ⟨47795158191428660863505423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127453755177143095636014461 47795158191428660863505423)
    ·
      refine ⟨71692737287142991295258135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47795158191428660863505423 71692737287142991295258135)
      ·
        refine ⟨107539105930714486942887203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71692737287142991295258135 107539105930714486942887203)
        ·
          refine ⟨161308658896071730414330805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107539105930714486942887203 161308658896071730414330805)
          ·
            refine ⟨15122686771506724726343513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161308658896071730414330805 15122686771506724726343513)
            ·
              refine ⟨11342015078630043544757635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15122686771506724726343513 11342015078630043544757635)
              ·
                refine ⟨17013022617945065317136453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11342015078630043544757635 17013022617945065317136453)
                ·
                  refine ⟨3189941740864699746963085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17013022617945065317136453 3189941740864699746963085)
                  ·
                    refine ⟨1196228152824262405111157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3189941740864699746963085 1196228152824262405111157)
                    ·
                      rfl

theorem cell22_3494469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_3494469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494469 prefixEnd_3494469 := by exact prefixLift 3494469
  have htrace : WordTrace (prefixWord ++ tailWord_3494469) baseStart_3494469 baseEnd_3494469 := by
    simpa [prefixWord, tailWord_3494469, baseEnd_3494469] using wordTrace_append hprefix tailTrace_3494469
  have hstable : (prefixWord ++ tailWord_3494469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494469).length < 2 ^ (prefixWord ++ tailWord_3494469).sum := by decide
  have hdescent : baseEnd_3494469 < baseStart_3494469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494501 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_3494501 : Nat := 118140960795 + 3494501 * 2 ^ 59
def prefixEnd_3494501 : Nat := 4983230072969 + 3 ^ 40 * 3494501 * 2
def baseEnd_3494501 : Nat := 1196239107078224988311059

theorem tailTrace_3494501 : CollatzResearch.WordTrace tailWord_3494501 prefixEnd_3494501 1196239107078224988311059 := by
  unfold tailWord_3494501
  simp only [CollatzResearch.WordTrace]
  refine ⟨127454922313027165101179357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84969948208684776734119571 127454922313027165101179357)
  ·
    refine ⟨47795595867385186912942259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127454922313027165101179357 47795595867385186912942259)
    ·
      refine ⟨71693393801077780369413389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47795595867385186912942259 71693393801077780369413389)
      ·
        refine ⟨26885022675404167638530021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71693393801077780369413389 26885022675404167638530021)
        ·
          refine ⟨5040941751638281432224379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26885022675404167638530021 5040941751638281432224379)
          ·
            refine ⟨7561412627457422148336569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5040941751638281432224379 7561412627457422148336569)
            ·
              refine ⟨5671059470593066611252427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7561412627457422148336569 5671059470593066611252427)
              ·
                refine ⟨8506589205889599916878641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5671059470593066611252427 8506589205889599916878641)
                ·
                  refine ⟨6379941904417199937658981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8506589205889599916878641 6379941904417199937658981)
                  ·
                    refine ⟨1196239107078224988311059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6379941904417199937658981 1196239107078224988311059)
                    ·
                      rfl

theorem cell22_3494501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_3494501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494501 prefixEnd_3494501 := by exact prefixLift 3494501
  have htrace : WordTrace (prefixWord ++ tailWord_3494501) baseStart_3494501 baseEnd_3494501 := by
    simpa [prefixWord, tailWord_3494501, baseEnd_3494501] using wordTrace_append hprefix tailTrace_3494501
  have hstable : (prefixWord ++ tailWord_3494501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494501).length < 2 ^ (prefixWord ++ tailWord_3494501).sum := by decide
  have hdescent : baseEnd_3494501 < baseStart_3494501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494548 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_3494548 : Nat := 118140960795 + 3494548 * 2 ^ 59
def prefixEnd_3494548 : Nat := 4983230072969 + 3 ^ 40 * 3494548 * 2
def baseEnd_3494548 : Nat := 1196255196138732532385915

theorem tailTrace_3494548 : CollatzResearch.WordTrace tailWord_3494548 prefixEnd_3494548 1196255196138732532385915 := by
  unfold tailWord_3494548
  simp only [CollatzResearch.WordTrace]
  refine ⟨63728318271928446064070149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84971091029237928085426865 63728318271928446064070149)
  ·
    refine ⟨11949059675986583637013153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63728318271928446064070149 11949059675986583637013153)
    ·
      refine ⟨8961794756989937727759865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11949059675986583637013153 8961794756989937727759865)
      ·
        refine ⟨6721346067742453295819899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8961794756989937727759865 6721346067742453295819899)
        ·
          refine ⟨10082019101613679943729849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6721346067742453295819899 10082019101613679943729849)
          ·
            refine ⟨7561514326210259957797387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10082019101613679943729849 7561514326210259957797387)
            ·
              refine ⟨11342271489315389936696081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7561514326210259957797387 11342271489315389936696081)
              ·
                refine ⟨8506703616986542452522061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11342271489315389936696081 8506703616986542452522061)
                ·
                  refine ⟨3190013856369953419695773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8506703616986542452522061 3190013856369953419695773)
                  ·
                    refine ⟨1196255196138732532385915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3190013856369953419695773 1196255196138732532385915)
                    ·
                      rfl

theorem cell22_3494548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_3494548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494548 prefixEnd_3494548 := by exact prefixLift 3494548
  have htrace : WordTrace (prefixWord ++ tailWord_3494548) baseStart_3494548 baseEnd_3494548 := by
    simpa [prefixWord, tailWord_3494548, baseEnd_3494548] using wordTrace_append hprefix tailTrace_3494548
  have hstable : (prefixWord ++ tailWord_3494548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494548).length < 2 ^ (prefixWord ++ tailWord_3494548).sum := by decide
  have hdescent : baseEnd_3494548 < baseStart_3494548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494587 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 2, 9]
def baseStart_3494587 : Nat := 118140960795 + 3494587 * 2 ^ 59
def prefixEnd_3494587 : Nat := 4983230072969 + 3 ^ 40 * 3494587 * 2
def baseEnd_3494587 : Nat := 1196268546635749430660795

theorem tailTrace_3494587 : CollatzResearch.WordTrace tailWord_3494587 prefixEnd_3494587 1196268546635749430660795 := by
  unfold tailWord_3494587
  simp only [CollatzResearch.WordTrace]
  refine ⟨127458058990715601788810015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84972039327143734525873343 127458058990715601788810015)
  ·
    refine ⟨191187088486073402683215023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127458058990715601788810015 191187088486073402683215023)
    ·
      refine ⟨286780632729110104024822535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191187088486073402683215023 286780632729110104024822535)
      ·
        refine ⟨430170949093665156037233803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286780632729110104024822535 430170949093665156037233803)
        ·
          refine ⟨645256423640497734055850705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430170949093665156037233803 645256423640497734055850705)
          ·
            refine ⟨483942317730373300541888029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645256423640497734055850705 483942317730373300541888029)
            ·
              refine ⟨181478369148889987703208011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483942317730373300541888029 181478369148889987703208011)
              ·
                refine ⟨272217553723334981554812017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181478369148889987703208011 272217553723334981554812017)
                ·
                  refine ⟨204163165292501236166109013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272217553723334981554812017 204163165292501236166109013)
                  ·
                    refine ⟨1196268546635749430660795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 204163165292501236166109013 1196268546635749430660795)
                    ·
                      rfl

theorem cell22_3494587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_3494587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494587 prefixEnd_3494587 := by exact prefixLift 3494587
  have htrace : WordTrace (prefixWord ++ tailWord_3494587) baseStart_3494587 baseEnd_3494587 := by
    simpa [prefixWord, tailWord_3494587, baseEnd_3494587] using wordTrace_append hprefix tailTrace_3494587
  have hstable : (prefixWord ++ tailWord_3494587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494587).length < 2 ^ (prefixWord ++ tailWord_3494587).sum := by decide
  have hdescent : baseEnd_3494587 < baseStart_3494587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494589 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 6]
def baseStart_3494589 : Nat := 118140960795 + 3494589 * 2 ^ 59
def prefixEnd_3494589 : Nat := 4983230072969 + 3 ^ 40 * 3494589 * 2
def baseEnd_3494589 : Nat := 398756410425540697370263

theorem tailTrace_3494589 : CollatzResearch.WordTrace tailWord_3494589 prefixEnd_3494589 398756410425540697370263 := by
  unfold tailWord_3494589
  simp only [CollatzResearch.WordTrace]
  refine ⟨127458131936708356130382821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84972087957805570753588547 127458131936708356130382821)
  ·
    refine ⟨23898399738132816774446779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127458131936708356130382821 23898399738132816774446779)
    ·
      refine ⟨35847599607199225161670169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23898399738132816774446779 35847599607199225161670169)
      ·
        refine ⟨26885699705399418871252627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35847599607199225161670169 26885699705399418871252627)
        ·
          refine ⟨40328549558099128306878941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26885699705399418871252627 40328549558099128306878941)
          ·
            refine ⟨15123206084287173115079603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40328549558099128306878941 15123206084287173115079603)
            ·
              refine ⟨22684809126430759672619405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15123206084287173115079603 22684809126430759672619405)
              ·
                refine ⟨8506803422411534877232277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22684809126430759672619405 8506803422411534877232277)
                ·
                  refine ⟨398756410425540697370263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8506803422411534877232277 398756410425540697370263)
                  ·
                    rfl

theorem cell22_3494589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_3494589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494589 prefixEnd_3494589 := by exact prefixLift 3494589
  have htrace : WordTrace (prefixWord ++ tailWord_3494589) baseStart_3494589 baseEnd_3494589 := by
    simpa [prefixWord, tailWord_3494589, baseEnd_3494589] using wordTrace_append hprefix tailTrace_3494589
  have hstable : (prefixWord ++ tailWord_3494589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494589).length < 2 ^ (prefixWord ++ tailWord_3494589).sum := by decide
  have hdescent : baseEnd_3494589 < baseStart_3494589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494623 : List Nat := [1, 1, 2, 3, 2, 5, 1, 3, 4]
def baseStart_3494623 : Nat := 118140960795 + 3494623 * 2 ^ 59
def prefixEnd_3494623 : Nat := 4983230072969 + 3 ^ 40 * 3494623 * 2
def baseEnd_3494623 : Nat := 398760290057152445586895

theorem tailTrace_3494623 : CollatzResearch.WordTrace tailWord_3494623 prefixEnd_3494623 398760290057152445586895 := by
  unfold tailWord_3494623
  simp only [CollatzResearch.WordTrace]
  refine ⟨127459372018585179937120523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84972914679056786624747015 127459372018585179937120523)
  ·
    refine ⟨191189058027877769905680785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127459372018585179937120523 191189058027877769905680785)
    ·
      refine ⟨143391793520908327429260589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191189058027877769905680785 143391793520908327429260589)
      ·
        refine ⟨53771922570340622785972721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143391793520908327429260589 53771922570340622785972721)
        ·
          refine ⟨40328941927755467089479541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53771922570340622785972721 40328941927755467089479541)
          ·
            refine ⟨3780838305727075039638707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40328941927755467089479541 3780838305727075039638707)
            ·
              refine ⟨5671257458590612559458061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3780838305727075039638707 5671257458590612559458061)
              ·
                refine ⟨2126721546971479709796773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5671257458590612559458061 2126721546971479709796773)
                ·
                  refine ⟨398760290057152445586895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2126721546971479709796773 398760290057152445586895)
                  ·
                    rfl

theorem cell22_3494623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 4].length) (baseStart_3494623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494623 prefixEnd_3494623 := by exact prefixLift 3494623
  have htrace : WordTrace (prefixWord ++ tailWord_3494623) baseStart_3494623 baseEnd_3494623 := by
    simpa [prefixWord, tailWord_3494623, baseEnd_3494623] using wordTrace_append hprefix tailTrace_3494623
  have hstable : (prefixWord ++ tailWord_3494623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494623).length < 2 ^ (prefixWord ++ tailWord_3494623).sum := by decide
  have hdescent : baseEnd_3494623 < baseStart_3494623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494666 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 5, 3]
def baseStart_3494666 : Nat := 118140960795 + 3494666 * 2 ^ 59
def prefixEnd_3494666 : Nat := 4983230072969 + 3 ^ 40 * 3494666 * 2
def baseEnd_3494666 : Nat := 1196295589950219557935553

theorem tailTrace_3494666 : CollatzResearch.WordTrace tailWord_3494666 prefixEnd_3494666 1196295589950219557935553 := by
  unfold tailWord_3494666
  simp only [CollatzResearch.WordTrace]
  refine ⟨31865235089357349570233963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84973960238286265520623901 31865235089357349570233963)
  ·
    refine ⟨47797852634036024355350945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31865235089357349570233963 47797852634036024355350945)
    ·
      refine ⟨35848389475527018266513209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47797852634036024355350945 35848389475527018266513209)
      ·
        refine ⟨26886292106645263699884907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35848389475527018266513209 26886292106645263699884907)
        ·
          refine ⟨40329438159967895549827361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26886292106645263699884907 40329438159967895549827361)
          ·
            refine ⟨30247078619975921662370521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40329438159967895549827361 30247078619975921662370521)
            ·
              refine ⟨22685308964981941246777891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30247078619975921662370521 22685308964981941246777891)
              ·
                refine ⟨34027963447472911870166837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22685308964981941246777891 34027963447472911870166837)
                ·
                  refine ⟨3190121573200585487828141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34027963447472911870166837 3190121573200585487828141)
                  ·
                    refine ⟨1196295589950219557935553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3190121573200585487828141 1196295589950219557935553)
                    ·
                      rfl

theorem cell22_3494666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_3494666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494666 prefixEnd_3494666 := by exact prefixLift 3494666
  have htrace : WordTrace (prefixWord ++ tailWord_3494666) baseStart_3494666 baseEnd_3494666 := by
    simpa [prefixWord, tailWord_3494666, baseEnd_3494666] using wordTrace_append hprefix tailTrace_3494666
  have hstable : (prefixWord ++ tailWord_3494666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494666).length < 2 ^ (prefixWord ++ tailWord_3494666).sum := by decide
  have hdescent : baseEnd_3494666 < baseStart_3494666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494743 : List Nat := [1, 1, 3, 2, 4, 2, 1, 3, 1, 4]
def baseStart_3494743 : Nat := 118140960795 + 3494743 * 2 ^ 59
def prefixEnd_3494743 : Nat := 4983230072969 + 3 ^ 40 * 3494743 * 2
def baseEnd_3494743 : Nat := 1196321948623817023760317

theorem tailTrace_3494743 : CollatzResearch.WordTrace tailWord_3494743 prefixEnd_3494743 1196321948623817023760317 := by
  unfold tailWord_3494743
  simp only [CollatzResearch.WordTrace]
  refine ⟨127463748778150440431488883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84975832518766960287659255 127463748778150440431488883)
  ·
    refine ⟨191195623167225660647233325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127463748778150440431488883 191195623167225660647233325)
    ·
      refine ⟨71698358687709622742712497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191195623167225660647233325 71698358687709622742712497)
      ·
        refine ⟨53773769015782217057034373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71698358687709622742712497 53773769015782217057034373)
        ·
          refine ⟨10082581690459165698193945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53773769015782217057034373 10082581690459165698193945)
          ·
            refine ⟨7561936267844374273645459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10082581690459165698193945 7561936267844374273645459)
            ·
              refine ⟨11342904401766561410468189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7561936267844374273645459 11342904401766561410468189)
              ·
                refine ⟨4253589150662460528925571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11342904401766561410468189 4253589150662460528925571)
                ·
                  refine ⟨6380383725993690793388357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4253589150662460528925571 6380383725993690793388357)
                  ·
                    refine ⟨1196321948623817023760317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6380383725993690793388357 1196321948623817023760317)
                    ·
                      rfl

theorem cell22_3494743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_3494743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494743 prefixEnd_3494743 := by exact prefixLift 3494743
  have htrace : WordTrace (prefixWord ++ tailWord_3494743) baseStart_3494743 baseEnd_3494743 := by
    simpa [prefixWord, tailWord_3494743, baseEnd_3494743] using wordTrace_append hprefix tailTrace_3494743
  have hstable : (prefixWord ++ tailWord_3494743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494743).length < 2 ^ (prefixWord ++ tailWord_3494743).sum := by decide
  have hdescent : baseEnd_3494743 < baseStart_3494743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494773 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3494773 : Nat := 118140960795 + 3494773 * 2 ^ 59
def prefixEnd_3494773 : Nat := 4983230072969 + 3 ^ 40 * 3494773 * 2
def baseEnd_3494773 : Nat := 1196332218236906945510225

theorem tailTrace_3494773 : CollatzResearch.WordTrace tailWord_3494773 prefixEnd_3494773 1196332218236906945510225 := by
  unfold tailWord_3494773
  simp only [CollatzResearch.WordTrace]
  refine ⟨127464842968041755555080973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84976561978694503703387315 127464842968041755555080973)
  ·
    refine ⟨47799316113015658333155365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127464842968041755555080973 47799316113015658333155365)
    ·
      refine ⟨8962371771190435937466631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47799316113015658333155365 8962371771190435937466631)
      ·
        refine ⟨13443557656785653906199947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8962371771190435937466631 13443557656785653906199947)
        ·
          refine ⟨20165336485178480859299921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13443557656785653906199947 20165336485178480859299921)
          ·
            refine ⟨15124002363883860644474941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20165336485178480859299921 15124002363883860644474941)
            ·
              refine ⟨5671500886456447741678103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15124002363883860644474941 5671500886456447741678103)
              ·
                refine ⟨8507251329684671612517155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5671500886456447741678103 8507251329684671612517155)
                ·
                  refine ⟨12760876994527007418775733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8507251329684671612517155 12760876994527007418775733)
                  ·
                    refine ⟨1196332218236906945510225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12760876994527007418775733 1196332218236906945510225)
                    ·
                      rfl

theorem cell22_3494773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3494773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494773 prefixEnd_3494773 := by exact prefixLift 3494773
  have htrace : WordTrace (prefixWord ++ tailWord_3494773) baseStart_3494773 baseEnd_3494773 := by
    simpa [prefixWord, tailWord_3494773, baseEnd_3494773] using wordTrace_append hprefix tailTrace_3494773
  have hstable : (prefixWord ++ tailWord_3494773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494773).length < 2 ^ (prefixWord ++ tailWord_3494773).sum := by decide
  have hdescent : baseEnd_3494773 < baseStart_3494773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494854 : List Nat := [6, 1, 3, 1, 2, 9]
def baseStart_3494854 : Nat := 118140960795 + 3494854 * 2 ^ 59
def prefixEnd_3494854 : Nat := 4983230072969 + 3 ^ 40 * 3494854 * 2
def baseEnd_3494854 : Nat := 14769875878916663385617

theorem tailTrace_3494854 : CollatzResearch.WordTrace tailWord_3494854 prefixEnd_3494854 14769875878916663385617 := by
  unfold tailWord_3494854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3983368665023384574649363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84978531520498870925853077 3983368665023384574649363)
  ·
    refine ⟨5975052997535076861974045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3983368665023384574649363 5975052997535076861974045)
    ·
      refine ⟨2240644874075653823240267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5975052997535076861974045 2240644874075653823240267)
      ·
        refine ⟨3360967311113480734860401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2240644874075653823240267 3360967311113480734860401)
        ·
          refine ⟨2520725483335110551145301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3360967311113480734860401 2520725483335110551145301)
          ·
            refine ⟨14769875878916663385617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2520725483335110551145301 14769875878916663385617)
            ·
              rfl

theorem cell22_3494854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 9].length) (baseStart_3494854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494854 prefixEnd_3494854 := by exact prefixLift 3494854
  have htrace : WordTrace (prefixWord ++ tailWord_3494854) baseStart_3494854 baseEnd_3494854 := by
    simpa [prefixWord, tailWord_3494854, baseEnd_3494854] using wordTrace_append hprefix tailTrace_3494854
  have hstable : (prefixWord ++ tailWord_3494854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494854).length < 2 ^ (prefixWord ++ tailWord_3494854).sum := by decide
  have hdescent : baseEnd_3494854 < baseStart_3494854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494908 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_3494908 : Nat := 118140960795 + 3494908 * 2 ^ 59
def prefixEnd_3494908 : Nat := 4983230072969 + 3 ^ 40 * 3494908 * 2
def baseEnd_3494908 : Nat := 1196378431495811593384811

theorem tailTrace_3494908 : CollatzResearch.WordTrace tailWord_3494908 prefixEnd_3494908 1196378431495811593384811 := by
  unfold tailWord_3494908
  simp only [CollatzResearch.WordTrace]
  refine ⟨63734883411276336805622689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84979844548368449074163585 63734883411276336805622689)
  ·
    refine ⟨47801162558457252604217017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63734883411276336805622689 47801162558457252604217017)
    ·
      refine ⟨35850871918842939453162763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47801162558457252604217017 35850871918842939453162763)
      ·
        refine ⟨53776307878264409179744145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35850871918842939453162763 53776307878264409179744145)
        ·
          refine ⟨40332230908698306884808109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53776307878264409179744145 40332230908698306884808109)
          ·
            refine ⟨15124586590761865081803041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40332230908698306884808109 15124586590761865081803041)
            ·
              refine ⟨11343439943071398811352281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15124586590761865081803041 11343439943071398811352281)
              ·
                refine ⟨8507579957303549108514211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11343439943071398811352281 8507579957303549108514211)
                ·
                  refine ⟨12761369935955323662771317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8507579957303549108514211 12761369935955323662771317)
                  ·
                    refine ⟨1196378431495811593384811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12761369935955323662771317 1196378431495811593384811)
                    ·
                      rfl

theorem cell22_3494908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_3494908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494908 prefixEnd_3494908 := by exact prefixLift 3494908
  have htrace : WordTrace (prefixWord ++ tailWord_3494908) baseStart_3494908 baseEnd_3494908 := by
    simpa [prefixWord, tailWord_3494908, baseEnd_3494908] using wordTrace_append hprefix tailTrace_3494908
  have hstable : (prefixWord ++ tailWord_3494908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494908).length < 2 ^ (prefixWord ++ tailWord_3494908).sum := by decide
  have hdescent : baseEnd_3494908 < baseStart_3494908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494983 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 7]
def baseStart_3494983 : Nat := 118140960795 + 3494983 * 2 ^ 59
def prefixEnd_3494983 : Nat := 4983230072969 + 3 ^ 40 * 3494983 * 2
def baseEnd_3494983 : Nat := 398801368509512132586527

theorem tailTrace_3494983 : CollatzResearch.WordTrace tailWord_3494983 prefixEnd_3494983 398801368509512132586527 := by
  unfold tailWord_3494983
  simp only [CollatzResearch.WordTrace]
  refine ⟨127472502297280961420225603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84981668198187307613483735 127472502297280961420225603)
  ·
    refine ⟨191208753445921442130338405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127472502297280961420225603 191208753445921442130338405)
    ·
      refine ⟨35851641271110270399438451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191208753445921442130338405 35851641271110270399438451)
      ·
        refine ⟨53777461906665405599157677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35851641271110270399438451 53777461906665405599157677)
        ·
          refine ⟨20166548214999527099684129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53777461906665405599157677 20166548214999527099684129)
          ·
            refine ⟨15124911161249645324763097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20166548214999527099684129 15124911161249645324763097)
            ·
              refine ⟨11343683370937233993572323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15124911161249645324763097 11343683370937233993572323)
              ·
                refine ⟨17015525056405850990358485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11343683370937233993572323 17015525056405850990358485)
                ·
                  refine ⟨398801368509512132586527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17015525056405850990358485 398801368509512132586527)
                  ·
                    rfl

theorem cell22_3494983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 7].length) (baseStart_3494983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3494983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3494983 prefixEnd_3494983 := by exact prefixLift 3494983
  have htrace : WordTrace (prefixWord ++ tailWord_3494983) baseStart_3494983 baseEnd_3494983 := by
    simpa [prefixWord, tailWord_3494983, baseEnd_3494983] using wordTrace_append hprefix tailTrace_3494983
  have hstable : (prefixWord ++ tailWord_3494983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494983).length < 2 ^ (prefixWord ++ tailWord_3494983).sum := by decide
  have hdescent : baseEnd_3494983 < baseStart_3494983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495043 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 3, 5]
def baseStart_3495043 : Nat := 118140960795 + 3495043 * 2 ^ 59
def prefixEnd_3495043 : Nat := 4983230072969 + 3 ^ 40 * 3495043 * 2
def baseEnd_3495043 : Nat := 1196424644754716241259397

theorem tailTrace_3495043 : CollatzResearch.WordTrace tailWord_3495043 prefixEnd_3495043 1196424644754716241259397 := by
  unfold tailWord_3495043
  simp only [CollatzResearch.WordTrace]
  refine ⟨127474690677063591667409783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84983127118042394444939855 127474690677063591667409783)
  ·
    refine ⟨191212036015595387501114675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127474690677063591667409783 191212036015595387501114675)
    ·
      refine ⟨286818054023393081251672013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191212036015595387501114675 286818054023393081251672013)
      ·
        refine ⟨107556770258772405469377005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286818054023393081251672013 107556770258772405469377005)
        ·
          refine ⟨40333788847039652051016377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107556770258772405469377005 40333788847039652051016377)
          ·
            refine ⟨30250341635279739038262283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40333788847039652051016377 30250341635279739038262283)
            ·
              refine ⟨45375512452919608557393425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30250341635279739038262283 45375512452919608557393425)
              ·
                refine ⟨34031634339689706418045069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45375512452919608557393425 34031634339689706418045069)
                ·
                  refine ⟨12761862877383639906766901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34031634339689706418045069 12761862877383639906766901)
                  ·
                    refine ⟨1196424644754716241259397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12761862877383639906766901 1196424644754716241259397)
                    ·
                      rfl

theorem cell22_3495043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_3495043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495043 prefixEnd_3495043 := by exact prefixLift 3495043
  have htrace : WordTrace (prefixWord ++ tailWord_3495043) baseStart_3495043 baseEnd_3495043 := by
    simpa [prefixWord, tailWord_3495043, baseEnd_3495043] using wordTrace_append hprefix tailTrace_3495043
  have hstable : (prefixWord ++ tailWord_3495043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495043).length < 2 ^ (prefixWord ++ tailWord_3495043).sum := by decide
  have hdescent : baseEnd_3495043 < baseStart_3495043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495079 : List Nat := [1, 1, 6, 2, 1, 2, 2, 3, 4]
def baseStart_3495079 : Nat := 118140960795 + 3495079 * 2 ^ 59
def prefixEnd_3495079 : Nat := 4983230072969 + 3 ^ 40 * 3495079 * 2
def baseEnd_3495079 : Nat := 398812322763474715786429

theorem tailTrace_3495079 : CollatzResearch.WordTrace tailWord_3495079 prefixEnd_3495079 398812322763474715786429 := by
  unfold tailWord_3495079
  simp only [CollatzResearch.WordTrace]
  refine ⟨127476003704933169815720291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84984002469955446543813527 127476003704933169815720291)
  ·
    refine ⟨191214005557399754723580437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127476003704933169815720291 191214005557399754723580437)
    ·
      refine ⟨8963156510503113502667833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 191214005557399754723580437 8963156510503113502667833)
      ·
        refine ⟨6722367382877335127000875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8963156510503113502667833 6722367382877335127000875)
        ·
          refine ⟨10083551074316002690501313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6722367382877335127000875 10083551074316002690501313)
          ·
            refine ⟨7562663305737002017875985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10083551074316002690501313 7562663305737002017875985)
            ·
              refine ⟨5671997479302751513406989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7562663305737002017875985 5671997479302751513406989)
              ·
                refine ⟨2126999054738531817527621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5671997479302751513406989 2126999054738531817527621)
                ·
                  refine ⟨398812322763474715786429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2126999054738531817527621 398812322763474715786429)
                  ·
                    rfl

theorem cell22_3495079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 4].length) (baseStart_3495079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495079 prefixEnd_3495079 := by exact prefixLift 3495079
  have htrace : WordTrace (prefixWord ++ tailWord_3495079) baseStart_3495079 baseEnd_3495079 := by
    simpa [prefixWord, tailWord_3495079, baseEnd_3495079] using wordTrace_append hprefix tailTrace_3495079
  have hstable : (prefixWord ++ tailWord_3495079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495079).length < 2 ^ (prefixWord ++ tailWord_3495079).sum := by decide
  have hdescent : baseEnd_3495079 < baseStart_3495079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495103 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 1, 8]
def baseStart_3495103 : Nat := 118140960795 + 3495103 * 2 ^ 59
def prefixEnd_3495103 : Nat := 4983230072969 + 3 ^ 40 * 3495103 * 2
def baseEnd_3495103 : Nat := 1196445183980896084759213

theorem tailTrace_3495103 : CollatzResearch.WordTrace tailWord_3495103 prefixEnd_3495103 1196445183980896084759213 := by
  unfold tailWord_3495103
  simp only [CollatzResearch.WordTrace]
  refine ⟨127476879056846221914593963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84984586037897481276395975 127476879056846221914593963)
  ·
    refine ⟨191215318585269332871890945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127476879056846221914593963 191215318585269332871890945)
    ·
      refine ⟨143411488938951999653918209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191215318585269332871890945 143411488938951999653918209)
      ·
        refine ⟨107558616704213999740438657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143411488938951999653918209 107558616704213999740438657)
        ·
          refine ⟨80668962528160499805328993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107558616704213999740438657 80668962528160499805328993)
          ·
            refine ⟨60501721896120374853996745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80668962528160499805328993 60501721896120374853996745)
            ·
              refine ⟨45376291422090281140497559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60501721896120374853996745 45376291422090281140497559)
              ·
                refine ⟨68064437133135421710746339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45376291422090281140497559 68064437133135421710746339)
                ·
                  refine ⟨102096655699703132566119509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68064437133135421710746339 102096655699703132566119509)
                  ·
                    refine ⟨1196445183980896084759213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102096655699703132566119509 1196445183980896084759213)
                    ·
                      rfl

theorem cell22_3495103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_3495103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495103 prefixEnd_3495103 := by exact prefixLift 3495103
  have htrace : WordTrace (prefixWord ++ tailWord_3495103) baseStart_3495103 baseEnd_3495103 := by
    simpa [prefixWord, tailWord_3495103, baseEnd_3495103] using wordTrace_append hprefix tailTrace_3495103
  have hstable : (prefixWord ++ tailWord_3495103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495103).length < 2 ^ (prefixWord ++ tailWord_3495103).sum := by decide
  have hdescent : baseEnd_3495103 < baseStart_3495103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495122 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_3495122 : Nat := 118140960795 + 3495122 * 2 ^ 59
def prefixEnd_3495122 : Nat := 4983230072969 + 3 ^ 40 * 3495122 * 2
def baseEnd_3495122 : Nat := 1196451688069186368534155

theorem tailTrace_3495122 : CollatzResearch.WordTrace tailWord_3495122 prefixEnd_3495122 1196451688069186368534155 := by
  unfold tailWord_3495122
  simp only [CollatzResearch.WordTrace]
  refine ⟨31869393010944347039883905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84985048029184925439690413 31869393010944347039883905)
  ·
    refine ⟨23902044758208260279912929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31869393010944347039883905 23902044758208260279912929)
    ·
      refine ⟨17926533568656195209934697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23902044758208260279912929 17926533568656195209934697)
      ·
        refine ⟨13444900176492146407451023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17926533568656195209934697 13444900176492146407451023)
        ·
          refine ⟨20167350264738219611176535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13444900176492146407451023 20167350264738219611176535)
          ·
            refine ⟨30251025397107329416764803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20167350264738219611176535 30251025397107329416764803)
            ·
              refine ⟨45376538095660994125147205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30251025397107329416764803 45376538095660994125147205)
              ·
                refine ⟨8508100892936436398465101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45376538095660994125147205 8508100892936436398465101)
                ·
                  refine ⟨3190537834851163649424413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8508100892936436398465101 3190537834851163649424413)
                  ·
                    refine ⟨1196451688069186368534155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3190537834851163649424413 1196451688069186368534155)
                    ·
                      rfl

theorem cell22_3495122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_3495122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495122 prefixEnd_3495122 := by exact prefixLift 3495122
  have htrace : WordTrace (prefixWord ++ tailWord_3495122) baseStart_3495122 baseEnd_3495122 := by
    simpa [prefixWord, tailWord_3495122, baseEnd_3495122] using wordTrace_append hprefix tailTrace_3495122
  have hstable : (prefixWord ++ tailWord_3495122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495122).length < 2 ^ (prefixWord ++ tailWord_3495122).sum := by decide
  have hdescent : baseEnd_3495122 < baseStart_3495122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495150 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_3495150 : Nat := 118140960795 + 3495150 * 2 ^ 59
def prefixEnd_3495150 : Nat := 4983230072969 + 3 ^ 40 * 3495150 * 2
def baseEnd_3495150 : Nat := 1196461273041403628834069

theorem tailTrace_3495150 : CollatzResearch.WordTrace tailWord_3495150 prefixEnd_3495150 1196461273041403628834069 := by
  unfold tailWord_3495150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15934824160959493617694363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84985728858450632627703269 15934824160959493617694363)
  ·
    refine ⟨23902236241439240426541545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15934824160959493617694363 23902236241439240426541545)
    ·
      refine ⟨17926677181079430319906159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23902236241439240426541545 17926677181079430319906159)
      ·
        refine ⟨26890015771619145479859239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17926677181079430319906159 26890015771619145479859239)
        ·
          refine ⟨40335023657428718219788859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26890015771619145479859239 40335023657428718219788859)
          ·
            refine ⟨60502535486143077329683289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40335023657428718219788859 60502535486143077329683289)
            ·
              refine ⟨45376901614607307997262467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60502535486143077329683289 45376901614607307997262467)
              ·
                refine ⟨68065352421910961995893701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45376901614607307997262467 68065352421910961995893701)
                ·
                  refine ⟨12762253579108305374230069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68065352421910961995893701 12762253579108305374230069)
                  ·
                    refine ⟨1196461273041403628834069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12762253579108305374230069 1196461273041403628834069)
                    ·
                      rfl

theorem cell22_3495150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_3495150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495150 prefixEnd_3495150 := by exact prefixLift 3495150
  have htrace : WordTrace (prefixWord ++ tailWord_3495150) baseStart_3495150 baseEnd_3495150 := by
    simpa [prefixWord, tailWord_3495150, baseEnd_3495150] using wordTrace_append hprefix tailTrace_3495150
  have hstable : (prefixWord ++ tailWord_3495150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495150).length < 2 ^ (prefixWord ++ tailWord_3495150).sum := by decide
  have hdescent : baseEnd_3495150 < baseStart_3495150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495169 : List Nat := [1, 2, 4, 1, 1, 5, 2, 1, 5]
def baseStart_3495169 : Nat := 118140960795 + 3495169 * 2 ^ 59
def prefixEnd_3495169 : Nat := 4983230072969 + 3 ^ 40 * 3495169 * 2
def baseEnd_3495169 : Nat := 398822592376564637536337

theorem tailTrace_3495169 : CollatzResearch.WordTrace tailWord_3495169 prefixEnd_3495169 398822592376564637536337 := by
  unfold tailWord_3495169
  simp only [CollatzResearch.WordTrace]
  refine ⟨127479286274607115186496561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84986190849738076790997707 127479286274607115186496561)
  ·
    refine ⟨95609464705955336389872421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127479286274607115186496561 95609464705955336389872421)
    ·
      refine ⟨17926774632366625573101079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95609464705955336389872421 17926774632366625573101079)
      ·
        refine ⟨26890161948549938359651619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17926774632366625573101079 26890161948549938359651619)
        ·
          refine ⟨40335242922824907539477429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26890161948549938359651619 40335242922824907539477429)
          ·
            refine ⟨3781429024014835081826009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40335242922824907539477429 3781429024014835081826009)
            ·
              refine ⟨2836071768011126311369507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3781429024014835081826009 2836071768011126311369507)
              ·
                refine ⟨4254107652016689467054261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2836071768011126311369507 4254107652016689467054261)
                ·
                  refine ⟨398822592376564637536337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4254107652016689467054261 398822592376564637536337)
                  ·
                    rfl

theorem cell22_3495169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 5].length) (baseStart_3495169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495169 prefixEnd_3495169 := by exact prefixLift 3495169
  have htrace : WordTrace (prefixWord ++ tailWord_3495169) baseStart_3495169 baseEnd_3495169 := by
    simpa [prefixWord, tailWord_3495169, baseEnd_3495169] using wordTrace_append hprefix tailTrace_3495169
  have hstable : (prefixWord ++ tailWord_3495169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495169).length < 2 ^ (prefixWord ++ tailWord_3495169).sum := by decide
  have hdescent : baseEnd_3495169 < baseStart_3495169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495182 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_3495182 : Nat := 118140960795 + 3495182 * 2 ^ 59
def prefixEnd_3495182 : Nat := 4983230072969 + 3 ^ 40 * 3495182 * 2
def baseEnd_3495182 : Nat := 1196472227295366212033971

theorem tailTrace_3495182 : CollatzResearch.WordTrace tailWord_3495182 prefixEnd_3495182 1196472227295366212033971 := by
  unfold tailWord_3495182
  simp only [CollatzResearch.WordTrace]
  refine ⟨15934970052945002300839975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84986506949040012271146533 15934970052945002300839975)
  ·
    refine ⟨23902455079417503451259963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15934970052945002300839975 23902455079417503451259963)
    ·
      refine ⟨35853682619126255176889945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23902455079417503451259963 35853682619126255176889945)
      ·
        refine ⟨26890261964344691382667459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35853682619126255176889945 26890261964344691382667459)
        ·
          refine ⟨40335392946517037074001189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26890261964344691382667459 40335392946517037074001189)
          ·
            refine ⟨7562886177471944451375223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40335392946517037074001189 7562886177471944451375223)
            ·
              refine ⟨11344329266207916677062835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7562886177471944451375223 11344329266207916677062835)
              ·
                refine ⟨17016493899311875015594253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11344329266207916677062835 17016493899311875015594253)
                ·
                  refine ⟨6381185212241953130847845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17016493899311875015594253 6381185212241953130847845)
                  ·
                    refine ⟨1196472227295366212033971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6381185212241953130847845 1196472227295366212033971)
                    ·
                      rfl

theorem cell22_3495182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_3495182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495182 prefixEnd_3495182 := by exact prefixLift 3495182
  have htrace : WordTrace (prefixWord ++ tailWord_3495182) baseStart_3495182 baseEnd_3495182 := by
    simpa [prefixWord, tailWord_3495182, baseEnd_3495182] using wordTrace_append hprefix tailTrace_3495182
  have hstable : (prefixWord ++ tailWord_3495182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495182).length < 2 ^ (prefixWord ++ tailWord_3495182).sum := by decide
  have hdescent : baseEnd_3495182 < baseStart_3495182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495244 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 2, 4]
def baseStart_3495244 : Nat := 118140960795 + 3495244 * 2 ^ 59
def prefixEnd_3495244 : Nat := 4983230072969 + 3 ^ 40 * 3495244 * 2
def baseEnd_3495244 : Nat := 1196493451162418716983781

theorem tailTrace_3495244 : CollatzResearch.WordTrace tailWord_3495244 prefixEnd_3495244 1196493451162418716983781 := by
  unfold tailWord_3495244
  simp only [CollatzResearch.WordTrace]
  refine ⟨63741010874667701497738393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84988014499556935330317857 63741010874667701497738393)
  ·
    refine ⟨47805758156000776123303795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63741010874667701497738393 47805758156000776123303795)
    ·
      refine ⟨71708637234001164184955693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47805758156000776123303795 71708637234001164184955693)
      ·
        refine ⟨26890738962750436569358385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71708637234001164184955693 26890738962750436569358385)
        ·
          refine ⟨20168054222062827427018789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26890738962750436569358385 20168054222062827427018789)
          ·
            refine ⟨3781510166636780142566023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20168054222062827427018789 3781510166636780142566023)
            ·
              refine ⟨5672265249955170213849035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781510166636780142566023 5672265249955170213849035)
              ·
                refine ⟨8508397874932755320773553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5672265249955170213849035 8508397874932755320773553)
                ·
                  refine ⟨6381298406199566490580165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8508397874932755320773553 6381298406199566490580165)
                  ·
                    refine ⟨1196493451162418716983781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6381298406199566490580165 1196493451162418716983781)
                    ·
                      rfl

theorem cell22_3495244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_3495244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495244 prefixEnd_3495244 := by exact prefixLift 3495244
  have htrace : WordTrace (prefixWord ++ tailWord_3495244) baseStart_3495244 baseEnd_3495244 := by
    simpa [prefixWord, tailWord_3495244, baseEnd_3495244] using wordTrace_append hprefix tailTrace_3495244
  have hstable : (prefixWord ++ tailWord_3495244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495244).length < 2 ^ (prefixWord ++ tailWord_3495244).sum := by decide
  have hdescent : baseEnd_3495244 < baseStart_3495244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495364 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3495364 : Nat := 118140960795 + 3495364 * 2 ^ 59
def prefixEnd_3495364 : Nat := 4983230072969 + 3 ^ 40 * 3495364 * 2
def baseEnd_3495364 : Nat := 1196534529614778403983413

theorem tailTrace_3495364 : CollatzResearch.WordTrace tailWord_3495364 prefixEnd_3495364 1196534529614778403983413 := by
  unfold tailWord_3495364
  simp only [CollatzResearch.WordTrace]
  refine ⟨63743199254450331744922573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84990932339267108993230097 63743199254450331744922573)
  ·
    refine ⟨23903699720418874404345965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63743199254450331744922573 23903699720418874404345965)
    ·
      refine ⟨8963887395157077901629737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23903699720418874404345965 8963887395157077901629737)
      ·
        refine ⟨6722915546367808426222303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8963887395157077901629737 6722915546367808426222303)
        ·
          refine ⟨10084373319551712639333455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6722915546367808426222303 10084373319551712639333455)
          ·
            refine ⟨15126559979327568959000183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10084373319551712639333455 15126559979327568959000183)
            ·
              refine ⟨22689839968991353438500275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15126559979327568959000183 22689839968991353438500275)
              ·
                refine ⟨34034759953487030157750413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22689839968991353438500275 34034759953487030157750413)
                ·
                  refine ⟨12763034982557636309156405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34034759953487030157750413 12763034982557636309156405)
                  ·
                    refine ⟨1196534529614778403983413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12763034982557636309156405 1196534529614778403983413)
                    ·
                      rfl

theorem cell22_3495364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3495364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495364 prefixEnd_3495364 := by exact prefixLift 3495364
  have htrace : WordTrace (prefixWord ++ tailWord_3495364) baseStart_3495364 baseEnd_3495364 := by
    simpa [prefixWord, tailWord_3495364, baseEnd_3495364] using wordTrace_append hprefix tailTrace_3495364
  have hstable : (prefixWord ++ tailWord_3495364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495364).length < 2 ^ (prefixWord ++ tailWord_3495364).sum := by decide
  have hdescent : baseEnd_3495364 < baseStart_3495364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495381 : List Nat := [1, 3, 2, 3, 1, 1, 4, 2, 2, 3]
def baseStart_3495381 : Nat := 118140960795 + 3495381 * 2 ^ 59
def prefixEnd_3495381 : Nat := 4983230072969 + 3 ^ 40 * 3495381 * 2
def baseEnd_3495381 : Nat := 1196540349062196026308361

theorem tailTrace_3495381 : CollatzResearch.WordTrace tailWord_3495381 prefixEnd_3495381 1196540349062196026308361 := by
  unfold tailWord_3495381
  simp only [CollatzResearch.WordTrace]
  refine ⟨127487018549839075393213997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84991345699892716928809331 127487018549839075393213997)
  ·
    refine ⟨47807631956189653272455249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127487018549839075393213997 47807631956189653272455249)
    ·
      refine ⟨35855723967142239954341437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47807631956189653272455249 35855723967142239954341437)
      ·
        refine ⟨13445896487678339982878039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35855723967142239954341437 13445896487678339982878039)
        ·
          refine ⟨20168844731517509974317059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13445896487678339982878039 20168844731517509974317059)
          ·
            refine ⟨30253267097276264961475589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20168844731517509974317059 30253267097276264961475589)
            ·
              refine ⟨5672487580739299680276673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30253267097276264961475589 5672487580739299680276673)
              ·
                refine ⟨4254365685554474760207505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5672487580739299680276673 4254365685554474760207505)
                ·
                  refine ⟨3190774264165856070155629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4254365685554474760207505 3190774264165856070155629)
                  ·
                    refine ⟨1196540349062196026308361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3190774264165856070155629 1196540349062196026308361)
                    ·
                      rfl

theorem cell22_3495381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_3495381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495381 prefixEnd_3495381 := by exact prefixLift 3495381
  have htrace : WordTrace (prefixWord ++ tailWord_3495381) baseStart_3495381 baseEnd_3495381 := by
    simpa [prefixWord, tailWord_3495381, baseEnd_3495381] using wordTrace_append hprefix tailTrace_3495381
  have hstable : (prefixWord ++ tailWord_3495381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495381).length < 2 ^ (prefixWord ++ tailWord_3495381).sum := by decide
  have hdescent : baseEnd_3495381 < baseStart_3495381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495409 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 5, 3]
def baseStart_3495409 : Nat := 118140960795 + 3495409 * 2 ^ 59
def prefixEnd_3495409 : Nat := 4983230072969 + 3 ^ 40 * 3495409 * 2
def baseEnd_3495409 : Nat := 1196549934034413286608275

theorem tailTrace_3495409 : CollatzResearch.WordTrace tailWord_3495409 prefixEnd_3495409 1196549934034413286608275 := by
  unfold tailWord_3495409
  simp only [CollatzResearch.WordTrace]
  refine ⟨127488039793737636175233281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84992026529158424116822187 127488039793737636175233281)
  ·
    refine ⟨95616029845303227131424961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127488039793737636175233281 95616029845303227131424961)
    ·
      refine ⟨71712022383977420348568721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95616029845303227131424961 71712022383977420348568721)
      ·
        refine ⟨53784016787983065261426541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71712022383977420348568721 53784016787983065261426541)
        ·
          refine ⟨20169006295493649473034953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53784016787983065261426541 20169006295493649473034953)
          ·
            refine ⟨15126754721620237104776215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20169006295493649473034953 15126754721620237104776215)
            ·
              refine ⟨22690132082430355657164323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15126754721620237104776215 22690132082430355657164323)
              ·
                refine ⟨34035198123645533485746485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22690132082430355657164323 34035198123645533485746485)
                ·
                  refine ⟨3190799824091768764288733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34035198123645533485746485 3190799824091768764288733)
                  ·
                    refine ⟨1196549934034413286608275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3190799824091768764288733 1196549934034413286608275)
                    ·
                      rfl

theorem cell22_3495409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_3495409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495409 prefixEnd_3495409 := by exact prefixLift 3495409
  have htrace : WordTrace (prefixWord ++ tailWord_3495409) baseStart_3495409 baseEnd_3495409 := by
    simpa [prefixWord, tailWord_3495409, baseEnd_3495409] using wordTrace_append hprefix tailTrace_3495409
  have hstable : (prefixWord ++ tailWord_3495409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495409).length < 2 ^ (prefixWord ++ tailWord_3495409).sum := by decide
  have hdescent : baseEnd_3495409 < baseStart_3495409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495413 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3495413 : Nat := 118140960795 + 3495413 * 2 ^ 59
def prefixEnd_3495413 : Nat := 4983230072969 + 3 ^ 40 * 3495413 * 2
def baseEnd_3495413 : Nat := 1196551303316158609508263

theorem tailTrace_3495413 : CollatzResearch.WordTrace tailWord_3495413 prefixEnd_3495413 1196551303316158609508263 := by
  unfold tailWord_3495413
  simp only [CollatzResearch.WordTrace]
  refine ⟨127488185685723144858378893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84992123790482096572252595 127488185685723144858378893)
  ·
    refine ⟨47808069632146179321892085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127488185685723144858378893 47808069632146179321892085)
    ·
      refine ⟨4482006528013704311427383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47808069632146179321892085 4482006528013704311427383)
      ·
        refine ⟨6723009792020556467141075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4482006528013704311427383 6723009792020556467141075)
        ·
          refine ⟨10084514688030834700711613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6723009792020556467141075 10084514688030834700711613)
          ·
            refine ⟨3781693008011563012766855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10084514688030834700711613 3781693008011563012766855)
            ·
              refine ⟨5672539512017344519150283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781693008011563012766855 5672539512017344519150283)
              ·
                refine ⟨8508809268026016778725425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5672539512017344519150283 8508809268026016778725425)
                ·
                  refine ⟨6381606951019512584044069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8508809268026016778725425 6381606951019512584044069)
                  ·
                    refine ⟨1196551303316158609508263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6381606951019512584044069 1196551303316158609508263)
                    ·
                      rfl

theorem cell22_3495413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3495413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495413 prefixEnd_3495413 := by exact prefixLift 3495413
  have htrace : WordTrace (prefixWord ++ tailWord_3495413) baseStart_3495413 baseEnd_3495413 := by
    simpa [prefixWord, tailWord_3495413, baseEnd_3495413] using wordTrace_append hprefix tailTrace_3495413
  have hstable : (prefixWord ++ tailWord_3495413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495413).length < 2 ^ (prefixWord ++ tailWord_3495413).sum := by decide
  have hdescent : baseEnd_3495413 < baseStart_3495413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495494 : List Nat := [6, 1, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_3495494 : Nat := 118140960795 + 3495494 * 2 ^ 59
def prefixEnd_3495494 : Nat := 4983230072969 + 3 ^ 40 * 3495494 * 2
def baseEnd_3495494 : Nat := 1196579031271501398233015

theorem tailTrace_3495494 : CollatzResearch.WordTrace tailWord_3495494 prefixEnd_3495494 1196579031271501398233015 := by
  unfold tailWord_3495494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3984098124950927990377423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84994093332286463794718357 3984098124950927990377423)
  ·
    refine ⟨5976147187426391985566135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3984098124950927990377423 5976147187426391985566135)
    ·
      refine ⟨8964220781139587978349203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5976147187426391985566135 8964220781139587978349203)
      ·
        refine ⟨13446331171709381967523805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8964220781139587978349203 13446331171709381967523805)
        ·
          refine ⟨5042374189391018237821427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13446331171709381967523805 5042374189391018237821427)
          ·
            refine ⟨7563561284086527356732141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5042374189391018237821427 7563561284086527356732141)
            ·
              refine ⟨2836335481532447758774553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7563561284086527356732141 2836335481532447758774553)
              ·
                refine ⟨2127251611149335819080915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2836335481532447758774553 2127251611149335819080915)
                ·
                  refine ⟨3190877416724003728621373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2127251611149335819080915 3190877416724003728621373)
                  ·
                    refine ⟨1196579031271501398233015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3190877416724003728621373 1196579031271501398233015)
                    ·
                      rfl

theorem cell22_3495494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_3495494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495494 prefixEnd_3495494 := by exact prefixLift 3495494
  have htrace : WordTrace (prefixWord ++ tailWord_3495494) baseStart_3495494 baseEnd_3495494 := by
    simpa [prefixWord, tailWord_3495494, baseEnd_3495494] using wordTrace_append hprefix tailTrace_3495494
  have hstable : (prefixWord ++ tailWord_3495494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495494).length < 2 ^ (prefixWord ++ tailWord_3495494).sum := by decide
  have hdescent : baseEnd_3495494 < baseStart_3495494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495559 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 2, 6]
def baseStart_3495559 : Nat := 118140960795 + 3495559 * 2 ^ 59
def prefixEnd_3495559 : Nat := 4983230072969 + 3 ^ 40 * 3495559 * 2
def baseEnd_3495559 : Nat := 1196601282099862895357815

theorem tailTrace_3495559 : CollatzResearch.WordTrace tailWord_3495559 prefixEnd_3495559 1196601282099862895357815 := by
  unfold tailWord_3495559
  simp only [CollatzResearch.WordTrace]
  refine ⟨127493510743194211793193731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84995673828796141195462487 127493510743194211793193731)
  ·
    refine ⟨191240266114791317689790597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127493510743194211793193731 191240266114791317689790597)
    ·
      refine ⟨35857549896523372066835737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191240266114791317689790597 35857549896523372066835737)
      ·
        refine ⟨26893162422392529050126803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35857549896523372066835737 26893162422392529050126803)
        ·
          refine ⟨40339743633588793575190205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26893162422392529050126803 40339743633588793575190205)
          ·
            refine ⟨15127403862595797590696327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40339743633588793575190205 15127403862595797590696327)
            ·
              refine ⟨22691105793893696386044491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15127403862595797590696327 22691105793893696386044491)
              ·
                refine ⟨34036658690840544579066737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22691105793893696386044491 34036658690840544579066737)
                ·
                  refine ⟨25527494018130408434300053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34036658690840544579066737 25527494018130408434300053)
                  ·
                    refine ⟨1196601282099862895357815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25527494018130408434300053 1196601282099862895357815)
                    ·
                      rfl

theorem cell22_3495559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_3495559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495559 prefixEnd_3495559 := by exact prefixLift 3495559
  have htrace : WordTrace (prefixWord ++ tailWord_3495559) baseStart_3495559 baseEnd_3495559 := by
    simpa [prefixWord, tailWord_3495559, baseEnd_3495559] using wordTrace_append hprefix tailTrace_3495559
  have hstable : (prefixWord ++ tailWord_3495559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495559).length < 2 ^ (prefixWord ++ tailWord_3495559).sum := by decide
  have hdescent : baseEnd_3495559 < baseStart_3495559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495698 : List Nat := [3, 2, 4, 1, 1, 1, 2, 8]
def baseStart_3495698 : Nat := 118140960795 + 3495698 * 2 ^ 59
def prefixEnd_3495698 : Nat := 4983230072969 + 3 ^ 40 * 3495698 * 2
def baseEnd_3495698 : Nat := 132960984960056985125821

theorem tailTrace_3495698 : CollatzResearch.WordTrace tailWord_3495698 prefixEnd_3495698 132960984960056985125821 := by
  unfold tailWord_3495698
  simp only [CollatzResearch.WordTrace]
  refine ⟨31874645122422659633125937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84999053659793759021669165 31874645122422659633125937)
  ·
    refine ⟨23905983841816994724844453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31874645122422659633125937 23905983841816994724844453)
    ·
      refine ⟨4482371970340686510908335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23905983841816994724844453 4482371970340686510908335)
      ·
        refine ⟨6723557955511029766362503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4482371970340686510908335 6723557955511029766362503)
        ·
          refine ⟨10085336933266544649543755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6723557955511029766362503 10085336933266544649543755)
          ·
            refine ⟨15128005399899816974315633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10085336933266544649543755 15128005399899816974315633)
            ·
              refine ⟨11346004049924862730736725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15128005399899816974315633 11346004049924862730736725)
              ·
                refine ⟨132960984960056985125821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11346004049924862730736725 132960984960056985125821)
                ·
                  rfl

theorem cell22_3495698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_3495698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495698 prefixEnd_3495698 := by exact prefixLift 3495698
  have htrace : WordTrace (prefixWord ++ tailWord_3495698) baseStart_3495698 baseEnd_3495698 := by
    simpa [prefixWord, tailWord_3495698, baseEnd_3495698] using wordTrace_append hprefix tailTrace_3495698
  have hstable : (prefixWord ++ tailWord_3495698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495698).length < 2 ^ (prefixWord ++ tailWord_3495698).sum := by decide
  have hdescent : baseEnd_3495698 < baseStart_3495698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495788 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 6]
def baseStart_3495788 : Nat := 118140960795 + 3495788 * 2 ^ 59
def prefixEnd_3495788 : Nat := 4983230072969 + 3 ^ 40 * 3495788 * 2
def baseEnd_3495788 : Nat := 398893224493260877127371

theorem tailTrace_3495788 : CollatzResearch.WordTrace tailWord_3495788 prefixEnd_3495788 398893224493260877127371 := by
  unfold tailWord_3495788
  simp only [CollatzResearch.WordTrace]
  refine ⟨63750931529682291951640009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85001242039576389268853345 63750931529682291951640009)
  ·
    refine ⟨47813198647261718963730007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63750931529682291951640009 47813198647261718963730007)
    ·
      refine ⟨71719797970892578445595011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47813198647261718963730007 71719797970892578445595011)
      ·
        refine ⟨107579696956338867668392517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71719797970892578445595011 107579696956338867668392517)
        ·
          refine ⟨20171193179313537687823597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107579696956338867668392517 20171193179313537687823597)
          ·
            refine ⟨7564197442242576632933849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20171193179313537687823597 7564197442242576632933849)
            ·
              refine ⟨5673148081681932474700387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7564197442242576632933849 5673148081681932474700387)
              ·
                refine ⟨8509722122522898712050581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673148081681932474700387 8509722122522898712050581)
                ·
                  refine ⟨398893224493260877127371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8509722122522898712050581 398893224493260877127371)
                  ·
                    rfl

theorem cell22_3495788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_3495788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495788 prefixEnd_3495788 := by exact prefixLift 3495788
  have htrace : WordTrace (prefixWord ++ tailWord_3495788) baseStart_3495788 baseEnd_3495788 := by
    simpa [prefixWord, tailWord_3495788, baseEnd_3495788] using wordTrace_append hprefix tailTrace_3495788
  have hstable : (prefixWord ++ tailWord_3495788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495788).length < 2 ^ (prefixWord ++ tailWord_3495788).sum := by decide
  have hdescent : baseEnd_3495788 < baseStart_3495788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495801 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 3, 6]
def baseStart_3495801 : Nat := 118140960795 + 3495801 * 2 ^ 59
def prefixEnd_3495801 : Nat := 4983230072969 + 3 ^ 40 * 3495801 * 2
def baseEnd_3495801 : Nat := 1196684123645454930807073

theorem tailTrace_3495801 : CollatzResearch.WordTrace tailWord_3495801 prefixEnd_3495801 1196684123645454930807073 := by
  unfold tailWord_3495801
  simp only [CollatzResearch.WordTrace]
  refine ⟨127502337208317487123503257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85001558138878324749002171 127502337208317487123503257)
  ·
    refine ⟨95626752906238115342627443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127502337208317487123503257 95626752906238115342627443)
    ·
      refine ⟨143440129359357173013941165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95626752906238115342627443 143440129359357173013941165)
      ·
        refine ⟨53790048509758939880227937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143440129359357173013941165 53790048509758939880227937)
        ·
          refine ⟨40342536382319204910170953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53790048509758939880227937 40342536382319204910170953)
          ·
            refine ⟨30256902286739403682628215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40342536382319204910170953 30256902286739403682628215)
            ·
              refine ⟨45385353430109105523942323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30256902286739403682628215 45385353430109105523942323)
              ·
                refine ⟨68078030145163658285913485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45385353430109105523942323 68078030145163658285913485)
                ·
                  refine ⟨25529261304436371857217557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68078030145163658285913485 25529261304436371857217557)
                  ·
                    refine ⟨1196684123645454930807073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25529261304436371857217557 1196684123645454930807073)
                    ·
                      rfl

theorem cell22_3495801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_3495801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495801 prefixEnd_3495801 := by exact prefixLift 3495801
  have htrace : WordTrace (prefixWord ++ tailWord_3495801) baseStart_3495801 baseEnd_3495801 := by
    simpa [prefixWord, tailWord_3495801, baseEnd_3495801] using wordTrace_append hprefix tailTrace_3495801
  have hstable : (prefixWord ++ tailWord_3495801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495801).length < 2 ^ (prefixWord ++ tailWord_3495801).sum := by decide
  have hdescent : baseEnd_3495801 < baseStart_3495801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495908 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_3495908 : Nat := 118140960795 + 3495908 * 2 ^ 59
def prefixEnd_3495908 : Nat := 4983230072969 + 3 ^ 40 * 3495908 * 2
def baseEnd_3495908 : Nat := 1196720751932142318381745

theorem tailTrace_3495908 : CollatzResearch.WordTrace tailWord_3495908 prefixEnd_3495908 1196720751932142318381745 := by
  unfold tailWord_3495908
  simp only [CollatzResearch.WordTrace]
  refine ⟨63753119909464922198824189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85004159879286562931765585 63753119909464922198824189)
  ·
    refine ⟨23907419966049345824559071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63753119909464922198824189 23907419966049345824559071)
    ·
      refine ⟨35861129949074018736838607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23907419966049345824559071 35861129949074018736838607)
      ·
        refine ⟨53791694923611028105257911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35861129949074018736838607 53791694923611028105257911)
        ·
          refine ⟨80687542385416542157886867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53791694923611028105257911 80687542385416542157886867)
          ·
            refine ⟨121031313578124813236830301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80687542385416542157886867 121031313578124813236830301)
            ·
              refine ⟨45386742591796804963811363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121031313578124813236830301 45386742591796804963811363)
              ·
                refine ⟨68080113887695207445717045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45386742591796804963811363 68080113887695207445717045)
                ·
                  refine ⟨6382510676971425698035973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68080113887695207445717045 6382510676971425698035973)
                  ·
                    refine ⟨1196720751932142318381745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6382510676971425698035973 1196720751932142318381745)
                    ·
                      rfl

theorem cell22_3495908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_3495908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495908 prefixEnd_3495908 := by exact prefixLift 3495908
  have htrace : WordTrace (prefixWord ++ tailWord_3495908) baseStart_3495908 baseEnd_3495908 := by
    simpa [prefixWord, tailWord_3495908, baseEnd_3495908] using wordTrace_append hprefix tailTrace_3495908
  have hstable : (prefixWord ++ tailWord_3495908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495908).length < 2 ^ (prefixWord ++ tailWord_3495908).sum := by decide
  have hdescent : baseEnd_3495908 < baseStart_3495908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495985 : List Nat := [1, 2, 2, 3, 1, 3, 4, 6]
def baseStart_3495985 : Nat := 118140960795 + 3495985 * 2 ^ 59
def prefixEnd_3495985 : Nat := 4983230072969 + 3 ^ 40 * 3495985 * 2
def baseEnd_3495985 : Nat := 132971901178415531578501

theorem tailTrace_3495985 : CollatzResearch.WordTrace tailWord_3495985 prefixEnd_3495985 132971901178415531578501 := by
  unfold tailWord_3495985
  simp only [CollatzResearch.WordTrace]
  refine ⟨127509048239650886548201409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85006032159767257698800939 127509048239650886548201409)
  ·
    refine ⟨95631786179738164911151057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127509048239650886548201409 95631786179738164911151057)
    ·
      refine ⟨71723839634803623683363293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95631786179738164911151057 71723839634803623683363293)
      ·
        refine ⟨26896439863051358881261235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71723839634803623683363293 26896439863051358881261235)
        ·
          refine ⟨40344659794577038321891853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26896439863051358881261235 40344659794577038321891853)
          ·
            refine ⟨15129247422966389370709445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40344659794577038321891853 15129247422966389370709445)
            ·
              refine ⟨2836733891806198007008021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15129247422966389370709445 2836733891806198007008021)
              ·
                refine ⟨132971901178415531578501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2836733891806198007008021 132971901178415531578501)
                ·
                  rfl

theorem cell22_3495985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 6].length) (baseStart_3495985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3495985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3495985 prefixEnd_3495985 := by exact prefixLift 3495985
  have htrace : WordTrace (prefixWord ++ tailWord_3495985) baseStart_3495985 baseEnd_3495985 := by
    simpa [prefixWord, tailWord_3495985, baseEnd_3495985] using wordTrace_append hprefix tailTrace_3495985
  have hstable : (prefixWord ++ tailWord_3495985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495985).length < 2 ^ (prefixWord ++ tailWord_3495985).sum := by decide
  have hdescent : baseEnd_3495985 < baseStart_3495985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496109 : List Nat := [1, 5, 2, 1, 2, 1, 1, 5, 4]
def baseStart_3496109 : Nat := 118140960795 + 3496109 * 2 ^ 59
def prefixEnd_3496109 : Nat := 4983230072969 + 3 ^ 40 * 3496109 * 2
def baseEnd_3496109 : Nat := 398929852779948264702043

theorem tailTrace_3496109 : CollatzResearch.WordTrace tailWord_3496109 prefixEnd_3496109 398929852779948264702043 := by
  unfold tailWord_3496109
  simp only [CollatzResearch.WordTrace]
  refine ⟨127513570891201655725715381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85009047260801103817143587 127513570891201655725715381)
  ·
    refine ⟨11954397271050155224285817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127513570891201655725715381 11954397271050155224285817)
    ·
      refine ⟨8965797953287616418214363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11954397271050155224285817 8965797953287616418214363)
      ·
        refine ⟨13448696929931424627321545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8965797953287616418214363 13448696929931424627321545)
        ·
          refine ⟨10086522697448568470491159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13448696929931424627321545 10086522697448568470491159)
          ·
            refine ⟨15129784046172852705736739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10086522697448568470491159 15129784046172852705736739)
            ·
              refine ⟨22694676069259279058605109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15129784046172852705736739 22694676069259279058605109)
              ·
                refine ⟨2127625881493057411744229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22694676069259279058605109 2127625881493057411744229)
                ·
                  refine ⟨398929852779948264702043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2127625881493057411744229 398929852779948264702043)
                  ·
                    rfl

theorem cell22_3496109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_3496109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496109 prefixEnd_3496109 := by exact prefixLift 3496109
  have htrace : WordTrace (prefixWord ++ tailWord_3496109) baseStart_3496109 baseEnd_3496109 := by
    simpa [prefixWord, tailWord_3496109, baseEnd_3496109] using wordTrace_append hprefix tailTrace_3496109
  have hstable : (prefixWord ++ tailWord_3496109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496109).length < 2 ^ (prefixWord ++ tailWord_3496109).sum := by decide
  have hdescent : baseEnd_3496109 < baseStart_3496109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496124 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 4, 3]
def baseStart_3496124 : Nat := 118140960795 + 3496124 * 2 ^ 59
def prefixEnd_3496124 : Nat := 4983230072969 + 3 ^ 40 * 3496124 * 2
def baseEnd_3496124 : Nat := 1196794693146389754981083

theorem tailTrace_3496124 : CollatzResearch.WordTrace tailWord_3496124 prefixEnd_3496124 1196794693146389754981083 := by
  unfold tailWord_3496124
  simp only [CollatzResearch.WordTrace]
  refine ⟨63757058993073656643755713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85009411990764875525007617 63757058993073656643755713)
  ·
    refine ⟨47817794244805242482816785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63757058993073656643755713 47817794244805242482816785)
    ·
      refine ⟨35863345683603931862112589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47817794244805242482816785 35863345683603931862112589)
      ·
        refine ⟨13448754631351474448292221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35863345683603931862112589 13448754631351474448292221)
        ·
          refine ⟨5043282986756802918109583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13448754631351474448292221 5043282986756802918109583)
          ·
            refine ⟨7564924480135204377164375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5043282986756802918109583 7564924480135204377164375)
            ·
              refine ⟨11347386720202806565746563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7564924480135204377164375 11347386720202806565746563)
              ·
                refine ⟨17021080080304209848619845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11347386720202806565746563 17021080080304209848619845)
                ·
                  refine ⟨3191452515057039346616221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17021080080304209848619845 3191452515057039346616221)
                  ·
                    refine ⟨1196794693146389754981083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3191452515057039346616221 1196794693146389754981083)
                    ·
                      rfl

theorem cell22_3496124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_3496124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496124 prefixEnd_3496124 := by exact prefixLift 3496124
  have htrace : WordTrace (prefixWord ++ tailWord_3496124) baseStart_3496124 baseEnd_3496124 := by
    simpa [prefixWord, tailWord_3496124, baseEnd_3496124] using wordTrace_append hprefix tailTrace_3496124
  have hstable : (prefixWord ++ tailWord_3496124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496124).length < 2 ^ (prefixWord ++ tailWord_3496124).sum := by decide
  have hdescent : baseEnd_3496124 < baseStart_3496124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496182 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_3496182 : Nat := 118140960795 + 3496182 * 2 ^ 59
def prefixEnd_3496182 : Nat := 4983230072969 + 3 ^ 40 * 3496182 * 2
def baseEnd_3496182 : Nat := 398938182577232312343635

theorem tailTrace_3496182 : CollatzResearch.WordTrace tailWord_3496182 prefixEnd_3496182 398938182577232312343635 := by
  unfold tailWord_3496182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7969764588746074324570175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85010822279958126128748533 7969764588746074324570175)
  ·
    refine ⟨11954646883119111486855263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7969764588746074324570175 11954646883119111486855263)
    ·
      refine ⟨17931970324678667230282895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11954646883119111486855263 17931970324678667230282895)
      ·
        refine ⟨26897955487018000845424343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17931970324678667230282895 26897955487018000845424343)
        ·
          refine ⟨40346933230527001268136515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26897955487018000845424343 40346933230527001268136515)
          ·
            refine ⟨60520399845790501902204773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40346933230527001268136515 60520399845790501902204773)
            ·
              refine ⟨11347574971085719106663395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60520399845790501902204773 11347574971085719106663395)
              ·
                refine ⟨17021362456628578659995093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11347574971085719106663395 17021362456628578659995093)
                ·
                  refine ⟨398938182577232312343635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17021362456628578659995093 398938182577232312343635)
                  ·
                    rfl

theorem cell22_3496182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_3496182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496182 prefixEnd_3496182 := by exact prefixLift 3496182
  have htrace : WordTrace (prefixWord ++ tailWord_3496182) baseStart_3496182 baseEnd_3496182 := by
    simpa [prefixWord, tailWord_3496182, baseEnd_3496182] using wordTrace_append hprefix tailTrace_3496182
  have hstable : (prefixWord ++ tailWord_3496182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496182).length < 2 ^ (prefixWord ++ tailWord_3496182).sum := by decide
  have hdescent : baseEnd_3496182 < baseStart_3496182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496237 : List Nat := [1, 5, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3496237 : Nat := 118140960795 + 3496237 * 2 ^ 59
def prefixEnd_3496237 : Nat := 4983230072969 + 3 ^ 40 * 3496237 * 2
def baseEnd_3496237 : Nat := 1196833375355695126905737

theorem tailTrace_3496237 : CollatzResearch.WordTrace tailWord_3496237 prefixEnd_3496237 1196833375355695126905737 := by
  unfold tailWord_3496237
  simp only [CollatzResearch.WordTrace]
  refine ⟨127518239434737933586374965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85012159623158622390916643 127518239434737933586374965)
  ·
    refine ⟨11954834947006681273722653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127518239434737933586374965 11954834947006681273722653)
    ·
      refine ⟨4483063105127505477645995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11954834947006681273722653 4483063105127505477645995)
      ·
        refine ⟨6724594657691258216468993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4483063105127505477645995 6724594657691258216468993)
        ·
          refine ⟨5043445993268443662351745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6724594657691258216468993 5043445993268443662351745)
          ·
            refine ⟨3782584494951332746763809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5043445993268443662351745 3782584494951332746763809)
            ·
              refine ⟨2836938371213499560072857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3782584494951332746763809 2836938371213499560072857)
              ·
                refine ⟨2127703778410124670054643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2836938371213499560072857 2127703778410124670054643)
                ·
                  refine ⟨3191555667615187005081965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2127703778410124670054643 3191555667615187005081965)
                  ·
                    refine ⟨1196833375355695126905737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3191555667615187005081965 1196833375355695126905737)
                    ·
                      rfl

theorem cell22_3496237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3496237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496237 prefixEnd_3496237 := by exact prefixLift 3496237
  have htrace : WordTrace (prefixWord ++ tailWord_3496237) baseStart_3496237 baseEnd_3496237 := by
    simpa [prefixWord, tailWord_3496237, baseEnd_3496237] using wordTrace_append hprefix tailTrace_3496237
  have hstable : (prefixWord ++ tailWord_3496237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496237).length < 2 ^ (prefixWord ++ tailWord_3496237).sum := by decide
  have hdescent : baseEnd_3496237 < baseStart_3496237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496259 : List Nat := [1, 1, 1, 3, 1, 3, 4, 3, 2, 3]
def baseStart_3496259 : Nat := 118140960795 + 3496259 * 2 ^ 59
def prefixEnd_3496259 : Nat := 4983230072969 + 3 ^ 40 * 3496259 * 2
def baseEnd_3496259 : Nat := 1196840906405294402855669

theorem tailTrace_3496259 : CollatzResearch.WordTrace tailWord_3496259 prefixEnd_3496259 1196840906405294402855669 := by
  unfold tailWord_3496259
  simp only [CollatzResearch.WordTrace]
  refine ⟨127519041840658231343675831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85012694560438820895783887 127519041840658231343675831)
  ·
    refine ⟨191278562760987347015513747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127519041840658231343675831 191278562760987347015513747)
    ·
      refine ⟨286917844141481020523270621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191278562760987347015513747 286917844141481020523270621)
      ·
        refine ⟨107594191553055382696226483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286917844141481020523270621 107594191553055382696226483)
        ·
          refine ⟨161391287329583074044339725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107594191553055382696226483 161391287329583074044339725)
          ·
            refine ⟨60521732748593652766627397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161391287329583074044339725 60521732748593652766627397)
            ·
              refine ⟨11347824890361309893742637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60521732748593652766627397 11347824890361309893742637)
              ·
                refine ⟨4255434333885491210153489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11347824890361309893742637 4255434333885491210153489)
                ·
                  refine ⟨3191575750414118407615117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4255434333885491210153489 3191575750414118407615117)
                  ·
                    refine ⟨1196840906405294402855669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3191575750414118407615117 1196840906405294402855669)
                    ·
                      rfl

theorem cell22_3496259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 3].length) (baseStart_3496259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496259 prefixEnd_3496259 := by exact prefixLift 3496259
  have htrace : WordTrace (prefixWord ++ tailWord_3496259) baseStart_3496259 baseEnd_3496259 := by
    simpa [prefixWord, tailWord_3496259, baseEnd_3496259] using wordTrace_append hprefix tailTrace_3496259
  have hstable : (prefixWord ++ tailWord_3496259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496259).length < 2 ^ (prefixWord ++ tailWord_3496259).sum := by decide
  have hdescent : baseEnd_3496259 < baseStart_3496259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496274 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_3496274 : Nat := 118140960795 + 3496274 * 2 ^ 59
def prefixEnd_3496274 : Nat := 4983230072969 + 3 ^ 40 * 3496274 * 2
def baseEnd_3496274 : Nat := 1196846041211839363730623

theorem tailTrace_3496274 : CollatzResearch.WordTrace tailWord_3496274 prefixEnd_3496274 1196846041211839363730623 := by
  unfold tailWord_3496274
  simp only [CollatzResearch.WordTrace]
  refine ⟨31879897233900972226367969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85013059290402592603647917 31879897233900972226367969)
  ·
    refine ⟨23909922925425729169775977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31879897233900972226367969 23909922925425729169775977)
    ·
      refine ⟨17932442194069296877331983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23909922925425729169775977 17932442194069296877331983)
      ·
        refine ⟨26898663291103945315997975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17932442194069296877331983 26898663291103945315997975)
        ·
          refine ⟨40347994936655917973996963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26898663291103945315997975 40347994936655917973996963)
          ·
            refine ⟨60521992404983876960995445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40347994936655917973996963 60521992404983876960995445)
            ·
              refine ⟨5673936787967238465093323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60521992404983876960995445 5673936787967238465093323)
              ·
                refine ⟨8510905181950857697639985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673936787967238465093323 8510905181950857697639985)
                ·
                  refine ⟨6383178886463143273229989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8510905181950857697639985 6383178886463143273229989)
                  ·
                    refine ⟨1196846041211839363730623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6383178886463143273229989 1196846041211839363730623)
                    ·
                      rfl

theorem cell22_3496274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_3496274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496274 prefixEnd_3496274 := by exact prefixLift 3496274
  have htrace : WordTrace (prefixWord ++ tailWord_3496274) baseStart_3496274 baseEnd_3496274 := by
    simpa [prefixWord, tailWord_3496274, baseEnd_3496274] using wordTrace_append hprefix tailTrace_3496274
  have hstable : (prefixWord ++ tailWord_3496274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496274).length < 2 ^ (prefixWord ++ tailWord_3496274).sum := by decide
  have hdescent : baseEnd_3496274 < baseStart_3496274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496304 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 3, 3]
def baseStart_3496304 : Nat := 118140960795 + 3496304 * 2 ^ 59
def prefixEnd_3496304 : Nat := 4983230072969 + 3 ^ 40 * 3496304 * 2
def baseEnd_3496304 : Nat := 1196856310824929285480531

theorem tailTrace_3496304 : CollatzResearch.WordTrace tailWord_3496304 prefixEnd_3496304 1196856310824929285480531 := by
  unfold tailWord_3496304
  simp only [CollatzResearch.WordTrace]
  refine ⟨63760341562747602014531983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85013788750330136019375977 63760341562747602014531983)
  ·
    refine ⟨95640512344121403021797975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63760341562747602014531983 95640512344121403021797975)
    ·
      refine ⟨143460768516182104532696963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95640512344121403021797975 143460768516182104532696963)
      ·
        refine ⟨215191152774273156799045445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143460768516182104532696963 215191152774273156799045445)
        ·
          refine ⟨40348341145176216899821021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215191152774273156799045445 40348341145176216899821021)
          ·
            refine ⟨15130627929441081337432883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40348341145176216899821021 15130627929441081337432883)
            ·
              refine ⟨22695941894161622006149325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15130627929441081337432883 22695941894161622006149325)
              ·
                refine ⟨8510978210310608252305997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22695941894161622006149325 8510978210310608252305997)
                ·
                  refine ⟨3191616828866478094614749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8510978210310608252305997 3191616828866478094614749)
                  ·
                    refine ⟨1196856310824929285480531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3191616828866478094614749 1196856310824929285480531)
                    ·
                      rfl

theorem cell22_3496304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 3, 3].length) (baseStart_3496304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496304 prefixEnd_3496304 := by exact prefixLift 3496304
  have htrace : WordTrace (prefixWord ++ tailWord_3496304) baseStart_3496304 baseEnd_3496304 := by
    simpa [prefixWord, tailWord_3496304, baseEnd_3496304] using wordTrace_append hprefix tailTrace_3496304
  have hstable : (prefixWord ++ tailWord_3496304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496304).length < 2 ^ (prefixWord ++ tailWord_3496304).sum := by decide
  have hdescent : baseEnd_3496304 < baseStart_3496304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496310 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_3496310 : Nat := 118140960795 + 3496310 * 2 ^ 59
def prefixEnd_3496310 : Nat := 4983230072969 + 3 ^ 40 * 3496310 * 2
def baseEnd_3496310 : Nat := 1196858364747547269830513

theorem tailTrace_3496310 : CollatzResearch.WordTrace tailWord_3496310 prefixEnd_3496310 1196858364747547269830513 := by
  unfold tailWord_3496310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7970056372717091690861399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85013934642315644702521589 7970056372717091690861399)
  ·
    refine ⟨11955084559075637536292099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7970056372717091690861399 11955084559075637536292099)
    ·
      refine ⟨17932626838613456304438149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11955084559075637536292099 17932626838613456304438149)
      ·
        refine ⟨3362367532240023057082153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17932626838613456304438149 3362367532240023057082153)
        ·
          refine ⟨2521775649180017292811615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3362367532240023057082153 2521775649180017292811615)
          ·
            refine ⟨3782663473770025939217423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521775649180017292811615 3782663473770025939217423)
            ·
              refine ⟨5673995210655038908826135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3782663473770025939217423 5673995210655038908826135)
              ·
                refine ⟨8510992815982558363239203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673995210655038908826135 8510992815982558363239203)
                ·
                  refine ⟨12766489223973837544858805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8510992815982558363239203 12766489223973837544858805)
                  ·
                    refine ⟨1196858364747547269830513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12766489223973837544858805 1196858364747547269830513)
                    ·
                      rfl

theorem cell22_3496310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_3496310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496310 prefixEnd_3496310 := by exact prefixLift 3496310
  have htrace : WordTrace (prefixWord ++ tailWord_3496310) baseStart_3496310 baseEnd_3496310 := by
    simpa [prefixWord, tailWord_3496310, baseEnd_3496310] using wordTrace_append hprefix tailTrace_3496310
  have hstable : (prefixWord ++ tailWord_3496310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496310).length < 2 ^ (prefixWord ++ tailWord_3496310).sum := by decide
  have hdescent : baseEnd_3496310 < baseStart_3496310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496321 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 3, 3]
def baseStart_3496321 : Nat := 118140960795 + 3496321 * 2 ^ 59
def prefixEnd_3496321 : Nat := 4983230072969 + 3 ^ 40 * 3496321 * 2
def baseEnd_3496321 : Nat := 1196862130272346907805479

theorem tailTrace_3496321 : CollatzResearch.WordTrace tailWord_3496321 prefixEnd_3496321 1196862130272346907805479 := by
  unfold tailWord_3496321
  simp only [CollatzResearch.WordTrace]
  refine ⟨127521303166433615932432817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85014202110955743954955211 127521303166433615932432817)
  ·
    refine ⟨95640977374825211949324613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127521303166433615932432817 95640977374825211949324613)
    ·
      refine ⟨17932683257779727240498365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95640977374825211949324613 17932683257779727240498365)
      ·
        refine ⟨6724756221667397715186887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17932683257779727240498365 6724756221667397715186887)
        ·
          refine ⟨10087134332501096572780331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6724756221667397715186887 10087134332501096572780331)
          ·
            refine ⟨15130701498751644859170497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10087134332501096572780331 15130701498751644859170497)
            ·
              refine ⟨11348026124063733644377873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15130701498751644859170497 11348026124063733644377873)
              ·
                refine ⟨8511019593047800233283405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11348026124063733644377873 8511019593047800233283405)
                ·
                  refine ⟨3191632347392925087481277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8511019593047800233283405 3191632347392925087481277)
                  ·
                    refine ⟨1196862130272346907805479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3191632347392925087481277 1196862130272346907805479)
                    ·
                      rfl

theorem cell22_3496321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_3496321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496321 prefixEnd_3496321 := by exact prefixLift 3496321
  have htrace : WordTrace (prefixWord ++ tailWord_3496321) baseStart_3496321 baseEnd_3496321 := by
    simpa [prefixWord, tailWord_3496321, baseEnd_3496321] using wordTrace_append hprefix tailTrace_3496321
  have hstable : (prefixWord ++ tailWord_3496321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496321).length < 2 ^ (prefixWord ++ tailWord_3496321).sum := by decide
  have hdescent : baseEnd_3496321 < baseStart_3496321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496334 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_3496334 : Nat := 118140960795 + 3496334 * 2 ^ 59
def prefixEnd_3496334 : Nat := 4983230072969 + 3 ^ 40 * 3496334 * 2
def baseEnd_3496334 : Nat := 398955526812673069076813

theorem tailTrace_3496334 : CollatzResearch.WordTrace tailWord_3496334 prefixEnd_3496334 398955526812673069076813 := by
  unfold tailWord_3496334
  simp only [CollatzResearch.WordTrace]
  refine ⟨15940222164423314894082007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85014518210257679435104037 15940222164423314894082007)
  ·
    refine ⟨23910333246634972341123011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15940222164423314894082007 23910333246634972341123011)
    ·
      refine ⟨35865499869952458511684517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23910333246634972341123011 35865499869952458511684517)
      ·
        refine ⟨6724781225616085970940847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35865499869952458511684517 6724781225616085970940847)
        ·
          refine ⟨10087171838424128956411271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6724781225616085970940847 10087171838424128956411271)
          ·
            refine ⟨15130757757636193434616907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10087171838424128956411271 15130757757636193434616907)
            ·
              refine ⟨22696136636454290151925361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15130757757636193434616907 22696136636454290151925361)
              ·
                refine ⟨17022102477340717613944021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22696136636454290151925361 17022102477340717613944021)
                ·
                  refine ⟨398955526812673069076813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17022102477340717613944021 398955526812673069076813)
                  ·
                    rfl

theorem cell22_3496334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_3496334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496334 prefixEnd_3496334 := by exact prefixLift 3496334
  have htrace : WordTrace (prefixWord ++ tailWord_3496334) baseStart_3496334 baseEnd_3496334 := by
    simpa [prefixWord, tailWord_3496334, baseEnd_3496334] using wordTrace_append hprefix tailTrace_3496334
  have hstable : (prefixWord ++ tailWord_3496334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496334).length < 2 ^ (prefixWord ++ tailWord_3496334).sum := by decide
  have hdescent : baseEnd_3496334 < baseStart_3496334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496381 : List Nat := [1, 4, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_3496381 : Nat := 118140960795 + 3496381 * 2 ^ 59
def prefixEnd_3496381 : Nat := 4983230072969 + 3 ^ 40 * 3496381 * 2
def baseEnd_3496381 : Nat := 1196882669498526751305295

theorem tailTrace_3496381 : CollatzResearch.WordTrace tailWord_3496381 prefixEnd_3496381 1196882669498526751305295 := by
  unfold tailWord_3496381
  simp only [CollatzResearch.WordTrace]
  refine ⟨127523491546216246179616997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85015661030810830786411331 127523491546216246179616997)
  ·
    refine ⟨23910654664915546158678187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127523491546216246179616997 23910654664915546158678187)
    ·
      refine ⟨35865981997373319238017281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23910654664915546158678187 35865981997373319238017281)
      ·
        refine ⟨26899486498029989428512961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35865981997373319238017281 26899486498029989428512961)
        ·
          refine ⟨20174614873522492071384721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26899486498029989428512961 20174614873522492071384721)
          ·
            refine ⟨15130961155141869053538541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20174614873522492071384721 15130961155141869053538541)
            ·
              refine ⟨5674110433178200895076953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15130961155141869053538541 5674110433178200895076953)
              ·
                refine ⟨4255582824883650671307715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5674110433178200895076953 4255582824883650671307715)
                ·
                  refine ⟨6383374237325476006961573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255582824883650671307715 6383374237325476006961573)
                  ·
                    refine ⟨1196882669498526751305295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6383374237325476006961573 1196882669498526751305295)
                    ·
                      rfl

theorem cell22_3496381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_3496381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496381 prefixEnd_3496381 := by exact prefixLift 3496381
  have htrace : WordTrace (prefixWord ++ tailWord_3496381) baseStart_3496381 baseEnd_3496381 := by
    simpa [prefixWord, tailWord_3496381, baseEnd_3496381] using wordTrace_append hprefix tailTrace_3496381
  have hstable : (prefixWord ++ tailWord_3496381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496381).length < 2 ^ (prefixWord ++ tailWord_3496381).sum := by decide
  have hdescent : baseEnd_3496381 < baseStart_3496381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496394 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_3496394 : Nat := 118140960795 + 3496394 * 2 ^ 59
def prefixEnd_3496394 : Nat := 4983230072969 + 3 ^ 40 * 3496394 * 2
def baseEnd_3496394 : Nat := 1196887119664199050730255

theorem tailTrace_3496394 : CollatzResearch.WordTrace tailWord_3496394 prefixEnd_3496394 1196887119664199050730255 := by
  unfold tailWord_3496394
  simp only [CollatzResearch.WordTrace]
  refine ⟨31880991423792287349960059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85015977130112766266560157 31880991423792287349960059)
  ·
    refine ⟨47821487135688431024940089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31880991423792287349960059 47821487135688431024940089)
    ·
      refine ⟨35866115351766323268705067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47821487135688431024940089 35866115351766323268705067)
      ·
        refine ⟨53799173027649484903057601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35866115351766323268705067 53799173027649484903057601)
        ·
          refine ⟨40349379770737113677293201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53799173027649484903057601 40349379770737113677293201)
          ·
            refine ⟨30262034828052835257969901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40349379770737113677293201 30262034828052835257969901)
            ·
              refine ⟨11348263060519813221738713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30262034828052835257969901 11348263060519813221738713)
              ·
                refine ⟨8511197295389859916304035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11348263060519813221738713 8511197295389859916304035)
                ·
                  refine ⟨12766795943084789874456053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8511197295389859916304035 12766795943084789874456053)
                  ·
                    refine ⟨1196887119664199050730255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12766795943084789874456053 1196887119664199050730255)
                    ·
                      rfl

theorem cell22_3496394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_3496394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496394 prefixEnd_3496394 := by exact prefixLift 3496394
  have htrace : WordTrace (prefixWord ++ tailWord_3496394) baseStart_3496394 baseEnd_3496394 := by
    simpa [prefixWord, tailWord_3496394, baseEnd_3496394] using wordTrace_append hprefix tailTrace_3496394
  have hstable : (prefixWord ++ tailWord_3496394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496394).length < 2 ^ (prefixWord ++ tailWord_3496394).sum := by decide
  have hdescent : baseEnd_3496394 < baseStart_3496394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496409 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 2, 4]
def baseStart_3496409 : Nat := 118140960795 + 3496409 * 2 ^ 59
def prefixEnd_3496409 : Nat := 4983230072969 + 3 ^ 40 * 3496409 * 2
def baseEnd_3496409 : Nat := 1196892254470744011605209

theorem tailTrace_3496409 : CollatzResearch.WordTrace tailWord_3496409 prefixEnd_3496409 1196892254470744011605209 := by
  unfold tailWord_3496409
  simp only [CollatzResearch.WordTrace]
  refine ⟨127524512790114806961636281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85016341860076537974424187 127524512790114806961636281)
  ·
    refine ⟨95643384592586105221227211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127524512790114806961636281 95643384592586105221227211)
    ·
      refine ⟨143465076888879157831840817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95643384592586105221227211 143465076888879157831840817)
      ·
        refine ⟨107598807666659368373880613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143465076888879157831840817 107598807666659368373880613)
        ·
          refine ⟨20174776437498631570102615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107598807666659368373880613 20174776437498631570102615)
          ·
            refine ⟨30262164656247947355153923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20174776437498631570102615 30262164656247947355153923)
            ·
              refine ⟨45393246984371921032730885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30262164656247947355153923 45393246984371921032730885)
              ·
                refine ⟨8511233809569735193637041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45393246984371921032730885 8511233809569735193637041)
                ·
                  refine ⟨6383425357177301395227781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8511233809569735193637041 6383425357177301395227781)
                  ·
                    refine ⟨1196892254470744011605209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6383425357177301395227781 1196892254470744011605209)
                    ·
                      rfl

theorem cell22_3496409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_3496409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496409 prefixEnd_3496409 := by exact prefixLift 3496409
  have htrace : WordTrace (prefixWord ++ tailWord_3496409) baseStart_3496409 baseEnd_3496409 := by
    simpa [prefixWord, tailWord_3496409, baseEnd_3496409] using wordTrace_append hprefix tailTrace_3496409
  have hstable : (prefixWord ++ tailWord_3496409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496409).length < 2 ^ (prefixWord ++ tailWord_3496409).sum := by decide
  have hdescent : baseEnd_3496409 < baseStart_3496409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496424 : List Nat := [2, 1, 4, 1, 1, 3, 3, 7]
def baseStart_3496424 : Nat := 118140960795 + 3496424 * 2 ^ 59
def prefixEnd_3496424 : Nat := 4983230072969 + 3 ^ 40 * 3496424 * 2
def baseEnd_3496424 : Nat := 132988598808587663608907

theorem tailTrace_3496424 : CollatzResearch.WordTrace tailWord_3496424 prefixEnd_3496424 132988598808587663608907 := by
  unfold tailWord_3496424
  simp only [CollatzResearch.WordTrace]
  refine ⟨63762529942530232261716163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85016706590040309682288217 63762529942530232261716163)
  ·
    refine ⟨95643794913795348392574245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63762529942530232261716163 95643794913795348392574245)
    ·
      refine ⟨17933211546336627823607671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95643794913795348392574245 17933211546336627823607671)
      ·
        refine ⟨26899817319504941735411507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17933211546336627823607671 26899817319504941735411507)
        ·
          refine ⟨40349725979257412603117261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26899817319504941735411507 40349725979257412603117261)
          ·
            refine ⟨15131147242221529726168973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40349725979257412603117261 15131147242221529726168973)
            ·
              refine ⟨5674180215833073647313365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15131147242221529726168973 5674180215833073647313365)
              ·
                refine ⟨132988598808587663608907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5674180215833073647313365 132988598808587663608907)
                ·
                  rfl

theorem cell22_3496424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 7].length) (baseStart_3496424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496424 prefixEnd_3496424 := by exact prefixLift 3496424
  have htrace : WordTrace (prefixWord ++ tailWord_3496424) baseStart_3496424 baseEnd_3496424 := by
    simpa [prefixWord, tailWord_3496424, baseEnd_3496424] using wordTrace_append hprefix tailTrace_3496424
  have hstable : (prefixWord ++ tailWord_3496424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496424).length < 2 ^ (prefixWord ++ tailWord_3496424).sum := by decide
  have hdescent : baseEnd_3496424 < baseStart_3496424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496469 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 7]
def baseStart_3496469 : Nat := 118140960795 + 3496469 * 2 ^ 59
def prefixEnd_3496469 : Nat := 4983230072969 + 3 ^ 40 * 3496469 * 2
def baseEnd_3496469 : Nat := 398970931232307951701675

theorem tailTrace_3496469 : CollatzResearch.WordTrace tailWord_3496469 prefixEnd_3496469 398970931232307951701675 := by
  unfold tailWord_3496469
  simp only [CollatzResearch.WordTrace]
  refine ⟨127526701169897437208820461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85017800779931624805880307 127526701169897437208820461)
  ·
    refine ⟨47822512938711538953307673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127526701169897437208820461 47822512938711538953307673)
    ·
      refine ⟨35866884704033654214980755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47822512938711538953307673 35866884704033654214980755)
      ·
        refine ⟨53800327056050481322471133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35866884704033654214980755 53800327056050481322471133)
        ·
          refine ⟨20175122646018930495926675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53800327056050481322471133 20175122646018930495926675)
          ·
            refine ⟨30262683969028395743890013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20175122646018930495926675 30262683969028395743890013)
            ·
              refine ⟨11348506488385648403958755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30262683969028395743890013 11348506488385648403958755)
              ·
                refine ⟨17022759732578472605938133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11348506488385648403958755 17022759732578472605938133)
                ·
                  refine ⟨398970931232307951701675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17022759732578472605938133 398970931232307951701675)
                  ·
                    rfl

theorem cell22_3496469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_3496469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496469 prefixEnd_3496469 := by exact prefixLift 3496469
  have htrace : WordTrace (prefixWord ++ tailWord_3496469) baseStart_3496469 baseEnd_3496469 := by
    simpa [prefixWord, tailWord_3496469, baseEnd_3496469] using wordTrace_append hprefix tailTrace_3496469
  have hstable : (prefixWord ++ tailWord_3496469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496469).length < 2 ^ (prefixWord ++ tailWord_3496469).sum := by decide
  have hdescent : baseEnd_3496469 < baseStart_3496469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496544 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 3, 6]
def baseStart_3496544 : Nat := 118140960795 + 3496544 * 2 ^ 59
def prefixEnd_3496544 : Nat := 4983230072969 + 3 ^ 40 * 3496544 * 2
def baseEnd_3496544 : Nat := 1196938467729648659479795

theorem tailTrace_3496544 : CollatzResearch.WordTrace tailWord_3496544 prefixEnd_3496544 1196938467729648659479795 := by
  unfold tailWord_3496544
  simp only [CollatzResearch.WordTrace]
  refine ⟨63764718322312862508900343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85019624429750483345200457 63764718322312862508900343)
  ·
    refine ⟨95647077483469293763350515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63764718322312862508900343 95647077483469293763350515)
    ·
      refine ⟨143470616225203940645025773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95647077483469293763350515 143470616225203940645025773)
      ·
        refine ⟨53801481084451477741884665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143470616225203940645025773 53801481084451477741884665)
        ·
          refine ⟨40351110813338608306413499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53801481084451477741884665 40351110813338608306413499)
          ·
            refine ⟨60526666220007912459620249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40351110813338608306413499 60526666220007912459620249)
            ·
              refine ⟨45394999665005934344715187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60526666220007912459620249 45394999665005934344715187)
              ·
                refine ⟨68092499497508901517072781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45394999665005934344715187 68092499497508901517072781)
                ·
                  refine ⟨25534687311565838068902293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68092499497508901517072781 25534687311565838068902293)
                  ·
                    refine ⟨1196938467729648659479795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25534687311565838068902293 1196938467729648659479795)
                    ·
                      rfl

theorem cell22_3496544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_3496544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496544 prefixEnd_3496544 := by exact prefixLift 3496544
  have htrace : WordTrace (prefixWord ++ tailWord_3496544) baseStart_3496544 baseEnd_3496544 := by
    simpa [prefixWord, tailWord_3496544, baseEnd_3496544] using wordTrace_append hprefix tailTrace_3496544
  have hstable : (prefixWord ++ tailWord_3496544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496544).length < 2 ^ (prefixWord ++ tailWord_3496544).sum := by decide
  have hdescent : baseEnd_3496544 < baseStart_3496544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496559 : List Nat := [1, 1, 2, 1, 3, 2, 4, 8]
def baseStart_3496559 : Nat := 118140960795 + 3496559 * 2 ^ 59
def prefixEnd_3496559 : Nat := 4983230072969 + 3 ^ 40 * 3496559 * 2
def baseEnd_3496559 : Nat := 132993733615132624483861

theorem tailTrace_3496559 : CollatzResearch.WordTrace tailWord_3496559 prefixEnd_3496559 132993733615132624483861 := by
  unfold tailWord_3496559
  simp only [CollatzResearch.WordTrace]
  refine ⟨127529983739571382579596731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85019989159714255053064487 127529983739571382579596731)
  ·
    refine ⟨191294975609357073869395097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127529983739571382579596731 191294975609357073869395097)
    ·
      refine ⟨143471231707017805402046323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191294975609357073869395097 143471231707017805402046323)
      ·
        refine ⟨215206847560526708103069485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143471231707017805402046323 215206847560526708103069485)
        ·
          refine ⟨80702567835197515538651057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215206847560526708103069485 80702567835197515538651057)
          ·
            refine ⟨60526925876398136653988293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80702567835197515538651057 60526925876398136653988293)
            ·
              refine ⟨11348798601824650622622805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60526925876398136653988293 11348798601824650622622805)
              ·
                refine ⟨132993733615132624483861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11348798601824650622622805 132993733615132624483861)
                ·
                  rfl

theorem cell22_3496559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 8].length) (baseStart_3496559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496559 prefixEnd_3496559 := by exact prefixLift 3496559
  have htrace : WordTrace (prefixWord ++ tailWord_3496559) baseStart_3496559 baseEnd_3496559 := by
    simpa [prefixWord, tailWord_3496559, baseEnd_3496559] using wordTrace_append hprefix tailTrace_3496559
  have hstable : (prefixWord ++ tailWord_3496559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496559).length < 2 ^ (prefixWord ++ tailWord_3496559).sum := by decide
  have hdescent : baseEnd_3496559 < baseStart_3496559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496580 : List Nat := [2, 3, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_3496580 : Nat := 118140960795 + 3496580 * 2 ^ 59
def prefixEnd_3496580 : Nat := 4983230072969 + 3 ^ 40 * 3496580 * 2
def baseEnd_3496580 : Nat := 1196950791265356565579685

theorem tailTrace_3496580 : CollatzResearch.WordTrace tailWord_3496580 prefixEnd_3496580 1196950791265356565579685 := by
  unfold tailWord_3496580
  simp only [CollatzResearch.WordTrace]
  refine ⟨63765374836247651583055597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85020499781663535444074129 63765374836247651583055597)
  ·
    refine ⟨23912015563592869343645849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63765374836247651583055597 23912015563592869343645849)
    ·
      refine ⟨17934011672694652007734387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23912015563592869343645849 17934011672694652007734387)
      ·
        refine ⟨26901017509041978011601581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17934011672694652007734387 26901017509041978011601581)
        ·
          refine ⟨10087881565890741754350593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26901017509041978011601581 10087881565890741754350593)
          ·
            refine ⟨7565911174418056315762945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10087881565890741754350593 7565911174418056315762945)
            ·
              refine ⟨5674433380813542236822209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7565911174418056315762945 5674433380813542236822209)
              ·
                refine ⟨4255825035610156677616657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5674433380813542236822209 4255825035610156677616657)
                ·
                  refine ⟨3191868776707617508212493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4255825035610156677616657 3191868776707617508212493)
                  ·
                    refine ⟨1196950791265356565579685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3191868776707617508212493 1196950791265356565579685)
                    ·
                      rfl

theorem cell22_3496580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_3496580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496580 prefixEnd_3496580 := by exact prefixLift 3496580
  have htrace : WordTrace (prefixWord ++ tailWord_3496580) baseStart_3496580 baseEnd_3496580 := by
    simpa [prefixWord, tailWord_3496580, baseEnd_3496580] using wordTrace_append hprefix tailTrace_3496580
  have hstable : (prefixWord ++ tailWord_3496580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496580).length < 2 ^ (prefixWord ++ tailWord_3496580).sum := by decide
  have hdescent : baseEnd_3496580 < baseStart_3496580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496636 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_3496636 : Nat := 118140960795 + 3496636 * 2 ^ 59
def prefixEnd_3496636 : Nat := 4983230072969 + 3 ^ 40 * 3496636 * 2
def baseEnd_3496636 : Nat := 1196969961209791086179513

theorem tailTrace_3496636 : CollatzResearch.WordTrace tailWord_3496636 prefixEnd_3496636 1196969961209791086179513 := by
  unfold tailWord_3496636
  simp only [CollatzResearch.WordTrace]
  refine ⟨63766396080146212365074881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85021861440194949820099841 63766396080146212365074881)
  ·
    refine ⟨47824797060109659273806161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63766396080146212365074881 47824797060109659273806161)
    ·
      refine ⟨35868597795082244455354621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47824797060109659273806161 35868597795082244455354621)
      ·
        refine ⟨13450724173155841670757983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35868597795082244455354621 13450724173155841670757983)
        ·
          refine ⟨20176086259733762506136975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13450724173155841670757983 20176086259733762506136975)
          ·
            refine ⟨30264129389600643759205463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20176086259733762506136975 30264129389600643759205463)
            ·
              refine ⟨45396194084400965638808195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30264129389600643759205463 45396194084400965638808195)
              ·
                refine ⟨68094291126601448458212293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45396194084400965638808195 68094291126601448458212293)
                ·
                  refine ⟨12767679586237771585914805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68094291126601448458212293 12767679586237771585914805)
                  ·
                    refine ⟨1196969961209791086179513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12767679586237771585914805 1196969961209791086179513)
                    ·
                      rfl

theorem cell22_3496636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_3496636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496636 prefixEnd_3496636 := by exact prefixLift 3496636
  have htrace : WordTrace (prefixWord ++ tailWord_3496636) baseStart_3496636 baseEnd_3496636 := by
    simpa [prefixWord, tailWord_3496636, baseEnd_3496636] using wordTrace_append hprefix tailTrace_3496636
  have hstable : (prefixWord ++ tailWord_3496636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496636).length < 2 ^ (prefixWord ++ tailWord_3496636).sum := by decide
  have hdescent : baseEnd_3496636 < baseStart_3496636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496666 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 6]
def baseStart_3496666 : Nat := 118140960795 + 3496666 * 2 ^ 59
def prefixEnd_3496666 : Nat := 4983230072969 + 3 ^ 40 * 3496666 * 2
def baseEnd_3496666 : Nat := 398993410274293669309807

theorem tailTrace_3496666 : CollatzResearch.WordTrace tailWord_3496666 prefixEnd_3496666 398993410274293669309807 := by
  unfold tailWord_3496666
  simp only [CollatzResearch.WordTrace]
  refine ⟨31883471587545934963435463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85022590900122493235827901 31883471587545934963435463)
  ·
    refine ⟨47825207381318902445153195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31883471587545934963435463 47825207381318902445153195)
    ·
      refine ⟨71737811071978353667729793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47825207381318902445153195 71737811071978353667729793)
      ·
        refine ⟨53803358303983765250797345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71737811071978353667729793 53803358303983765250797345)
        ·
          refine ⟨40352518727987823938098009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53803358303983765250797345 40352518727987823938098009)
          ·
            refine ⟨30264389045990867953573507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40352518727987823938098009 30264389045990867953573507)
            ·
              refine ⟨45396583568986301930360261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30264389045990867953573507 45396583568986301930360261)
              ·
                refine ⟨8511859419184931611942549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45396583568986301930360261 8511859419184931611942549)
                ·
                  refine ⟨398993410274293669309807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8511859419184931611942549 398993410274293669309807)
                  ·
                    rfl

theorem cell22_3496666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_3496666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496666 prefixEnd_3496666 := by exact prefixLift 3496666
  have htrace : WordTrace (prefixWord ++ tailWord_3496666) baseStart_3496666 baseEnd_3496666 := by
    simpa [prefixWord, tailWord_3496666, baseEnd_3496666] using wordTrace_append hprefix tailTrace_3496666
  have hstable : (prefixWord ++ tailWord_3496666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496666).length < 2 ^ (prefixWord ++ tailWord_3496666).sum := by decide
  have hdescent : baseEnd_3496666 < baseStart_3496666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496681 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 1, 5]
def baseStart_3496681 : Nat := 118140960795 + 3496681 * 2 ^ 59
def prefixEnd_3496681 : Nat := 4983230072969 + 3 ^ 40 * 3496681 * 2
def baseEnd_3496681 : Nat := 1196985365629425968804375

theorem tailTrace_3496681 : CollatzResearch.WordTrace tailWord_3496681 prefixEnd_3496681 1196985365629425968804375 := by
  unfold tailWord_3496681
  simp only [CollatzResearch.WordTrace]
  refine ⟨127534433445129397415537897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85022955630086264943691931 127534433445129397415537897)
  ·
    refine ⟨95650825083847048061653423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127534433445129397415537897 95650825083847048061653423)
    ·
      refine ⟨143476237625770572092480135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95650825083847048061653423 143476237625770572092480135)
      ·
        refine ⟨215214356438655858138720203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143476237625770572092480135 215214356438655858138720203)
        ·
          refine ⟨322821534657983787208080305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215214356438655858138720203 322821534657983787208080305)
          ·
            refine ⟨242116150993487840406060229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322821534657983787208080305 242116150993487840406060229)
            ·
              refine ⟨45396778311278970076136293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242116150993487840406060229 45396778311278970076136293)
              ·
                refine ⟨8511895933364806889275555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45396778311278970076136293 8511895933364806889275555)
                ·
                  refine ⟨12767843900047210333913333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8511895933364806889275555 12767843900047210333913333)
                  ·
                    refine ⟨1196985365629425968804375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12767843900047210333913333 1196985365629425968804375)
                    ·
                      rfl

theorem cell22_3496681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_3496681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496681 prefixEnd_3496681 := by exact prefixLift 3496681
  have htrace : WordTrace (prefixWord ++ tailWord_3496681) baseStart_3496681 baseEnd_3496681 := by
    simpa [prefixWord, tailWord_3496681, baseEnd_3496681] using wordTrace_append hprefix tailTrace_3496681
  have hstable : (prefixWord ++ tailWord_3496681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496681).length < 2 ^ (prefixWord ++ tailWord_3496681).sum := by decide
  have hdescent : baseEnd_3496681 < baseStart_3496681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496693 : List Nat := [1, 3, 6, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3496693 : Nat := 118140960795 + 3496693 * 2 ^ 59
def prefixEnd_3496693 : Nat := 4983230072969 + 3 ^ 40 * 3496693 * 2
def baseEnd_3496693 : Nat := 1196989473474661937504339

theorem tailTrace_3496693 : CollatzResearch.WordTrace tailWord_3496693 prefixEnd_3496693 1196989473474661937504339 := by
  unfold tailWord_3496693
  simp only [CollatzResearch.WordTrace]
  refine ⟨127534871121085923464974733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85023247414057282309983155 127534871121085923464974733)
  ·
    refine ⟨47825576670407221299365525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127534871121085923464974733 47825576670407221299365525)
    ·
      refine ⟨2241823906425338498407759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47825576670407221299365525 2241823906425338498407759)
      ·
        refine ⟨3362735859638007747611639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241823906425338498407759 3362735859638007747611639)
        ·
          refine ⟨5044103789457011621417459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362735859638007747611639 5044103789457011621417459)
          ·
            refine ⟨7566155684185517432126189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044103789457011621417459 7566155684185517432126189)
            ·
              refine ⟨2837308381569569037047321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7566155684185517432126189 2837308381569569037047321)
              ·
                refine ⟨2127981286177176777785491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2837308381569569037047321 2127981286177176777785491)
                ·
                  refine ⟨3191971929265765166678237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2127981286177176777785491 3191971929265765166678237)
                  ·
                    refine ⟨1196989473474661937504339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3191971929265765166678237 1196989473474661937504339)
                    ·
                      rfl

theorem cell22_3496693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3496693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496693 prefixEnd_3496693 := by exact prefixLift 3496693
  have htrace : WordTrace (prefixWord ++ tailWord_3496693) baseStart_3496693 baseEnd_3496693 := by
    simpa [prefixWord, tailWord_3496693, baseEnd_3496693] using wordTrace_append hprefix tailTrace_3496693
  have hstable : (prefixWord ++ tailWord_3496693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496693).length < 2 ^ (prefixWord ++ tailWord_3496693).sum := by decide
  have hdescent : baseEnd_3496693 < baseStart_3496693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496698 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 4, 3]
def baseStart_3496698 : Nat := 118140960795 + 3496698 * 2 ^ 59
def prefixEnd_3496698 : Nat := 4983230072969 + 3 ^ 40 * 3496698 * 2
def baseEnd_3496698 : Nat := 1196991185076843591129323

theorem tailTrace_3496698 : CollatzResearch.WordTrace tailWord_3496698 prefixEnd_3496698 1196991185076843591129323 := by
  unfold tailWord_3496698
  simp only [CollatzResearch.WordTrace]
  refine ⟨31883763371516952329726687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85023368990711872879271165 31883763371516952329726687)
  ·
    refine ⟨47825645057275428494590031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31883763371516952329726687 47825645057275428494590031)
    ·
      refine ⟨71738467585913142741885047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47825645057275428494590031 71738467585913142741885047)
      ·
        refine ⟨107607701378869714112827571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71738467585913142741885047 107607701378869714112827571)
        ·
          refine ⟨161411552068304571169241357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107607701378869714112827571 161411552068304571169241357)
          ·
            refine ⟨60529332025614214188465509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161411552068304571169241357 60529332025614214188465509)
            ·
              refine ⟨11349249754802665160337283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60529332025614214188465509 11349249754802665160337283)
              ·
                refine ⟨17023874632203997740505925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11349249754802665160337283 17023874632203997740505925)
                ·
                  refine ⟨3191976493538249576344861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17023874632203997740505925 3191976493538249576344861)
                  ·
                    refine ⟨1196991185076843591129323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3191976493538249576344861 1196991185076843591129323)
                    ·
                      rfl

theorem cell22_3496698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_3496698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496698 prefixEnd_3496698 := by exact prefixLift 3496698
  have htrace : WordTrace (prefixWord ++ tailWord_3496698) baseStart_3496698 baseEnd_3496698 := by
    simpa [prefixWord, tailWord_3496698, baseEnd_3496698] using wordTrace_append hprefix tailTrace_3496698
  have hstable : (prefixWord ++ tailWord_3496698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496698).length < 2 ^ (prefixWord ++ tailWord_3496698).sum := by decide
  have hdescent : baseEnd_3496698 < baseStart_3496698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496818 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 6]
def baseStart_3496818 : Nat := 118140960795 + 3496818 * 2 ^ 59
def prefixEnd_3496818 : Nat := 4983230072969 + 3 ^ 40 * 3496818 * 2
def baseEnd_3496818 : Nat := 399010754509734426042985

theorem tailTrace_3496818 : CollatzResearch.WordTrace tailWord_3496818 prefixEnd_3496818 399010754509734426042985 := by
  unfold tailWord_3496818
  simp only [CollatzResearch.WordTrace]
  refine ⟨31884857561408267453318777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85026286830422046542183405 31884857561408267453318777)
  ·
    refine ⟨23913643171056200589989083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31884857561408267453318777 23913643171056200589989083)
    ·
      refine ⟨35870464756584300884983625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23913643171056200589989083 35870464756584300884983625)
      ·
        refine ⟨26902848567438225663737719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35870464756584300884983625 26902848567438225663737719)
        ·
          refine ⟨40354272851157338495606579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26902848567438225663737719 40354272851157338495606579)
          ·
            refine ⟨60531409276736007743409869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40354272851157338495606579 60531409276736007743409869)
            ·
              refine ⟨22699278478776002903778701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60531409276736007743409869 22699278478776002903778701)
              ·
                refine ⟨8512229429541001088917013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22699278478776002903778701 8512229429541001088917013)
                ·
                  refine ⟨399010754509734426042985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8512229429541001088917013 399010754509734426042985)
                  ·
                    rfl

theorem cell22_3496818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_3496818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496818 prefixEnd_3496818 := by exact prefixLift 3496818
  have htrace : WordTrace (prefixWord ++ tailWord_3496818) baseStart_3496818 baseEnd_3496818 := by
    simpa [prefixWord, tailWord_3496818, baseEnd_3496818] using wordTrace_append hprefix tailTrace_3496818
  have hstable : (prefixWord ++ tailWord_3496818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496818).length < 2 ^ (prefixWord ++ tailWord_3496818).sum := by decide
  have hdescent : baseEnd_3496818 < baseStart_3496818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496863 : List Nat := [1, 1, 2, 5, 2, 1, 10]
def baseStart_3496863 : Nat := 118140960795 + 3496863 * 2 ^ 59
def prefixEnd_3496863 : Nat := 4983230072969 + 3 ^ 40 * 3496863 * 2
def baseEnd_3496863 : Nat := 44335098812919931879771

theorem tailTrace_3496863 : CollatzResearch.WordTrace tailWord_3496863 prefixEnd_3496863 44335098812919931879771 := by
  unfold tailWord_3496863
  simp only [CollatzResearch.WordTrace]
  refine ⟨127541071530470042498663243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85027381020313361665775495 127541071530470042498663243)
  ·
    refine ⟨191311607295705063747994865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127541071530470042498663243 191311607295705063747994865)
    ·
      refine ⟨143483705471778797810996149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191311607295705063747994865 143483705471778797810996149)
      ·
        refine ⟨13451597387979262294780889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143483705471778797810996149 13451597387979262294780889)
        ·
          refine ⟨10088698040984446721085667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13451597387979262294780889 10088698040984446721085667)
          ·
            refine ⟨15133047061476670081628501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10088698040984446721085667 15133047061476670081628501)
            ·
              refine ⟨44335098812919931879771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15133047061476670081628501 44335098812919931879771)
              ·
                rfl

theorem cell22_3496863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 10].length) (baseStart_3496863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496863 prefixEnd_3496863 := by exact prefixLift 3496863
  have htrace : WordTrace (prefixWord ++ tailWord_3496863) baseStart_3496863 baseEnd_3496863 := by
    simpa [prefixWord, tailWord_3496863, baseEnd_3496863] using wordTrace_append hprefix tailTrace_3496863
  have hstable : (prefixWord ++ tailWord_3496863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496863).length < 2 ^ (prefixWord ++ tailWord_3496863).sum := by decide
  have hdescent : baseEnd_3496863 < baseStart_3496863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496865 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 4, 4]
def baseStart_3496865 : Nat := 118140960795 + 3496865 * 2 ^ 59
def prefixEnd_3496865 : Nat := 4983230072969 + 3 ^ 40 * 3496865 * 2
def baseEnd_3496865 : Nat := 1197048352589710822203811

theorem tailTrace_3496865 : CollatzResearch.WordTrace tailWord_3496865 prefixEnd_3496865 1197048352589710822203811 := by
  unfold tailWord_3496865
  simp only [CollatzResearch.WordTrace]
  refine ⟨127541144476462796840236049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85027429650975197893490699 127541144476462796840236049)
  ·
    refine ⟨95655858357347097630177037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127541144476462796840236049 95655858357347097630177037)
    ·
      refine ⟨35870946884005161611316389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95655858357347097630177037 35870946884005161611316389)
      ·
        refine ⟨6725802540750967802121823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35870946884005161611316389 6725802540750967802121823)
        ·
          refine ⟨10088703811126451703182735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6725802540750967802121823 10088703811126451703182735)
          ·
            refine ⟨15133055716689677554774103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10088703811126451703182735 15133055716689677554774103)
            ·
              refine ⟨22699583575034516332161155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15133055716689677554774103 22699583575034516332161155)
              ·
                refine ⟨34049375362551774498241733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22699583575034516332161155 34049375362551774498241733)
                ·
                  refine ⟨6384257880478457718420325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34049375362551774498241733 6384257880478457718420325)
                  ·
                    refine ⟨1197048352589710822203811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6384257880478457718420325 1197048352589710822203811)
                    ·
                      rfl

theorem cell22_3496865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_3496865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496865 prefixEnd_3496865 := by exact prefixLift 3496865
  have htrace : WordTrace (prefixWord ++ tailWord_3496865) baseStart_3496865 baseEnd_3496865 := by
    simpa [prefixWord, tailWord_3496865, baseEnd_3496865] using wordTrace_append hprefix tailTrace_3496865
  have hstable : (prefixWord ++ tailWord_3496865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496865).length < 2 ^ (prefixWord ++ tailWord_3496865).sum := by decide
  have hdescent : baseEnd_3496865 < baseStart_3496865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496912 : List Nat := [2, 1, 1, 1, 1, 2, 3, 7, 1, 3]
def baseStart_3496912 : Nat := 118140960795 + 3496912 * 2 ^ 59
def prefixEnd_3496912 : Nat := 4983230072969 + 3 ^ 40 * 3496912 * 2
def baseEnd_3496912 : Nat := 1197064441650218366278667

theorem tailTrace_3496912 : CollatzResearch.WordTrace tailWord_3496912 prefixEnd_3496912 1197064441650218366278667 := by
  unfold tailWord_3496912
  simp only [CollatzResearch.WordTrace]
  refine ⟨63771429353646261933598495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85028572471528349244797993 63771429353646261933598495)
  ·
    refine ⟨95657144030469392900397743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63771429353646261933598495 95657144030469392900397743)
    ·
      refine ⟨143485716045704089350596615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95657144030469392900397743 143485716045704089350596615)
      ·
        refine ⟨215228574068556134025894923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143485716045704089350596615 215228574068556134025894923)
        ·
          refine ⟨322842861102834201038842385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215228574068556134025894923 322842861102834201038842385)
          ·
            refine ⟨242132145827125650779131789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322842861102834201038842385 242132145827125650779131789)
            ·
              refine ⟨90799554685172119042174421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242132145827125650779131789 90799554685172119042174421)
              ·
                refine ⟨2128114562933721540050963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90799554685172119042174421 2128114562933721540050963)
                ·
                  refine ⟨3192171844400582310076445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128114562933721540050963 3192171844400582310076445)
                  ·
                    refine ⟨1197064441650218366278667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3192171844400582310076445 1197064441650218366278667)
                    ·
                      rfl

theorem cell22_3496912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 1, 3].length) (baseStart_3496912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496912 prefixEnd_3496912 := by exact prefixLift 3496912
  have htrace : WordTrace (prefixWord ++ tailWord_3496912) baseStart_3496912 baseEnd_3496912 := by
    simpa [prefixWord, tailWord_3496912, baseEnd_3496912] using wordTrace_append hprefix tailTrace_3496912
  have hstable : (prefixWord ++ tailWord_3496912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496912).length < 2 ^ (prefixWord ++ tailWord_3496912).sum := by decide
  have hdescent : baseEnd_3496912 < baseStart_3496912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496948 : List Nat := [2, 6, 2, 1, 1, 1, 3, 6]
def baseStart_3496948 : Nat := 118140960795 + 3496948 * 2 ^ 59
def prefixEnd_3496948 : Nat := 4983230072969 + 3 ^ 40 * 3496948 * 2
def baseEnd_3496948 : Nat := 133008529465102919153173

theorem tailTrace_3496948 : CollatzResearch.WordTrace tailWord_3496948 prefixEnd_3496948 133008529465102919153173 := by
  unfold tailWord_3496948
  simp only [CollatzResearch.WordTrace]
  refine ⟨63772085867581051007753749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85029447823441401343671665 63772085867581051007753749)
  ·
    refine ⟨2989316525042861765988457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63772085867581051007753749 2989316525042861765988457)
    ·
      refine ⟨2241987393782146324491343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2989316525042861765988457 2241987393782146324491343)
      ·
        refine ⟨3362981090673219486737015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241987393782146324491343 3362981090673219486737015)
        ·
          refine ⟨5044471636009829230105523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362981090673219486737015 5044471636009829230105523)
          ·
            refine ⟨7566707454014743845158285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044471636009829230105523 7566707454014743845158285)
            ·
              refine ⟨2837515295255528941934357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7566707454014743845158285 2837515295255528941934357)
              ·
                refine ⟨133008529465102919153173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2837515295255528941934357 133008529465102919153173)
                ·
                  rfl

theorem cell22_3496948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 6].length) (baseStart_3496948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496948 prefixEnd_3496948 := by exact prefixLift 3496948
  have htrace : WordTrace (prefixWord ++ tailWord_3496948) baseStart_3496948 baseEnd_3496948 := by
    simpa [prefixWord, tailWord_3496948, baseEnd_3496948] using wordTrace_append hprefix tailTrace_3496948
  have hstable : (prefixWord ++ tailWord_3496948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496948).length < 2 ^ (prefixWord ++ tailWord_3496948).sum := by decide
  have hdescent : baseEnd_3496948 < baseStart_3496948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496955 : List Nat := [1, 1, 1, 1, 1, 3, 3, 6, 1, 4]
def baseStart_3496955 : Nat := 118140960795 + 3496955 * 2 ^ 59
def prefixEnd_3496955 : Nat := 4983230072969 + 3 ^ 40 * 3496955 * 2
def baseEnd_3496955 : Nat := 1197079161428980587453535

theorem tailTrace_3496955 : CollatzResearch.WordTrace tailWord_3496955 prefixEnd_3496955 1197079161428980587453535 := by
  unfold tailWord_3496955
  simp only [CollatzResearch.WordTrace]
  refine ⟨127544427046136742211012319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85029618030757828140674879 127544427046136742211012319)
  ·
    refine ⟨191316640569205113316518479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127544427046136742211012319 191316640569205113316518479)
    ·
      refine ⟨286974960853807669974777719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191316640569205113316518479 286974960853807669974777719)
      ·
        refine ⟨430462441280711504962166579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286974960853807669974777719 430462441280711504962166579)
        ·
          refine ⟨645693661921067257443249869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430462441280711504962166579 645693661921067257443249869)
          ·
            refine ⟨242135123220400221541218701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 645693661921067257443249869 242135123220400221541218701)
            ·
              refine ⟨90800671207650083077957013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242135123220400221541218701 90800671207650083077957013)
              ·
                refine ⟨4256281462858597644279235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90800671207650083077957013 4256281462858597644279235)
                ·
                  refine ⟨6384422194287896466418853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256281462858597644279235 6384422194287896466418853)
                  ·
                    refine ⟨1197079161428980587453535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6384422194287896466418853 1197079161428980587453535)
                    ·
                      rfl

theorem cell22_3496955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 4].length) (baseStart_3496955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496955 prefixEnd_3496955 := by exact prefixLift 3496955
  have htrace : WordTrace (prefixWord ++ tailWord_3496955) baseStart_3496955 baseEnd_3496955 := by
    simpa [prefixWord, tailWord_3496955, baseEnd_3496955] using wordTrace_append hprefix tailTrace_3496955
  have hstable : (prefixWord ++ tailWord_3496955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496955).length < 2 ^ (prefixWord ++ tailWord_3496955).sum := by decide
  have hdescent : baseEnd_3496955 < baseStart_3496955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496972 : List Nat := [2, 2, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_3496972 : Nat := 118140960795 + 3496972 * 2 ^ 59
def prefixEnd_3496972 : Nat := 4983230072969 + 3 ^ 40 * 3496972 * 2
def baseEnd_3496972 : Nat := 1197084980876398209778483

theorem tailTrace_3496972 : CollatzResearch.WordTrace tailWord_3496972 prefixEnd_3496972 1197084980876398209778483 := by
  unfold tailWord_3496972
  simp only [CollatzResearch.WordTrace]
  refine ⟨63772523543537577057190585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85030031391383436076254113 63772523543537577057190585)
  ·
    refine ⟨47829392657653182792892939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63772523543537577057190585 47829392657653182792892939)
    ·
      refine ⟨71744088986479774189339409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47829392657653182792892939 71744088986479774189339409)
      ·
        refine ⟨53808066739859830642004557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71744088986479774189339409 53808066739859830642004557)
        ·
          refine ⟨20178025027447436490751709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53808066739859830642004557 20178025027447436490751709)
          ·
            refine ⟨7566759385292788684031891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20178025027447436490751709 7566759385292788684031891)
            ·
              refine ⟨11350139077939183026047837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7566759385292788684031891 11350139077939183026047837)
              ·
                refine ⟨4256302154227193634767939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11350139077939183026047837 4256302154227193634767939)
                ·
                  refine ⟨6384453231340790452151909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256302154227193634767939 6384453231340790452151909)
                  ·
                    refine ⟨1197084980876398209778483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6384453231340790452151909 1197084980876398209778483)
                    ·
                      rfl

theorem cell22_3496972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_3496972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3496972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3496972 prefixEnd_3496972 := by exact prefixLift 3496972
  have htrace : WordTrace (prefixWord ++ tailWord_3496972) baseStart_3496972 baseEnd_3496972 := by
    simpa [prefixWord, tailWord_3496972, baseEnd_3496972] using wordTrace_append hprefix tailTrace_3496972
  have hstable : (prefixWord ++ tailWord_3496972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496972).length < 2 ^ (prefixWord ++ tailWord_3496972).sum := by decide
  have hdescent : baseEnd_3496972 < baseStart_3496972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
