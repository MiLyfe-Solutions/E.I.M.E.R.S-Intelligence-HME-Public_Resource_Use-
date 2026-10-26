import V185TrunkScan22Chunk318

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2848514 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 6]
def baseStart_2848514 : Nat := 118140960795 + 2848514 * 2 ^ 59
def prefixEnd_2848514 : Nat := 4983230072969 + 3 ^ 40 * 2848514 * 2
def baseEnd_2848514 : Nat := 325034851791416313238873

theorem tailTrace_2848514 : CollatzResearch.WordTrace tailWord_2848514 prefixEnd_2848514 325034851791416313238873 := by
  unfold tailWord_2848514
  simp only [CollatzResearch.WordTrace]
  refine ⟨25973460200581935076266149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69262560534885160203376397 25973460200581935076266149)
  ·
    refine ⟨4870023787609112826799903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25973460200581935076266149 4870023787609112826799903)
    ·
      refine ⟨7305035681413669240199855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4870023787609112826799903 7305035681413669240199855)
      ·
        refine ⟨10957553522120503860299783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7305035681413669240199855 10957553522120503860299783)
        ·
          refine ⟨16436330283180755790449675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10957553522120503860299783 16436330283180755790449675)
          ·
            refine ⟨24654495424771133685674513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16436330283180755790449675 24654495424771133685674513)
            ·
              refine ⟨18490871568578350264255885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24654495424771133685674513 18490871568578350264255885)
              ·
                refine ⟨6934076838216881349095957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18490871568578350264255885 6934076838216881349095957)
                ·
                  refine ⟨325034851791416313238873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6934076838216881349095957 325034851791416313238873)
                  ·
                    rfl

theorem cell22_2848514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_2848514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848514 prefixEnd_2848514 := by exact prefixLift 2848514
  have htrace : WordTrace (prefixWord ++ tailWord_2848514) baseStart_2848514 baseEnd_2848514 := by
    simpa [prefixWord, tailWord_2848514, baseEnd_2848514] using wordTrace_append hprefix tailTrace_2848514
  have hstable : (prefixWord ++ tailWord_2848514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848514).length < 2 ^ (prefixWord ++ tailWord_2848514).sum := by decide
  have hdescent : baseEnd_2848514 < baseStart_2848514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848563 : List Nat := [1, 1, 1, 2, 7, 2, 1, 2, 2, 3]
def baseStart_2848563 : Nat := 118140960795 + 2848563 * 2 ^ 59
def prefixEnd_2848563 : Nat := 4983230072969 + 3 ^ 40 * 2848563 * 2
def baseEnd_2848563 : Nat := 975121329075629145241469

theorem tailTrace_2848563 : CollatzResearch.WordTrace tailWord_2848563 prefixEnd_2848563 975121329075629145241469 := by
  unfold tailWord_2848563
  simp only [CollatzResearch.WordTrace]
  refine ⟨103895627979150221673598343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69263751986100147782398895 103895627979150221673598343)
  ·
    refine ⟨155843441968725332510397515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103895627979150221673598343 155843441968725332510397515)
    ·
      refine ⟨233765162953087998765596273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155843441968725332510397515 233765162953087998765596273)
      ·
        refine ⟨175323872214815999074197205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233765162953087998765596273 175323872214815999074197205)
        ·
          refine ⟨4109153255034749978301497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 175323872214815999074197205 4109153255034749978301497)
          ·
            refine ⟨3081864941276062483726123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4109153255034749978301497 3081864941276062483726123)
            ·
              refine ⟨4622797411914093725589185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081864941276062483726123 4622797411914093725589185)
              ·
                refine ⟨3467098058935570294191889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4622797411914093725589185 3467098058935570294191889)
                ·
                  refine ⟨2600323544201677720643917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3467098058935570294191889 2600323544201677720643917)
                  ·
                    refine ⟨975121329075629145241469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2600323544201677720643917 975121329075629145241469)
                    ·
                      rfl

theorem cell22_2848563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 3].length) (baseStart_2848563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848563 prefixEnd_2848563 := by exact prefixLift 2848563
  have htrace : WordTrace (prefixWord ++ tailWord_2848563) baseStart_2848563 baseEnd_2848563 := by
    simpa [prefixWord, tailWord_2848563, baseEnd_2848563] using wordTrace_append hprefix tailTrace_2848563
  have hstable : (prefixWord ++ tailWord_2848563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848563).length < 2 ^ (prefixWord ++ tailWord_2848563).sum := by decide
  have hdescent : baseEnd_2848563 < baseStart_2848563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848572 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_2848572 : Nat := 118140960795 + 2848572 * 2 ^ 59
def prefixEnd_2848572 : Nat := 4983230072969 + 3 ^ 40 * 2848572 * 2
def baseEnd_2848572 : Nat := 975124409959556121766441

theorem tailTrace_2848572 : CollatzResearch.WordTrace tailWord_2848572 prefixEnd_2848572 975124409959556121766441 := by
  unfold tailWord_2848572
  simp only [CollatzResearch.WordTrace]
  refine ⟨51947978118058808105337985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69263970824078410807117313 51947978118058808105337985)
  ·
    refine ⟨38960983588544106079003489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51947978118058808105337985 38960983588544106079003489)
    ·
      refine ⟨29220737691408079559252617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38960983588544106079003489 29220737691408079559252617)
      ·
        refine ⟨21915553268556059669439463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29220737691408079559252617 21915553268556059669439463)
        ·
          refine ⟨32873329902834089504159195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21915553268556059669439463 32873329902834089504159195)
          ·
            refine ⟨49309994854251134256238793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32873329902834089504159195 49309994854251134256238793)
            ·
              refine ⟨36982496140688350692179095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49309994854251134256238793 36982496140688350692179095)
              ·
                refine ⟨55473744211032526038268643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36982496140688350692179095 55473744211032526038268643)
                ·
                  refine ⟨83210616316548789057402965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55473744211032526038268643 83210616316548789057402965)
                  ·
                    refine ⟨975124409959556121766441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83210616316548789057402965 975124409959556121766441)
                    ·
                      rfl

theorem cell22_2848572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_2848572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848572 prefixEnd_2848572 := by exact prefixLift 2848572
  have htrace : WordTrace (prefixWord ++ tailWord_2848572) baseStart_2848572 baseEnd_2848572 := by
    simpa [prefixWord, tailWord_2848572, baseEnd_2848572] using wordTrace_append hprefix tailTrace_2848572
  have hstable : (prefixWord ++ tailWord_2848572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848572).length < 2 ^ (prefixWord ++ tailWord_2848572).sum := by decide
  have hdescent : baseEnd_2848572 < baseStart_2848572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848608 : List Nat := [2, 1, 1, 3, 3, 2, 3, 3, 1, 3]
def baseStart_2848608 : Nat := 118140960795 + 2848608 * 2 ^ 59
def prefixEnd_2848608 : Nat := 4983230072969 + 3 ^ 40 * 2848608 * 2
def baseEnd_2848608 : Nat := 975136733495264027866331

theorem tailTrace_2848608 : CollatzResearch.WordTrace tailWord_2848608 prefixEnd_2848608 975136733495264027866331 := by
  unfold tailWord_2848608
  simp only [CollatzResearch.WordTrace]
  refine ⟨51948634631993597179493239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69264846175991462905990985 51948634631993597179493239)
  ·
    refine ⟨77922951947990395769239859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51948634631993597179493239 77922951947990395769239859)
    ·
      refine ⟨116884427921985593653859789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77922951947990395769239859 116884427921985593653859789)
      ·
        refine ⟨43831660470744597620197421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116884427921985593653859789 43831660470744597620197421)
        ·
          refine ⟨16436872676529224107574033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43831660470744597620197421 16436872676529224107574033)
          ·
            refine ⟨12327654507396918080680525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16436872676529224107574033 12327654507396918080680525)
            ·
              refine ⟨4622870440273844280255197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12327654507396918080680525 4622870440273844280255197)
              ·
                refine ⟨1733576415102691605095699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4622870440273844280255197 1733576415102691605095699)
                ·
                  refine ⟨2600364622654037407643549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733576415102691605095699 2600364622654037407643549)
                  ·
                    refine ⟨975136733495264027866331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2600364622654037407643549 975136733495264027866331)
                    ·
                      rfl

theorem cell22_2848608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 1, 3].length) (baseStart_2848608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848608 prefixEnd_2848608 := by exact prefixLift 2848608
  have htrace : WordTrace (prefixWord ++ tailWord_2848608) baseStart_2848608 baseEnd_2848608 := by
    simpa [prefixWord, tailWord_2848608, baseEnd_2848608] using wordTrace_append hprefix tailTrace_2848608
  have hstable : (prefixWord ++ tailWord_2848608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848608).length < 2 ^ (prefixWord ++ tailWord_2848608).sum := by decide
  have hdescent : baseEnd_2848608 < baseStart_2848608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848638 : List Nat := [4, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_2848638 : Nat := 118140960795 + 2848638 * 2 ^ 59
def prefixEnd_2848638 : Nat := 4983230072969 + 3 ^ 40 * 2848638 * 2
def baseEnd_2848638 : Nat := 325049001036117983205413

theorem tailTrace_2848638 : CollatzResearch.WordTrace tailWord_2848638 prefixEnd_2848638 325049001036117983205413 := by
  unfold tailWord_2848638
  simp only [CollatzResearch.WordTrace]
  refine ⟨12987295431734813685322321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69265575635919006321719045 12987295431734813685322321)
  ·
    refine ⟨9740471573801110263991741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12987295431734813685322321 9740471573801110263991741)
    ·
      refine ⟨3652676840175416348996903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9740471573801110263991741 3652676840175416348996903)
      ·
        refine ⟨5479015260263124523495355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3652676840175416348996903 5479015260263124523495355)
        ·
          refine ⟨8218522890394686785243033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479015260263124523495355 8218522890394686785243033)
          ·
            refine ⟨6163892167796015088932275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8218522890394686785243033 6163892167796015088932275)
            ·
              refine ⟨9245838251694022633398413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6163892167796015088932275 9245838251694022633398413)
              ·
                refine ⟨3467189344385258487524405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9245838251694022633398413 3467189344385258487524405)
                ·
                  refine ⟨325049001036117983205413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3467189344385258487524405 325049001036117983205413)
                  ·
                    rfl

theorem cell22_2848638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_2848638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848638 prefixEnd_2848638 := by exact prefixLift 2848638
  have htrace : WordTrace (prefixWord ++ tailWord_2848638) baseStart_2848638 baseEnd_2848638 := by
    simpa [prefixWord, tailWord_2848638, baseEnd_2848638] using wordTrace_append hprefix tailTrace_2848638
  have hstable : (prefixWord ++ tailWord_2848638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848638).length < 2 ^ (prefixWord ++ tailWord_2848638).sum := by decide
  have hdescent : baseEnd_2848638 < baseStart_2848638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848732 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2848732 : Nat := 118140960795 + 2848732 * 2 ^ 59
def prefixEnd_2848732 : Nat := 4983230072969 + 3 ^ 40 * 2848732 * 2
def baseEnd_2848732 : Nat := 975179181229369037765951

theorem tailTrace_2848732 : CollatzResearch.WordTrace tailWord_2848732 prefixEnd_2848732 975179181229369037765951 := by
  unfold tailWord_2848732
  simp only [CollatzResearch.WordTrace]
  refine ⟨51950895957768981768250225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69267861277025309024333633 51950895957768981768250225)
  ·
    refine ⟨38963171968326736326187669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51950895957768981768250225 38963171968326736326187669)
    ·
      refine ⟨1826398686015315765290047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38963171968326736326187669 1826398686015315765290047)
      ·
        refine ⟨2739598029022973647935071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1826398686015315765290047 2739598029022973647935071)
        ·
          refine ⟨4109397043534460471902607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739598029022973647935071 4109397043534460471902607)
          ·
            refine ⟨6164095565301690707853911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109397043534460471902607 6164095565301690707853911)
            ·
              refine ⟨9246143347952536061780867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164095565301690707853911 9246143347952536061780867)
              ·
                refine ⟨13869215021928804092671301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9246143347952536061780867 13869215021928804092671301)
                ·
                  refine ⟨2600477816611650767375869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13869215021928804092671301 2600477816611650767375869)
                  ·
                    refine ⟨975179181229369037765951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2600477816611650767375869 975179181229369037765951)
                    ·
                      rfl

theorem cell22_2848732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2848732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848732 prefixEnd_2848732 := by exact prefixLift 2848732
  have htrace : WordTrace (prefixWord ++ tailWord_2848732) baseStart_2848732 baseEnd_2848732 := by
    simpa [prefixWord, tailWord_2848732, baseEnd_2848732] using wordTrace_append hprefix tailTrace_2848732
  have hstable : (prefixWord ++ tailWord_2848732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848732).length < 2 ^ (prefixWord ++ tailWord_2848732).sum := by decide
  have hdescent : baseEnd_2848732 < baseStart_2848732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848807 : List Nat := [1, 1, 7, 1, 2, 2, 2, 1, 5]
def baseStart_2848807 : Nat := 118140960795 + 2848807 * 2 ^ 59
def prefixEnd_2848807 : Nat := 4983230072969 + 3 ^ 40 * 2848807 * 2
def baseEnd_2848807 : Nat := 325068285087364614046907

theorem tailTrace_2848807 : CollatzResearch.WordTrace tailWord_2848807 prefixEnd_2848807 325068285087364614046907 := by
  unfold tailWord_2848807
  simp only [CollatzResearch.WordTrace]
  refine ⟨103904527390266251345480675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69269684926844167563653783 103904527390266251345480675)
  ·
    refine ⟨155856791085399377018221013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103904527390266251345480675 155856791085399377018221013)
    ·
      refine ⟨3652893541064047898864555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 155856791085399377018221013 3652893541064047898864555)
      ·
        refine ⟨5479340311596071848296833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3652893541064047898864555 5479340311596071848296833)
        ·
          refine ⟨4109505233697053886222625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5479340311596071848296833 4109505233697053886222625)
          ·
            refine ⟨3082128925272790414666969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4109505233697053886222625 3082128925272790414666969)
            ·
              refine ⟨2311596693954592811000227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3082128925272790414666969 2311596693954592811000227)
              ·
                refine ⟨3467395040931889216500341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311596693954592811000227 3467395040931889216500341)
                ·
                  refine ⟨325068285087364614046907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3467395040931889216500341 325068285087364614046907)
                  ·
                    rfl

theorem cell22_2848807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 5].length) (baseStart_2848807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848807 prefixEnd_2848807 := by exact prefixLift 2848807
  have htrace : WordTrace (prefixWord ++ tailWord_2848807) baseStart_2848807 baseEnd_2848807 := by
    simpa [prefixWord, tailWord_2848807, baseEnd_2848807] using wordTrace_append hprefix tailTrace_2848807
  have hstable : (prefixWord ++ tailWord_2848807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848807).length < 2 ^ (prefixWord ++ tailWord_2848807).sum := by decide
  have hdescent : baseEnd_2848807 < baseStart_2848807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848820 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_2848820 : Nat := 118140960795 + 2848820 * 2 ^ 59
def prefixEnd_2848820 : Nat := 4983230072969 + 3 ^ 40 * 2848820 * 2
def baseEnd_2848820 : Nat := 975209305427766141565681

theorem tailTrace_2848820 : CollatzResearch.WordTrace tailWord_2848820 prefixEnd_2848820 975209305427766141565681 := by
  unfold tailWord_2848820
  simp only [CollatzResearch.WordTrace]
  refine ⟨51952500769609577282851957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69270001026146103043802609 51952500769609577282851957)
  ·
    refine ⟨4870546947150897870267371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51952500769609577282851957 4870546947150897870267371)
    ·
      refine ⟨7305820420726346805401057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4870546947150897870267371 7305820420726346805401057)
      ·
        refine ⟨5479365315544760104050793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7305820420726346805401057 5479365315544760104050793)
        ·
          refine ⟨4109523986658570078038095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5479365315544760104050793 4109523986658570078038095)
          ·
            refine ⟨6164285979987855117057143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109523986658570078038095 6164285979987855117057143)
            ·
              refine ⟨9246428969981782675585715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164285979987855117057143 9246428969981782675585715)
              ·
                refine ⟨13869643454972674013378573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9246428969981782675585715 13869643454972674013378573)
                ·
                  refine ⟨5201116295614752755016965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13869643454972674013378573 5201116295614752755016965)
                  ·
                    refine ⟨975209305427766141565681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5201116295614752755016965 975209305427766141565681)
                    ·
                      rfl

theorem cell22_2848820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_2848820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848820 prefixEnd_2848820 := by exact prefixLift 2848820
  have htrace : WordTrace (prefixWord ++ tailWord_2848820) baseStart_2848820 baseEnd_2848820 := by
    simpa [prefixWord, tailWord_2848820, baseEnd_2848820] using wordTrace_append hprefix tailTrace_2848820
  have hstable : (prefixWord ++ tailWord_2848820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848820).length < 2 ^ (prefixWord ++ tailWord_2848820).sum := by decide
  have hdescent : baseEnd_2848820 < baseStart_2848820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848831 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 2, 4]
def baseStart_2848831 : Nat := 118140960795 + 2848831 * 2 ^ 59
def prefixEnd_2848831 : Nat := 4983230072969 + 3 ^ 40 * 2848831 * 2
def baseEnd_2848831 : Nat := 975213070952565779540647

theorem tailTrace_2848831 : CollatzResearch.WordTrace tailWord_2848831 prefixEnd_2848831 975213070952565779540647 := by
  unfold tailWord_2848831
  simp only [CollatzResearch.WordTrace]
  refine ⟨103905402742179303444354347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69270268494786202296236231 103905402742179303444354347)
  ·
    refine ⟨155858104113268955166531521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103905402742179303444354347 155858104113268955166531521)
    ·
      refine ⟨116893578084951716374898641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155858104113268955166531521 116893578084951716374898641)
      ·
        refine ⟨87670183563713787281173981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116893578084951716374898641 87670183563713787281173981)
        ·
          refine ⟨32876318836392670230440243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87670183563713787281173981 32876318836392670230440243)
          ·
            refine ⟨49314478254589005345660365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32876318836392670230440243 49314478254589005345660365)
            ·
              refine ⟨18492929345470877004622637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49314478254589005345660365 18492929345470877004622637)
              ·
                refine ⟨6934848504551578876733489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18492929345470877004622637 6934848504551578876733489)
                ·
                  refine ⟨5201136378413684157550117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6934848504551578876733489 5201136378413684157550117)
                  ·
                    refine ⟨975213070952565779540647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5201136378413684157550117 975213070952565779540647)
                    ·
                      rfl

theorem cell22_2848831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_2848831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848831 prefixEnd_2848831 := by exact prefixLift 2848831
  have htrace : WordTrace (prefixWord ++ tailWord_2848831) baseStart_2848831 baseEnd_2848831 := by
    simpa [prefixWord, tailWord_2848831, baseEnd_2848831] using wordTrace_append hprefix tailTrace_2848831
  have hstable : (prefixWord ++ tailWord_2848831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848831).length < 2 ^ (prefixWord ++ tailWord_2848831).sum := by decide
  have hdescent : baseEnd_2848831 < baseStart_2848831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848833 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2848833 : Nat := 118140960795 + 2848833 * 2 ^ 59
def prefixEnd_2848833 : Nat := 4983230072969 + 3 ^ 40 * 2848833 * 2
def baseEnd_2848833 : Nat := 975213755593438440990641

theorem tailTrace_2848833 : CollatzResearch.WordTrace tailWord_2848833 prefixEnd_2848833 975213755593438440990641 := by
  unfold tailWord_2848833
  simp only [CollatzResearch.WordTrace]
  refine ⟨103905475688172057785927153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69270317125448038523951435 103905475688172057785927153)
  ·
    refine ⟨77929106766129043339445365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103905475688172057785927153 77929106766129043339445365)
    ·
      refine ⟨7305853759324597813073003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77929106766129043339445365 7305853759324597813073003)
      ·
        refine ⟨10958780638986896719609505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7305853759324597813073003 10958780638986896719609505)
        ·
          refine ⟨8219085479240172539707129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10958780638986896719609505 8219085479240172539707129)
          ·
            refine ⟨6164314109430129404780347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8219085479240172539707129 6164314109430129404780347)
            ·
              refine ⟨9246471164145194107170521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164314109430129404780347 9246471164145194107170521)
              ·
                refine ⟨6934853373108895580377891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9246471164145194107170521 6934853373108895580377891)
                ·
                  refine ⟨10402280059663343370566837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6934853373108895580377891 10402280059663343370566837)
                  ·
                    refine ⟨975213755593438440990641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10402280059663343370566837 975213755593438440990641)
                    ·
                      rfl

theorem cell22_2848833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2848833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848833 prefixEnd_2848833 := by exact prefixLift 2848833
  have htrace : WordTrace (prefixWord ++ tailWord_2848833) baseStart_2848833 baseEnd_2848833 := by
    simpa [prefixWord, tailWord_2848833, baseEnd_2848833] using wordTrace_append hprefix tailTrace_2848833
  have hstable : (prefixWord ++ tailWord_2848833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848833).length < 2 ^ (prefixWord ++ tailWord_2848833).sum := by decide
  have hdescent : baseEnd_2848833 < baseStart_2848833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848918 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2848918 : Nat := 118140960795 + 2848918 * 2 ^ 59
def prefixEnd_2848918 : Nat := 4983230072969 + 3 ^ 40 * 2848918 * 2
def baseEnd_2848918 : Nat := 975242852830526552615381

theorem tailTrace_2848918 : CollatzResearch.WordTrace tailWord_2848918 prefixEnd_2848918 975242852830526552615381 := by
  unfold tailWord_2848918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6494285993304007331423213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69272383928576078201847605 6494285993304007331423213)
  ·
    refine ⟨2435357247489002749283705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6494285993304007331423213 2435357247489002749283705)
    ·
      refine ⟨1826517935616752061962779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2435357247489002749283705 1826517935616752061962779)
      ·
        refine ⟨2739776903425128092944169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1826517935616752061962779 2739776903425128092944169)
        ·
          refine ⟨2054832677568846069708127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2739776903425128092944169 2054832677568846069708127)
          ·
            refine ⟨3082249016353269104562191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054832677568846069708127 3082249016353269104562191)
            ·
              refine ⟨4623373524529903656843287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3082249016353269104562191 4623373524529903656843287)
              ·
                refine ⟨6935060286794855485264931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4623373524529903656843287 6935060286794855485264931)
                ·
                  refine ⟨10402590430192283227897397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6935060286794855485264931 10402590430192283227897397)
                  ·
                    refine ⟨975242852830526552615381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10402590430192283227897397 975242852830526552615381)
                    ·
                      rfl

theorem cell22_2848918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2848918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848918 prefixEnd_2848918 := by exact prefixLift 2848918
  have htrace : WordTrace (prefixWord ++ tailWord_2848918) baseStart_2848918 baseEnd_2848918 := by
    simpa [prefixWord, tailWord_2848918, baseEnd_2848918] using wordTrace_append hprefix tailTrace_2848918
  have hstable : (prefixWord ++ tailWord_2848918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848918).length < 2 ^ (prefixWord ++ tailWord_2848918).sum := by decide
  have hdescent : baseEnd_2848918 < baseStart_2848918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848921 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 5, 4]
def baseStart_2848921 : Nat := 118140960795 + 2848921 * 2 ^ 59
def prefixEnd_2848921 : Nat := 4983230072969 + 3 ^ 40 * 2848921 * 2
def baseEnd_2848921 : Nat := 975243879791835544790371

theorem tailTrace_2848921 : CollatzResearch.WordTrace tailWord_2848921 prefixEnd_2848921 975243879791835544790371 := by
  unfold tailWord_2848921
  simp only [CollatzResearch.WordTrace]
  refine ⟨103908685311853248815130617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69272456874568832543420411 103908685311853248815130617)
  ·
    refine ⟨77931513983889936611347963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103908685311853248815130617 77931513983889936611347963)
    ·
      refine ⟨116897270975834904917021945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77931513983889936611347963 116897270975834904917021945)
      ·
        refine ⟨87672953231876178687766459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116897270975834904917021945 87672953231876178687766459)
        ·
          refine ⟨131509429847814268031649689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87672953231876178687766459 131509429847814268031649689)
          ·
            refine ⟨98632072385860701023737267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131509429847814268031649689 98632072385860701023737267)
            ·
              refine ⟨147948108578791051535605901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98632072385860701023737267 147948108578791051535605901)
              ·
                refine ⟨55480540717046644325852213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147948108578791051535605901 55480540717046644325852213)
                ·
                  refine ⟨5201300692223122905548645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55480540717046644325852213 5201300692223122905548645)
                  ·
                    refine ⟨975243879791835544790371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5201300692223122905548645 975243879791835544790371)
                    ·
                      rfl

theorem cell22_2848921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_2848921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848921 prefixEnd_2848921 := by exact prefixLift 2848921
  have htrace : WordTrace (prefixWord ++ tailWord_2848921) baseStart_2848921 baseEnd_2848921 := by
    simpa [prefixWord, tailWord_2848921, baseEnd_2848921] using wordTrace_append hprefix tailTrace_2848921
  have hstable : (prefixWord ++ tailWord_2848921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848921).length < 2 ^ (prefixWord ++ tailWord_2848921).sum := by decide
  have hdescent : baseEnd_2848921 < baseStart_2848921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848925 : List Nat := [1, 4, 2, 1, 1, 4, 3, 1, 5]
def baseStart_2848925 : Nat := 118140960795 + 2848925 * 2 ^ 59
def prefixEnd_2848925 : Nat := 4983230072969 + 3 ^ 40 * 2848925 * 2
def baseEnd_2848925 : Nat := 325081749691193622563453

theorem tailTrace_2848925 : CollatzResearch.WordTrace tailWord_2848925 prefixEnd_2848925 325081749691193622563453 := by
  unfold tailWord_2848925
  simp only [CollatzResearch.WordTrace]
  refine ⟨103908831203838757498276229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69272554135892504998850819 103908831203838757498276229)
  ·
    refine ⟨19482905850719767030926793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103908831203838757498276229 19482905850719767030926793)
    ·
      refine ⟨14612179388039825273195095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19482905850719767030926793 14612179388039825273195095)
      ·
        refine ⟨21918269082059737909792643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14612179388039825273195095 21918269082059737909792643)
        ·
          refine ⟨32877403623089606864688965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21918269082059737909792643 32877403623089606864688965)
          ·
            refine ⟨6164513179329301287129181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32877403623089606864688965 6164513179329301287129181)
            ·
              refine ⟨2311692442248487982673443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6164513179329301287129181 2311692442248487982673443)
              ·
                refine ⟨3467538663372731974010165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311692442248487982673443 3467538663372731974010165)
                ·
                  refine ⟨325081749691193622563453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3467538663372731974010165 325081749691193622563453)
                  ·
                    rfl

theorem cell22_2848925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_2848925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848925 prefixEnd_2848925 := by exact prefixLift 2848925
  have htrace : WordTrace (prefixWord ++ tailWord_2848925) baseStart_2848925 baseEnd_2848925 := by
    simpa [prefixWord, tailWord_2848925, baseEnd_2848925] using wordTrace_append hprefix tailTrace_2848925
  have hstable : (prefixWord ++ tailWord_2848925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848925).length < 2 ^ (prefixWord ++ tailWord_2848925).sum := by decide
  have hdescent : baseEnd_2848925 < baseStart_2848925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849000 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 2, 4]
def baseStart_2849000 : Nat := 118140960795 + 2849000 * 2 ^ 59
def prefixEnd_2849000 : Nat := 4983230072969 + 3 ^ 40 * 2849000 * 2
def baseEnd_2849000 : Nat := 975270923106305672065129

theorem tailTrace_2849000 : CollatzResearch.WordTrace tailWord_2849000 prefixEnd_2849000 975270923106305672065129 := by
  unfold tailWord_2849000
  simp only [CollatzResearch.WordTrace]
  refine ⟨51955783339283522653628227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69274377785711363538170969 51955783339283522653628227)
  ·
    refine ⟨77933675008925283980442341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51955783339283522653628227 77933675008925283980442341)
    ·
      refine ⟨14612564064173490746332939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77933675008925283980442341 14612564064173490746332939)
      ·
        refine ⟨21918846096260236119499409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14612564064173490746332939 21918846096260236119499409)
        ·
          refine ⟨16439134572195177089624557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21918846096260236119499409 16439134572195177089624557)
          ·
            refine ⟨6164675464573191408609209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16439134572195177089624557 6164675464573191408609209)
            ·
              refine ⟨4623506598429893556456907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6164675464573191408609209 4623506598429893556456907)
              ·
                refine ⟨6935259897644840334685361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4623506598429893556456907 6935259897644840334685361)
                ·
                  refine ⟨5201444923233630251014021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6935259897644840334685361 5201444923233630251014021)
                  ·
                    refine ⟨975270923106305672065129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5201444923233630251014021 975270923106305672065129)
                    ·
                      rfl

theorem cell22_2849000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_2849000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849000 prefixEnd_2849000 := by exact prefixLift 2849000
  have htrace : WordTrace (prefixWord ++ tailWord_2849000) baseStart_2849000 baseEnd_2849000 := by
    simpa [prefixWord, tailWord_2849000, baseEnd_2849000] using wordTrace_append hprefix tailTrace_2849000
  have hstable : (prefixWord ++ tailWord_2849000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849000).length < 2 ^ (prefixWord ++ tailWord_2849000).sum := by decide
  have hdescent : baseEnd_2849000 < baseStart_2849000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849103 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 1, 5]
def baseStart_2849103 : Nat := 118140960795 + 2849103 * 2 ^ 59
def prefixEnd_2849103 : Nat := 4983230072969 + 3 ^ 40 * 2849103 * 2
def baseEnd_2849103 : Nat := 975306182111247736739813

theorem tailTrace_2849103 : CollatzResearch.WordTrace tailWord_2849103 prefixEnd_2849103 975306182111247736739813 := by
  unfold tailWord_2849103
  simp only [CollatzResearch.WordTrace]
  refine ⟨103915323397193893898255963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69276882264795929265503975 103915323397193893898255963)
  ·
    refine ⟨155872985095790840847383945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103915323397193893898255963 155872985095790840847383945)
    ·
      refine ⟨116904738821843130635537959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155872985095790840847383945 116904738821843130635537959)
      ·
        refine ⟨175357108232764695953306939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116904738821843130635537959 175357108232764695953306939)
        ·
          refine ⟨263035662349147043929960409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175357108232764695953306939 263035662349147043929960409)
          ·
            refine ⟨197276746761860282947470307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263035662349147043929960409 197276746761860282947470307)
            ·
              refine ⟨295915120142790424421205461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197276746761860282947470307 295915120142790424421205461)
              ·
                refine ⟨6935510628346650572372003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 295915120142790424421205461 6935510628346650572372003)
                ·
                  refine ⟨10403265942519975858558005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6935510628346650572372003 10403265942519975858558005)
                  ·
                    refine ⟨975306182111247736739813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10403265942519975858558005 975306182111247736739813)
                    ·
                      rfl

theorem cell22_2849103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_2849103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849103 prefixEnd_2849103 := by exact prefixLift 2849103
  have htrace : WordTrace (prefixWord ++ tailWord_2849103) baseStart_2849103 baseEnd_2849103 := by
    simpa [prefixWord, tailWord_2849103, baseEnd_2849103] using wordTrace_append hprefix tailTrace_2849103
  have hstable : (prefixWord ++ tailWord_2849103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849103).length < 2 ^ (prefixWord ++ tailWord_2849103).sum := by decide
  have hdescent : baseEnd_2849103 < baseStart_2849103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849148 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_2849148 : Nat := 118140960795 + 2849148 * 2 ^ 59
def prefixEnd_2849148 : Nat := 4983230072969 + 3 ^ 40 * 2849148 * 2
def baseEnd_2849148 : Nat := 975321586530882619364675

theorem tailTrace_2849148 : CollatzResearch.WordTrace tailWord_2849148 prefixEnd_2849148 975321586530882619364675 := by
  unfold tailWord_2849148
  simp only [CollatzResearch.WordTrace]
  refine ⟨51958482341015433291822049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69277976454687244389096065 51958482341015433291822049)
  ·
    refine ⟨38968861755761574968866537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51958482341015433291822049 38968861755761574968866537)
    ·
      refine ⟨29226646316821181226649903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38968861755761574968866537 29226646316821181226649903)
      ·
        refine ⟨43839969475231771839974855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29226646316821181226649903 43839969475231771839974855)
        ·
          refine ⟨65759954212847657759962283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43839969475231771839974855 65759954212847657759962283)
          ·
            refine ⟨98639931319271486639943425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65759954212847657759962283 98639931319271486639943425)
            ·
              refine ⟨73979948489453614979957569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98639931319271486639943425 73979948489453614979957569)
              ·
                refine ⟨55484961367090211234968177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73979948489453614979957569 55484961367090211234968177)
                ·
                  refine ⟨41613721025317658426226133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55484961367090211234968177 41613721025317658426226133)
                  ·
                    refine ⟨975321586530882619364675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41613721025317658426226133 975321586530882619364675)
                    ·
                      rfl

theorem cell22_2849148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_2849148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849148 prefixEnd_2849148 := by exact prefixLift 2849148
  have htrace : WordTrace (prefixWord ++ tailWord_2849148) baseStart_2849148 baseEnd_2849148 := by
    simpa [prefixWord, tailWord_2849148, baseEnd_2849148] using wordTrace_append hprefix tailTrace_2849148
  have hstable : (prefixWord ++ tailWord_2849148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849148).length < 2 ^ (prefixWord ++ tailWord_2849148).sum := by decide
  have hdescent : baseEnd_2849148 < baseStart_2849148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849193 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 3, 7]
def baseStart_2849193 : Nat := 118140960795 + 2849193 * 2 ^ 59
def prefixEnd_2849193 : Nat := 4983230072969 + 3 ^ 40 * 2849193 * 2
def baseEnd_2849193 : Nat := 975336990950517501989537

theorem tailTrace_2849193 : CollatzResearch.WordTrace tailWord_2849193 prefixEnd_2849193 975336990950517501989537 := by
  unfold tailWord_2849193
  simp only [CollatzResearch.WordTrace]
  refine ⟨103918605966867839269032233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69279070644578559512688155 103918605966867839269032233)
  ·
    refine ⟨77938954475150879451774175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103918605966867839269032233 77938954475150879451774175)
    ·
      refine ⟨116908431712726319177661263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77938954475150879451774175 116908431712726319177661263)
      ·
        refine ⟨175362647569089478766491895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116908431712726319177661263 175362647569089478766491895)
        ·
          refine ⟨263043971353634218149737843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175362647569089478766491895 263043971353634218149737843)
          ·
            refine ⟨394565957030451327224606765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263043971353634218149737843 394565957030451327224606765)
            ·
              refine ⟨147962233886419247709227537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394565957030451327224606765 147962233886419247709227537)
              ·
                refine ⟨110971675414814435781920653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147962233886419247709227537 110971675414814435781920653)
                ·
                  refine ⟨41614378280555413418220245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110971675414814435781920653 41614378280555413418220245)
                  ·
                    refine ⟨975336990950517501989537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41614378280555413418220245 975336990950517501989537)
                    ·
                      rfl

theorem cell22_2849193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_2849193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849193 prefixEnd_2849193 := by exact prefixLift 2849193
  have htrace : WordTrace (prefixWord ++ tailWord_2849193) baseStart_2849193 baseEnd_2849193 := by
    simpa [prefixWord, tailWord_2849193, baseEnd_2849193] using wordTrace_append hprefix tailTrace_2849193
  have hstable : (prefixWord ++ tailWord_2849193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849193).length < 2 ^ (prefixWord ++ tailWord_2849193).sum := by decide
  have hdescent : baseEnd_2849193 < baseStart_2849193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849212 : List Nat := [2, 2, 2, 4, 1, 1, 2, 3, 5]
def baseStart_2849212 : Nat := 118140960795 + 2849212 * 2 ^ 59
def prefixEnd_2849212 : Nat := 4983230072969 + 3 ^ 40 * 2849212 * 2
def baseEnd_2849212 : Nat := 325114498346269261921493

theorem tailTrace_2849212 : CollatzResearch.WordTrace tailWord_2849212 prefixEnd_2849212 325114498346269261921493 := by
  unfold tailWord_2849212
  simp only [CollatzResearch.WordTrace]
  refine ⟨51959649476899502756986945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69279532635866003675982593 51959649476899502756986945)
  ·
    refine ⟨38969737107674627067740209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51959649476899502756986945 38969737107674627067740209)
    ·
      refine ⟨29227302830755970300805157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38969737107674627067740209 29227302830755970300805157)
      ·
        refine ⟨5480119280766744431400967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29227302830755970300805157 5480119280766744431400967)
        ·
          refine ⟨8220178921150116647101451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5480119280766744431400967 8220178921150116647101451)
          ·
            refine ⟨12330268381725174970652177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8220178921150116647101451 12330268381725174970652177)
            ·
              refine ⟨9247701286293881227989133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12330268381725174970652177 9247701286293881227989133)
              ·
                refine ⟨3467887982360205460495925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9247701286293881227989133 3467887982360205460495925)
                ·
                  refine ⟨325114498346269261921493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3467887982360205460495925 325114498346269261921493)
                  ·
                    rfl

theorem cell22_2849212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_2849212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849212 prefixEnd_2849212 := by exact prefixLift 2849212
  have htrace : WordTrace (prefixWord ++ tailWord_2849212) baseStart_2849212 baseEnd_2849212 := by
    simpa [prefixWord, tailWord_2849212, baseEnd_2849212] using wordTrace_append hprefix tailTrace_2849212
  have hstable : (prefixWord ++ tailWord_2849212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849212).length < 2 ^ (prefixWord ++ tailWord_2849212).sum := by decide
  have hdescent : baseEnd_2849212 < baseStart_2849212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849225 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 3, 4]
def baseStart_2849225 : Nat := 118140960795 + 2849225 * 2 ^ 59
def prefixEnd_2849225 : Nat := 4983230072969 + 3 ^ 40 * 2849225 * 2
def baseEnd_2849225 : Nat := 975347945204480085189439

theorem tailTrace_2849225 : CollatzResearch.WordTrace tailWord_2849225 prefixEnd_2849225 975347945204480085189439 := by
  unfold tailWord_2849225
  simp only [CollatzResearch.WordTrace]
  refine ⟨103919773102751908734197129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69279848735167939156131419 103919773102751908734197129)
  ·
    refine ⟨77939829827063931550647847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103919773102751908734197129 77939829827063931550647847)
    ·
      refine ⟨116909744740595897325971771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77939829827063931550647847 116909744740595897325971771)
      ·
        refine ⟨175364617110893845988957657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116909744740595897325971771 175364617110893845988957657)
        ·
          refine ⟨131523462833170384491718243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175364617110893845988957657 131523462833170384491718243)
          ·
            refine ⟨197285194249755576737577365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131523462833170384491718243 197285194249755576737577365)
            ·
              refine ⟨9247743480457292659573939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197285194249755576737577365 9247743480457292659573939)
              ·
                refine ⟨13871615220685938989360909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9247743480457292659573939 13871615220685938989360909)
                ·
                  refine ⟨5201855707757227121010341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13871615220685938989360909 5201855707757227121010341)
                  ·
                    refine ⟨975347945204480085189439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5201855707757227121010341 975347945204480085189439)
                    ·
                      rfl

theorem cell22_2849225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_2849225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849225 prefixEnd_2849225 := by exact prefixLift 2849225
  have htrace : WordTrace (prefixWord ++ tailWord_2849225) baseStart_2849225 baseEnd_2849225 := by
    simpa [prefixWord, tailWord_2849225, baseEnd_2849225] using wordTrace_append hprefix tailTrace_2849225
  have hstable : (prefixWord ++ tailWord_2849225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849225).length < 2 ^ (prefixWord ++ tailWord_2849225).sum := by decide
  have hdescent : baseEnd_2849225 < baseStart_2849225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849242 : List Nat := [3, 1, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_2849242 : Nat := 118140960795 + 2849242 * 2 ^ 59
def prefixEnd_2849242 : Nat := 4983230072969 + 3 ^ 40 * 2849242 * 2
def baseEnd_2849242 : Nat := 975353764651897707514387

theorem tailTrace_2849242 : CollatzResearch.WordTrace tailWord_2849242 prefixEnd_2849242 975353764651897707514387 := by
  unfold tailWord_2849242
  simp only [CollatzResearch.WordTrace]
  refine ⟨25980098285922580159391495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69280262095793547091710653 25980098285922580159391495)
  ·
    refine ⟨38970147428883870239087243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25980098285922580159391495 38970147428883870239087243)
    ·
      refine ⟨58455221143325805358630865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38970147428883870239087243 58455221143325805358630865)
      ·
        refine ⟨43841415857494354018973149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58455221143325805358630865 43841415857494354018973149)
        ·
          refine ⟨16440530946560382757114931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43841415857494354018973149 16440530946560382757114931)
          ·
            refine ⟨24660796419840574135672397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16440530946560382757114931 24660796419840574135672397)
            ·
              refine ⟨9247798657440215300877149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24660796419840574135672397 9247798657440215300877149)
              ·
                refine ⟨3467924496540080737828931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9247798657440215300877149 3467924496540080737828931)
                ·
                  refine ⟨5201886744810121106743397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467924496540080737828931 5201886744810121106743397)
                  ·
                    refine ⟨975353764651897707514387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5201886744810121106743397 975353764651897707514387)
                    ·
                      rfl

theorem cell22_2849242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_2849242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849242 prefixEnd_2849242 := by exact prefixLift 2849242
  have htrace : WordTrace (prefixWord ++ tailWord_2849242) baseStart_2849242 baseEnd_2849242 := by
    simpa [prefixWord, tailWord_2849242, baseEnd_2849242] using wordTrace_append hprefix tailTrace_2849242
  have hstable : (prefixWord ++ tailWord_2849242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849242).length < 2 ^ (prefixWord ++ tailWord_2849242).sum := by decide
  have hdescent : baseEnd_2849242 < baseStart_2849242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849362 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_2849362 : Nat := 118140960795 + 2849362 * 2 ^ 59
def prefixEnd_2849362 : Nat := 4983230072969 + 3 ^ 40 * 2849362 * 2
def baseEnd_2849362 : Nat := 975394843104257394514019

theorem tailTrace_2849362 : CollatzResearch.WordTrace tailWord_2849362 prefixEnd_2849362 975394843104257394514019 := by
  unfold tailWord_2849362
  simp only [CollatzResearch.WordTrace]
  refine ⟨25981192475813895282983585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69283179935503720754622893 25981192475813895282983585)
  ·
    refine ⟨19485894356860421462237689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25981192475813895282983585 19485894356860421462237689)
    ·
      refine ⟨14614420767645316096678267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19485894356860421462237689 14614420767645316096678267)
      ·
        refine ⟨21921631151467974145017401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14614420767645316096678267 21921631151467974145017401)
        ·
          refine ⟨16441223363600980608763051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21921631151467974145017401 16441223363600980608763051)
          ·
            refine ⟨24661835045401470913144577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16441223363600980608763051 24661835045401470913144577)
            ·
              refine ⟨18496376284051103184858433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24661835045401470913144577 18496376284051103184858433)
              ·
                refine ⟨13872282213038327388643825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18496376284051103184858433 13872282213038327388643825)
                ·
                  refine ⟨10404211659778745541482869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13872282213038327388643825 10404211659778745541482869)
                  ·
                    refine ⟨975394843104257394514019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10404211659778745541482869 975394843104257394514019)
                    ·
                      rfl

theorem cell22_2849362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_2849362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849362 prefixEnd_2849362 := by exact prefixLift 2849362
  have htrace : WordTrace (prefixWord ++ tailWord_2849362) baseStart_2849362 baseEnd_2849362 := by
    simpa [prefixWord, tailWord_2849362, baseEnd_2849362] using wordTrace_append hprefix tailTrace_2849362
  have hstable : (prefixWord ++ tailWord_2849362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849362).length < 2 ^ (prefixWord ++ tailWord_2849362).sum := by decide
  have hdescent : baseEnd_2849362 < baseStart_2849362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849364 : List Nat := [2, 4, 1, 1, 1, 4, 2, 2, 5]
def baseStart_2849364 : Nat := 118140960795 + 2849364 * 2 ^ 59
def prefixEnd_2849364 : Nat := 4983230072969 + 3 ^ 40 * 2849364 * 2
def baseEnd_2849364 : Nat := 325131842581710018654671

theorem tailTrace_2849364 : CollatzResearch.WordTrace tailWord_2849364 prefixEnd_2849364 325131842581710018654671 := by
  unfold tailWord_2849364
  simp only [CollatzResearch.WordTrace]
  refine ⟨51962421424624167736753573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69283228566165556982338097 51962421424624167736753573)
  ·
    refine ⟨9742954017117031450641295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51962421424624167736753573 9742954017117031450641295)
    ·
      refine ⟨14614431025675547175961943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9742954017117031450641295 14614431025675547175961943)
      ·
        refine ⟨21921646538513320763942915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14614431025675547175961943 21921646538513320763942915)
        ·
          refine ⟨32882469807769981145914373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21921646538513320763942915 32882469807769981145914373)
          ·
            refine ⟨6165463088956871464858945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32882469807769981145914373 6165463088956871464858945)
            ·
              refine ⟨4624097316717653598644209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6165463088956871464858945 4624097316717653598644209)
              ·
                refine ⟨3468072987538240198983157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4624097316717653598644209 3468072987538240198983157)
                ·
                  refine ⟨325131842581710018654671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3468072987538240198983157 325131842581710018654671)
                  ·
                    rfl

theorem cell22_2849364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_2849364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849364 prefixEnd_2849364 := by exact prefixLift 2849364
  have htrace : WordTrace (prefixWord ++ tailWord_2849364) baseStart_2849364 baseEnd_2849364 := by
    simpa [prefixWord, tailWord_2849364, baseEnd_2849364] using wordTrace_append hprefix tailTrace_2849364
  have hstable : (prefixWord ++ tailWord_2849364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849364).length < 2 ^ (prefixWord ++ tailWord_2849364).sum := by decide
  have hdescent : baseEnd_2849364 < baseStart_2849364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849375 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 10]
def baseStart_2849375 : Nat := 118140960795 + 2849375 * 2 ^ 59
def prefixEnd_2849375 : Nat := 4983230072969 + 3 ^ 40 * 2849375 * 2
def baseEnd_2849375 : Nat := 325133097756643231312993

theorem tailTrace_2849375 : CollatzResearch.WordTrace tailWord_2849375 prefixEnd_2849375 325133097756643231312993 := by
  unfold tailWord_2849375
  simp only [CollatzResearch.WordTrace]
  refine ⟨103925244052208484352157579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69283496034805656234771719 103925244052208484352157579)
  ·
    refine ⟨155887866078312726528236369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103925244052208484352157579 155887866078312726528236369)
    ·
      refine ⟨116915899558734544896177277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155887866078312726528236369 116915899558734544896177277)
      ·
        refine ⟨43843462334525454336066479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116915899558734544896177277 43843462334525454336066479)
        ·
          refine ⟨65765193501788181504099719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43843462334525454336066479 65765193501788181504099719)
          ·
            refine ⟨98647790252682272256149579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65765193501788181504099719 98647790252682272256149579)
            ·
              refine ⟨147971685379023408384224369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98647790252682272256149579 147971685379023408384224369)
              ·
                refine ⟨110978764034267556288168277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147971685379023408384224369 110978764034267556288168277)
                ·
                  refine ⟨325133097756643231312993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 110978764034267556288168277 325133097756643231312993)
                  ·
                    rfl

theorem cell22_2849375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 10].length) (baseStart_2849375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849375 prefixEnd_2849375 := by exact prefixLift 2849375
  have htrace : WordTrace (prefixWord ++ tailWord_2849375) baseStart_2849375 baseEnd_2849375 := by
    simpa [prefixWord, tailWord_2849375, baseEnd_2849375] using wordTrace_append hprefix tailTrace_2849375
  have hstable : (prefixWord ++ tailWord_2849375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849375).length < 2 ^ (prefixWord ++ tailWord_2849375).sum := by decide
  have hdescent : baseEnd_2849375 < baseStart_2849375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849377 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 3, 4]
def baseStart_2849377 : Nat := 118140960795 + 2849377 * 2 ^ 59
def prefixEnd_2849377 : Nat := 4983230072969 + 3 ^ 40 * 2849377 * 2
def baseEnd_2849377 : Nat := 975399977910802355388973

theorem tailTrace_2849377 : CollatzResearch.WordTrace tailWord_2849377 prefixEnd_2849377 975399977910802355388973 := by
  unfold tailWord_2849377
  simp only [CollatzResearch.WordTrace]
  refine ⟨103925316998201238693730385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69283544665467492462486923 103925316998201238693730385)
  ·
    refine ⟨77943987748650929020297789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103925316998201238693730385 77943987748650929020297789)
    ·
      refine ⟨29228995405744098382611671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77943987748650929020297789 29228995405744098382611671)
      ·
        refine ⟨43843493108616147573917507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29228995405744098382611671 43843493108616147573917507)
        ·
          refine ⟨65765239662924221360876261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43843493108616147573917507 65765239662924221360876261)
          ·
            refine ⟨12330982436798291505164299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65765239662924221360876261 12330982436798291505164299)
            ·
              refine ⟨18496473655197437257746449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12330982436798291505164299 18496473655197437257746449)
              ·
                refine ⟨13872355241398077943309837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18496473655197437257746449 13872355241398077943309837)
                ·
                  refine ⟨5202133215524279228741189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13872355241398077943309837 5202133215524279228741189)
                  ·
                    refine ⟨975399977910802355388973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5202133215524279228741189 975399977910802355388973)
                    ·
                      rfl

theorem cell22_2849377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_2849377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849377 prefixEnd_2849377 := by exact prefixLift 2849377
  have htrace : WordTrace (prefixWord ++ tailWord_2849377) baseStart_2849377 baseEnd_2849377 := by
    simpa [prefixWord, tailWord_2849377, baseEnd_2849377] using wordTrace_append hprefix tailTrace_2849377
  have hstable : (prefixWord ++ tailWord_2849377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849377).length < 2 ^ (prefixWord ++ tailWord_2849377).sum := by decide
  have hdescent : baseEnd_2849377 < baseStart_2849377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849426 : List Nat := [3, 2, 3, 1, 2, 1, 2, 4, 4]
def baseStart_2849426 : Nat := 118140960795 + 2849426 * 2 ^ 59
def prefixEnd_2849426 : Nat := 4983230072969 + 3 ^ 40 * 2849426 * 2
def baseEnd_2849426 : Nat := 325138917204060853637941

theorem tailTrace_2849426 : CollatzResearch.WordTrace tailWord_2849426 prefixEnd_2849426 325138917204060853637941 := by
  unfold tailWord_2849426
  simp only [CollatzResearch.WordTrace]
  refine ⟨25981776043755930015566033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69284736116682480041509421 25981776043755930015566033)
  ·
    refine ⟨19486332032816947511674525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25981776043755930015566033 19486332032816947511674525)
    ·
      refine ⟨7307374512306355316877947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19486332032816947511674525 7307374512306355316877947)
      ·
        refine ⟨10961061768459532975316921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7307374512306355316877947 10961061768459532975316921)
        ·
          refine ⟨8220796326344649731487691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10961061768459532975316921 8220796326344649731487691)
          ·
            refine ⟨12331194489516974597231537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8220796326344649731487691 12331194489516974597231537)
            ·
              refine ⟨9248395867137730947923653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12331194489516974597231537 9248395867137730947923653)
              ·
                refine ⟨1734074225088324552735685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9248395867137730947923653 1734074225088324552735685)
                ·
                  refine ⟨325138917204060853637941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1734074225088324552735685 325138917204060853637941)
                  ·
                    rfl

theorem cell22_2849426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_2849426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849426 prefixEnd_2849426 := by exact prefixLift 2849426
  have htrace : WordTrace (prefixWord ++ tailWord_2849426) baseStart_2849426 baseEnd_2849426 := by
    simpa [prefixWord, tailWord_2849426, baseEnd_2849426] using wordTrace_append hprefix tailTrace_2849426
  have hstable : (prefixWord ++ tailWord_2849426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849426).length < 2 ^ (prefixWord ++ tailWord_2849426).sum := by decide
  have hdescent : baseEnd_2849426 < baseStart_2849426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849441 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 1, 5]
def baseStart_2849441 : Nat := 118140960795 + 2849441 * 2 ^ 59
def prefixEnd_2849441 : Nat := 4983230072969 + 3 ^ 40 * 2849441 * 2
def baseEnd_2849441 : Nat := 975421886418727521788777

theorem tailTrace_2849441 : CollatzResearch.WordTrace tailWord_2849441 prefixEnd_2849441 975421886418727521788777 := by
  unfold tailWord_2849441
  simp only [CollatzResearch.WordTrace]
  refine ⟨103927651269969377624060177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69285100846646251749373451 103927651269969377624060177)
  ·
    refine ⟨77945738452477033218045133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103927651269969377624060177 77945738452477033218045133)
    ·
      refine ⟨29229651919678887456766925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77945738452477033218045133 29229651919678887456766925)
      ·
        refine ⟨10961119469879582796287597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29229651919678887456766925 10961119469879582796287597)
        ·
          refine ⟨4110419801204843548607849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10961119469879582796287597 4110419801204843548607849)
          ·
            refine ⟨3082814850903632661455887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4110419801204843548607849 3082814850903632661455887)
            ·
              refine ⟨4624222276355448992183831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3082814850903632661455887 4624222276355448992183831)
              ·
                refine ⟨6936333414533173488275747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624222276355448992183831 6936333414533173488275747)
                ·
                  refine ⟨10404500121799760232413621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6936333414533173488275747 10404500121799760232413621)
                  ·
                    refine ⟨975421886418727521788777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10404500121799760232413621 975421886418727521788777)
                    ·
                      rfl

theorem cell22_2849441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_2849441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849441 prefixEnd_2849441 := by exact prefixLift 2849441
  have htrace : WordTrace (prefixWord ++ tailWord_2849441) baseStart_2849441 baseEnd_2849441 := by
    simpa [prefixWord, tailWord_2849441, baseEnd_2849441] using wordTrace_append hprefix tailTrace_2849441
  have hstable : (prefixWord ++ tailWord_2849441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849441).length < 2 ^ (prefixWord ++ tailWord_2849441).sum := by decide
  have hdescent : baseEnd_2849441 < baseStart_2849441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849473 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2849473 : Nat := 118140960795 + 2849473 * 2 ^ 59
def prefixEnd_2849473 : Nat := 4983230072969 + 3 ^ 40 * 2849473 * 2
def baseEnd_2849473 : Nat := 975432840672690104988679

theorem tailTrace_2849473 : CollatzResearch.WordTrace tailWord_2849473 prefixEnd_2849473 975432840672690104988679 := by
  unfold tailWord_2849473
  simp only [CollatzResearch.WordTrace]
  refine ⟨103928818405853447089225073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69285878937235631392816715 103928818405853447089225073)
  ·
    refine ⟨77946613804390085316918805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103928818405853447089225073 77946613804390085316918805)
    ·
      refine ⟨3653747522080785249230569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77946613804390085316918805 3653747522080785249230569)
      ·
        refine ⟨2740310641560588936922927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3653747522080785249230569 2740310641560588936922927)
        ·
          refine ⟨4110465962340883405384391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2740310641560588936922927 4110465962340883405384391)
          ·
            refine ⟨6165698943511325108076587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110465962340883405384391 6165698943511325108076587)
            ·
              refine ⟨9248548415266987662114881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6165698943511325108076587 9248548415266987662114881)
              ·
                refine ⟨6936411311450240746586161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9248548415266987662114881 6936411311450240746586161)
                ·
                  refine ⟨5202308483587680559939621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6936411311450240746586161 5202308483587680559939621)
                  ·
                    refine ⟨975432840672690104988679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5202308483587680559939621 975432840672690104988679)
                    ·
                      rfl

theorem cell22_2849473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2849473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849473 prefixEnd_2849473 := by exact prefixLift 2849473
  have htrace : WordTrace (prefixWord ++ tailWord_2849473) baseStart_2849473 baseEnd_2849473 := by
    simpa [prefixWord, tailWord_2849473, baseEnd_2849473] using wordTrace_append hprefix tailTrace_2849473
  have hstable : (prefixWord ++ tailWord_2849473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849473).length < 2 ^ (prefixWord ++ tailWord_2849473).sum := by decide
  have hdescent : baseEnd_2849473 < baseStart_2849473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849486 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_2849486 : Nat := 118140960795 + 2849486 * 2 ^ 59
def prefixEnd_2849486 : Nat := 4983230072969 + 3 ^ 40 * 2849486 * 2
def baseEnd_2849486 : Nat := 975437290838362404413639

theorem tailTrace_2849486 : CollatzResearch.WordTrace tailWord_2849486 prefixEnd_2849486 975437290838362404413639 := by
  unfold tailWord_2849486
  simp only [CollatzResearch.WordTrace]
  refine ⟨12991161569350793788681039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69286195036537566872965541 12991161569350793788681039)
  ·
    refine ⟨19486742354026190683021559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12991161569350793788681039 19486742354026190683021559)
    ·
      refine ⟨29230113531039286024532339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19486742354026190683021559 29230113531039286024532339)
      ·
        refine ⟨43845170296558929036798509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29230113531039286024532339 43845170296558929036798509)
        ·
          refine ⟨16441938861209598388799441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43845170296558929036798509 16441938861209598388799441)
          ·
            refine ⟨12331454145907198791599581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16441938861209598388799441 12331454145907198791599581)
            ·
              refine ⟨4624295304715199546849843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12331454145907198791599581 4624295304715199546849843)
              ·
                refine ⟨6936442957072799320274765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624295304715199546849843 6936442957072799320274765)
                ·
                  refine ⟨2601166108902299745103037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6936442957072799320274765 2601166108902299745103037)
                  ·
                    refine ⟨975437290838362404413639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601166108902299745103037 975437290838362404413639)
                    ·
                      rfl

theorem cell22_2849486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_2849486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849486 prefixEnd_2849486 := by exact prefixLift 2849486
  have htrace : WordTrace (prefixWord ++ tailWord_2849486) baseStart_2849486 baseEnd_2849486 := by
    simpa [prefixWord, tailWord_2849486, baseEnd_2849486] using wordTrace_append hprefix tailTrace_2849486
  have hstable : (prefixWord ++ tailWord_2849486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849486).length < 2 ^ (prefixWord ++ tailWord_2849486).sum := by decide
  have hdescent : baseEnd_2849486 < baseStart_2849486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849492 : List Nat := [2, 4, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_2849492 : Nat := 118140960795 + 2849492 * 2 ^ 59
def prefixEnd_2849492 : Nat := 4983230072969 + 3 ^ 40 * 2849492 * 2
def baseEnd_2849492 : Nat := 975439344760980388763621

theorem tailTrace_2849492 : CollatzResearch.WordTrace tailWord_2849492 prefixEnd_2849492 975439344760980388763621 := by
  unfold tailWord_2849492
  simp only [CollatzResearch.WordTrace]
  refine ⟨51964755696392306667083365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69286340928523075556111153 51964755696392306667083365)
  ·
    refine ⟨9743391693073557500078131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51964755696392306667083365 9743391693073557500078131)
    ·
      refine ⟨14615087539610336250117197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9743391693073557500078131 14615087539610336250117197)
      ·
        refine ⟨5480657827353876093793949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14615087539610336250117197 5480657827353876093793949)
        ·
          refine ⟨2055246685257703535172731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5480657827353876093793949 2055246685257703535172731)
          ·
            refine ⟨3082870027886555302759097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055246685257703535172731 3082870027886555302759097)
            ·
              refine ⟨2312152520914916477069323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3082870027886555302759097 2312152520914916477069323)
              ·
                refine ⟨3468228781372374715603985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312152520914916477069323 3468228781372374715603985)
                ·
                  refine ⟨2601171586029281036702989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3468228781372374715603985 2601171586029281036702989)
                  ·
                    refine ⟨975439344760980388763621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601171586029281036702989 975439344760980388763621)
                    ·
                      rfl

theorem cell22_2849492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_2849492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849492 prefixEnd_2849492 := by exact prefixLift 2849492
  have htrace : WordTrace (prefixWord ++ tailWord_2849492) baseStart_2849492 baseEnd_2849492 := by
    simpa [prefixWord, tailWord_2849492, baseEnd_2849492] using wordTrace_append hprefix tailTrace_2849492
  have hstable : (prefixWord ++ tailWord_2849492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849492).length < 2 ^ (prefixWord ++ tailWord_2849492).sum := by decide
  have hdescent : baseEnd_2849492 < baseStart_2849492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849497 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 1, 7]
def baseStart_2849497 : Nat := 118140960795 + 2849497 * 2 ^ 59
def prefixEnd_2849497 : Nat := 4983230072969 + 3 ^ 40 * 2849497 * 2
def baseEnd_2849497 : Nat := 975441056363162042388605

theorem tailTrace_2849497 : CollatzResearch.WordTrace tailWord_2849497 prefixEnd_2849497 975441056363162042388605 := by
  unfold tailWord_2849497
  simp only [CollatzResearch.WordTrace]
  refine ⟨103929693757766499188098745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69286462505177666125399163 103929693757766499188098745)
  ·
    refine ⟨77947270318324874391074059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103929693757766499188098745 77947270318324874391074059)
    ·
      refine ⟨116920905477487311586611089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77947270318324874391074059 116920905477487311586611089)
      ·
        refine ⟨87690679108115483689958317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116920905477487311586611089 87690679108115483689958317)
        ·
          refine ⟨32884004665543306383734369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87690679108115483689958317 32884004665543306383734369)
          ·
            refine ⟨24663003499157479787800777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32884004665543306383734369 24663003499157479787800777)
            ·
              refine ⟨18497252624368109840850583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24663003499157479787800777 18497252624368109840850583)
              ·
                refine ⟨27745878936552164761275875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18497252624368109840850583 27745878936552164761275875)
                ·
                  refine ⟨41618818404828247141913813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27745878936552164761275875 41618818404828247141913813)
                  ·
                    refine ⟨975441056363162042388605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41618818404828247141913813 975441056363162042388605)
                    ·
                      rfl

theorem cell22_2849497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_2849497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849497 prefixEnd_2849497 := by exact prefixLift 2849497
  have htrace : WordTrace (prefixWord ++ tailWord_2849497) baseStart_2849497 baseEnd_2849497 := by
    simpa [prefixWord, tailWord_2849497, baseEnd_2849497] using wordTrace_append hprefix tailTrace_2849497
  have hstable : (prefixWord ++ tailWord_2849497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849497).length < 2 ^ (prefixWord ++ tailWord_2849497).sum := by decide
  have hdescent : baseEnd_2849497 < baseStart_2849497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849529 : List Nat := [1, 2, 1, 3, 1, 1, 1, 7, 1, 4]
def baseStart_2849529 : Nat := 118140960795 + 2849529 * 2 ^ 59
def prefixEnd_2849529 : Nat := 4983230072969 + 3 ^ 40 * 2849529 * 2
def baseEnd_2849529 : Nat := 975452010617124625588507

theorem tailTrace_2849529 : CollatzResearch.WordTrace tailWord_2849529 prefixEnd_2849529 975452010617124625588507 := by
  unfold tailWord_2849529
  simp only [CollatzResearch.WordTrace]
  refine ⟨103930860893650568653263641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69287240595767045768842427 103930860893650568653263641)
  ·
    refine ⟨77948145670237926489947731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103930860893650568653263641 77948145670237926489947731)
    ·
      refine ⟨116922218505356889734921597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77948145670237926489947731 116922218505356889734921597)
      ·
        refine ⟨43845831939508833650595599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116922218505356889734921597 43845831939508833650595599)
        ·
          refine ⟨65768747909263250475893399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43845831939508833650595599 65768747909263250475893399)
          ·
            refine ⟨98653121863894875713840099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65768747909263250475893399 98653121863894875713840099)
            ·
              refine ⟨147979682795842313570760149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98653121863894875713840099 147979682795842313570760149)
              ·
                refine ⟨3468273815527554224314691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 147979682795842313570760149 3468273815527554224314691)
                ·
                  refine ⟨5202410723291331336472037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3468273815527554224314691 5202410723291331336472037)
                  ·
                    refine ⟨975452010617124625588507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5202410723291331336472037 975452010617124625588507)
                    ·
                      rfl

theorem cell22_2849529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_2849529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849529 prefixEnd_2849529 := by exact prefixLift 2849529
  have htrace : WordTrace (prefixWord ++ tailWord_2849529) baseStart_2849529 baseEnd_2849529 := by
    simpa [prefixWord, tailWord_2849529, baseEnd_2849529] using wordTrace_append hprefix tailTrace_2849529
  have hstable : (prefixWord ++ tailWord_2849529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849529).length < 2 ^ (prefixWord ++ tailWord_2849529).sum := by decide
  have hdescent : baseEnd_2849529 < baseStart_2849529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849576 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2849576 : Nat := 118140960795 + 2849576 * 2 ^ 59
def prefixEnd_2849576 : Nat := 4983230072969 + 3 ^ 40 * 2849576 * 2
def baseEnd_2849576 : Nat := 975468099677632169663363

theorem tailTrace_2849576 : CollatzResearch.WordTrace tailWord_2849576 prefixEnd_2849576 975468099677632169663363 := by
  unfold tailWord_2849576
  simp only [CollatzResearch.WordTrace]
  refine ⟨51966287562240147840112291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69288383416320197120149721 51966287562240147840112291)
  ·
    refine ⟨77949431343360221760168437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51966287562240147840112291 77949431343360221760168437)
    ·
      refine ⟨7307759188440020790015791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77949431343360221760168437 7307759188440020790015791)
      ·
        refine ⟨10961638782660031185023687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7307759188440020790015791 10961638782660031185023687)
        ·
          refine ⟨16442458173990046777535531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10961638782660031185023687 16442458173990046777535531)
          ·
            refine ⟨24663687260985070166303297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16442458173990046777535531 24663687260985070166303297)
            ·
              refine ⟨18497765445738802624727473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24663687260985070166303297 18497765445738802624727473)
              ·
                refine ⟨13873324084304101968545605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18497765445738802624727473 13873324084304101968545605)
                ·
                  refine ⟨2601248265807019119102301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13873324084304101968545605 2601248265807019119102301)
                  ·
                    refine ⟨975468099677632169663363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601248265807019119102301 975468099677632169663363)
                    ·
                      rfl

theorem cell22_2849576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2849576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849576 prefixEnd_2849576 := by exact prefixLift 2849576
  have htrace : WordTrace (prefixWord ++ tailWord_2849576) baseStart_2849576 baseEnd_2849576 := by
    simpa [prefixWord, tailWord_2849576, baseEnd_2849576] using wordTrace_append hprefix tailTrace_2849576
  have hstable : (prefixWord ++ tailWord_2849576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849576).length < 2 ^ (prefixWord ++ tailWord_2849576).sum := by decide
  have hdescent : baseEnd_2849576 < baseStart_2849576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849589 : List Nat := [1, 3, 3, 1, 3, 2, 9]
def baseStart_2849589 : Nat := 118140960795 + 2849589 * 2 ^ 59
def prefixEnd_2849589 : Nat := 4983230072969 + 3 ^ 40 * 2849589 * 2
def baseEnd_2849589 : Nat := 36128612957159424781049

theorem tailTrace_2849589 : CollatzResearch.WordTrace tailWord_2849589 prefixEnd_2849589 36128612957159424781049 := by
  unfold tailWord_2849589
  simp only [CollatzResearch.WordTrace]
  refine ⟨103933049273433198900447821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69288699515622132600298547 103933049273433198900447821)
  ·
    refine ⟨38974893477537449587667933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103933049273433198900447821 38974893477537449587667933)
    ·
      refine ⟨14615585054076543595375475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38974893477537449587667933 14615585054076543595375475)
      ·
        refine ⟨21923377581114815393063213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14615585054076543595375475 21923377581114815393063213)
        ·
          refine ⟨8221266592918055772398705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21923377581114815393063213 8221266592918055772398705)
          ·
            refine ⟨6165949944688541829299029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8221266592918055772398705 6165949944688541829299029)
            ·
              refine ⟨36128612957159424781049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6165949944688541829299029 36128612957159424781049)
              ·
                rfl

theorem cell22_2849589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 9].length) (baseStart_2849589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849589 prefixEnd_2849589 := by exact prefixLift 2849589
  have htrace : WordTrace (prefixWord ++ tailWord_2849589) baseStart_2849589 baseEnd_2849589 := by
    simpa [prefixWord, tailWord_2849589, baseEnd_2849589] using wordTrace_append hprefix tailTrace_2849589
  have hstable : (prefixWord ++ tailWord_2849589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849589).length < 2 ^ (prefixWord ++ tailWord_2849589).sum := by decide
  have hdescent : baseEnd_2849589 < baseStart_2849589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849621 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 3, 3]
def baseStart_2849621 : Nat := 118140960795 + 2849621 * 2 ^ 59
def prefixEnd_2849621 : Nat := 4983230072969 + 3 ^ 40 * 2849621 * 2
def baseEnd_2849621 : Nat := 975483504097267052288225

theorem tailTrace_2849621 : CollatzResearch.WordTrace tailWord_2849621 prefixEnd_2849621 975483504097267052288225 := by
  unfold tailWord_2849621
  simp only [CollatzResearch.WordTrace]
  refine ⟨103934216409317268365612717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69289477606211512243741811 103934216409317268365612717)
  ·
    refine ⟨38975331153493975637104769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103934216409317268365612717 38975331153493975637104769)
    ·
      refine ⟨29231498365120481727828577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38975331153493975637104769 29231498365120481727828577)
      ·
        refine ⟨21923623773840361295871433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29231498365120481727828577 21923623773840361295871433)
        ·
          refine ⟨16442717830380270971903575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21923623773840361295871433 16442717830380270971903575)
          ·
            refine ⟨24664076745570406457855363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16442717830380270971903575 24664076745570406457855363)
            ·
              refine ⟨36996115118355609686783045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24664076745570406457855363 36996115118355609686783045)
              ·
                refine ⟨6936771584691676816271821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36996115118355609686783045 6936771584691676816271821)
                ·
                  refine ⟨2601289344259378806101933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6936771584691676816271821 2601289344259378806101933)
                  ·
                    refine ⟨975483504097267052288225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601289344259378806101933 975483504097267052288225)
                    ·
                      rfl

theorem cell22_2849621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_2849621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849621 prefixEnd_2849621 := by exact prefixLift 2849621
  have htrace : WordTrace (prefixWord ++ tailWord_2849621) baseStart_2849621 baseEnd_2849621 := by
    simpa [prefixWord, tailWord_2849621, baseEnd_2849621] using wordTrace_append hprefix tailTrace_2849621
  have hstable : (prefixWord ++ tailWord_2849621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849621).length < 2 ^ (prefixWord ++ tailWord_2849621).sum := by decide
  have hdescent : baseEnd_2849621 < baseStart_2849621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849726 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2849726 : Nat := 118140960795 + 2849726 * 2 ^ 59
def prefixEnd_2849726 : Nat := 4983230072969 + 3 ^ 40 * 2849726 * 2
def baseEnd_2849726 : Nat := 975519447743081778412903

theorem tailTrace_2849726 : CollatzResearch.WordTrace tailWord_2849726 prefixEnd_2849726 975519447743081778412903 := by
  unfold tailWord_2849726
  simp only [CollatzResearch.WordTrace]
  refine ⟨12992255759242108912273129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69292030715957914198790021 12992255759242108912273129)
  ·
    refine ⟨9744191819431581684204847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12992255759242108912273129 9744191819431581684204847)
    ·
      refine ⟨14616287729147372526307271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9744191819431581684204847 14616287729147372526307271)
      ·
        refine ⟨21924431593721058789460907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14616287729147372526307271 21924431593721058789460907)
        ·
          refine ⟨32886647390581588184191361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21924431593721058789460907 32886647390581588184191361)
          ·
            refine ⟨24664985542936191138143521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32886647390581588184191361 24664985542936191138143521)
            ·
              refine ⟨18498739157202143353607641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24664985542936191138143521 18498739157202143353607641)
              ·
                refine ⟨13874054367901607515205731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18498739157202143353607641 13874054367901607515205731)
                ·
                  refine ⟨20811081551852411272808597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13874054367901607515205731 20811081551852411272808597)
                  ·
                    refine ⟨975519447743081778412903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20811081551852411272808597 975519447743081778412903)
                    ·
                      rfl

theorem cell22_2849726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2849726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849726 prefixEnd_2849726 := by exact prefixLift 2849726
  have htrace : WordTrace (prefixWord ++ tailWord_2849726) baseStart_2849726 baseEnd_2849726 := by
    simpa [prefixWord, tailWord_2849726, baseEnd_2849726] using wordTrace_append hprefix tailTrace_2849726
  have hstable : (prefixWord ++ tailWord_2849726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849726).length < 2 ^ (prefixWord ++ tailWord_2849726).sum := by decide
  have hdescent : baseEnd_2849726 < baseStart_2849726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849728 : List Nat := [2, 1, 1, 2, 3, 3, 2, 3, 2, 3]
def baseStart_2849728 : Nat := 118140960795 + 2849728 * 2 ^ 59
def prefixEnd_2849728 : Nat := 4983230072969 + 3 ^ 40 * 2849728 * 2
def baseEnd_2849728 : Nat := 975520132383954439862897

theorem tailTrace_2849728 : CollatzResearch.WordTrace tailWord_2849728 prefixEnd_2849728 975520132383954439862897 := by
  unfold tailWord_2849728
  simp only [CollatzResearch.WordTrace]
  refine ⟨51969059509964812819878919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69292079346619750426505225 51969059509964812819878919)
  ·
    refine ⟨77953589264947219229818379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51969059509964812819878919 77953589264947219229818379)
    ·
      refine ⟨116930383897420828844727569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77953589264947219229818379 116930383897420828844727569)
      ·
        refine ⟨87697787923065621633545677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116930383897420828844727569 87697787923065621633545677)
        ·
          refine ⟨32886670471149608112579629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87697787923065621633545677 32886670471149608112579629)
          ·
            refine ⟨12332501426681103042217361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32886670471149608112579629 12332501426681103042217361)
            ·
              refine ⟨9249376070010827281663021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12332501426681103042217361 9249376070010827281663021)
              ·
                refine ⟨3468516026254060230623633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9249376070010827281663021 3468516026254060230623633)
                ·
                  refine ⟨2601387019690545172967725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3468516026254060230623633 2601387019690545172967725)
                  ·
                    refine ⟨975520132383954439862897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601387019690545172967725 975520132383954439862897)
                    ·
                      rfl

theorem cell22_2849728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 3].length) (baseStart_2849728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849728 prefixEnd_2849728 := by exact prefixLift 2849728
  have htrace : WordTrace (prefixWord ++ tailWord_2849728) baseStart_2849728 baseEnd_2849728 := by
    simpa [prefixWord, tailWord_2849728, baseEnd_2849728] using wordTrace_append hprefix tailTrace_2849728
  have hstable : (prefixWord ++ tailWord_2849728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849728).length < 2 ^ (prefixWord ++ tailWord_2849728).sum := by decide
  have hdescent : baseEnd_2849728 < baseStart_2849728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849743 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 2, 4]
def baseStart_2849743 : Nat := 118140960795 + 2849743 * 2 ^ 59
def prefixEnd_2849743 : Nat := 4983230072969 + 3 ^ 40 * 2849743 * 2
def baseEnd_2849743 : Nat := 975525267190499400737851

theorem tailTrace_2849743 : CollatzResearch.WordTrace tailWord_2849743 prefixEnd_2849743 975525267190499400737851 := by
  unfold tailWord_2849743
  simp only [CollatzResearch.WordTrace]
  refine ⟨103938666114875283201553883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69292444076583522134369255 103938666114875283201553883)
  ·
    refine ⟨155907999172312924802330825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103938666114875283201553883 155907999172312924802330825)
    ·
      refine ⟨116930999379234693601748119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155907999172312924802330825 116930999379234693601748119)
      ·
        refine ⟨175396499068852040402622179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116930999379234693601748119 175396499068852040402622179)
        ·
          refine ⟨263094748603278060603933269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175396499068852040402622179 263094748603278060603933269)
          ·
            refine ⟨3083141585194664772702343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 263094748603278060603933269 3083141585194664772702343)
            ·
              refine ⟨4624712377791997159053515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083141585194664772702343 4624712377791997159053515)
              ·
                refine ⟨6937068566687995738580273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624712377791997159053515 6937068566687995738580273)
                ·
                  refine ⟨5202801425015996803935205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6937068566687995738580273 5202801425015996803935205)
                  ·
                    refine ⟨975525267190499400737851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5202801425015996803935205 975525267190499400737851)
                    ·
                      rfl

theorem cell22_2849743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 4].length) (baseStart_2849743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849743 prefixEnd_2849743 := by exact prefixLift 2849743
  have htrace : WordTrace (prefixWord ++ tailWord_2849743) baseStart_2849743 baseEnd_2849743 := by
    simpa [prefixWord, tailWord_2849743, baseEnd_2849743] using wordTrace_append hprefix tailTrace_2849743
  have hstable : (prefixWord ++ tailWord_2849743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849743).length < 2 ^ (prefixWord ++ tailWord_2849743).sum := by decide
  have hdescent : baseEnd_2849743 < baseStart_2849743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849762 : List Nat := [3, 3, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2849762 : Nat := 118140960795 + 2849762 * 2 ^ 59
def prefixEnd_2849762 : Nat := 4983230072969 + 3 ^ 40 * 2849762 * 2
def baseEnd_2849762 : Nat := 975531771278789684512793

theorem tailTrace_2849762 : CollatzResearch.WordTrace tailWord_2849762 prefixEnd_2849762 975531771278789684512793 := by
  unfold tailWord_2849762
  simp only [CollatzResearch.WordTrace]
  refine ⟨25984839775451612361623885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69292906067870966297663693 25984839775451612361623885)
  ·
    refine ⟨9744314915794354635608957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25984839775451612361623885 9744314915794354635608957)
    ·
      refine ⟨3654118093422882988353359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9744314915794354635608957 3654118093422882988353359)
      ·
        refine ⟨5481177140134324482530039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3654118093422882988353359 5481177140134324482530039)
        ·
          refine ⟨8221765710201486723795059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5481177140134324482530039 8221765710201486723795059)
          ·
            refine ⟨12332648565302230085692589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8221765710201486723795059 12332648565302230085692589)
            ·
              refine ⟨4624743211988336282134721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12332648565302230085692589 4624743211988336282134721)
              ·
                refine ⟨3468557408991252211601041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4624743211988336282134721 3468557408991252211601041)
                ·
                  refine ⟨2601418056743439158700781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3468557408991252211601041 2601418056743439158700781)
                  ·
                    refine ⟨975531771278789684512793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601418056743439158700781 975531771278789684512793)
                    ·
                      rfl

theorem cell22_2849762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2849762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849762 prefixEnd_2849762 := by exact prefixLift 2849762
  have htrace : WordTrace (prefixWord ++ tailWord_2849762) baseStart_2849762 baseEnd_2849762 := by
    simpa [prefixWord, tailWord_2849762, baseEnd_2849762] using wordTrace_append hprefix tailTrace_2849762
  have hstable : (prefixWord ++ tailWord_2849762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849762).length < 2 ^ (prefixWord ++ tailWord_2849762).sum := by decide
  have hdescent : baseEnd_2849762 < baseStart_2849762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849786 : List Nat := [3, 1, 1, 1, 1, 2, 1, 7, 5]
def baseStart_2849786 : Nat := 118140960795 + 2849786 * 2 ^ 59
def prefixEnd_2849786 : Nat := 4983230072969 + 3 ^ 40 * 2849786 * 2
def baseEnd_2849786 : Nat := 325179995656420540637573

theorem tailTrace_2849786 : CollatzResearch.WordTrace tailWord_2849786 prefixEnd_2849786 325179995656420540637573 := by
  unfold tailWord_2849786
  simp only [CollatzResearch.WordTrace]
  refine ⟨25985058613429875386342303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69293489635813001030246141 25985058613429875386342303)
  ·
    refine ⟨38977587920144813079513455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25985058613429875386342303 38977587920144813079513455)
    ·
      refine ⟨58466381880217219619270183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38977587920144813079513455 58466381880217219619270183)
      ·
        refine ⟨87699572820325829428905275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58466381880217219619270183 87699572820325829428905275)
        ·
          refine ⟨131549359230488744143357913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87699572820325829428905275 131549359230488744143357913)
          ·
            refine ⟨98662019422866558107518435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131549359230488744143357913 98662019422866558107518435)
            ·
              refine ⟨147993029134299837161277653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98662019422866558107518435 147993029134299837161277653)
              ·
                refine ⟨3468586620335152433467445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 147993029134299837161277653 3468586620335152433467445)
                ·
                  refine ⟨325179995656420540637573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3468586620335152433467445 325179995656420540637573)
                  ·
                    rfl

theorem cell22_2849786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_2849786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849786 prefixEnd_2849786 := by exact prefixLift 2849786
  have htrace : WordTrace (prefixWord ++ tailWord_2849786) baseStart_2849786 baseEnd_2849786 := by
    simpa [prefixWord, tailWord_2849786, baseEnd_2849786] using wordTrace_append hprefix tailTrace_2849786
  have hstable : (prefixWord ++ tailWord_2849786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849786).length < 2 ^ (prefixWord ++ tailWord_2849786).sum := by decide
  have hdescent : baseEnd_2849786 < baseStart_2849786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849824 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 3, 3]
def baseStart_2849824 : Nat := 118140960795 + 2849824 * 2 ^ 59
def prefixEnd_2849824 : Nat := 4983230072969 + 3 ^ 40 * 2849824 * 2
def baseEnd_2849824 : Nat := 975552995145842189462603

theorem tailTrace_2849824 : CollatzResearch.WordTrace tailWord_2849824 prefixEnd_2849824 975552995145842189462603 := by
  unfold tailWord_2849824
  simp only [CollatzResearch.WordTrace]
  refine ⟨51970810213790917017626263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69294413618387889356835017 51970810213790917017626263)
  ·
    refine ⟨77956215320686375526439395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51970810213790917017626263 77956215320686375526439395)
    ·
      refine ⟨116934322981029563289659093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77956215320686375526439395 116934322981029563289659093)
      ·
        refine ⟨2740648194867880389601385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 116934322981029563289659093 2740648194867880389601385)
        ·
          refine ⟨2055486146150910292201039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2740648194867880389601385 2055486146150910292201039)
          ·
            refine ⟨3083229219226365438301559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055486146150910292201039 3083229219226365438301559)
            ·
              refine ⟨4624843828839548157452339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083229219226365438301559 4624843828839548157452339)
              ·
                refine ⟨6937265743259322236178509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624843828839548157452339 6937265743259322236178509)
                ·
                  refine ⟨2601474653722245838566941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6937265743259322236178509 2601474653722245838566941)
                  ·
                    refine ⟨975552995145842189462603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601474653722245838566941 975552995145842189462603)
                    ·
                      rfl

theorem cell22_2849824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 3, 3].length) (baseStart_2849824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849824 prefixEnd_2849824 := by exact prefixLift 2849824
  have htrace : WordTrace (prefixWord ++ tailWord_2849824) baseStart_2849824 baseEnd_2849824 := by
    simpa [prefixWord, tailWord_2849824, baseEnd_2849824] using wordTrace_append hprefix tailTrace_2849824
  have hstable : (prefixWord ++ tailWord_2849824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849824).length < 2 ^ (prefixWord ++ tailWord_2849824).sum := by decide
  have hdescent : baseEnd_2849824 < baseStart_2849824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849861 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_2849861 : Nat := 118140960795 + 2849861 * 2 ^ 59
def prefixEnd_2849861 : Nat := 4983230072969 + 3 ^ 40 * 2849861 * 2
def baseEnd_2849861 : Nat := 975565661001986426287489

theorem tailTrace_2849861 : CollatzResearch.WordTrace tailWord_2849861 prefixEnd_2849861 975565661001986426287489 := by
  unfold tailWord_2849861
  simp only [CollatzResearch.WordTrace]
  refine ⟨103942969928447789354349437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69295313285631859569566291 103942969928447789354349437)
  ·
    refine ⟨38978613723167921007881039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103942969928447789354349437 38978613723167921007881039)
    ·
      refine ⟨58467920584751881511821559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38978613723167921007881039 58467920584751881511821559)
      ·
        refine ⟨87701880877127822267732339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58467920584751881511821559 87701880877127822267732339)
        ·
          refine ⟨131552821315691733401598509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87701880877127822267732339 131552821315691733401598509)
          ·
            refine ⟨49332307993384400025599441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131552821315691733401598509 49332307993384400025599441)
            ·
              refine ⟨36999230995038300019199581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49332307993384400025599441 36999230995038300019199581)
              ·
                refine ⟨13874711623139362507199843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36999230995038300019199581 13874711623139362507199843)
                ·
                  refine ⟨20812067434709043760799765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13874711623139362507199843 20812067434709043760799765)
                  ·
                    refine ⟨975565661001986426287489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20812067434709043760799765 975565661001986426287489)
                    ·
                      rfl

theorem cell22_2849861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_2849861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849861 prefixEnd_2849861 := by exact prefixLift 2849861
  have htrace : WordTrace (prefixWord ++ tailWord_2849861) baseStart_2849861 baseEnd_2849861 := by
    simpa [prefixWord, tailWord_2849861, baseEnd_2849861] using wordTrace_append hprefix tailTrace_2849861
  have hstable : (prefixWord ++ tailWord_2849861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849861).length < 2 ^ (prefixWord ++ tailWord_2849861).sum := by decide
  have hdescent : baseEnd_2849861 < baseStart_2849861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849863 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 1, 5]
def baseStart_2849863 : Nat := 118140960795 + 2849863 * 2 ^ 59
def prefixEnd_2849863 : Nat := 4983230072969 + 3 ^ 40 * 2849863 * 2
def baseEnd_2849863 : Nat := 975566345642859087737483

theorem tailTrace_2849863 : CollatzResearch.WordTrace tailWord_2849863 prefixEnd_2849863 975566345642859087737483 := by
  unfold tailWord_2849863
  simp only [CollatzResearch.WordTrace]
  refine ⟨103943042874440543695922243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69295361916293695797281495 103943042874440543695922243)
  ·
    refine ⟨155914564311660815543883365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103943042874440543695922243 155914564311660815543883365)
    ·
      refine ⟨29233980808436402914478131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155914564311660815543883365 29233980808436402914478131)
      ·
        refine ⟨43850971212654604371717197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29233980808436402914478131 43850971212654604371717197)
        ·
          refine ⟨16444114204745476639393949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43850971212654604371717197 16444114204745476639393949)
          ·
            refine ⟨6166542826779553739772731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16444114204745476639393949 6166542826779553739772731)
            ·
              refine ⟨9249814240169330609659097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6166542826779553739772731 9249814240169330609659097)
              ·
                refine ⟨6937360680126997957244323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9249814240169330609659097 6937360680126997957244323)
                ·
                  refine ⟨10406041020190496935866485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6937360680126997957244323 10406041020190496935866485)
                  ·
                    refine ⟨975566345642859087737483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10406041020190496935866485 975566345642859087737483)
                    ·
                      rfl

theorem cell22_2849863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_2849863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849863 prefixEnd_2849863 := by exact prefixLift 2849863
  have htrace : WordTrace (prefixWord ++ tailWord_2849863) baseStart_2849863 baseEnd_2849863 := by
    simpa [prefixWord, tailWord_2849863, baseEnd_2849863] using wordTrace_append hprefix tailTrace_2849863
  have hstable : (prefixWord ++ tailWord_2849863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849863).length < 2 ^ (prefixWord ++ tailWord_2849863).sum := by decide
  have hdescent : baseEnd_2849863 < baseStart_2849863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849880 : List Nat := [2, 1, 2, 2, 1, 3, 4, 2, 2, 3]
def baseStart_2849880 : Nat := 118140960795 + 2849880 * 2 ^ 59
def prefixEnd_2849880 : Nat := 4983230072969 + 3 ^ 40 * 2849880 * 2
def baseEnd_2849880 : Nat := 975572165090276710062431

theorem tailTrace_2849880 : CollatzResearch.WordTrace tailWord_2849880 prefixEnd_2849880 975572165090276710062431 := by
  unfold tailWord_2849880
  simp only [CollatzResearch.WordTrace]
  refine ⟨51971831457689477799645547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69295775276919303732860729 51971831457689477799645547)
  ·
    refine ⟨77957747186534216699468321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51971831457689477799645547 77957747186534216699468321)
    ·
      refine ⟨58468310389900662524601241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77957747186534216699468321 58468310389900662524601241)
      ·
        refine ⟨43851232792425496893450931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58468310389900662524601241 43851232792425496893450931)
        ·
          refine ⟨65776849188638245340176397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43851232792425496893450931 65776849188638245340176397)
          ·
            refine ⟨24666318445739342002566149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65776849188638245340176397 24666318445739342002566149)
            ·
              refine ⟨4624934708576126625481153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24666318445739342002566149 4624934708576126625481153)
              ·
                refine ⟨3468701031432094969110865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4624934708576126625481153 3468701031432094969110865)
                ·
                  refine ⟨2601525773574071226833149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3468701031432094969110865 2601525773574071226833149)
                  ·
                    refine ⟨975572165090276710062431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601525773574071226833149 975572165090276710062431)
                    ·
                      rfl

theorem cell22_2849880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_2849880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849880 prefixEnd_2849880 := by exact prefixLift 2849880
  have htrace : WordTrace (prefixWord ++ tailWord_2849880) baseStart_2849880 baseEnd_2849880 := by
    simpa [prefixWord, tailWord_2849880, baseEnd_2849880] using wordTrace_append hprefix tailTrace_2849880
  have hstable : (prefixWord ++ tailWord_2849880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849880).length < 2 ^ (prefixWord ++ tailWord_2849880).sum := by decide
  have hdescent : baseEnd_2849880 < baseStart_2849880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849891 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 2, 7]
def baseStart_2849891 : Nat := 118140960795 + 2849891 * 2 ^ 59
def prefixEnd_2849891 : Nat := 4983230072969 + 3 ^ 40 * 2849891 * 2
def baseEnd_2849891 : Nat := 975575930615076348037397

theorem tailTrace_2849891 : CollatzResearch.WordTrace tailWord_2849891 prefixEnd_2849891 975575930615076348037397 := by
  unfold tailWord_2849891
  simp only [CollatzResearch.WordTrace]
  refine ⟨103944064118339104477941527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69296042745559402985294351 103944064118339104477941527)
  ·
    refine ⟨155916096177508656716912291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103944064118339104477941527 155916096177508656716912291)
    ·
      refine ⟨233874144266262985075368437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155916096177508656716912291 233874144266262985075368437)
      ·
        refine ⟨21925701024962154850815791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 233874144266262985075368437 21925701024962154850815791)
        ·
          refine ⟨32888551537443232276223687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21925701024962154850815791 32888551537443232276223687)
          ·
            refine ⟨49332827306164848414335531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32888551537443232276223687 49332827306164848414335531)
            ·
              refine ⟨73999240959247272621503297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49332827306164848414335531 73999240959247272621503297)
              ·
                refine ⟨55499430719435454466127473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73999240959247272621503297 55499430719435454466127473)
                ·
                  refine ⟨41624573039576590849595605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55499430719435454466127473 41624573039576590849595605)
                  ·
                    refine ⟨975575930615076348037397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41624573039576590849595605 975575930615076348037397)
                    ·
                      rfl

theorem cell22_2849891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_2849891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849891 prefixEnd_2849891 := by exact prefixLift 2849891
  have htrace : WordTrace (prefixWord ++ tailWord_2849891) baseStart_2849891 baseEnd_2849891 := by
    simpa [prefixWord, tailWord_2849891, baseEnd_2849891] using wordTrace_append hprefix tailTrace_2849891
  have hstable : (prefixWord ++ tailWord_2849891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849891).length < 2 ^ (prefixWord ++ tailWord_2849891).sum := by decide
  have hdescent : baseEnd_2849891 < baseStart_2849891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849910 : List Nat := [5, 1, 1, 2, 1, 1, 5, 6]
def baseStart_2849910 : Nat := 118140960795 + 2849910 * 2 ^ 59
def prefixEnd_2849910 : Nat := 4983230072969 + 3 ^ 40 * 2849910 * 2
def baseEnd_2849910 : Nat := 108398048300374070201371

theorem tailTrace_2849910 : CollatzResearch.WordTrace tailWord_2849910 prefixEnd_2849910 108398048300374070201371 := by
  unfold tailWord_2849910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6496547319079391920180199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69296504736846847148588789 6496547319079391920180199)
  ·
    refine ⟨9744820978619087880270299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6496547319079391920180199 9744820978619087880270299)
    ·
      refine ⟨14617231467928631820405449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9744820978619087880270299 14617231467928631820405449)
      ·
        refine ⟨10962923600946473865304087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14617231467928631820405449 10962923600946473865304087)
        ·
          refine ⟨16444385401419710797956131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10962923600946473865304087 16444385401419710797956131)
          ·
            refine ⟨24666578102129566196934197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16444385401419710797956131 24666578102129566196934197)
            ·
              refine ⟨2312491697074646830962581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24666578102129566196934197 2312491697074646830962581)
              ·
                refine ⟨108398048300374070201371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2312491697074646830962581 108398048300374070201371)
                ·
                  rfl

theorem cell22_2849910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_2849910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849910 prefixEnd_2849910 := by exact prefixLift 2849910
  have htrace : WordTrace (prefixWord ++ tailWord_2849910) baseStart_2849910 baseEnd_2849910 := by
    simpa [prefixWord, tailWord_2849910, baseEnd_2849910] using wordTrace_append hprefix tailTrace_2849910
  have hstable : (prefixWord ++ tailWord_2849910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849910).length < 2 ^ (prefixWord ++ tailWord_2849910).sum := by decide
  have hdescent : baseEnd_2849910 < baseStart_2849910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849918 : List Nat := [4, 2, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2849918 : Nat := 118140960795 + 2849918 * 2 ^ 59
def prefixEnd_2849918 : Nat := 4983230072969 + 3 ^ 40 * 2849918 * 2
def baseEnd_2849918 : Nat := 975585173266857277612315

theorem tailTrace_2849918 : CollatzResearch.WordTrace tailWord_2849918 prefixEnd_2849918 975585173266857277612315 := by
  unfold tailWord_2849918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12993131111155161011146801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69296699259494192059449605 12993131111155161011146801)
  ·
    refine ⟨9744848333366370758360101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12993131111155161011146801 9744848333366370758360101)
    ·
      refine ⟨1827159062506194517192519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9744848333366370758360101 1827159062506194517192519)
      ·
        refine ⟨2740738593759291775788779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827159062506194517192519 2740738593759291775788779)
        ·
          refine ⟨4111107890638937663683169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2740738593759291775788779 4111107890638937663683169)
          ·
            refine ⟨3083330917979203247762377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4111107890638937663683169 3083330917979203247762377)
            ·
              refine ⟨2312498188484402435821783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3083330917979203247762377 2312498188484402435821783)
              ·
                refine ⟨3468747282726603653732675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312498188484402435821783 3468747282726603653732675)
                ·
                  refine ⟨5203120924089905480599013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3468747282726603653732675 5203120924089905480599013)
                  ·
                    refine ⟨975585173266857277612315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5203120924089905480599013 975585173266857277612315)
                    ·
                      rfl

theorem cell22_2849918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2849918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849918 prefixEnd_2849918 := by exact prefixLift 2849918
  have htrace : WordTrace (prefixWord ++ tailWord_2849918) baseStart_2849918 baseEnd_2849918 := by
    simpa [prefixWord, tailWord_2849918, baseEnd_2849918] using wordTrace_append hprefix tailTrace_2849918
  have hstable : (prefixWord ++ tailWord_2849918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849918).length < 2 ^ (prefixWord ++ tailWord_2849918).sum := by decide
  have hdescent : baseEnd_2849918 < baseStart_2849918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849953 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 2, 5]
def baseStart_2849953 : Nat := 118140960795 + 2849953 * 2 ^ 59
def prefixEnd_2849953 : Nat := 4983230072969 + 3 ^ 40 * 2849953 * 2
def baseEnd_2849953 : Nat := 975597154482128852987207

theorem tailTrace_2849953 : CollatzResearch.WordTrace tailWord_2849953 prefixEnd_2849953 975597154482128852987207 := by
  unfold tailWord_2849953
  simp only [CollatzResearch.WordTrace]
  refine ⟨103946325444114489066698513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69297550296076326044465675 103946325444114489066698513)
  ·
    refine ⟨77959744083085866800023885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103946325444114489066698513 77959744083085866800023885)
    ·
      refine ⟨29234904031157200050008957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77959744083085866800023885 29234904031157200050008957)
      ·
        refine ⟨10963089011683950018753359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29234904031157200050008957 10963089011683950018753359)
        ·
          refine ⟨16444633517525925028130039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10963089011683950018753359 16444633517525925028130039)
          ·
            refine ⟨24666950276288887542195059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16444633517525925028130039 24666950276288887542195059)
            ·
              refine ⟨37000425414433331313292589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24666950276288887542195059 37000425414433331313292589)
              ·
                refine ⟨13875159530412499242484721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37000425414433331313292589 13875159530412499242484721)
                ·
                  refine ⟨10406369647809374431863541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13875159530412499242484721 10406369647809374431863541)
                  ·
                    refine ⟨975597154482128852987207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10406369647809374431863541 975597154482128852987207)
                    ·
                      rfl

theorem cell22_2849953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_2849953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2849953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2849953 prefixEnd_2849953 := by exact prefixLift 2849953
  have htrace : WordTrace (prefixWord ++ tailWord_2849953) baseStart_2849953 baseEnd_2849953 := by
    simpa [prefixWord, tailWord_2849953, baseEnd_2849953] using wordTrace_append hprefix tailTrace_2849953
  have hstable : (prefixWord ++ tailWord_2849953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849953).length < 2 ^ (prefixWord ++ tailWord_2849953).sum := by decide
  have hdescent : baseEnd_2849953 < baseStart_2849953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850006 : List Nat := [5, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_2850006 : Nat := 118140960795 + 2850006 * 2 ^ 59
def prefixEnd_2850006 : Nat := 4983230072969 + 3 ^ 40 * 2850006 * 2
def baseEnd_2850006 : Nat := 325205099155084793804015

theorem tailTrace_2850006 : CollatzResearch.WordTrace tailWord_2850006 prefixEnd_2850006 325205099155084793804015 := by
  unfold tailWord_2850006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6496766157057654944898617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69298839008614986078918581 6496766157057654944898617)
  ·
    refine ⟨4872574617793241208673963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6496766157057654944898617 4872574617793241208673963)
    ·
      refine ⟨7308861926689861813010945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4872574617793241208673963 7308861926689861813010945)
      ·
        refine ⟨5481646445017396359758209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7308861926689861813010945 5481646445017396359758209)
        ·
          refine ⟨4111234833763047269818657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5481646445017396359758209 4111234833763047269818657)
          ·
            refine ⟨3083426125322285452363993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4111234833763047269818657 3083426125322285452363993)
            ·
              refine ⟨2312569593991714089272995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3083426125322285452363993 2312569593991714089272995)
              ·
                refine ⟨3468854390987571133909493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312569593991714089272995 3468854390987571133909493)
                ·
                  refine ⟨325205099155084793804015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3468854390987571133909493 325205099155084793804015)
                  ·
                    rfl

theorem cell22_2850006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_2850006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850006 prefixEnd_2850006 := by exact prefixLift 2850006
  have htrace : WordTrace (prefixWord ++ tailWord_2850006) baseStart_2850006 baseEnd_2850006 := by
    simpa [prefixWord, tailWord_2850006, baseEnd_2850006] using wordTrace_append hprefix tailTrace_2850006
  have hstable : (prefixWord ++ tailWord_2850006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850006).length < 2 ^ (prefixWord ++ tailWord_2850006).sum := by decide
  have hdescent : baseEnd_2850006 < baseStart_2850006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850028 : List Nat := [2, 2, 1, 1, 2, 4, 2, 8]
def baseStart_2850028 : Nat := 118140960795 + 2850028 * 2 ^ 59
def prefixEnd_2850028 : Nat := 4983230072969 + 3 ^ 40 * 2850028 * 2
def baseEnd_2850028 : Nat := 108402536501650406373553

theorem tailTrace_2850028 : CollatzResearch.WordTrace tailWord_2850028 prefixEnd_2850028 108402536501650406373553 := by
  unfold tailWord_2850028
  simp only [CollatzResearch.WordTrace]
  refine ⟨51974530459421388437839369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69299373945895184583785825 51974530459421388437839369)
  ·
    refine ⟨38980897844566041328379527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51974530459421388437839369 38980897844566041328379527)
    ·
      refine ⟨58471346766849061992569291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38980897844566041328379527 58471346766849061992569291)
      ·
        refine ⟨87707020150273592988853937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58471346766849061992569291 87707020150273592988853937)
        ·
          refine ⟨65780265112705194741640453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87707020150273592988853937 65780265112705194741640453)
          ·
            refine ⟨12333799708632224014057585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65780265112705194741640453 12333799708632224014057585)
            ·
              refine ⟨9250349781474168010543189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12333799708632224014057585 9250349781474168010543189)
              ·
                refine ⟨108402536501650406373553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9250349781474168010543189 108402536501650406373553)
                ·
                  rfl

theorem cell22_2850028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 8].length) (baseStart_2850028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850028 prefixEnd_2850028 := by exact prefixLift 2850028
  have htrace : WordTrace (prefixWord ++ tailWord_2850028) baseStart_2850028 baseEnd_2850028 := by
    simpa [prefixWord, tailWord_2850028, baseEnd_2850028] using wordTrace_append hprefix tailTrace_2850028
  have hstable : (prefixWord ++ tailWord_2850028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850028).length < 2 ^ (prefixWord ++ tailWord_2850028).sum := by decide
  have hdescent : baseEnd_2850028 < baseStart_2850028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850030 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_2850030 : Nat := 118140960795 + 2850030 * 2 ^ 59
def prefixEnd_2850030 : Nat := 4983230072969 + 3 ^ 40 * 2850030 * 2
def baseEnd_2850030 : Nat := 975623513155726318811971

theorem tailTrace_2850030 : CollatzResearch.WordTrace tailWord_2850030 prefixEnd_2850030 975623513155726318811971 := by
  unfold tailWord_2850030
  simp only [CollatzResearch.WordTrace]
  refine ⟨12993641733104441402156443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69299422576557020811501029 12993641733104441402156443)
  ·
    refine ⟨19490462599656662103234665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12993641733104441402156443 19490462599656662103234665)
    ·
      refine ⟨14617846949742496577425999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19490462599656662103234665 14617846949742496577425999)
      ·
        refine ⟨21926770424613744866138999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14617846949742496577425999 21926770424613744866138999)
        ·
          refine ⟨32890155636920617299208499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21926770424613744866138999 32890155636920617299208499)
          ·
            refine ⟨49335233455380925948812749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32890155636920617299208499 49335233455380925948812749)
            ·
              refine ⟨18500712545767847230804781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49335233455380925948812749 18500712545767847230804781)
              ·
                refine ⟨6937767204662942711551793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18500712545767847230804781 6937767204662942711551793)
                ·
                  refine ⟨5203325403497207033663845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6937767204662942711551793 5203325403497207033663845)
                  ·
                    refine ⟨975623513155726318811971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5203325403497207033663845 975623513155726318811971)
                    ·
                      rfl

theorem cell22_2850030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_2850030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850030 prefixEnd_2850030 := by exact prefixLift 2850030
  have htrace : WordTrace (prefixWord ++ tailWord_2850030) baseStart_2850030 baseEnd_2850030 := by
    simpa [prefixWord, tailWord_2850030, baseEnd_2850030] using wordTrace_append hprefix tailTrace_2850030
  have hstable : (prefixWord ++ tailWord_2850030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850030).length < 2 ^ (prefixWord ++ tailWord_2850030).sum := by decide
  have hdescent : baseEnd_2850030 < baseStart_2850030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850077 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_2850077 : Nat := 118140960795 + 2850077 * 2 ^ 59
def prefixEnd_2850077 : Nat := 4983230072969 + 3 ^ 40 * 2850077 * 2
def baseEnd_2850077 : Nat := 975639602216233862886827

theorem tailTrace_2850077 : CollatzResearch.WordTrace tailWord_2850077 prefixEnd_2850077 975639602216233862886827 := by
  unfold tailWord_2850077
  simp only [CollatzResearch.WordTrace]
  refine ⟨103950848095665258244212485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69300565397110172162808323 103950848095665258244212485)
  ·
    refine ⟨19490784017937235920789841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103950848095665258244212485 19490784017937235920789841)
    ·
      refine ⟨14618088013452926940592381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19490784017937235920789841 14618088013452926940592381)
      ·
        refine ⟨5481783005044847602722143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14618088013452926940592381 5481783005044847602722143)
        ·
          refine ⟨8222674507567271404083215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5481783005044847602722143 8222674507567271404083215)
          ·
            refine ⟨12334011761350907106124823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8222674507567271404083215 12334011761350907106124823)
            ·
              refine ⟨18501017642026360659187235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12334011761350907106124823 18501017642026360659187235)
              ·
                refine ⟨27751526463039540988780853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18501017642026360659187235 27751526463039540988780853)
                ·
                  refine ⟨2601705605909956967698205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27751526463039540988780853 2601705605909956967698205)
                  ·
                    refine ⟨975639602216233862886827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601705605909956967698205 975639602216233862886827)
                    ·
                      rfl

theorem cell22_2850077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_2850077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850077 prefixEnd_2850077 := by exact prefixLift 2850077
  have htrace : WordTrace (prefixWord ++ tailWord_2850077) baseStart_2850077 baseEnd_2850077 := by
    simpa [prefixWord, tailWord_2850077, baseEnd_2850077] using wordTrace_append hprefix tailTrace_2850077
  have hstable : (prefixWord ++ tailWord_2850077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850077).length < 2 ^ (prefixWord ++ tailWord_2850077).sum := by decide
  have hdescent : baseEnd_2850077 < baseStart_2850077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850135 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 6]
def baseStart_2850135 : Nat := 118140960795 + 2850135 * 2 ^ 59
def prefixEnd_2850135 : Nat := 4983230072969 + 3 ^ 40 * 2850135 * 2
def baseEnd_2850135 : Nat := 325219818933847014978883

theorem tailTrace_2850135 : CollatzResearch.WordTrace tailWord_2850135 prefixEnd_2850135 325219818933847014978883 := by
  unfold tailWord_2850135
  simp only [CollatzResearch.WordTrace]
  refine ⟨103952963529455134149823859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69301975686303422766549239 103952963529455134149823859)
  ·
    refine ⟨155929445294182701224735789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103952963529455134149823859 155929445294182701224735789)
    ·
      refine ⟨58473541985318512959275921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155929445294182701224735789 58473541985318512959275921)
      ·
        refine ⟨43855156488988884719456941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58473541985318512959275921 43855156488988884719456941)
        ·
          refine ⟨16445683683370831769796353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43855156488988884719456941 16445683683370831769796353)
          ·
            refine ⟨12334262762528123827347265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16445683683370831769796353 12334262762528123827347265)
            ·
              refine ⟨9250697071896092870510449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12334262762528123827347265 9250697071896092870510449)
              ·
                refine ⟨6938022803922069652882837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9250697071896092870510449 6938022803922069652882837)
                ·
                  refine ⟨325219818933847014978883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6938022803922069652882837 325219818933847014978883)
                  ·
                    rfl

theorem cell22_2850135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 6].length) (baseStart_2850135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850135 prefixEnd_2850135 := by exact prefixLift 2850135
  have htrace : WordTrace (prefixWord ++ tailWord_2850135) baseStart_2850135 baseEnd_2850135 := by
    simpa [prefixWord, tailWord_2850135, baseEnd_2850135] using wordTrace_append hprefix tailTrace_2850135
  have hstable : (prefixWord ++ tailWord_2850135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850135).length < 2 ^ (prefixWord ++ tailWord_2850135).sum := by decide
  have hdescent : baseEnd_2850135 < baseStart_2850135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850167 : List Nat := [1, 1, 3, 1, 1, 2, 4, 4, 2, 3]
def baseStart_2850167 : Nat := 118140960795 + 2850167 * 2 ^ 59
def prefixEnd_2850167 : Nat := 4983230072969 + 3 ^ 40 * 2850167 * 2
def baseEnd_2850167 : Nat := 975670411055503628136551

theorem tailTrace_2850167 : CollatzResearch.WordTrace tailWord_2850167 prefixEnd_2850167 975670411055503628136551 := by
  unfold tailWord_2850167
  simp only [CollatzResearch.WordTrace]
  refine ⟨103954130665339203614988755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69302753776892802409992503 103954130665339203614988755)
  ·
    refine ⟨155931195998008805422483133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103954130665339203614988755 155931195998008805422483133)
    ·
      refine ⟨58474198499253302033431175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155931195998008805422483133 58474198499253302033431175)
      ·
        refine ⟨87711297748879953050146763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58474198499253302033431175 87711297748879953050146763)
        ·
          refine ⟨131566946623319929575220145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87711297748879953050146763 131566946623319929575220145)
          ·
            refine ⟨98675209967489947181415109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131566946623319929575220145 98675209967489947181415109)
            ·
              refine ⟨18501601868904365096515333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98675209967489947181415109 18501601868904365096515333)
              ·
                refine ⟨3469050350419568455596625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18501601868904365096515333 3469050350419568455596625)
                ·
                  refine ⟨2601787762814676341697469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3469050350419568455596625 2601787762814676341697469)
                  ·
                    refine ⟨975670411055503628136551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601787762814676341697469 975670411055503628136551)
                    ·
                      rfl

theorem cell22_2850167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_2850167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850167 prefixEnd_2850167 := by exact prefixLift 2850167
  have htrace : WordTrace (prefixWord ++ tailWord_2850167) baseStart_2850167 baseEnd_2850167 := by
    simpa [prefixWord, tailWord_2850167, baseEnd_2850167] using wordTrace_append hprefix tailTrace_2850167
  have hstable : (prefixWord ++ tailWord_2850167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850167).length < 2 ^ (prefixWord ++ tailWord_2850167).sum := by decide
  have hdescent : baseEnd_2850167 < baseStart_2850167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850180 : List Nat := [2, 3, 2, 1, 1, 3, 1, 9]
def baseStart_2850180 : Nat := 118140960795 + 2850180 * 2 ^ 59
def prefixEnd_2850180 : Nat := 4983230072969 + 3 ^ 40 * 2850180 * 2
def baseEnd_2850180 : Nat := 108408317913463991951279

theorem tailTrace_2850180 : CollatzResearch.WordTrace tailWord_2850180 prefixEnd_2850180 108408317913463991951279 := by
  unfold tailWord_2850180
  simp only [CollatzResearch.WordTrace]
  refine ⟨51977302407146053417605997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69303069876194737890141329 51977302407146053417605997)
  ·
    refine ⟨19491488402679770031602249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51977302407146053417605997 19491488402679770031602249)
    ·
      refine ⟨14618616302009827523701687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19491488402679770031602249 14618616302009827523701687)
      ·
        refine ⟨21927924453014741285552531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14618616302009827523701687 21927924453014741285552531)
        ·
          refine ⟨32891886679522111928328797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21927924453014741285552531 32891886679522111928328797)
          ·
            refine ⟨12334457504820791973123299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32891886679522111928328797 12334457504820791973123299)
            ·
              refine ⟨18501686257231187959684949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12334457504820791973123299 18501686257231187959684949)
              ·
                refine ⟨108408317913463991951279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18501686257231187959684949 108408317913463991951279)
                ·
                  rfl

theorem cell22_2850180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 9].length) (baseStart_2850180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850180 prefixEnd_2850180 := by exact prefixLift 2850180
  have htrace : WordTrace (prefixWord ++ tailWord_2850180) baseStart_2850180 baseEnd_2850180 := by
    simpa [prefixWord, tailWord_2850180, baseEnd_2850180] using wordTrace_append hprefix tailTrace_2850180
  have hstable : (prefixWord ++ tailWord_2850180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850180).length < 2 ^ (prefixWord ++ tailWord_2850180).sum := by decide
  have hdescent : baseEnd_2850180 < baseStart_2850180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850184 : List Nat := [2, 1, 3, 3, 1, 3, 1, 3, 2, 3]
def baseStart_2850184 : Nat := 118140960795 + 2850184 * 2 ^ 59
def prefixEnd_2850184 : Nat := 4983230072969 + 3 ^ 40 * 2850184 * 2
def baseEnd_2850184 : Nat := 975676230502921250461499

theorem tailTrace_2850184 : CollatzResearch.WordTrace tailWord_2850184 prefixEnd_2850184 975676230502921250461499 := by
  unfold tailWord_2850184
  simp only [CollatzResearch.WordTrace]
  refine ⟨51977375353138807759178803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69303167137518410345571737 51977375353138807759178803)
  ·
    refine ⟨77966063029708211638768205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51977375353138807759178803 77966063029708211638768205)
    ·
      refine ⟨29237273636140579364538077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77966063029708211638768205 29237273636140579364538077)
      ·
        refine ⟨10963977613552717261701779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29237273636140579364538077 10963977613552717261701779)
        ·
          refine ⟨16445966420329075892552669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10963977613552717261701779 16445966420329075892552669)
          ·
            refine ⟨6167237407623403459707251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16445966420329075892552669 6167237407623403459707251)
            ·
              refine ⟨9250856111435105189560877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6167237407623403459707251 9250856111435105189560877)
              ·
                refine ⟨3469071041788164446085329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9250856111435105189560877 3469071041788164446085329)
                ·
                  refine ⟨2601803281341123334563997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3469071041788164446085329 2601803281341123334563997)
                  ·
                    refine ⟨975676230502921250461499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601803281341123334563997 975676230502921250461499)
                    ·
                      rfl

theorem cell22_2850184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_2850184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850184 prefixEnd_2850184 := by exact prefixLift 2850184
  have htrace : WordTrace (prefixWord ++ tailWord_2850184) baseStart_2850184 baseEnd_2850184 := by
    simpa [prefixWord, tailWord_2850184, baseEnd_2850184] using wordTrace_append hprefix tailTrace_2850184
  have hstable : (prefixWord ++ tailWord_2850184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850184).length < 2 ^ (prefixWord ++ tailWord_2850184).sum := by decide
  have hdescent : baseEnd_2850184 < baseStart_2850184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850240 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 1, 7]
def baseStart_2850240 : Nat := 118140960795 + 2850240 * 2 ^ 59
def prefixEnd_2850240 : Nat := 4983230072969 + 3 ^ 40 * 2850240 * 2
def baseEnd_2850240 : Nat := 975695400447355771061327

theorem tailTrace_2850240 : CollatzResearch.WordTrace tailWord_2850240 prefixEnd_2850240 975695400447355771061327 := by
  unfold tailWord_2850240
  simp only [CollatzResearch.WordTrace]
  refine ⟨51978396597037368541198087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69304528796049824721597449 51978396597037368541198087)
  ·
    refine ⟨77967594895556052811797131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51978396597037368541198087 77967594895556052811797131)
    ·
      refine ⟨116951392343334079217695697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77967594895556052811797131 116951392343334079217695697)
      ·
        refine ⟨87713544257500559413271773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116951392343334079217695697 87713544257500559413271773)
        ·
          refine ⟨32892579096562709779976915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87713544257500559413271773 32892579096562709779976915)
          ·
            refine ⟨49338868644844064669965373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32892579096562709779976915 49338868644844064669965373)
            ·
              refine ⟨18502075741816524251237015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49338868644844064669965373 18502075741816524251237015)
              ·
                refine ⟨27753113612724786376855523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18502075741816524251237015 27753113612724786376855523)
                ·
                  refine ⟨41629670419087179565283285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27753113612724786376855523 41629670419087179565283285)
                  ·
                    refine ⟨975695400447355771061327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41629670419087179565283285 975695400447355771061327)
                    ·
                      rfl

theorem cell22_2850240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_2850240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850240 prefixEnd_2850240 := by exact prefixLift 2850240
  have htrace : WordTrace (prefixWord ++ tailWord_2850240) baseStart_2850240 baseEnd_2850240 := by
    simpa [prefixWord, tailWord_2850240, baseEnd_2850240] using wordTrace_append hprefix tailTrace_2850240
  have hstable : (prefixWord ++ tailWord_2850240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850240).length < 2 ^ (prefixWord ++ tailWord_2850240).sum := by decide
  have hdescent : baseEnd_2850240 < baseStart_2850240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850306 : List Nat := [3, 4, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2850306 : Nat := 118140960795 + 2850306 * 2 ^ 59
def prefixEnd_2850306 : Nat := 4983230072969 + 3 ^ 40 * 2850306 * 2
def baseEnd_2850306 : Nat := 975717993596153598911125

theorem tailTrace_2850306 : CollatzResearch.WordTrace tailWord_2850306 prefixEnd_2850306 975717993596153598911125 := by
  unfold tailWord_2850306
  simp only [CollatzResearch.WordTrace]
  refine ⟨25989800102958907588574693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69306133607890420236199181 25989800102958907588574693)
  ·
    refine ⟨4873087519304795172857755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25989800102958907588574693 4873087519304795172857755)
    ·
      refine ⟨7309631278957192759286633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4873087519304795172857755 7309631278957192759286633)
      ·
        refine ⟨5482223459217894569464975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7309631278957192759286633 5482223459217894569464975)
        ·
          refine ⟨8223335188826841854197463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5482223459217894569464975 8223335188826841854197463)
          ·
            refine ⟨12335002783240262781296195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8223335188826841854197463 12335002783240262781296195)
            ·
              refine ⟨18502504174860394171944293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12335002783240262781296195 18502504174860394171944293)
              ·
                refine ⟨3469219532786323907239555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18502504174860394171944293 3469219532786323907239555)
                ·
                  refine ⟨5203829299179485860859333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3469219532786323907239555 5203829299179485860859333)
                  ·
                    refine ⟨975717993596153598911125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5203829299179485860859333 975717993596153598911125)
                    ·
                      rfl

theorem cell22_2850306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2850306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850306 prefixEnd_2850306 := by exact prefixLift 2850306
  have htrace : WordTrace (prefixWord ++ tailWord_2850306) baseStart_2850306 baseEnd_2850306 := by
    simpa [prefixWord, tailWord_2850306, baseEnd_2850306] using wordTrace_append hprefix tailTrace_2850306
  have hstable : (prefixWord ++ tailWord_2850306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850306).length < 2 ^ (prefixWord ++ tailWord_2850306).sum := by decide
  have hdescent : baseEnd_2850306 < baseStart_2850306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850392 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 2, 5]
def baseStart_2850392 : Nat := 118140960795 + 2850392 * 2 ^ 59
def prefixEnd_2850392 : Nat := 4983230072969 + 3 ^ 40 * 2850392 * 2
def baseEnd_2850392 : Nat := 975747433153678041260861

theorem tailTrace_2850392 : CollatzResearch.WordTrace tailWord_2850392 prefixEnd_2850392 975747433153678041260861 := by
  unfold tailWord_2850392
  simp only [CollatzResearch.WordTrace]
  refine ⟨51981168544762033520964715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69308224726349378027952953 51981168544762033520964715)
  ·
    refine ⟨77971752817143050281447073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51981168544762033520964715 77971752817143050281447073)
    ·
      refine ⟨58478814612857287711085305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77971752817143050281447073 58478814612857287711085305)
      ·
        refine ⟨43859110959642965783313979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58478814612857287711085305 43859110959642965783313979)
        ·
          refine ⟨65788666439464448674970969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43859110959642965783313979 65788666439464448674970969)
          ·
            refine ⟨49341499829598336506228227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65788666439464448674970969 49341499829598336506228227)
            ·
              refine ⟨74012249744397504759342341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49341499829598336506228227 74012249744397504759342341)
              ·
                refine ⟨13877296827074532142376689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74012249744397504759342341 13877296827074532142376689)
                ·
                  refine ⟨10407972620305899106782517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13877296827074532142376689 10407972620305899106782517)
                  ·
                    refine ⟨975747433153678041260861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10407972620305899106782517 975747433153678041260861)
                    ·
                      rfl

theorem cell22_2850392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_2850392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850392 prefixEnd_2850392 := by exact prefixLift 2850392
  have htrace : WordTrace (prefixWord ++ tailWord_2850392) baseStart_2850392 baseEnd_2850392 := by
    simpa [prefixWord, tailWord_2850392, baseEnd_2850392] using wordTrace_append hprefix tailTrace_2850392
  have hstable : (prefixWord ++ tailWord_2850392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850392).length < 2 ^ (prefixWord ++ tailWord_2850392).sum := by decide
  have hdescent : baseEnd_2850392 < baseStart_2850392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850441 : List Nat := [1, 2, 1, 1, 4, 1, 6, 1, 1, 4]
def baseStart_2850441 : Nat := 118140960795 + 2850441 * 2 ^ 59
def prefixEnd_2850441 : Nat := 4983230072969 + 3 ^ 40 * 2850441 * 2
def baseEnd_2850441 : Nat := 975764206855058246785711

theorem tailTrace_2850441 : CollatzResearch.WordTrace tailWord_2850441 prefixEnd_2850441 975764206855058246785711 := by
  unfold tailWord_2850441
  simp only [CollatzResearch.WordTrace]
  refine ⟨103964124266346548410463177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69309416177564365606975451 103964124266346548410463177)
  ·
    refine ⟨77973093199759911307847383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103964124266346548410463177 77973093199759911307847383)
    ·
      refine ⟨116959639799639866961771075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77973093199759911307847383 116959639799639866961771075)
      ·
        refine ⟨175439459699459800442656613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116959639799639866961771075 175439459699459800442656613)
        ·
          refine ⟨32894898693648712582998115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175439459699459800442656613 32894898693648712582998115)
          ·
            refine ⟨49342348040473068874497173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32894898693648712582998115 49342348040473068874497173)
            ·
              refine ⟨2312922564397175103492055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49342348040473068874497173 2312922564397175103492055)
              ·
                refine ⟨3469383846595762655238083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312922564397175103492055 3469383846595762655238083)
                ·
                  refine ⟨5204075769893643982857125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3469383846595762655238083 5204075769893643982857125)
                  ·
                    refine ⟨975764206855058246785711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5204075769893643982857125 975764206855058246785711)
                    ·
                      rfl

theorem cell22_2850441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 1, 4].length) (baseStart_2850441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850441 prefixEnd_2850441 := by exact prefixLift 2850441
  have htrace : WordTrace (prefixWord ++ tailWord_2850441) baseStart_2850441 baseEnd_2850441 := by
    simpa [prefixWord, tailWord_2850441, baseEnd_2850441] using wordTrace_append hprefix tailTrace_2850441
  have hstable : (prefixWord ++ tailWord_2850441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850441).length < 2 ^ (prefixWord ++ tailWord_2850441).sum := by decide
  have hdescent : baseEnd_2850441 < baseStart_2850441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850456 : List Nat := [2, 1, 2, 4, 1, 2, 2, 4, 4]
def baseStart_2850456 : Nat := 118140960795 + 2850456 * 2 ^ 59
def prefixEnd_2850456 : Nat := 4983230072969 + 3 ^ 40 * 2850456 * 2
def baseEnd_2850456 : Nat := 325256447220534402553555

theorem tailTrace_2850456 : CollatzResearch.WordTrace tailWord_2850456 prefixEnd_2850456 325256447220534402553555 := by
  unfold tailWord_2850456
  simp only [CollatzResearch.WordTrace]
  refine ⟨51982335680646102986129611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69309780907528137314839481 51982335680646102986129611)
  ·
    refine ⟨77973503520969154479194417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51982335680646102986129611 77973503520969154479194417)
    ·
      refine ⟨58480127640726865859395813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77973503520969154479194417 58480127640726865859395813)
      ·
        refine ⟨10965023932636287348636715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58480127640726865859395813 10965023932636287348636715)
        ·
          refine ⟨16447535898954431022955073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10965023932636287348636715 16447535898954431022955073)
          ·
            refine ⟨12335651924215823267216305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16447535898954431022955073 12335651924215823267216305)
            ·
              refine ⟨9251738943161867450412229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12335651924215823267216305 9251738943161867450412229)
              ·
                refine ⟨1734701051842850146952293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9251738943161867450412229 1734701051842850146952293)
                ·
                  refine ⟨325256447220534402553555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1734701051842850146952293 325256447220534402553555)
                  ·
                    rfl

theorem cell22_2850456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 4].length) (baseStart_2850456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850456 prefixEnd_2850456 := by exact prefixLift 2850456
  have htrace : WordTrace (prefixWord ++ tailWord_2850456) baseStart_2850456 baseEnd_2850456 := by
    simpa [prefixWord, tailWord_2850456, baseEnd_2850456] using wordTrace_append hprefix tailTrace_2850456
  have hstable : (prefixWord ++ tailWord_2850456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850456).length < 2 ^ (prefixWord ++ tailWord_2850456).sum := by decide
  have hdescent : baseEnd_2850456 < baseStart_2850456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850467 : List Nat := [1, 1, 1, 4, 1, 1, 4, 9]
def baseStart_2850467 : Nat := 118140960795 + 2850467 * 2 ^ 59
def prefixEnd_2850467 : Nat := 4983230072969 + 3 ^ 40 * 2850467 * 2
def baseEnd_2850467 : Nat := 108419234131822538403959

theorem tailTrace_2850467 : CollatzResearch.WordTrace tailWord_2850467 prefixEnd_2850467 108419234131822538403959 := by
  unfold tailWord_2850467
  simp only [CollatzResearch.WordTrace]
  refine ⟨103965072564252354850909655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69310048376168236567273103 103965072564252354850909655)
  ·
    refine ⟨155947608846378532276364483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103965072564252354850909655 155947608846378532276364483)
    ·
      refine ⟨233921413269567798414546725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155947608846378532276364483 233921413269567798414546725)
      ·
        refine ⟨43860264988043962202727511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233921413269567798414546725 43860264988043962202727511)
        ·
          refine ⟨65790397482065943304091267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43860264988043962202727511 65790397482065943304091267)
          ·
            refine ⟨98685596223098914956136901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65790397482065943304091267 98685596223098914956136901)
            ·
              refine ⟨18503549291831046554275669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98685596223098914956136901 18503549291831046554275669)
              ·
                refine ⟨108419234131822538403959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18503549291831046554275669 108419234131822538403959)
                ·
                  rfl

theorem cell22_2850467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 9].length) (baseStart_2850467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850467 prefixEnd_2850467 := by exact prefixLift 2850467
  have htrace : WordTrace (prefixWord ++ tailWord_2850467) baseStart_2850467 baseEnd_2850467 := by
    simpa [prefixWord, tailWord_2850467, baseEnd_2850467] using wordTrace_append hprefix tailTrace_2850467
  have hstable : (prefixWord ++ tailWord_2850467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850467).length < 2 ^ (prefixWord ++ tailWord_2850467).sum := by decide
  have hdescent : baseEnd_2850467 < baseStart_2850467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850578 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2850578 : Nat := 118140960795 + 2850578 * 2 ^ 59
def prefixEnd_2850578 : Nat := 4983230072969 + 3 ^ 40 * 2850578 * 2
def baseEnd_2850578 : Nat := 975811104754835556110291

theorem tailTrace_2850578 : CollatzResearch.WordTrace tailWord_2850578 prefixEnd_2850578 975811104754835556110291 := by
  unfold tailWord_2850578
  simp only [CollatzResearch.WordTrace]
  refine ⟨25992280266712555202050097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69312747377900147205466925 25992280266712555202050097)
  ·
    refine ⟨19494210200034416401537573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25992280266712555202050097 19494210200034416401537573)
    ·
      refine ⟨3655164412506453075288295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19494210200034416401537573 3655164412506453075288295)
      ·
        refine ⟨5482746618759679612932443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3655164412506453075288295 5482746618759679612932443)
        ·
          refine ⟨8224119928139519419398665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5482746618759679612932443 8224119928139519419398665)
          ·
            refine ⟨6168089946104639564548999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8224119928139519419398665 6168089946104639564548999)
            ·
              refine ⟨9252134919156959346823499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168089946104639564548999 9252134919156959346823499)
              ·
                refine ⟨13878202378735439020235249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9252134919156959346823499 13878202378735439020235249)
                ·
                  refine ⟨10408651784051579265176437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13878202378735439020235249 10408651784051579265176437)
                  ·
                    refine ⟨975811104754835556110291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10408651784051579265176437 975811104754835556110291)
                    ·
                      rfl

theorem cell22_2850578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2850578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850578 prefixEnd_2850578 := by exact prefixLift 2850578
  have htrace : WordTrace (prefixWord ++ tailWord_2850578) baseStart_2850578 baseEnd_2850578 := by
    simpa [prefixWord, tailWord_2850578, baseEnd_2850578] using wordTrace_append hprefix tailTrace_2850578
  have hstable : (prefixWord ++ tailWord_2850578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850578).length < 2 ^ (prefixWord ++ tailWord_2850578).sum := by decide
  have hdescent : baseEnd_2850578 < baseStart_2850578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850610 : List Nat := [3, 2, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_2850610 : Nat := 118140960795 + 2850610 * 2 ^ 59
def prefixEnd_2850610 : Nat := 4983230072969 + 3 ^ 40 * 2850610 * 2
def baseEnd_2850610 : Nat := 975822059008798139310193

theorem tailTrace_2850610 : CollatzResearch.WordTrace tailWord_2850610 prefixEnd_2850610 975822059008798139310193 := by
  unfold tailWord_2850610
  simp only [CollatzResearch.WordTrace]
  refine ⟨25992572050683572568341321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69313525468489526848910189 25992572050683572568341321)
  ·
    refine ⟨19494429038012679426255991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25992572050683572568341321 19494429038012679426255991)
    ·
      refine ⟨29241643557019019139383987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19494429038012679426255991 29241643557019019139383987)
      ·
        refine ⟨43862465335528528709075981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29241643557019019139383987 43862465335528528709075981)
        ·
          refine ⟨16448424500823198265903493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43862465335528528709075981 16448424500823198265903493)
          ·
            refine ⟨3084079593904349674856905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16448424500823198265903493 3084079593904349674856905)
            ·
              refine ⟨2313059695428262256142679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3084079593904349674856905 2313059695428262256142679)
              ·
                refine ⟨3469589543142393384214019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313059695428262256142679 3469589543142393384214019)
                ·
                  refine ⟨5204384314713590076321029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3469589543142393384214019 5204384314713590076321029)
                  ·
                    refine ⟨975822059008798139310193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5204384314713590076321029 975822059008798139310193)
                    ·
                      rfl

theorem cell22_2850610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_2850610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850610 prefixEnd_2850610 := by exact prefixLift 2850610
  have htrace : WordTrace (prefixWord ++ tailWord_2850610) baseStart_2850610 baseEnd_2850610 := by
    simpa [prefixWord, tailWord_2850610, baseEnd_2850610] using wordTrace_append hprefix tailTrace_2850610
  have hstable : (prefixWord ++ tailWord_2850610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850610).length < 2 ^ (prefixWord ++ tailWord_2850610).sum := by decide
  have hdescent : baseEnd_2850610 < baseStart_2850610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850623 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 4, 3]
def baseStart_2850623 : Nat := 118140960795 + 2850623 * 2 ^ 59
def prefixEnd_2850623 : Nat := 4983230072969 + 3 ^ 40 * 2850623 * 2
def baseEnd_2850623 : Nat := 975826509174470438735153

theorem tailTrace_2850623 : CollatzResearch.WordTrace tailWord_2850623 prefixEnd_2850623 975826509174470438735153 := by
  unfold tailWord_2850623
  simp only [CollatzResearch.WordTrace]
  refine ⟨103970762351687193493588523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69313841567791462329059015 103970762351687193493588523)
  ·
    refine ⟨155956143527530790240382785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103970762351687193493588523 155956143527530790240382785)
    ·
      refine ⟨116967107645648092680287089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155956143527530790240382785 116967107645648092680287089)
      ·
        refine ⟨87725330734236069510215317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116967107645648092680287089 87725330734236069510215317)
        ·
          refine ⟨4112124878167315758291343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87725330734236069510215317 4112124878167315758291343)
          ·
            refine ⟨6168187317250973637437015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4112124878167315758291343 6168187317250973637437015)
            ·
              refine ⟨9252280975876460456155523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168187317250973637437015 9252280975876460456155523)
              ·
                refine ⟨13878421463814690684233285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9252280975876460456155523 13878421463814690684233285)
                ·
                  refine ⟨2602204024465254503293741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13878421463814690684233285 2602204024465254503293741)
                  ·
                    refine ⟨975826509174470438735153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2602204024465254503293741 975826509174470438735153)
                    ·
                      rfl

theorem cell22_2850623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 3].length) (baseStart_2850623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850623 prefixEnd_2850623 := by exact prefixLift 2850623
  have htrace : WordTrace (prefixWord ++ tailWord_2850623) baseStart_2850623 baseEnd_2850623 := by
    simpa [prefixWord, tailWord_2850623, baseEnd_2850623] using wordTrace_append hprefix tailTrace_2850623
  have hstable : (prefixWord ++ tailWord_2850623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850623).length < 2 ^ (prefixWord ++ tailWord_2850623).sum := by decide
  have hdescent : baseEnd_2850623 < baseStart_2850623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850681 : List Nat := [1, 2, 1, 3, 2, 2, 2, 4, 5]
def baseStart_2850681 : Nat := 118140960795 + 2850681 * 2 ^ 59
def prefixEnd_2850681 : Nat := 4983230072969 + 3 ^ 40 * 2850681 * 2
def baseEnd_2850681 : Nat := 325282121253259206928325

theorem tailTrace_2850681 : CollatzResearch.WordTrace tailWord_2850681 prefixEnd_2850681 325282121253259206928325 := by
  unfold tailWord_2850681
  simp only [CollatzResearch.WordTrace]
  refine ⟨103972877785477069399199897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69315251856984712932799931 103972877785477069399199897)
  ·
    refine ⟨77979658339107802049399923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103972877785477069399199897 77979658339107802049399923)
    ·
      refine ⟨116969487508661703074099885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77979658339107802049399923 116969487508661703074099885)
      ·
        refine ⟨43863557815748138652787457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116969487508661703074099885 43863557815748138652787457)
        ·
          refine ⟨32897668361811103989590593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43863557815748138652787457 32897668361811103989590593)
          ·
            refine ⟨24673251271358327992192945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32897668361811103989590593 24673251271358327992192945)
            ·
              refine ⟨18504938453518745994144709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24673251271358327992192945 18504938453518745994144709)
              ·
                refine ⟨3469675960034764873902133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18504938453518745994144709 3469675960034764873902133)
                ·
                  refine ⟨325282121253259206928325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3469675960034764873902133 325282121253259206928325)
                  ·
                    rfl

theorem cell22_2850681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_2850681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850681 prefixEnd_2850681 := by exact prefixLift 2850681
  have htrace : WordTrace (prefixWord ++ tailWord_2850681) baseStart_2850681 baseEnd_2850681 := by
    simpa [prefixWord, tailWord_2850681, baseEnd_2850681] using wordTrace_append hprefix tailTrace_2850681
  have hstable : (prefixWord ++ tailWord_2850681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850681).length < 2 ^ (prefixWord ++ tailWord_2850681).sum := by decide
  have hdescent : baseEnd_2850681 < baseStart_2850681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850773 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_2850773 : Nat := 118140960795 + 2850773 * 2 ^ 59
def prefixEnd_2850773 : Nat := 4983230072969 + 3 ^ 40 * 2850773 * 2
def baseEnd_2850773 : Nat := 975877857239920047484693

theorem tailTrace_2850773 : CollatzResearch.WordTrace tailWord_2850773 prefixEnd_2850773 975877857239920047484693 := by
  unfold tailWord_2850773
  simp only [CollatzResearch.WordTrace]
  refine ⟨103976233301143769111548973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69317488867429179407699315 103976233301143769111548973)
  ·
    refine ⟨38991087487928913416830865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103976233301143769111548973 38991087487928913416830865)
    ·
      refine ⟨29243315615946685062623149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38991087487928913416830865 29243315615946685062623149)
      ·
        refine ⟨10966243355980006898483681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29243315615946685062623149 10966243355980006898483681)
        ·
          refine ⟨8224682516985005173862761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10966243355980006898483681 8224682516985005173862761)
          ·
            refine ⟨6168511887738753880397071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8224682516985005173862761 6168511887738753880397071)
            ·
              refine ⟨9252767831608130820595607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168511887738753880397071 9252767831608130820595607)
              ·
                refine ⟨13879151747412196230893411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9252767831608130820595607 13879151747412196230893411)
                ·
                  refine ⟨20818727621118294346340117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13879151747412196230893411 20818727621118294346340117)
                  ·
                    refine ⟨975877857239920047484693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20818727621118294346340117 975877857239920047484693)
                    ·
                      rfl

theorem cell22_2850773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_2850773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850773 prefixEnd_2850773 := by exact prefixLift 2850773
  have htrace : WordTrace (prefixWord ++ tailWord_2850773) baseStart_2850773 baseEnd_2850773 := by
    simpa [prefixWord, tailWord_2850773, baseEnd_2850773] using wordTrace_append hprefix tailTrace_2850773
  have hstable : (prefixWord ++ tailWord_2850773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850773).length < 2 ^ (prefixWord ++ tailWord_2850773).sum := by decide
  have hdescent : baseEnd_2850773 < baseStart_2850773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850880 : List Nat := [2, 1, 1, 2, 2, 4, 3, 2, 1, 4]
def baseStart_2850880 : Nat := 118140960795 + 2850880 * 2 ^ 59
def prefixEnd_2850880 : Nat := 4983230072969 + 3 ^ 40 * 2850880 * 2
def baseEnd_2850880 : Nat := 975914485526607435059365

theorem tailTrace_2850880 : CollatzResearch.WordTrace tailWord_2850880 prefixEnd_2850880 975914485526607435059365 := by
  unfold tailWord_2850880
  simp only [CollatzResearch.WordTrace]
  refine ⟨51990067955878063192847047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69320090607837417590462729 51990067955878063192847047)
  ·
    refine ⟨77985101933817094789270571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51990067955878063192847047 77985101933817094789270571)
    ·
      refine ⟨116977652900725642183905857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77985101933817094789270571 116977652900725642183905857)
      ·
        refine ⟨87733239675544231637929393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116977652900725642183905857 87733239675544231637929393)
        ·
          refine ⟨65799929756658173728447045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87733239675544231637929393 65799929756658173728447045)
          ·
            refine ⟨12337486829373407574083821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65799929756658173728447045 12337486829373407574083821)
            ·
              refine ⟨4626557561015027840281433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12337486829373407574083821 4626557561015027840281433)
              ·
                refine ⟨3469918170761270880211075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4626557561015027840281433 3469918170761270880211075)
                ·
                  refine ⟨5204877256141906320316613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3469918170761270880211075 5204877256141906320316613)
                  ·
                    refine ⟨975914485526607435059365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5204877256141906320316613 975914485526607435059365)
                    ·
                      rfl

theorem cell22_2850880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_2850880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850880 prefixEnd_2850880 := by exact prefixLift 2850880
  have htrace : WordTrace (prefixWord ++ tailWord_2850880) baseStart_2850880 baseEnd_2850880 := by
    simpa [prefixWord, tailWord_2850880, baseEnd_2850880] using wordTrace_append hprefix tailTrace_2850880
  have hstable : (prefixWord ++ tailWord_2850880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850880).length < 2 ^ (prefixWord ++ tailWord_2850880).sum := by decide
  have hdescent : baseEnd_2850880 < baseStart_2850880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850912 : List Nat := [2, 1, 1, 3, 2, 3, 4, 2, 4]
def baseStart_2850912 : Nat := 118140960795 + 2850912 * 2 ^ 59
def prefixEnd_2850912 : Nat := 4983230072969 + 3 ^ 40 * 2850912 * 2
def baseEnd_2850912 : Nat := 325308479926856672753089

theorem tailTrace_2850912 : CollatzResearch.WordTrace tailWord_2850912 prefixEnd_2850912 325308479926856672753089 := by
  unfold tailWord_2850912
  simp only [CollatzResearch.WordTrace]
  refine ⟨51990651523820097925429495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69320868698426797233905993 51990651523820097925429495)
  ·
    refine ⟨77985977285730146888144243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51990651523820097925429495 77985977285730146888144243)
    ·
      refine ⟨116978965928595220332216365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77985977285730146888144243 116978965928595220332216365)
      ·
        refine ⟨43867112223223207624581137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116978965928595220332216365 43867112223223207624581137)
        ·
          refine ⟨32900334167417405718435853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43867112223223207624581137 32900334167417405718435853)
          ·
            refine ⟨12337625312781527144413445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32900334167417405718435853 12337625312781527144413445)
            ·
              refine ⟨2313304746146536339577521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12337625312781527144413445 2313304746146536339577521)
              ·
                refine ⟨1734978559609902254683141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2313304746146536339577521 1734978559609902254683141)
                ·
                  refine ⟨325308479926856672753089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1734978559609902254683141 325308479926856672753089)
                  ·
                    rfl

theorem cell22_2850912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 4].length) (baseStart_2850912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850912 prefixEnd_2850912 := by exact prefixLift 2850912
  have htrace : WordTrace (prefixWord ++ tailWord_2850912) baseStart_2850912 baseEnd_2850912 := by
    simpa [prefixWord, tailWord_2850912, baseEnd_2850912] using wordTrace_append hprefix tailTrace_2850912
  have hstable : (prefixWord ++ tailWord_2850912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850912).length < 2 ^ (prefixWord ++ tailWord_2850912).sum := by decide
  have hdescent : baseEnd_2850912 < baseStart_2850912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850940 : List Nat := [2, 2, 2, 1, 1, 5, 3, 6]
def baseStart_2850940 : Nat := 118140960795 + 2850940 * 2 ^ 59
def prefixEnd_2850940 : Nat := 4983230072969 + 3 ^ 40 * 2850940 * 2
def baseEnd_2850940 : Nat := 108437224972531919839909

theorem tailTrace_2850940 : CollatzResearch.WordTrace tailWord_2850940 prefixEnd_2850940 108437224972531919839909 := by
  unfold tailWord_2850940
  simp only [CollatzResearch.WordTrace]
  refine ⟨51991162145769378316439137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69321549527692504421918849 51991162145769378316439137)
  ·
    refine ⟨38993371609327033737329353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51991162145769378316439137 38993371609327033737329353)
    ·
      refine ⟨29245028706995275302997015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38993371609327033737329353 29245028706995275302997015)
      ·
        refine ⟨43867543060492912954495523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29245028706995275302997015 43867543060492912954495523)
        ·
          refine ⟨65801314590739369431743285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43867543060492912954495523 65801314590739369431743285)
          ·
            refine ⟨6168873242881815884225933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65801314590739369431743285 6168873242881815884225933)
            ·
              refine ⟨2313327466080680956584725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6168873242881815884225933 2313327466080680956584725)
              ·
                refine ⟨108437224972531919839909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2313327466080680956584725 108437224972531919839909)
                ·
                  rfl

theorem cell22_2850940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 6].length) (baseStart_2850940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850940 prefixEnd_2850940 := by exact prefixLift 2850940
  have htrace : WordTrace (prefixWord ++ tailWord_2850940) baseStart_2850940 baseEnd_2850940 := by
    simpa [prefixWord, tailWord_2850940, baseEnd_2850940] using wordTrace_append hprefix tailTrace_2850940
  have hstable : (prefixWord ++ tailWord_2850940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850940).length < 2 ^ (prefixWord ++ tailWord_2850940).sum := by decide
  have hdescent : baseEnd_2850940 < baseStart_2850940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850972 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 3, 3]
def baseStart_2850972 : Nat := 118140960795 + 2850972 * 2 ^ 59
def prefixEnd_2850972 : Nat := 4983230072969 + 3 ^ 40 * 2850972 * 2
def baseEnd_2850972 : Nat := 975945979006749861759083

theorem tailTrace_2850972 : CollatzResearch.WordTrace tailWord_2850972 prefixEnd_2850972 975945979006749861759083 := by
  unfold tailWord_2850972
  simp only [CollatzResearch.WordTrace]
  refine ⟨51991745713711413049021585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69322327618281884065362113 51991745713711413049021585)
  ·
    refine ⟨38993809285283559786766189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51991745713711413049021585 38993809285283559786766189)
    ·
      refine ⟨14622678481981334920037321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38993809285283559786766189 14622678481981334920037321)
      ·
        refine ⟨10967008861486001190027991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14622678481981334920037321 10967008861486001190027991)
        ·
          refine ⟨16450513292229001785041987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10967008861486001190027991 16450513292229001785041987)
          ·
            refine ⟨24675769938343502677562981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16450513292229001785041987 24675769938343502677562981)
            ·
              refine ⟨4626706863439406752043059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24675769938343502677562981 4626706863439406752043059)
              ·
                refine ⟨6940060295159110128064589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4626706863439406752043059 6940060295159110128064589)
                ·
                  refine ⟨2602522610684666298024221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6940060295159110128064589 2602522610684666298024221)
                  ·
                    refine ⟨975945979006749861759083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2602522610684666298024221 975945979006749861759083)
                    ·
                      rfl

theorem cell22_2850972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_2850972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2850972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2850972 prefixEnd_2850972 := by exact prefixLift 2850972
  have htrace : WordTrace (prefixWord ++ tailWord_2850972) baseStart_2850972 baseEnd_2850972 := by
    simpa [prefixWord, tailWord_2850972, baseEnd_2850972] using wordTrace_append hprefix tailTrace_2850972
  have hstable : (prefixWord ++ tailWord_2850972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850972).length < 2 ^ (prefixWord ++ tailWord_2850972).sum := by decide
  have hdescent : baseEnd_2850972 < baseStart_2850972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851013 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 8]
def baseStart_2851013 : Nat := 118140960795 + 2851013 * 2 ^ 59
def prefixEnd_2851013 : Nat := 4983230072969 + 3 ^ 40 * 2851013 * 2
def baseEnd_2851013 : Nat := 325320004714879807161319

theorem tailTrace_2851013 : CollatzResearch.WordTrace tailWord_2851013 prefixEnd_2851013 325320004714879807161319 := by
  unfold tailWord_2851013
  simp only [CollatzResearch.WordTrace]
  refine ⟨103984986820274290100285693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69323324546849526733523795 103984986820274290100285693)
  ·
    refine ⟨38994370057602858787607135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103984986820274290100285693 38994370057602858787607135)
    ·
      refine ⟨58491555086404288181410703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38994370057602858787607135 58491555086404288181410703)
      ·
        refine ⟨87737332629606432272116055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58491555086404288181410703 87737332629606432272116055)
        ·
          refine ⟨131605998944409648408174083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87737332629606432272116055 131605998944409648408174083)
          ·
            refine ⟨197408998416614472612261125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131605998944409648408174083 197408998416614472612261125)
            ·
              refine ⟨37014187203115213614798961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197408998416614472612261125 37014187203115213614798961)
              ·
                refine ⟨27760640402336410211099221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37014187203115213614798961 27760640402336410211099221)
                ·
                  refine ⟨325320004714879807161319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27760640402336410211099221 325320004714879807161319)
                  ·
                    rfl

theorem cell22_2851013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_2851013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851013 prefixEnd_2851013 := by exact prefixLift 2851013
  have htrace : WordTrace (prefixWord ++ tailWord_2851013) baseStart_2851013 baseEnd_2851013 := by
    simpa [prefixWord, tailWord_2851013, baseEnd_2851013] using wordTrace_append hprefix tailTrace_2851013
  have hstable : (prefixWord ++ tailWord_2851013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851013).length < 2 ^ (prefixWord ++ tailWord_2851013).sum := by decide
  have hdescent : baseEnd_2851013 < baseStart_2851013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851062 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_2851062 : Nat := 118140960795 + 2851062 * 2 ^ 59
def prefixEnd_2851062 : Nat := 4983230072969 + 3 ^ 40 * 2851062 * 2
def baseEnd_2851062 : Nat := 975976787846019627008807

theorem tailTrace_2851062 : CollatzResearch.WordTrace tailWord_2851062 prefixEnd_2851062 975976787846019627008807 := by
  unfold tailWord_2851062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6499173374818548216801215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69324515998064514312546293 6499173374818548216801215)
  ·
    refine ⟨9748760062227822325201823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6499173374818548216801215 9748760062227822325201823)
    ·
      refine ⟨14623140093341733487802735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9748760062227822325201823 14623140093341733487802735)
      ·
        refine ⟨21934710140012600231704103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14623140093341733487802735 21934710140012600231704103)
        ·
          refine ⟨32902065210018900347556155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21934710140012600231704103 32902065210018900347556155)
          ·
            refine ⟨49353097815028350521334233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32902065210018900347556155 49353097815028350521334233)
            ·
              refine ⟨37014823361271262891000675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49353097815028350521334233 37014823361271262891000675)
              ·
                refine ⟨55522235041906894336501013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37014823361271262891000675 55522235041906894336501013)
                ·
                  refine ⟨2602604767589385672023485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55522235041906894336501013 2602604767589385672023485)
                  ·
                    refine ⟨975976787846019627008807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2602604767589385672023485 975976787846019627008807)
                    ·
                      rfl

theorem cell22_2851062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_2851062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851062 prefixEnd_2851062 := by exact prefixLift 2851062
  have htrace : WordTrace (prefixWord ++ tailWord_2851062) baseStart_2851062 baseEnd_2851062 := by
    simpa [prefixWord, tailWord_2851062, baseEnd_2851062] using wordTrace_append hprefix tailTrace_2851062
  have hstable : (prefixWord ++ tailWord_2851062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851062).length < 2 ^ (prefixWord ++ tailWord_2851062).sum := by decide
  have hdescent : baseEnd_2851062 < baseStart_2851062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851107 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 3, 3]
def baseStart_2851107 : Nat := 118140960795 + 2851107 * 2 ^ 59
def prefixEnd_2851107 : Nat := 4983230072969 + 3 ^ 40 * 2851107 * 2
def baseEnd_2851107 : Nat := 975992192265654509633669

theorem tailTrace_2851107 : CollatzResearch.WordTrace tailWord_2851107 prefixEnd_2851107 975992192265654509633669 := by
  unfold tailWord_2851107
  simp only [CollatzResearch.WordTrace]
  refine ⟨103988415281933744154207575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69325610187955829436138383 103988415281933744154207575)
  ·
    refine ⟨155982622922900616231311363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103988415281933744154207575 155982622922900616231311363)
    ·
      refine ⟨233973934384350924346967045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155982622922900616231311363 233973934384350924346967045)
      ·
        refine ⟨43870112697065798315056321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233973934384350924346967045 43870112697065798315056321)
        ·
          refine ⟨32902584522799348736292241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43870112697065798315056321 32902584522799348736292241)
          ·
            refine ⟨24676938392099511552219181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32902584522799348736292241 24676938392099511552219181)
            ·
              refine ⟨9253851897037316832082193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24676938392099511552219181 9253851897037316832082193)
              ·
                refine ⟨6940388922777987624061645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9253851897037316832082193 6940388922777987624061645)
                ·
                  refine ⟨2602645846041745359023117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6940388922777987624061645 2602645846041745359023117)
                  ·
                    refine ⟨975992192265654509633669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2602645846041745359023117 975992192265654509633669)
                    ·
                      rfl

theorem cell22_2851107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 3].length) (baseStart_2851107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851107 prefixEnd_2851107 := by exact prefixLift 2851107
  have htrace : WordTrace (prefixWord ++ tailWord_2851107) baseStart_2851107 baseEnd_2851107 := by
    simpa [prefixWord, tailWord_2851107, baseEnd_2851107] using wordTrace_append hprefix tailTrace_2851107
  have hstable : (prefixWord ++ tailWord_2851107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851107).length < 2 ^ (prefixWord ++ tailWord_2851107).sum := by decide
  have hdescent : baseEnd_2851107 < baseStart_2851107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851111 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2851111 : Nat := 118140960795 + 2851111 * 2 ^ 59
def prefixEnd_2851111 : Nat := 4983230072969 + 3 ^ 40 * 2851111 * 2
def baseEnd_2851111 : Nat := 975993561547399832533657

theorem tailTrace_2851111 : CollatzResearch.WordTrace tailWord_2851111 prefixEnd_2851111 975993561547399832533657 := by
  unfold tailWord_2851111
  simp only [CollatzResearch.WordTrace]
  refine ⟨103988561173919252837353187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69325707449279501891568791 103988561173919252837353187)
  ·
    refine ⟨155982841760878879256029781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103988561173919252837353187 155982841760878879256029781)
    ·
      refine ⟨1827923926885299366281599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 155982841760878879256029781 1827923926885299366281599)
      ·
        refine ⟨2741885890327949049422399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827923926885299366281599 2741885890327949049422399)
        ·
          refine ⟨4112828835491923574133599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2741885890327949049422399 4112828835491923574133599)
          ·
            refine ⟨6169243253237885361200399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4112828835491923574133599 6169243253237885361200399)
            ·
              refine ⟨9253864879856828041800599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6169243253237885361200399 9253864879856828041800599)
              ·
                refine ⟨13880797319785242062700899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9253864879856828041800599 13880797319785242062700899)
                ·
                  refine ⟨20821195979677863094051349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13880797319785242062700899 20821195979677863094051349)
                  ·
                    refine ⟨975993561547399832533657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20821195979677863094051349 975993561547399832533657)
                    ·
                      rfl

theorem cell22_2851111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2851111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851111 prefixEnd_2851111 := by exact prefixLift 2851111
  have htrace : WordTrace (prefixWord ++ tailWord_2851111) baseStart_2851111 baseEnd_2851111 := by
    simpa [prefixWord, tailWord_2851111, baseEnd_2851111] using wordTrace_append hprefix tailTrace_2851111
  have hstable : (prefixWord ++ tailWord_2851111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851111).length < 2 ^ (prefixWord ++ tailWord_2851111).sum := by decide
  have hdescent : baseEnd_2851111 < baseStart_2851111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851135 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 4, 5]
def baseStart_2851135 : Nat := 118140960795 + 2851135 * 2 ^ 59
def prefixEnd_2851135 : Nat := 4983230072969 + 3 ^ 40 * 2851135 * 2
def baseEnd_2851135 : Nat := 976001777237871769933583

theorem tailTrace_2851135 : CollatzResearch.WordTrace tailWord_2851135 prefixEnd_2851135 976001777237871769933583 := by
  unfold tailWord_2851135
  simp only [CollatzResearch.WordTrace]
  refine ⟨103989436525832304936226859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69326291017221536624151239 103989436525832304936226859)
  ·
    refine ⟨155984154788748457404340289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103989436525832304936226859 155984154788748457404340289)
    ·
      refine ⟨116988116091561343053255217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155984154788748457404340289 116988116091561343053255217)
      ·
        refine ⟨87741087068671007289941413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116988116091561343053255217 87741087068671007289941413)
        ·
          refine ⟨16451453825375813866864015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87741087068671007289941413 16451453825375813866864015)
          ·
            refine ⟨24677180738063720800296023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16451453825375813866864015 24677180738063720800296023)
            ·
              refine ⟨37015771107095581200444035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24677180738063720800296023 37015771107095581200444035)
              ·
                refine ⟨55523656660643371800666053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37015771107095581200444035 55523656660643371800666053)
                ·
                  refine ⟨10410685623870632212624885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55523656660643371800666053 10410685623870632212624885)
                  ·
                    refine ⟨976001777237871769933583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10410685623870632212624885 976001777237871769933583)
                    ·
                      rfl

theorem cell22_2851135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_2851135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851135 prefixEnd_2851135 := by exact prefixLift 2851135
  have htrace : WordTrace (prefixWord ++ tailWord_2851135) baseStart_2851135 baseEnd_2851135 := by
    simpa [prefixWord, tailWord_2851135, baseEnd_2851135] using wordTrace_append hprefix tailTrace_2851135
  have hstable : (prefixWord ++ tailWord_2851135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851135).length < 2 ^ (prefixWord ++ tailWord_2851135).sum := by decide
  have hdescent : baseEnd_2851135 < baseStart_2851135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851150 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_2851150 : Nat := 118140960795 + 2851150 * 2 ^ 59
def prefixEnd_2851150 : Nat := 4983230072969 + 3 ^ 40 * 2851150 * 2
def baseEnd_2851150 : Nat := 976006912044416730808537

theorem tailTrace_2851150 : CollatzResearch.WordTrace tailWord_2851150 prefixEnd_2851150 976006912044416730808537 := by
  unfold tailWord_2851150
  simp only [CollatzResearch.WordTrace]
  refine ⟨12998747952597245312252863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69326655747185308332015269 12998747952597245312252863)
  ·
    refine ⟨19498121928895867968379295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12998747952597245312252863 19498121928895867968379295)
    ·
      refine ⟨29247182893343801952568943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19498121928895867968379295 29247182893343801952568943)
      ·
        refine ⟨43870774340015702928853415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29247182893343801952568943 43870774340015702928853415)
        ·
          refine ⟨65806161510023554393280123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43870774340015702928853415 65806161510023554393280123)
          ·
            refine ⟨98709242265035331589920185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65806161510023554393280123 98709242265035331589920185)
            ·
              refine ⟨74031931698776498692440139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98709242265035331589920185 74031931698776498692440139)
              ·
                refine ⟨111047897548164748038660209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74031931698776498692440139 111047897548164748038660209)
                ·
                  refine ⟨83285923161123561028995157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111047897548164748038660209 83285923161123561028995157)
                  ·
                    refine ⟨976006912044416730808537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83285923161123561028995157 976006912044416730808537)
                    ·
                      rfl

theorem cell22_2851150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_2851150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851150 prefixEnd_2851150 := by exact prefixLift 2851150
  have htrace : WordTrace (prefixWord ++ tailWord_2851150) baseStart_2851150 baseEnd_2851150 := by
    simpa [prefixWord, tailWord_2851150, baseEnd_2851150] using wordTrace_append hprefix tailTrace_2851150
  have hstable : (prefixWord ++ tailWord_2851150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851150).length < 2 ^ (prefixWord ++ tailWord_2851150).sum := by decide
  have hdescent : baseEnd_2851150 < baseStart_2851150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851167 : List Nat := [1, 1, 2, 3, 1, 2, 3, 4, 1, 4]
def baseStart_2851167 : Nat := 118140960795 + 2851167 * 2 ^ 59
def prefixEnd_2851167 : Nat := 4983230072969 + 3 ^ 40 * 2851167 * 2
def baseEnd_2851167 : Nat := 976012731491834353133485

theorem tailTrace_2851167 : CollatzResearch.WordTrace tailWord_2851167 prefixEnd_2851167 976012731491834353133485 := by
  unfold tailWord_2851167
  simp only [CollatzResearch.WordTrace]
  refine ⟨103990603661716374401391755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69327069107810916267594503 103990603661716374401391755)
  ·
    refine ⟨155985905492574561602087633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103990603661716374401391755 155985905492574561602087633)
    ·
      refine ⟨116989429119430921201565725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155985905492574561602087633 116989429119430921201565725)
      ·
        refine ⟨43871035919786595450587147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116989429119430921201565725 43871035919786595450587147)
        ·
          refine ⟨65806553879679893175880721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43871035919786595450587147 65806553879679893175880721)
          ·
            refine ⟨49354915409759919881910541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65806553879679893175880721 49354915409759919881910541)
            ·
              refine ⟨18508093278659969955716453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49354915409759919881910541 18508093278659969955716453)
              ·
                refine ⟨3470267489748744366696835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18508093278659969955716453 3470267489748744366696835)
                ·
                  refine ⟨5205401234623116550045253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470267489748744366696835 5205401234623116550045253)
                  ·
                    refine ⟨976012731491834353133485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5205401234623116550045253 976012731491834353133485)
                    ·
                      rfl

theorem cell22_2851167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_2851167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851167 prefixEnd_2851167 := by exact prefixLift 2851167
  have htrace : WordTrace (prefixWord ++ tailWord_2851167) baseStart_2851167 baseEnd_2851167 := by
    simpa [prefixWord, tailWord_2851167, baseEnd_2851167] using wordTrace_append hprefix tailTrace_2851167
  have hstable : (prefixWord ++ tailWord_2851167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851167).length < 2 ^ (prefixWord ++ tailWord_2851167).sum := by decide
  have hdescent : baseEnd_2851167 < baseStart_2851167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851257 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 2, 6]
def baseStart_2851257 : Nat := 118140960795 + 2851257 * 2 ^ 59
def prefixEnd_2851257 : Nat := 4983230072969 + 3 ^ 40 * 2851257 * 2
def baseEnd_2851257 : Nat := 976043540331104118383209

theorem tailTrace_2851257 : CollatzResearch.WordTrace tailWord_2851257 prefixEnd_2851257 976043540331104118383209 := by
  unfold tailWord_2851257
  simp only [CollatzResearch.WordTrace]
  refine ⟨103993886231390319772168025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69329257487593546514778683 103993886231390319772168025)
  ·
    refine ⟨77995414673542739829126019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103993886231390319772168025 77995414673542739829126019)
    ·
      refine ⟨116993122010314109743689029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77995414673542739829126019 116993122010314109743689029)
      ·
        refine ⟨21936210376933895576941693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116993122010314109743689029 21936210376933895576941693)
        ·
          refine ⟨8226078891350210841353135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21936210376933895576941693 8226078891350210841353135)
          ·
            refine ⟨12339118337025316262029703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8226078891350210841353135 12339118337025316262029703)
            ·
              refine ⟨18508677505537974393044555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12339118337025316262029703 18508677505537974393044555)
              ·
                refine ⟨27763016258306961589566833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18508677505537974393044555 27763016258306961589566833)
                ·
                  refine ⟨20822262193730221192175125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27763016258306961589566833 20822262193730221192175125)
                  ·
                    refine ⟨976043540331104118383209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20822262193730221192175125 976043540331104118383209)
                    ·
                      rfl

theorem cell22_2851257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_2851257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851257 prefixEnd_2851257 := by exact prefixLift 2851257
  have htrace : WordTrace (prefixWord ++ tailWord_2851257) baseStart_2851257 baseEnd_2851257 := by
    simpa [prefixWord, tailWord_2851257, baseEnd_2851257] using wordTrace_append hprefix tailTrace_2851257
  have hstable : (prefixWord ++ tailWord_2851257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851257).length < 2 ^ (prefixWord ++ tailWord_2851257).sum := by decide
  have hdescent : baseEnd_2851257 < baseStart_2851257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851276 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 3, 3]
def baseStart_2851276 : Nat := 118140960795 + 2851276 * 2 ^ 59
def prefixEnd_2851276 : Nat := 4983230072969 + 3 ^ 40 * 2851276 * 2
def baseEnd_2851276 : Nat := 976050044419394402158151

theorem tailTrace_2851276 : CollatzResearch.WordTrace tailWord_2851276 prefixEnd_2851276 976050044419394402158151 := by
  unfold tailWord_2851276
  simp only [CollatzResearch.WordTrace]
  refine ⟨51997289609160743008554841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69329719478880990678073121 51997289609160743008554841)
  ·
    refine ⟨38997967206870557256416131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51997289609160743008554841 38997967206870557256416131)
    ·
      refine ⟨58496950810305835884624197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38997967206870557256416131 58496950810305835884624197)
      ·
        refine ⟨10968178276932344228367037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58496950810305835884624197 10968178276932344228367037)
        ·
          refine ⟨4113066853849629085637639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10968178276932344228367037 4113066853849629085637639)
          ·
            refine ⟨6169600280774443628456459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113066853849629085637639 6169600280774443628456459)
            ·
              refine ⟨9254400421161665442684689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6169600280774443628456459 9254400421161665442684689)
              ·
                refine ⟨6940800315871249082013517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9254400421161665442684689 6940800315871249082013517)
                ·
                  refine ⟨2602800118451718405755069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6940800315871249082013517 2602800118451718405755069)
                  ·
                    refine ⟨976050044419394402158151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2602800118451718405755069 976050044419394402158151)
                    ·
                      rfl

theorem cell22_2851276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_2851276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851276 prefixEnd_2851276 := by exact prefixLift 2851276
  have htrace : WordTrace (prefixWord ++ tailWord_2851276) baseStart_2851276 baseEnd_2851276 := by
    simpa [prefixWord, tailWord_2851276, baseEnd_2851276] using wordTrace_append hprefix tailTrace_2851276
  have hstable : (prefixWord ++ tailWord_2851276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851276).length < 2 ^ (prefixWord ++ tailWord_2851276).sum := by decide
  have hdescent : baseEnd_2851276 < baseStart_2851276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851293 : List Nat := [1, 4, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2851293 : Nat := 118140960795 + 2851293 * 2 ^ 59
def prefixEnd_2851293 : Nat := 4983230072969 + 3 ^ 40 * 2851293 * 2
def baseEnd_2851293 : Nat := 976055863866812024483099

theorem tailTrace_2851293 : CollatzResearch.WordTrace tailWord_2851293 prefixEnd_2851293 976055863866812024483099 := by
  unfold tailWord_2851293
  simp only [CollatzResearch.WordTrace]
  refine ⟨103995199259259897920478533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69330132839506598613652355 103995199259259897920478533)
  ·
    refine ⟨19499099861111230860089725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103995199259259897920478533 19499099861111230860089725)
    ·
      refine ⟨7312162447916711572533647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19499099861111230860089725 7312162447916711572533647)
      ·
        refine ⟨10968243671875067358800471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7312162447916711572533647 10968243671875067358800471)
        ·
          refine ⟨16452365507812601038200707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10968243671875067358800471 16452365507812601038200707)
          ·
            refine ⟨24678548261718901557301061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16452365507812601038200707 24678548261718901557301061)
            ·
              refine ⟨4627227799072294041993949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24678548261718901557301061 4627227799072294041993949)
              ·
                refine ⟨1735210424652110265747731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4627227799072294041993949 1735210424652110265747731)
                ·
                  refine ⟨2602815636978165398621597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735210424652110265747731 2602815636978165398621597)
                  ·
                    refine ⟨976055863866812024483099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2602815636978165398621597 976055863866812024483099)
                    ·
                      rfl

theorem cell22_2851293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2851293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851293 prefixEnd_2851293 := by exact prefixLift 2851293
  have htrace : WordTrace (prefixWord ++ tailWord_2851293) baseStart_2851293 baseEnd_2851293 := by
    simpa [prefixWord, tailWord_2851293, baseEnd_2851293] using wordTrace_append hprefix tailTrace_2851293
  have hstable : (prefixWord ++ tailWord_2851293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851293).length < 2 ^ (prefixWord ++ tailWord_2851293).sum := by decide
  have hdescent : baseEnd_2851293 < baseStart_2851293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851306 : List Nat := [3, 1, 3, 1, 3, 3, 1, 2, 5]
def baseStart_2851306 : Nat := 118140960795 + 2851306 * 2 ^ 59
def prefixEnd_2851306 : Nat := 4983230072969 + 3 ^ 40 * 2851306 * 2
def baseEnd_2851306 : Nat := 325353438010828107969353

theorem tailTrace_2851306 : CollatzResearch.WordTrace tailWord_2851306 prefixEnd_2851306 325353438010828107969353 := by
  unfold tailWord_2851306
  simp only [CollatzResearch.WordTrace]
  refine ⟨25998918352053200285175443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69330448938808534093801181 25998918352053200285175443)
  ·
    refine ⟨38998377528079800427763165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25998918352053200285175443 38998377528079800427763165)
    ·
      refine ⟨14624391573029925160411187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38998377528079800427763165 14624391573029925160411187)
      ·
        refine ⟨21936587359544887740616781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14624391573029925160411187 21936587359544887740616781)
        ·
          refine ⟨8226220259829332902731293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21936587359544887740616781 8226220259829332902731293)
          ·
            refine ⟨3084832597435999838524235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8226220259829332902731293 3084832597435999838524235)
            ·
              refine ⟨4627248896153999757786353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3084832597435999838524235 4627248896153999757786353)
              ·
                refine ⟨3470436672115499818339765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4627248896153999757786353 3470436672115499818339765)
                ·
                  refine ⟨325353438010828107969353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3470436672115499818339765 325353438010828107969353)
                  ·
                    rfl

theorem cell22_2851306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_2851306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851306 prefixEnd_2851306 := by exact prefixLift 2851306
  have htrace : WordTrace (prefixWord ++ tailWord_2851306) baseStart_2851306 baseEnd_2851306 := by
    simpa [prefixWord, tailWord_2851306, baseEnd_2851306] using wordTrace_append hprefix tailTrace_2851306
  have hstable : (prefixWord ++ tailWord_2851306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851306).length < 2 ^ (prefixWord ++ tailWord_2851306).sum := by decide
  have hdescent : baseEnd_2851306 < baseStart_2851306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851347 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 1, 6]
def baseStart_2851347 : Nat := 118140960795 + 2851347 * 2 ^ 59
def prefixEnd_2851347 : Nat := 4983230072969 + 3 ^ 40 * 2851347 * 2
def baseEnd_2851347 : Nat := 976074349170373883632933

theorem tailTrace_2851347 : CollatzResearch.WordTrace tailWord_2851347 prefixEnd_2851347 976074349170373883632933 := by
  unfold tailWord_2851347
  simp only [CollatzResearch.WordTrace]
  refine ⟨103997168801064265142944295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69331445867376176761962863 103997168801064265142944295)
  ·
    refine ⟨155995753201596397714416443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103997168801064265142944295 155995753201596397714416443)
    ·
      refine ⟨233993629802394596571624665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155995753201596397714416443 233993629802394596571624665)
      ·
        refine ⟨175495222351795947428718499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233993629802394596571624665 175495222351795947428718499)
        ·
          refine ⟨263242833527693921143077749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175495222351795947428718499 263242833527693921143077749)
          ·
            refine ⟨24679015643221305107163539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 263242833527693921143077749 24679015643221305107163539)
            ·
              refine ⟨37018523464831957660745309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24679015643221305107163539 37018523464831957660745309)
              ·
                refine ⟨13881946299311984122779491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37018523464831957660745309 13881946299311984122779491)
                ·
                  refine ⟨20822919448967976184169237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13881946299311984122779491 20822919448967976184169237)
                  ·
                    refine ⟨976074349170373883632933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20822919448967976184169237 976074349170373883632933)
                    ·
                      rfl

theorem cell22_2851347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_2851347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851347 prefixEnd_2851347 := by exact prefixLift 2851347
  have htrace : WordTrace (prefixWord ++ tailWord_2851347) baseStart_2851347 baseEnd_2851347 := by
    simpa [prefixWord, tailWord_2851347, baseEnd_2851347] using wordTrace_append hprefix tailTrace_2851347
  have hstable : (prefixWord ++ tailWord_2851347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851347).length < 2 ^ (prefixWord ++ tailWord_2851347).sum := by decide
  have hdescent : baseEnd_2851347 < baseStart_2851347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851349 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 6, 3]
def baseStart_2851349 : Nat := 118140960795 + 2851349 * 2 ^ 59
def prefixEnd_2851349 : Nat := 4983230072969 + 3 ^ 40 * 2851349 * 2
def baseEnd_2851349 : Nat := 976075033811246545082927

theorem tailTrace_2851349 : CollatzResearch.WordTrace tailWord_2851349 prefixEnd_2851349 976075033811246545082927 := by
  unfold tailWord_2851349
  simp only [CollatzResearch.WordTrace]
  refine ⟨103997241747057019484517101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69331494498038012989678067 103997241747057019484517101)
  ·
    refine ⟨38998965655146382306693913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103997241747057019484517101 38998965655146382306693913)
    ·
      refine ⟨29249224241359786730020435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38998965655146382306693913 29249224241359786730020435)
      ·
        refine ⟨43873836362039680095030653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29249224241359786730020435 43873836362039680095030653)
        ·
          refine ⟨16452688635764880035636495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43873836362039680095030653 16452688635764880035636495)
          ·
            refine ⟨24679032953647320053454743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16452688635764880035636495 24679032953647320053454743)
            ·
              refine ⟨37018549430470980080182115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24679032953647320053454743 37018549430470980080182115)
              ·
                refine ⟨55527824145706470120273173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37018549430470980080182115 55527824145706470120273173)
                ·
                  refine ⟨2602866756829990786887805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55527824145706470120273173 2602866756829990786887805)
                  ·
                    refine ⟨976075033811246545082927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2602866756829990786887805 976075033811246545082927)
                    ·
                      rfl

theorem cell22_2851349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_2851349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851349 prefixEnd_2851349 := by exact prefixLift 2851349
  have htrace : WordTrace (prefixWord ++ tailWord_2851349) baseStart_2851349 baseEnd_2851349 := by
    simpa [prefixWord, tailWord_2851349, baseEnd_2851349] using wordTrace_append hprefix tailTrace_2851349
  have hstable : (prefixWord ++ tailWord_2851349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851349).length < 2 ^ (prefixWord ++ tailWord_2851349).sum := by decide
  have hdescent : baseEnd_2851349 < baseStart_2851349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851398 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2851398 : Nat := 118140960795 + 2851398 * 2 ^ 59
def prefixEnd_2851398 : Nat := 4983230072969 + 3 ^ 40 * 2851398 * 2
def baseEnd_2851398 : Nat := 976091807512626750607777

theorem tailTrace_2851398 : CollatzResearch.WordTrace tailWord_2851398 prefixEnd_2851398 976091807512626750607777 := by
  unfold tailWord_2851398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3249969653871234401657839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69332685949253000568700565 3249969653871234401657839)
  ·
    refine ⟨4874954480806851602486759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3249969653871234401657839 4874954480806851602486759)
    ·
      refine ⟨7312431721210277403730139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4874954480806851602486759 7312431721210277403730139)
      ·
        refine ⟨10968647581815416105595209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7312431721210277403730139 10968647581815416105595209)
        ·
          refine ⟨8226485686361562079196407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10968647581815416105595209 8226485686361562079196407)
          ·
            refine ⟨12339728529542343118794611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8226485686361562079196407 12339728529542343118794611)
            ·
              refine ⟨18509592794313514678191917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12339728529542343118794611 18509592794313514678191917)
              ·
                refine ⟨6941097297867568004321969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18509592794313514678191917 6941097297867568004321969)
                ·
                  refine ⟨5205822973400676003241477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6941097297867568004321969 5205822973400676003241477)
                  ·
                    refine ⟨976091807512626750607777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5205822973400676003241477 976091807512626750607777)
                    ·
                      rfl

theorem cell22_2851398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2851398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851398 prefixEnd_2851398 := by exact prefixLift 2851398
  have htrace : WordTrace (prefixWord ++ tailWord_2851398) baseStart_2851398 baseEnd_2851398 := by
    simpa [prefixWord, tailWord_2851398, baseEnd_2851398] using wordTrace_append hprefix tailTrace_2851398
  have hstable : (prefixWord ++ tailWord_2851398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851398).length < 2 ^ (prefixWord ++ tailWord_2851398).sum := by decide
  have hdescent : baseEnd_2851398 < baseStart_2851398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851407 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 9]
def baseStart_2851407 : Nat := 118140960795 + 2851407 * 2 ^ 59
def prefixEnd_2851407 : Nat := 4983230072969 + 3 ^ 40 * 2851407 * 2
def baseEnd_2851407 : Nat := 325364962798851242377583

theorem tailTrace_2851407 : CollatzResearch.WordTrace tailWord_2851407 prefixEnd_2851407 325364962798851242377583 := by
  unfold tailWord_2851407
  simp only [CollatzResearch.WordTrace]
  refine ⟨103999357180846895390128475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69332904787231263593418983 103999357180846895390128475)
  ·
    refine ⟨155999035771270343085192713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103999357180846895390128475 155999035771270343085192713)
    ·
      refine ⟨116999276828452757313894535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155999035771270343085192713 116999276828452757313894535)
      ·
        refine ⟨175498915242679135970841803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116999276828452757313894535 175498915242679135970841803)
        ·
          refine ⟨263248372864018703956262705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175498915242679135970841803 263248372864018703956262705)
          ·
            refine ⟨197436279648014027967197029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263248372864018703956262705 197436279648014027967197029)
            ·
              refine ⟨37019302434002630243849443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197436279648014027967197029 37019302434002630243849443)
              ·
                refine ⟨55528953651003945365774165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37019302434002630243849443 55528953651003945365774165)
                ·
                  refine ⟨325364962798851242377583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55528953651003945365774165 325364962798851242377583)
                  ·
                    rfl

theorem cell22_2851407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 9].length) (baseStart_2851407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851407 prefixEnd_2851407 := by exact prefixLift 2851407
  have htrace : WordTrace (prefixWord ++ tailWord_2851407) baseStart_2851407 baseEnd_2851407 := by
    simpa [prefixWord, tailWord_2851407, baseEnd_2851407] using wordTrace_append hprefix tailTrace_2851407
  have hstable : (prefixWord ++ tailWord_2851407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851407).length < 2 ^ (prefixWord ++ tailWord_2851407).sum := by decide
  have hdescent : baseEnd_2851407 < baseStart_2851407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851424 : List Nat := [2, 1, 1, 3, 2, 1, 3, 4, 5]
def baseStart_2851424 : Nat := 118140960795 + 2851424 * 2 ^ 59
def prefixEnd_2851424 : Nat := 4983230072969 + 3 ^ 40 * 2851424 * 2
def baseEnd_2851424 : Nat := 325366902614657116485899

theorem tailTrace_2851424 : CollatzResearch.WordTrace tailWord_2851424 prefixEnd_2851424 325366902614657116485899 := by
  unfold tailWord_2851424
  simp only [CollatzResearch.WordTrace]
  refine ⟨51999988610892653646748663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69333318147856871528998217 51999988610892653646748663)
  ·
    refine ⟨77999982916338980470122995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51999988610892653646748663 77999982916338980470122995)
    ·
      refine ⟨116999974374508470705184493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77999982916338980470122995 116999974374508470705184493)
      ·
        refine ⟨43874990390440676514444185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116999974374508470705184493 43874990390440676514444185)
        ·
          refine ⟨32906242792830507385833139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43874990390440676514444185 32906242792830507385833139)
          ·
            refine ⟨49359364189245761078749709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32906242792830507385833139 49359364189245761078749709)
            ·
              refine ⟨18509761570967160404531141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49359364189245761078749709 18509761570967160404531141)
              ·
                refine ⟨3470580294556342575849589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18509761570967160404531141 3470580294556342575849589)
                ·
                  refine ⟨325366902614657116485899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3470580294556342575849589 325366902614657116485899)
                  ·
                    rfl

theorem cell22_2851424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_2851424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851424 prefixEnd_2851424 := by exact prefixLift 2851424
  have htrace : WordTrace (prefixWord ++ tailWord_2851424) baseStart_2851424 baseEnd_2851424 := by
    simpa [prefixWord, tailWord_2851424, baseEnd_2851424] using wordTrace_append hprefix tailTrace_2851424
  have hstable : (prefixWord ++ tailWord_2851424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851424).length < 2 ^ (prefixWord ++ tailWord_2851424).sum := by decide
  have hdescent : baseEnd_2851424 < baseStart_2851424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851428 : List Nat := [2, 3, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_2851428 : Nat := 118140960795 + 2851428 * 2 ^ 59
def prefixEnd_2851428 : Nat := 4983230072969 + 3 ^ 40 * 2851428 * 2
def baseEnd_2851428 : Nat := 976102077125716672357685

theorem tailTrace_2851428 : CollatzResearch.WordTrace tailWord_2851428 prefixEnd_2851428 976102077125716672357685 := by
  unfold tailWord_2851428
  simp only [CollatzResearch.WordTrace]
  refine ⟨52000061556885407988321469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69333415409180543984428625 52000061556885407988321469)
  ·
    refine ⟨19500023083832027995620551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52000061556885407988321469 19500023083832027995620551)
    ·
      refine ⟨29250034625748041993430827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19500023083832027995620551 29250034625748041993430827)
      ·
        refine ⟨43875051938622062990146241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29250034625748041993430827 43875051938622062990146241)
        ·
          refine ⟨32906288953966547242609681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43875051938622062990146241 32906288953966547242609681)
          ·
            refine ⟨24679716715474910431957261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32906288953966547242609681 24679716715474910431957261)
            ·
              refine ⟨9254893768303091411983973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24679716715474910431957261 9254893768303091411983973)
              ·
                refine ⟨1735292581556829639746995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9254893768303091411983973 1735292581556829639746995)
                ·
                  refine ⟨2602938872335244459620493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735292581556829639746995 2602938872335244459620493)
                  ·
                    refine ⟨976102077125716672357685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2602938872335244459620493 976102077125716672357685)
                    ·
                      rfl

theorem cell22_2851428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_2851428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851428 prefixEnd_2851428 := by exact prefixLift 2851428
  have htrace : WordTrace (prefixWord ++ tailWord_2851428) baseStart_2851428 baseEnd_2851428 := by
    simpa [prefixWord, tailWord_2851428, baseEnd_2851428] using wordTrace_append hprefix tailTrace_2851428
  have hstable : (prefixWord ++ tailWord_2851428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851428).length < 2 ^ (prefixWord ++ tailWord_2851428).sum := by decide
  have hdescent : baseEnd_2851428 < baseStart_2851428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851505 : List Nat := [1, 2, 2, 6, 1, 1, 2, 2, 1, 4]
def baseStart_2851505 : Nat := 118140960795 + 2851505 * 2 ^ 59
def prefixEnd_2851505 : Nat := 4983230072969 + 3 ^ 40 * 2851505 * 2
def baseEnd_2851505 : Nat := 976128435799314138182449

theorem tailTrace_2851505 : CollatzResearch.WordTrace tailWord_2851505 prefixEnd_2851505 976128435799314138182449 := by
  unfold tailWord_2851505
  simp only [CollatzResearch.WordTrace]
  refine ⟨104002931534491858127195969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69335287689661238751463979 104002931534491858127195969)
  ·
    refine ⟨78002198650868893595396977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104002931534491858127195969 78002198650868893595396977)
    ·
      refine ⟨58501648988151670196547733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78002198650868893595396977 58501648988151670196547733)
      ·
        refine ⟨2742264796319609540463175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58501648988151670196547733 2742264796319609540463175)
        ·
          refine ⟨4113397194479414310694763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2742264796319609540463175 4113397194479414310694763)
          ·
            refine ⟨6170095791719121466042145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113397194479414310694763 6170095791719121466042145)
            ·
              refine ⟨4627571843789341099531609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6170095791719121466042145 4627571843789341099531609)
              ·
                refine ⟨3470678882842005824648707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4627571843789341099531609 3470678882842005824648707)
                ·
                  refine ⟨5206018324263008736973061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470678882842005824648707 5206018324263008736973061)
                  ·
                    refine ⟨976128435799314138182449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5206018324263008736973061 976128435799314138182449)
                    ·
                      rfl

theorem cell22_2851505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_2851505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851505 prefixEnd_2851505 := by exact prefixLift 2851505
  have htrace : WordTrace (prefixWord ++ tailWord_2851505) baseStart_2851505 baseEnd_2851505 := by
    simpa [prefixWord, tailWord_2851505, baseEnd_2851505] using wordTrace_append hprefix tailTrace_2851505
  have hstable : (prefixWord ++ tailWord_2851505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851505).length < 2 ^ (prefixWord ++ tailWord_2851505).sum := by decide
  have hdescent : baseEnd_2851505 < baseStart_2851505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851514 : List Nat := [3, 1, 1, 1, 2, 3, 3, 8]
def baseStart_2851514 : Nat := 118140960795 + 2851514 * 2 ^ 59
def prefixEnd_2851514 : Nat := 4983230072969 + 3 ^ 40 * 2851514 * 2
def baseEnd_2851514 : Nat := 108459057409249012745269

theorem tailTrace_2851514 : CollatzResearch.WordTrace tailWord_2851514 prefixEnd_2851514 108459057409249012745269 := by
  unfold tailWord_2851514
  simp only [CollatzResearch.WordTrace]
  refine ⟨26000814947864813166068399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69335506527639501776182397 26000814947864813166068399)
  ·
    refine ⟨39001222421797219749102599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26000814947864813166068399 39001222421797219749102599)
    ·
      refine ⟨58501833632695829623653899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39001222421797219749102599 58501833632695829623653899)
      ·
        refine ⟨87752750449043744435480849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58501833632695829623653899 87752750449043744435480849)
        ·
          refine ⟨65814562836782808326610637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87752750449043744435480849 65814562836782808326610637)
          ·
            refine ⟨24680461063793553122478989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65814562836782808326610637 24680461063793553122478989)
            ·
              refine ⟨9255172898922582420929621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24680461063793553122478989 9255172898922582420929621)
              ·
                refine ⟨108459057409249012745269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9255172898922582420929621 108459057409249012745269)
                ·
                  rfl

theorem cell22_2851514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_2851514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851514 prefixEnd_2851514 := by exact prefixLift 2851514
  have htrace : WordTrace (prefixWord ++ tailWord_2851514) baseStart_2851514 baseEnd_2851514 := by
    simpa [prefixWord, tailWord_2851514, baseEnd_2851514] using wordTrace_append hprefix tailTrace_2851514
  have hstable : (prefixWord ++ tailWord_2851514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851514).length < 2 ^ (prefixWord ++ tailWord_2851514).sum := by decide
  have hdescent : baseEnd_2851514 < baseStart_2851514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851516 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_2851516 : Nat := 118140960795 + 2851516 * 2 ^ 59
def prefixEnd_2851516 : Nat := 4983230072969 + 3 ^ 40 * 2851516 * 2
def baseEnd_2851516 : Nat := 976132201324113776157415

theorem tailTrace_2851516 : CollatzResearch.WordTrace tailWord_2851516 prefixEnd_2851516 976132201324113776157415 := by
  unfold tailWord_2851516
  simp only [CollatzResearch.WordTrace]
  refine ⟨52001666368726003502923201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69335555158301338003897601 52001666368726003502923201)
  ·
    refine ⟨39001249776544502627192401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52001666368726003502923201 39001249776544502627192401)
    ·
      refine ⟨29250937332408376970394301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39001249776544502627192401 29250937332408376970394301)
      ·
        refine ⟨10969101499653141363897863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29250937332408376970394301 10969101499653141363897863)
        ·
          refine ⟨16453652249479712045846795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10969101499653141363897863 16453652249479712045846795)
          ·
            refine ⟨24680478374219568068770193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16453652249479712045846795 24680478374219568068770193)
            ·
              refine ⟨18510358780664676051577645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24680478374219568068770193 18510358780664676051577645)
              ·
                refine ⟨6941384542749253519341617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18510358780664676051577645 6941384542749253519341617)
                ·
                  refine ⟨5206038407061940139506213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6941384542749253519341617 5206038407061940139506213)
                  ·
                    refine ⟨976132201324113776157415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5206038407061940139506213 976132201324113776157415)
                    ·
                      rfl

theorem cell22_2851516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_2851516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851516 prefixEnd_2851516 := by exact prefixLift 2851516
  have htrace : WordTrace (prefixWord ++ tailWord_2851516) baseStart_2851516 baseEnd_2851516 := by
    simpa [prefixWord, tailWord_2851516, baseEnd_2851516] using wordTrace_append hprefix tailTrace_2851516
  have hstable : (prefixWord ++ tailWord_2851516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851516).length < 2 ^ (prefixWord ++ tailWord_2851516).sum := by decide
  have hdescent : baseEnd_2851516 < baseStart_2851516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851548 : List Nat := [2, 2, 5, 1, 1, 2, 2, 7]
def baseStart_2851548 : Nat := 118140960795 + 2851548 * 2 ^ 59
def prefixEnd_2851548 : Nat := 4983230072969 + 3 ^ 40 * 2851548 * 2
def baseEnd_2851548 : Nat := 108460350619786262150813

theorem tailTrace_2851548 : CollatzResearch.WordTrace tailWord_2851548 prefixEnd_2851548 108460350619786262150813 := by
  unfold tailWord_2851548
  simp only [CollatzResearch.WordTrace]
  refine ⟨52002249936668038235505649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69336333248890717647340865 52002249936668038235505649)
  ·
    refine ⟨39001687452501028676629237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52002249936668038235505649 39001687452501028676629237)
    ·
      refine ⟨3656408198671971438433991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39001687452501028676629237 3656408198671971438433991)
      ·
        refine ⟨5484612298007957157650987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3656408198671971438433991 5484612298007957157650987)
        ·
          refine ⟨8226918447011935736476481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5484612298007957157650987 8226918447011935736476481)
          ·
            refine ⟨6170188835258951802357361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8226918447011935736476481 6170188835258951802357361)
            ·
              refine ⟨4627641626444213851768021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6170188835258951802357361 4627641626444213851768021)
              ·
                refine ⟨108460350619786262150813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4627641626444213851768021 108460350619786262150813)
                ·
                  rfl

theorem cell22_2851548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 7].length) (baseStart_2851548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851548 prefixEnd_2851548 := by exact prefixLift 2851548
  have htrace : WordTrace (prefixWord ++ tailWord_2851548) baseStart_2851548 baseEnd_2851548 := by
    simpa [prefixWord, tailWord_2851548, baseEnd_2851548] using wordTrace_append hprefix tailTrace_2851548
  have hstable : (prefixWord ++ tailWord_2851548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851548).length < 2 ^ (prefixWord ++ tailWord_2851548).sum := by decide
  have hdescent : baseEnd_2851548 < baseStart_2851548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851621 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 6]
def baseStart_2851621 : Nat := 118140960795 + 2851621 * 2 ^ 59
def prefixEnd_2851621 : Nat := 4983230072969 + 3 ^ 40 * 2851621 * 2
def baseEnd_2851621 : Nat := 325389381656642834094031

theorem tailTrace_2851621 : CollatzResearch.WordTrace tailWord_2851621 prefixEnd_2851621 325389381656642834094031 := by
  unfold tailWord_2851621
  simp only [CollatzResearch.WordTrace]
  refine ⟨104007162402071609938418717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69338108268047739958945811 104007162402071609938418717)
  ·
    refine ⟨39002685900776853726907019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104007162402071609938418717 39002685900776853726907019)
    ·
      refine ⟨58504028851165280590360529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39002685900776853726907019 58504028851165280590360529)
      ·
        refine ⟨43878021638373960442770397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58504028851165280590360529 43878021638373960442770397)
        ·
          refine ⟨16454258114390235166038899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43878021638373960442770397 16454258114390235166038899)
          ·
            refine ⟨24681387171585352749058349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16454258114390235166038899 24681387171585352749058349)
            ·
              refine ⟨9255520189344507280896881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24681387171585352749058349 9255520189344507280896881)
              ·
                refine ⟨6941640142008380460672661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9255520189344507280896881 6941640142008380460672661)
                ·
                  refine ⟨325389381656642834094031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6941640142008380460672661 325389381656642834094031)
                  ·
                    rfl

theorem cell22_2851621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_2851621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851621 prefixEnd_2851621 := by exact prefixLift 2851621
  have htrace : WordTrace (prefixWord ++ tailWord_2851621) baseStart_2851621 baseEnd_2851621 := by
    simpa [prefixWord, tailWord_2851621, baseEnd_2851621] using wordTrace_append hprefix tailTrace_2851621
  have hstable : (prefixWord ++ tailWord_2851621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851621).length < 2 ^ (prefixWord ++ tailWord_2851621).sum := by decide
  have hdescent : baseEnd_2851621 < baseStart_2851621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851651 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 4, 4]
def baseStart_2851651 : Nat := 118140960795 + 2851651 * 2 ^ 59
def prefixEnd_2851651 : Nat := 4983230072969 + 3 ^ 40 * 2851651 * 2
def baseEnd_2851651 : Nat := 976178414583018424032001

theorem tailTrace_2851651 : CollatzResearch.WordTrace tailWord_2851651 prefixEnd_2851651 976178414583018424032001 := by
  unfold tailWord_2851651
  simp only [CollatzResearch.WordTrace]
  refine ⟨104008256591962925062010807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69338837727975283374673871 104008256591962925062010807)
  ·
    refine ⟨156012384887944387593016211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104008256591962925062010807 156012384887944387593016211)
    ·
      refine ⟨234018577331916581389524317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156012384887944387593016211 234018577331916581389524317)
      ·
        refine ⟨87756966499468718021071619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234018577331916581389524317 87756966499468718021071619)
        ·
          refine ⟨131635449749203077031607429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87756966499468718021071619 131635449749203077031607429)
          ·
            refine ⟨24681646827975576943426393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131635449749203077031607429 24681646827975576943426393)
            ·
              refine ⟨18511235120981682707569795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24681646827975576943426393 18511235120981682707569795)
              ·
                refine ⟨27766852681472524061354693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18511235120981682707569795 27766852681472524061354693)
                ·
                  refine ⟨5206284877776098261504005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27766852681472524061354693 5206284877776098261504005)
                  ·
                    refine ⟨976178414583018424032001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5206284877776098261504005 976178414583018424032001)
                    ·
                      rfl

theorem cell22_2851651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 4].length) (baseStart_2851651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851651 prefixEnd_2851651 := by exact prefixLift 2851651
  have htrace : WordTrace (prefixWord ++ tailWord_2851651) baseStart_2851651 baseEnd_2851651 := by
    simpa [prefixWord, tailWord_2851651, baseEnd_2851651] using wordTrace_append hprefix tailTrace_2851651
  have hstable : (prefixWord ++ tailWord_2851651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851651).length < 2 ^ (prefixWord ++ tailWord_2851651).sum := by decide
  have hdescent : baseEnd_2851651 < baseStart_2851651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851653 : List Nat := [1, 3, 1, 1, 1, 2, 2, 6, 2, 3]
def baseStart_2851653 : Nat := 118140960795 + 2851653 * 2 ^ 59
def prefixEnd_2851653 : Nat := 4983230072969 + 3 ^ 40 * 2851653 * 2
def baseEnd_2851653 : Nat := 976179099223891085481995

theorem tailTrace_2851653 : CollatzResearch.WordTrace tailWord_2851653 prefixEnd_2851653 976179099223891085481995 := by
  unfold tailWord_2851653
  simp only [CollatzResearch.WordTrace]
  refine ⟨104008329537955679403583613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69338886358637119602389075 104008329537955679403583613)
  ·
    refine ⟨39003123576733379776343855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104008329537955679403583613 39003123576733379776343855)
    ·
      refine ⟨58504685365100069664515783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39003123576733379776343855 58504685365100069664515783)
      ·
        refine ⟨87757028047650104496773675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58504685365100069664515783 87757028047650104496773675)
        ·
          refine ⟨131635542071475156745160513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87757028047650104496773675 131635542071475156745160513)
          ·
            refine ⟨98726656553606367558870385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131635542071475156745160513 98726656553606367558870385)
            ·
              refine ⟨74044992415204775669152789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98726656553606367558870385 74044992415204775669152789)
              ·
                refine ⟨3470859019462723859491537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74044992415204775669152789 3470859019462723859491537)
                ·
                  refine ⟨2603144264597042894618653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3470859019462723859491537 2603144264597042894618653)
                  ·
                    refine ⟨976179099223891085481995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2603144264597042894618653 976179099223891085481995)
                    ·
                      rfl

theorem cell22_2851653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_2851653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851653 prefixEnd_2851653 := by exact prefixLift 2851653
  have htrace : WordTrace (prefixWord ++ tailWord_2851653) baseStart_2851653 baseEnd_2851653 := by
    simpa [prefixWord, tailWord_2851653, baseEnd_2851653] using wordTrace_append hprefix tailTrace_2851653
  have hstable : (prefixWord ++ tailWord_2851653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851653).length < 2 ^ (prefixWord ++ tailWord_2851653).sum := by decide
  have hdescent : baseEnd_2851653 < baseStart_2851653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851666 : List Nat := [3, 2, 2, 1, 1, 2, 2, 9]
def baseStart_2851666 : Nat := 118140960795 + 2851666 * 2 ^ 59
def prefixEnd_2851666 : Nat := 4983230072969 + 3 ^ 40 * 2851666 * 2
def baseEnd_2851666 : Nat := 108464838821062598322995

theorem tailTrace_2851666 : CollatzResearch.WordTrace tailWord_2851666 prefixEnd_2851666 108464838821062598322995 := by
  unfold tailWord_2851666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26002200921727145655951713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69339202457939055082537901 26002200921727145655951713)
  ·
    refine ⟨19501650691295359241963785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26002200921727145655951713 19501650691295359241963785)
    ·
      refine ⟨14626238018471519431472839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19501650691295359241963785 14626238018471519431472839)
      ·
        refine ⟨21939357027707279147209259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14626238018471519431472839 21939357027707279147209259)
        ·
          refine ⟨32909035541560918720813889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21939357027707279147209259 32909035541560918720813889)
          ·
            refine ⟨24681776656170689040610417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32909035541560918720813889 24681776656170689040610417)
            ·
              refine ⟨18511332492128016780457813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24681776656170689040610417 18511332492128016780457813)
              ·
                refine ⟨108464838821062598322995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18511332492128016780457813 108464838821062598322995)
                ·
                  rfl

theorem cell22_2851666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_2851666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851666 prefixEnd_2851666 := by exact prefixLift 2851666
  have htrace : WordTrace (prefixWord ++ tailWord_2851666) baseStart_2851666 baseEnd_2851666 := by
    simpa [prefixWord, tailWord_2851666, baseEnd_2851666] using wordTrace_append hprefix tailTrace_2851666
  have hstable : (prefixWord ++ tailWord_2851666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851666).length < 2 ^ (prefixWord ++ tailWord_2851666).sum := by decide
  have hdescent : baseEnd_2851666 < baseStart_2851666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851683 : List Nat := [1, 1, 1, 5, 3, 1, 4, 6]
def baseStart_2851683 : Nat := 118140960795 + 2851683 * 2 ^ 59
def prefixEnd_2851683 : Nat := 4983230072969 + 3 ^ 40 * 2851683 * 2
def baseEnd_2851683 : Nat := 108465485426331223025767

theorem tailTrace_2851683 : CollatzResearch.WordTrace tailWord_2851683 prefixEnd_2851683 108465485426331223025767 := by
  unfold tailWord_2851683
  simp only [CollatzResearch.WordTrace]
  refine ⟨104009423727846994527175703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69339615818564663018117135 104009423727846994527175703)
  ·
    refine ⟨156014135591770491790763555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104009423727846994527175703 156014135591770491790763555)
    ·
      refine ⟨234021203387655737686145333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156014135591770491790763555 234021203387655737686145333)
      ·
        refine ⟨21939487817592725408076125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234021203387655737686145333 21939487817592725408076125)
        ·
          refine ⟨8227307931597272028028547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21939487817592725408076125 8227307931597272028028547)
          ·
            refine ⟨12340961897395908042042821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8227307931597272028028547 12340961897395908042042821)
            ·
              refine ⟨2313930355761732757883029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12340961897395908042042821 2313930355761732757883029)
              ·
                refine ⟨108465485426331223025767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2313930355761732757883029 108465485426331223025767)
                ·
                  rfl

theorem cell22_2851683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 6].length) (baseStart_2851683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851683 prefixEnd_2851683 := by exact prefixLift 2851683
  have htrace : WordTrace (prefixWord ++ tailWord_2851683) baseStart_2851683 baseEnd_2851683 := by
    simpa [prefixWord, tailWord_2851683, baseEnd_2851683] using wordTrace_append hprefix tailTrace_2851683
  have hstable : (prefixWord ++ tailWord_2851683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851683).length < 2 ^ (prefixWord ++ tailWord_2851683).sum := by decide
  have hdescent : baseEnd_2851683 < baseStart_2851683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851698 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_2851698 : Nat := 118140960795 + 2851698 * 2 ^ 59
def prefixEnd_2851698 : Nat := 4983230072969 + 3 ^ 40 * 2851698 * 2
def baseEnd_2851698 : Nat := 976194503643525968106857

theorem tailTrace_2851698 : CollatzResearch.WordTrace tailWord_2851698 prefixEnd_2851698 976194503643525968106857 := by
  unfold tailWord_2851698
  simp only [CollatzResearch.WordTrace]
  refine ⟨26002492705698163022242937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69339980548528434725981165 26002492705698163022242937)
  ·
    refine ⟨19501869529273622266682203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26002492705698163022242937 19501869529273622266682203)
    ·
      refine ⟨29252804293910433400023305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19501869529273622266682203 29252804293910433400023305)
      ·
        refine ⟨21939603220432825050017479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29252804293910433400023305 21939603220432825050017479)
        ·
          refine ⟨32909404830649237575026219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21939603220432825050017479 32909404830649237575026219)
          ·
            refine ⟨49364107245973856362539329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32909404830649237575026219 49364107245973856362539329)
            ·
              refine ⟨37023080434480392271904497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49364107245973856362539329 37023080434480392271904497)
              ·
                refine ⟨27767310325860294203928373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37023080434480392271904497 27767310325860294203928373)
                ·
                  refine ⟨2603185343049402581618285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27767310325860294203928373 2603185343049402581618285)
                  ·
                    refine ⟨976194503643525968106857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2603185343049402581618285 976194503643525968106857)
                    ·
                      rfl

theorem cell22_2851698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_2851698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851698 prefixEnd_2851698 := by exact prefixLift 2851698
  have htrace : WordTrace (prefixWord ++ tailWord_2851698) baseStart_2851698 baseEnd_2851698 := by
    simpa [prefixWord, tailWord_2851698, baseEnd_2851698] using wordTrace_append hprefix tailTrace_2851698
  have hstable : (prefixWord ++ tailWord_2851698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851698).length < 2 ^ (prefixWord ++ tailWord_2851698).sum := by decide
  have hdescent : baseEnd_2851698 < baseStart_2851698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851711 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 7]
def baseStart_2851711 : Nat := 118140960795 + 2851711 * 2 ^ 59
def prefixEnd_2851711 : Nat := 4983230072969 + 3 ^ 40 * 2851711 * 2
def baseEnd_2851711 : Nat := 325399651269732755843939

theorem tailTrace_2851711 : CollatzResearch.WordTrace tailWord_2851711 prefixEnd_2851711 325399651269732755843939 := by
  unfold tailWord_2851711
  simp only [CollatzResearch.WordTrace]
  refine ⟨104010444971745555309194987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69340296647830370206129991 104010444971745555309194987)
  ·
    refine ⟨156015667457618332963792481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104010444971745555309194987 156015667457618332963792481)
    ·
      refine ⟨117011750593213749722844361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156015667457618332963792481 117011750593213749722844361)
      ·
        refine ⟨87758812944910312292133271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117011750593213749722844361 87758812944910312292133271)
        ·
          refine ⟨131638219417365468438199907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87758812944910312292133271 131638219417365468438199907)
          ·
            refine ⟨197457329126048202657299861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131638219417365468438199907 197457329126048202657299861)
            ·
              refine ⟨9255812302783509499560931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197457329126048202657299861 9255812302783509499560931)
              ·
                refine ⟨13883718454175264249341397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9255812302783509499560931 13883718454175264249341397)
                ·
                  refine ⟨325399651269732755843939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13883718454175264249341397 325399651269732755843939)
                  ·
                    rfl

theorem cell22_2851711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 7].length) (baseStart_2851711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851711 prefixEnd_2851711 := by exact prefixLift 2851711
  have htrace : WordTrace (prefixWord ++ tailWord_2851711) baseStart_2851711 baseEnd_2851711 := by
    simpa [prefixWord, tailWord_2851711, baseEnd_2851711] using wordTrace_append hprefix tailTrace_2851711
  have hstable : (prefixWord ++ tailWord_2851711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851711).length < 2 ^ (prefixWord ++ tailWord_2851711).sum := by decide
  have hdescent : baseEnd_2851711 < baseStart_2851711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851756 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 8]
def baseStart_2851756 : Nat := 118140960795 + 2851756 * 2 ^ 59
def prefixEnd_2851756 : Nat := 4983230072969 + 3 ^ 40 * 2851756 * 2
def baseEnd_2851756 : Nat := 325404786076277716718893

theorem tailTrace_2851756 : CollatzResearch.WordTrace tailWord_2851756 prefixEnd_2851756 325404786076277716718893 := by
  unfold tailWord_2851756
  simp only [CollatzResearch.WordTrace]
  refine ⟨52006043128291263997291561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69341390837721685329722081 52006043128291263997291561)
  ·
    refine ⟨39004532346218447997968671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52006043128291263997291561 39004532346218447997968671)
    ·
      refine ⟨58506798519327671996953007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39004532346218447997968671 58506798519327671996953007)
      ·
        refine ⟨87760197778991507995429511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58506798519327671996953007 87760197778991507995429511)
        ·
          refine ⟨131640296668487261993144267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87760197778991507995429511 131640296668487261993144267)
          ·
            refine ⟨197460445002730892989716401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131640296668487261993144267 197460445002730892989716401)
            ·
              refine ⟨148095333752048169742287301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197460445002730892989716401 148095333752048169742287301)
              ·
                refine ⟨27767875078509031826678869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148095333752048169742287301 27767875078509031826678869)
                ·
                  refine ⟨325404786076277716718893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27767875078509031826678869 325404786076277716718893)
                  ·
                    rfl

theorem cell22_2851756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_2851756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851756 prefixEnd_2851756 := by exact prefixLift 2851756
  have htrace : WordTrace (prefixWord ++ tailWord_2851756) baseStart_2851756 baseEnd_2851756 := by
    simpa [prefixWord, tailWord_2851756, baseEnd_2851756] using wordTrace_append hprefix tailTrace_2851756
  have hstable : (prefixWord ++ tailWord_2851756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851756).length < 2 ^ (prefixWord ++ tailWord_2851756).sum := by decide
  have hdescent : baseEnd_2851756 < baseStart_2851756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851805 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2851805 : Nat := 118140960795 + 2851805 * 2 ^ 59
def prefixEnd_2851805 : Nat := 4983230072969 + 3 ^ 40 * 2851805 * 2
def baseEnd_2851805 : Nat := 976231131930213355681529

theorem tailTrace_2851805 : CollatzResearch.WordTrace tailWord_2851805 prefixEnd_2851805 976231131930213355681529 := by
  unfold tailWord_2851805
  simp only [CollatzResearch.WordTrace]
  refine ⟨104013873433405009363116869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69342582288936672908744579 104013873433405009363116869)
  ·
    refine ⟨19502601268763439255584413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104013873433405009363116869 19502601268763439255584413)
    ·
      refine ⟨7313475475786289720844155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19502601268763439255584413 7313475475786289720844155)
      ·
        refine ⟨10970213213679434581266233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7313475475786289720844155 10970213213679434581266233)
        ·
          refine ⟨8227659910259575935949675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10970213213679434581266233 8227659910259575935949675)
          ·
            refine ⟨12341489865389363903924513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8227659910259575935949675 12341489865389363903924513)
            ·
              refine ⟨9256117399042022927943385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12341489865389363903924513 9256117399042022927943385)
              ·
                refine ⟨6942088049281517195957539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9256117399042022927943385 6942088049281517195957539)
                ·
                  refine ⟨10413132073922275793936309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6942088049281517195957539 10413132073922275793936309)
                  ·
                    refine ⟨976231131930213355681529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10413132073922275793936309 976231131930213355681529)
                    ·
                      rfl

theorem cell22_2851805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2851805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851805 prefixEnd_2851805 := by exact prefixLift 2851805
  have htrace : WordTrace (prefixWord ++ tailWord_2851805) baseStart_2851805 baseEnd_2851805 := by
    simpa [prefixWord, tailWord_2851805, baseEnd_2851805] using wordTrace_append hprefix tailTrace_2851805
  have hstable : (prefixWord ++ tailWord_2851805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851805).length < 2 ^ (prefixWord ++ tailWord_2851805).sum := by decide
  have hdescent : baseEnd_2851805 < baseStart_2851805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851807 : List Nat := [1, 1, 2, 3, 5, 1, 2, 3, 4]
def baseStart_2851807 : Nat := 118140960795 + 2851807 * 2 ^ 59
def prefixEnd_2851807 : Nat := 4983230072969 + 3 ^ 40 * 2851807 * 2
def baseEnd_2851807 : Nat := 325410605523695339043841

theorem tailTrace_2851807 : CollatzResearch.WordTrace tailWord_2851807 prefixEnd_2851807 325410605523695339043841 := by
  unfold tailWord_2851807
  simp only [CollatzResearch.WordTrace]
  refine ⟨104013946379397763704689675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69342630919598509136459783 104013946379397763704689675)
  ·
    refine ⟨156020919569096645557034513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104013946379397763704689675 156020919569096645557034513)
    ·
      refine ⟨117015689676822484167775885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156020919569096645557034513 117015689676822484167775885)
      ·
        refine ⟨43880883628808431562915957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117015689676822484167775885 43880883628808431562915957)
        ·
          refine ⟨4113832840200790459023371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43880883628808431562915957 4113832840200790459023371)
          ·
            refine ⟨6170749260301185688535057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113832840200790459023371 6170749260301185688535057)
            ·
              refine ⟨4628061945225889266401293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6170749260301185688535057 4628061945225889266401293)
              ·
                refine ⟨1735523229459708474900485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4628061945225889266401293 1735523229459708474900485)
                ·
                  refine ⟨325410605523695339043841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1735523229459708474900485 325410605523695339043841)
                  ·
                    rfl

theorem cell22_2851807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 4].length) (baseStart_2851807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851807 prefixEnd_2851807 := by exact prefixLift 2851807
  have htrace : WordTrace (prefixWord ++ tailWord_2851807) baseStart_2851807 baseEnd_2851807 := by
    simpa [prefixWord, tailWord_2851807, baseEnd_2851807] using wordTrace_append hprefix tailTrace_2851807
  have hstable : (prefixWord ++ tailWord_2851807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851807).length < 2 ^ (prefixWord ++ tailWord_2851807).sum := by decide
  have hdescent : baseEnd_2851807 < baseStart_2851807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851818 : List Nat := [3, 1, 3, 1, 2, 3, 9]
def baseStart_2851818 : Nat := 118140960795 + 2851818 * 2 ^ 59
def prefixEnd_2851818 : Nat := 4983230072969 + 3 ^ 40 * 2851818 * 2
def baseEnd_2851818 : Nat := 36156873410958727966907

theorem tailTrace_2851818 : CollatzResearch.WordTrace tailWord_2851818 prefixEnd_2851818 36156873410958727966907 := by
  unfold tailWord_2851818
  simp only [CollatzResearch.WordTrace]
  refine ⟨26003586895589478145835027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69342898388238608388893405 26003586895589478145835027)
  ·
    refine ⟨39005380343384217218752541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26003586895589478145835027 39005380343384217218752541)
    ·
      refine ⟨14627017628769081457032203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39005380343384217218752541 14627017628769081457032203)
      ·
        refine ⟨21940526443153622185548305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14627017628769081457032203 21940526443153622185548305)
        ·
          refine ⟨16455394832365216639161229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21940526443153622185548305 16455394832365216639161229)
          ·
            refine ⟨6170773062136956239685461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16455394832365216639161229 6170773062136956239685461)
            ·
              refine ⟨36156873410958727966907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6170773062136956239685461 36156873410958727966907)
              ·
                rfl

theorem cell22_2851818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 9].length) (baseStart_2851818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851818 prefixEnd_2851818 := by exact prefixLift 2851818
  have htrace : WordTrace (prefixWord ++ tailWord_2851818) baseStart_2851818 baseEnd_2851818 := by
    simpa [prefixWord, tailWord_2851818, baseEnd_2851818] using wordTrace_append hprefix tailTrace_2851818
  have hstable : (prefixWord ++ tailWord_2851818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851818).length < 2 ^ (prefixWord ++ tailWord_2851818).sum := by decide
  have hdescent : baseEnd_2851818 < baseStart_2851818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851822 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_2851822 : Nat := 118140960795 + 2851822 * 2 ^ 59
def prefixEnd_2851822 : Nat := 4983230072969 + 3 ^ 40 * 2851822 * 2
def baseEnd_2851822 : Nat := 976236951377630978006477

theorem tailTrace_2851822 : CollatzResearch.WordTrace tailWord_2851822 prefixEnd_2851822 976236951377630978006477 := by
  unfold tailWord_2851822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13001811684292927658310715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69342995649562280844323813 13001811684292927658310715)
  ·
    refine ⟨19502717526439391487466073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13001811684292927658310715 19502717526439391487466073)
    ·
      refine ⟨14627038144829543615599555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19502717526439391487466073 14627038144829543615599555)
      ·
        refine ⟨21940557217244315423399333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14627038144829543615599555 21940557217244315423399333)
        ·
          refine ⟨4113854478233309141887375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21940557217244315423399333 4113854478233309141887375)
          ·
            refine ⟨6170781717349963712831063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113854478233309141887375 6170781717349963712831063)
            ·
              refine ⟨9256172576024945569246595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6170781717349963712831063 9256172576024945569246595)
              ·
                refine ⟨13884258864037418353869893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9256172576024945569246595 13884258864037418353869893)
                ·
                  refine ⟨2603298537007015941350605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13884258864037418353869893 2603298537007015941350605)
                  ·
                    refine ⟨976236951377630978006477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2603298537007015941350605 976236951377630978006477)
                    ·
                      rfl

theorem cell22_2851822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_2851822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851822 prefixEnd_2851822 := by exact prefixLift 2851822
  have htrace : WordTrace (prefixWord ++ tailWord_2851822) baseStart_2851822 baseEnd_2851822 := by
    simpa [prefixWord, tailWord_2851822, baseEnd_2851822] using wordTrace_append hprefix tailTrace_2851822
  have hstable : (prefixWord ++ tailWord_2851822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851822).length < 2 ^ (prefixWord ++ tailWord_2851822).sum := by decide
  have hdescent : baseEnd_2851822 < baseStart_2851822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851858 : List Nat := [3, 2, 5, 1, 1, 2, 1, 3, 4]
def baseStart_2851858 : Nat := 118140960795 + 2851858 * 2 ^ 59
def prefixEnd_2851858 : Nat := 4983230072969 + 3 ^ 40 * 2851858 * 2
def baseEnd_2851858 : Nat := 325416424971112961368789

theorem tailTrace_2851858 : CollatzResearch.WordTrace tailWord_2851858 prefixEnd_2851858 325416424971112961368789 := by
  unfold tailWord_2851858
  simp only [CollatzResearch.WordTrace]
  refine ⟨26003951625553249853699057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69343871001475332943197485 26003951625553249853699057)
  ·
    refine ⟨19502963719164937390274293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26003951625553249853699057 19502963719164937390274293)
    ·
      refine ⟨1828402848671712880338215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19502963719164937390274293 1828402848671712880338215)
      ·
        refine ⟨2742604273007569320507323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828402848671712880338215 2742604273007569320507323)
        ·
          refine ⟨4113906409511353980760985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2742604273007569320507323 4113906409511353980760985)
          ·
            refine ⟨3085429807133515485570739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4113906409511353980760985 3085429807133515485570739)
            ·
              refine ⟨4628144710700273228356109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085429807133515485570739 4628144710700273228356109)
              ·
                refine ⟨1735554266512602460633541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4628144710700273228356109 1735554266512602460633541)
                ·
                  refine ⟨325416424971112961368789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1735554266512602460633541 325416424971112961368789)
                  ·
                    rfl

theorem cell22_2851858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_2851858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851858 prefixEnd_2851858 := by exact prefixLift 2851858
  have htrace : WordTrace (prefixWord ++ tailWord_2851858) baseStart_2851858 baseEnd_2851858 := by
    simpa [prefixWord, tailWord_2851858, baseEnd_2851858] using wordTrace_append hprefix tailTrace_2851858
  have hstable : (prefixWord ++ tailWord_2851858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851858).length < 2 ^ (prefixWord ++ tailWord_2851858).sum := by decide
  have hdescent : baseEnd_2851858 < baseStart_2851858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851884 : List Nat := [2, 2, 1, 1, 1, 2, 7, 2, 1, 3]
def baseStart_2851884 : Nat := 118140960795 + 2851884 * 2 ^ 59
def prefixEnd_2851884 : Nat := 4983230072969 + 3 ^ 40 * 2851884 * 2
def baseEnd_2851884 : Nat := 976258175244683482956287

theorem tailTrace_2851884 : CollatzResearch.WordTrace tailWord_2851884 prefixEnd_2851884 976258175244683482956287 := by
  unfold tailWord_2851884
  simp only [CollatzResearch.WordTrace]
  refine ⟨52008377400059402927621353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69344503200079203903495137 52008377400059402927621353)
  ·
    refine ⟨39006283050044552195716015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52008377400059402927621353 39006283050044552195716015)
    ·
      refine ⟨58509424575066828293574023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39006283050044552195716015 58509424575066828293574023)
      ·
        refine ⟨87764136862600242440361035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58509424575066828293574023 87764136862600242440361035)
        ·
          refine ⟨131646205293900363660541553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87764136862600242440361035 131646205293900363660541553)
          ·
            refine ⟨98734653970425272745406165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131646205293900363660541553 98734653970425272745406165)
            ·
              refine ⟨2314093452431842329970457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 98734653970425272745406165 2314093452431842329970457)
              ·
                refine ⟨1735570089323881747477843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2314093452431842329970457 1735570089323881747477843)
                ·
                  refine ⟨2603355133985822621216765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735570089323881747477843 2603355133985822621216765)
                  ·
                    refine ⟨976258175244683482956287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2603355133985822621216765 976258175244683482956287)
                    ·
                      rfl

theorem cell22_2851884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_2851884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851884 prefixEnd_2851884 := by exact prefixLift 2851884
  have htrace : WordTrace (prefixWord ++ tailWord_2851884) baseStart_2851884 baseEnd_2851884 := by
    simpa [prefixWord, tailWord_2851884, baseEnd_2851884] using wordTrace_append hprefix tailTrace_2851884
  have hstable : (prefixWord ++ tailWord_2851884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851884).length < 2 ^ (prefixWord ++ tailWord_2851884).sum := by decide
  have hdescent : baseEnd_2851884 < baseStart_2851884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851893 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2851893 : Nat := 118140960795 + 2851893 * 2 ^ 59
def prefixEnd_2851893 : Nat := 4983230072969 + 3 ^ 40 * 2851893 * 2
def baseEnd_2851893 : Nat := 976261256128610459481259

theorem tailTrace_2851893 : CollatzResearch.WordTrace tailWord_2851893 prefixEnd_2851893 976261256128610459481259 := by
  unfold tailWord_2851893
  simp only [CollatzResearch.WordTrace]
  refine ⟨104017083057086200392320333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69344722038057466928213555 104017083057086200392320333)
  ·
    refine ⟨39006406146407325147120125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104017083057086200392320333 39006406146407325147120125)
    ·
      refine ⟨14627402304902746930170047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39006406146407325147120125 14627402304902746930170047)
      ·
        refine ⟨21941103457354120395255071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14627402304902746930170047 21941103457354120395255071)
        ·
          refine ⟨32911655186031180592882607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21941103457354120395255071 32911655186031180592882607)
          ·
            refine ⟨49367482779046770889323911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32911655186031180592882607 49367482779046770889323911)
            ·
              refine ⟨74051224168570156333985867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49367482779046770889323911 74051224168570156333985867)
              ·
                refine ⟨111076836252855234500978801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74051224168570156333985867 111076836252855234500978801)
                ·
                  refine ⟨83307627189641425875734101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111076836252855234500978801 83307627189641425875734101)
                  ·
                    refine ⟨976261256128610459481259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83307627189641425875734101 976261256128610459481259)
                    ·
                      rfl

theorem cell22_2851893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2851893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851893 prefixEnd_2851893 := by exact prefixLift 2851893
  have htrace : WordTrace (prefixWord ++ tailWord_2851893) baseStart_2851893 baseEnd_2851893 := by
    simpa [prefixWord, tailWord_2851893, baseEnd_2851893] using wordTrace_append hprefix tailTrace_2851893
  have hstable : (prefixWord ++ tailWord_2851893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851893).length < 2 ^ (prefixWord ++ tailWord_2851893).sum := by decide
  have hdescent : baseEnd_2851893 < baseStart_2851893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851897 : List Nat := [1, 2, 1, 5, 2, 1, 4, 1, 5]
def baseStart_2851897 : Nat := 118140960795 + 2851897 * 2 ^ 59
def prefixEnd_2851897 : Nat := 4983230072969 + 3 ^ 40 * 2851897 * 2
def baseEnd_2851897 : Nat := 325420875136785260793749

theorem tailTrace_2851897 : CollatzResearch.WordTrace tailWord_2851897 prefixEnd_2851897 325420875136785260793749 := by
  unfold tailWord_2851897
  simp only [CollatzResearch.WordTrace]
  refine ⟨104017228949071709075465945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69344819299381139383643963 104017228949071709075465945)
  ·
    refine ⟨78012921711803781806599459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104017228949071709075465945 78012921711803781806599459)
    ·
      refine ⟨117019382567705672709899189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78012921711803781806599459 117019382567705672709899189)
      ·
        refine ⟨10970567115722406816553049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117019382567705672709899189 10970567115722406816553049)
        ·
          refine ⟨8227925336791805112414787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10970567115722406816553049 8227925336791805112414787)
          ·
            refine ⟨12341888005187707668622181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8227925336791805112414787 12341888005187707668622181)
            ·
              refine ⟨2314104000972695187866659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12341888005187707668622181 2314104000972695187866659)
              ·
                refine ⟨3471156001459042781799989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314104000972695187866659 3471156001459042781799989)
                ·
                  refine ⟨325420875136785260793749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3471156001459042781799989 325420875136785260793749)
                  ·
                    rfl

theorem cell22_2851897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 5].length) (baseStart_2851897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851897 prefixEnd_2851897 := by exact prefixLift 2851897
  have htrace : WordTrace (prefixWord ++ tailWord_2851897) baseStart_2851897 baseEnd_2851897 := by
    simpa [prefixWord, tailWord_2851897, baseEnd_2851897] using wordTrace_append hprefix tailTrace_2851897
  have hstable : (prefixWord ++ tailWord_2851897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851897).length < 2 ^ (prefixWord ++ tailWord_2851897).sum := by decide
  have hdescent : baseEnd_2851897 < baseStart_2851897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851923 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 3, 5]
def baseStart_2851923 : Nat := 118140960795 + 2851923 * 2 ^ 59
def prefixEnd_2851923 : Nat := 4983230072969 + 3 ^ 40 * 2851923 * 2
def baseEnd_2851923 : Nat := 976271525741700381231167

theorem tailTrace_2851923 : CollatzResearch.WordTrace tailWord_2851923 prefixEnd_2851923 976271525741700381231167 := by
  unfold tailWord_2851923
  simp only [CollatzResearch.WordTrace]
  refine ⟨104018177246977515515912423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69345451497985010343941615 104018177246977515515912423)
  ·
    refine ⟨156027265870466273273868635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104018177246977515515912423 156027265870466273273868635)
    ·
      refine ⟨234040898805699409910802953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156027265870466273273868635 234040898805699409910802953)
      ·
        refine ⟨175530674104274557433102215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234040898805699409910802953 175530674104274557433102215)
        ·
          refine ⟨263296011156411836149653323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175530674104274557433102215 263296011156411836149653323)
          ·
            refine ⟨394944016734617754224479985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263296011156411836149653323 394944016734617754224479985)
            ·
              refine ⟨296208012550963315668359989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394944016734617754224479985 296208012550963315668359989)
              ·
                refine ⟨27769501176652810843908749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 296208012550963315668359989 27769501176652810843908749)
                ·
                  refine ⟨10413562941244804066465781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27769501176652810843908749 10413562941244804066465781)
                  ·
                    refine ⟨976271525741700381231167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10413562941244804066465781 976271525741700381231167)
                    ·
                      rfl

theorem cell22_2851923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_2851923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851923 prefixEnd_2851923 := by exact prefixLift 2851923
  have htrace : WordTrace (prefixWord ++ tailWord_2851923) baseStart_2851923 baseEnd_2851923 := by
    simpa [prefixWord, tailWord_2851923, baseEnd_2851923] using wordTrace_append hprefix tailTrace_2851923
  have hstable : (prefixWord ++ tailWord_2851923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851923).length < 2 ^ (prefixWord ++ tailWord_2851923).sum := by decide
  have hdescent : baseEnd_2851923 < baseStart_2851923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851953 : List Nat := [1, 2, 2, 2, 1, 1, 2, 11]
def baseStart_2851953 : Nat := 118140960795 + 2851953 * 2 ^ 59
def prefixEnd_2851953 : Nat := 4983230072969 + 3 ^ 40 * 2851953 * 2
def baseEnd_2851953 : Nat := 108475755039421144775675

theorem tailTrace_2851953 : CollatzResearch.WordTrace tailWord_2851953 prefixEnd_2851953 108475755039421144775675 := by
  unfold tailWord_2851953
  simp only [CollatzResearch.WordTrace]
  refine ⟨104019271436868830639504513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69346180957912553759669675 104019271436868830639504513)
  ·
    refine ⟨78014453577651622979628385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104019271436868830639504513 78014453577651622979628385)
    ·
      refine ⟨58510840183238717234721289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78014453577651622979628385 58510840183238717234721289)
      ·
        refine ⟨43883130137429037926040967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58510840183238717234721289 43883130137429037926040967)
        ·
          refine ⟨65824695206143556889061451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43883130137429037926040967 65824695206143556889061451)
          ·
            refine ⟨98737042809215335333592177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65824695206143556889061451 98737042809215335333592177)
            ·
              refine ⟨74052782106911501500194133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98737042809215335333592177 74052782106911501500194133)
              ·
                refine ⟨108475755039421144775675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 74052782106911501500194133 108475755039421144775675)
                ·
                  rfl

theorem cell22_2851953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 11].length) (baseStart_2851953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851953 prefixEnd_2851953 := by exact prefixLift 2851953
  have htrace : WordTrace (prefixWord ++ tailWord_2851953) baseStart_2851953 baseEnd_2851953 := by
    simpa [prefixWord, tailWord_2851953, baseEnd_2851953] using wordTrace_append hprefix tailTrace_2851953
  have hstable : (prefixWord ++ tailWord_2851953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851953).length < 2 ^ (prefixWord ++ tailWord_2851953).sum := by decide
  have hdescent : baseEnd_2851953 < baseStart_2851953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851972 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_2851972 : Nat := 118140960795 + 2851972 * 2 ^ 59
def prefixEnd_2851972 : Nat := 4983230072969 + 3 ^ 40 * 2851972 * 2
def baseEnd_2851972 : Nat := 976288299443080586756017

theorem tailTrace_2851972 : CollatzResearch.WordTrace tailWord_2851972 prefixEnd_2851972 976288299443080586756017 := by
  unfold tailWord_2851972
  simp only [CollatzResearch.WordTrace]
  refine ⟨52009982211899998442223085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69346642949199997922964113 52009982211899998442223085)
  ·
    refine ⟨19503743329462499415833657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52009982211899998442223085 19503743329462499415833657)
    ·
      refine ⟨14627807497096874561875243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19503743329462499415833657 14627807497096874561875243)
      ·
        refine ⟨21941711245645311842812865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14627807497096874561875243 21941711245645311842812865)
        ·
          refine ⟨16456283434233983882109649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21941711245645311842812865 16456283434233983882109649)
          ·
            refine ⟨12342212575675487911582237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16456283434233983882109649 12342212575675487911582237)
            ·
              refine ⟨4628329715878307966843339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12342212575675487911582237 4628329715878307966843339)
              ·
                refine ⟨6942494573817461950265009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628329715878307966843339 6942494573817461950265009)
                ·
                  refine ⟨5206870930363096462698757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6942494573817461950265009 5206870930363096462698757)
                  ·
                    refine ⟨976288299443080586756017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5206870930363096462698757 976288299443080586756017)
                    ·
                      rfl

theorem cell22_2851972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_2851972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2851972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2851972 prefixEnd_2851972 := by exact prefixLift 2851972
  have htrace : WordTrace (prefixWord ++ tailWord_2851972) baseStart_2851972 baseEnd_2851972 := by
    simpa [prefixWord, tailWord_2851972, baseEnd_2851972] using wordTrace_append hprefix tailTrace_2851972
  have hstable : (prefixWord ++ tailWord_2851972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851972).length < 2 ^ (prefixWord ++ tailWord_2851972).sum := by decide
  have hdescent : baseEnd_2851972 < baseStart_2851972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852015 : List Nat := [1, 1, 2, 1, 2, 3, 2, 5, 5]
def baseStart_2852015 : Nat := 118140960795 + 2852015 * 2 ^ 59
def prefixEnd_2852015 : Nat := 4983230072969 + 3 ^ 40 * 2852015 * 2
def baseEnd_2852015 : Nat := 325434339740614269310295

theorem tailTrace_2852015 : CollatzResearch.WordTrace tailWord_2852015 prefixEnd_2852015 325434339740614269310295 := by
  unfold tailWord_2852015
  simp only [CollatzResearch.WordTrace]
  refine ⟨104021532762644215228261499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69347688508429476818840999 104021532762644215228261499)
  ·
    refine ⟨156032299143966322842392249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104021532762644215228261499 156032299143966322842392249)
    ·
      refine ⟨117024224357974742131794187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156032299143966322842392249 117024224357974742131794187)
      ·
        refine ⟨175536336536962113197691281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117024224357974742131794187 175536336536962113197691281)
        ·
          refine ⟨131652252402721584898268461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175536336536962113197691281 131652252402721584898268461)
          ·
            refine ⟨49369594651020594336850673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131652252402721584898268461 49369594651020594336850673)
            ·
              refine ⟨37027195988265445752638005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49369594651020594336850673 37027195988265445752638005)
              ·
                refine ⟨3471299623899885539309813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37027195988265445752638005 3471299623899885539309813)
                ·
                  refine ⟨325434339740614269310295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3471299623899885539309813 325434339740614269310295)
                  ·
                    rfl

theorem cell22_2852015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 5].length) (baseStart_2852015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852015 prefixEnd_2852015 := by exact prefixLift 2852015
  have htrace : WordTrace (prefixWord ++ tailWord_2852015) baseStart_2852015 baseEnd_2852015 := by
    simpa [prefixWord, tailWord_2852015, baseEnd_2852015] using wordTrace_append hprefix tailTrace_2852015
  have hstable : (prefixWord ++ tailWord_2852015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852015).length < 2 ^ (prefixWord ++ tailWord_2852015).sum := by decide
  have hdescent : baseEnd_2852015 < baseStart_2852015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852038 : List Nat := [6, 1, 2, 2, 2, 1, 8]
def baseStart_2852038 : Nat := 118140960795 + 2852038 * 2 ^ 59
def prefixEnd_2852038 : Nat := 4983230072969 + 3 ^ 40 * 2852038 * 2
def baseEnd_2852038 : Nat := 36159662688588089429845

theorem tailTrace_2852038 : CollatzResearch.WordTrace tailWord_2852038 prefixEnd_2852038 36159662688588089429845 := by
  unfold tailWord_2852038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3250699113798777817385899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69348247761040593437565845 3250699113798777817385899)
  ·
    refine ⟨4876048670698166726078849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3250699113798777817385899 4876048670698166726078849)
    ·
      refine ⟨3657036503023625044559137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4876048670698166726078849 3657036503023625044559137)
      ·
        refine ⟨2742777377267718783419353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3657036503023625044559137 2742777377267718783419353)
        ·
          refine ⟨2057083032950789087564515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2742777377267718783419353 2057083032950789087564515)
          ·
            refine ⟨3085624549426183631346773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057083032950789087564515 3085624549426183631346773)
            ·
              refine ⟨36159662688588089429845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3085624549426183631346773 36159662688588089429845)
              ·
                rfl

theorem cell22_2852038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 8].length) (baseStart_2852038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852038 prefixEnd_2852038 := by exact prefixLift 2852038
  have htrace : WordTrace (prefixWord ++ tailWord_2852038) baseStart_2852038 baseEnd_2852038 := by
    simpa [prefixWord, tailWord_2852038, baseEnd_2852038] using wordTrace_append hprefix tailTrace_2852038
  have hstable : (prefixWord ++ tailWord_2852038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852038).length < 2 ^ (prefixWord ++ tailWord_2852038).sum := by decide
  have hdescent : baseEnd_2852038 < baseStart_2852038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852053 : List Nat := [1, 3, 2, 4, 1, 2, 3, 2, 1, 3]
def baseStart_2852053 : Nat := 118140960795 + 2852053 * 2 ^ 59
def prefixEnd_2852053 : Nat := 4983230072969 + 3 ^ 40 * 2852053 * 2
def baseEnd_2852053 : Nat := 976316027398423375480769

theorem tailTrace_2852053 : CollatzResearch.WordTrace tailWord_2852053 prefixEnd_2852053 976316027398423375480769 := by
  unfold tailWord_2852053
  simp only [CollatzResearch.WordTrace]
  refine ⟨104022918736506547718144813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69348612491004365145429875 104022918736506547718144813)
  ·
    refine ⟨39008594526189955394304305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104022918736506547718144813 39008594526189955394304305)
    ·
      refine ⟨29256445894642466545728229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39008594526189955394304305 29256445894642466545728229)
      ·
        refine ⟨5485583605245462477324043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29256445894642466545728229 5485583605245462477324043)
        ·
          refine ⟨8228375407868193715986065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5485583605245462477324043 8228375407868193715986065)
          ·
            refine ⟨6171281555901145286989549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8228375407868193715986065 6171281555901145286989549)
            ·
              refine ⟨2314230583462929482621081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6171281555901145286989549 2314230583462929482621081)
              ·
                refine ⟨1735672937597197111965811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2314230583462929482621081 1735672937597197111965811)
                ·
                  refine ⟨2603509406395795667948717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735672937597197111965811 2603509406395795667948717)
                  ·
                    refine ⟨976316027398423375480769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2603509406395795667948717 976316027398423375480769)
                    ·
                      rfl

theorem cell22_2852053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_2852053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852053 prefixEnd_2852053 := by exact prefixLift 2852053
  have htrace : WordTrace (prefixWord ++ tailWord_2852053) baseStart_2852053 baseEnd_2852053 := by
    simpa [prefixWord, tailWord_2852053, baseEnd_2852053] using wordTrace_append hprefix tailTrace_2852053
  have hstable : (prefixWord ++ tailWord_2852053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852053).length < 2 ^ (prefixWord ++ tailWord_2852053).sum := by decide
  have hdescent : baseEnd_2852053 < baseStart_2852053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852107 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 2, 4]
def baseStart_2852107 : Nat := 118140960795 + 2852107 * 2 ^ 59
def prefixEnd_2852107 : Nat := 4983230072969 + 3 ^ 40 * 2852107 * 2
def baseEnd_2852107 : Nat := 976334512701985234630603

theorem tailTrace_2852107 : CollatzResearch.WordTrace tailWord_2852107 prefixEnd_2852107 976334512701985234630603 := by
  unfold tailWord_2852107
  simp only [CollatzResearch.WordTrace]
  refine ⟨104024888278310914940610575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69349925518873943293740383 104024888278310914940610575)
  ·
    refine ⟨156037332417466372410915863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104024888278310914940610575 156037332417466372410915863)
    ·
      refine ⟨234055998626199558616373795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156037332417466372410915863 234055998626199558616373795)
      ·
        refine ⟨351083997939299337924560693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234055998626199558616373795 351083997939299337924560693)
        ·
          refine ⟨32914124806809312930427565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351083997939299337924560693 32914124806809312930427565)
          ·
            refine ⟨12342796802553492348910337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32914124806809312930427565 12342796802553492348910337)
            ·
              refine ⟨9257097601915119261682753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12342796802553492348910337 9257097601915119261682753)
              ·
                refine ⟨6942823201436339446262065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9257097601915119261682753 6942823201436339446262065)
                ·
                  refine ⟨5207117401077254584696549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6942823201436339446262065 5207117401077254584696549)
                  ·
                    refine ⟨976334512701985234630603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5207117401077254584696549 976334512701985234630603)
                    ·
                      rfl

theorem cell22_2852107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 4].length) (baseStart_2852107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852107 prefixEnd_2852107 := by exact prefixLift 2852107
  have htrace : WordTrace (prefixWord ++ tailWord_2852107) baseStart_2852107 baseEnd_2852107 := by
    simpa [prefixWord, tailWord_2852107, baseEnd_2852107] using wordTrace_append hprefix tailTrace_2852107
  have hstable : (prefixWord ++ tailWord_2852107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852107).length < 2 ^ (prefixWord ++ tailWord_2852107).sum := by decide
  have hdescent : baseEnd_2852107 < baseStart_2852107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852122 : List Nat := [3, 1, 1, 3, 3, 1, 3, 7]
def baseStart_2852122 : Nat := 118140960795 + 2852122 * 2 ^ 59
def prefixEnd_2852122 : Nat := 4983230072969 + 3 ^ 40 * 2852122 * 2
def baseEnd_2852122 : Nat := 108482183056503355056173

theorem tailTrace_2852122 : CollatzResearch.WordTrace tailWord_2852122 prefixEnd_2852122 108482183056503355056173 := by
  unfold tailWord_2852122
  simp only [CollatzResearch.WordTrace]
  refine ⟨26006358843314143125601655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69350290248837715001604413 26006358843314143125601655)
  ·
    refine ⟨39009538264971214688402483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26006358843314143125601655 39009538264971214688402483)
    ·
      refine ⟨58514307397456822032603725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39009538264971214688402483 58514307397456822032603725)
      ·
        refine ⟨21942865274046308262226397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58514307397456822032603725 21942865274046308262226397)
        ·
          refine ⟨8228574477767365598334899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21942865274046308262226397 8228574477767365598334899)
          ·
            refine ⟨12342861716651048397502349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8228574477767365598334899 12342861716651048397502349)
            ·
              refine ⟨4628573143744143149063381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12342861716651048397502349 4628573143744143149063381)
              ·
                refine ⟨108482183056503355056173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4628573143744143149063381 108482183056503355056173)
                ·
                  rfl

theorem cell22_2852122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_2852122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852122 prefixEnd_2852122 := by exact prefixLift 2852122
  have htrace : WordTrace (prefixWord ++ tailWord_2852122) baseStart_2852122 baseEnd_2852122 := by
    simpa [prefixWord, tailWord_2852122, baseEnd_2852122] using wordTrace_append hprefix tailTrace_2852122
  have hstable : (prefixWord ++ tailWord_2852122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852122).length < 2 ^ (prefixWord ++ tailWord_2852122).sum := by decide
  have hdescent : baseEnd_2852122 < baseStart_2852122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852141 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2852141 : Nat := 118140960795 + 2852141 * 2 ^ 59
def prefixEnd_2852141 : Nat := 4983230072969 + 3 ^ 40 * 2852141 * 2
def baseEnd_2852141 : Nat := 976346151596820479280499

theorem tailTrace_2852141 : CollatzResearch.WordTrace tailWord_2852141 prefixEnd_2852141 976346151596820479280499 := by
  unfold tailWord_2852141
  simp only [CollatzResearch.WordTrace]
  refine ⟨104026128360187738747348277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69350752240125159164898851 104026128360187738747348277)
  ·
    refine ⟨9752449533767600507563901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104026128360187738747348277 9752449533767600507563901)
    ·
      refine ⟨3657168575162850190336463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9752449533767600507563901 3657168575162850190336463)
      ·
        refine ⟨5485752862744275285504695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3657168575162850190336463 5485752862744275285504695)
        ·
          refine ⟨8228629294116412928257043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5485752862744275285504695 8228629294116412928257043)
          ·
            refine ⟨12342943941174619392385565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8228629294116412928257043 12342943941174619392385565)
            ·
              refine ⟨4628603977940482272144587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12342943941174619392385565 4628603977940482272144587)
              ·
                refine ⟨6942905966910723408216881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628603977940482272144587 6942905966910723408216881)
                ·
                  refine ⟨5207179475183042556162661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6942905966910723408216881 5207179475183042556162661)
                  ·
                    refine ⟨976346151596820479280499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5207179475183042556162661 976346151596820479280499)
                    ·
                      rfl

theorem cell22_2852141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2852141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852141 prefixEnd_2852141 := by exact prefixLift 2852141
  have htrace : WordTrace (prefixWord ++ tailWord_2852141) baseStart_2852141 baseEnd_2852141 := by
    simpa [prefixWord, tailWord_2852141, baseEnd_2852141] using wordTrace_append hprefix tailTrace_2852141
  have hstable : (prefixWord ++ tailWord_2852141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852141).length < 2 ^ (prefixWord ++ tailWord_2852141).sum := by decide
  have hdescent : baseEnd_2852141 < baseStart_2852141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852167 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 7]
def baseStart_2852167 : Nat := 118140960795 + 2852167 * 2 ^ 59
def prefixEnd_2852167 : Nat := 4983230072969 + 3 ^ 40 * 2852167 * 2
def baseEnd_2852167 : Nat := 325451683976055026043473

theorem tailTrace_2852167 : CollatzResearch.WordTrace tailWord_2852167 prefixEnd_2852167 325451683976055026043473 := by
  unfold tailWord_2852167
  simp only [CollatzResearch.WordTrace]
  refine ⟨104027076658093545187794755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69351384438729030125196503 104027076658093545187794755)
  ·
    refine ⟨156040614987140317781692133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104027076658093545187794755 156040614987140317781692133)
    ·
      refine ⟨29257615310088809584067275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156040614987140317781692133 29257615310088809584067275)
      ·
        refine ⟨43886422965133214376100913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29257615310088809584067275 43886422965133214376100913)
        ·
          refine ⟨32914817223849910782075685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43886422965133214376100913 32914817223849910782075685)
          ·
            refine ⟨6171528229471858271639191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32914817223849910782075685 6171528229471858271639191)
            ·
              refine ⟨9257292344207787407458787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6171528229471858271639191 9257292344207787407458787)
              ·
                refine ⟨13885938516311681111188181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9257292344207787407458787 13885938516311681111188181)
                ·
                  refine ⟨325451683976055026043473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13885938516311681111188181 325451683976055026043473)
                  ·
                    rfl

theorem cell22_2852167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 7].length) (baseStart_2852167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852167 prefixEnd_2852167 := by exact prefixLift 2852167
  have htrace : WordTrace (prefixWord ++ tailWord_2852167) baseStart_2852167 baseEnd_2852167 := by
    simpa [prefixWord, tailWord_2852167, baseEnd_2852167] using wordTrace_append hprefix tailTrace_2852167
  have hstable : (prefixWord ++ tailWord_2852167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852167).length < 2 ^ (prefixWord ++ tailWord_2852167).sum := by decide
  have hdescent : baseEnd_2852167 < baseStart_2852167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852184 : List Nat := [2, 1, 2, 2, 1, 1, 7, 1, 5]
def baseStart_2852184 : Nat := 118140960795 + 2852184 * 2 ^ 59
def prefixEnd_2852184 : Nat := 4983230072969 + 3 ^ 40 * 2852184 * 2
def baseEnd_2852184 : Nat := 325453623791860900151789

theorem tailTrace_2852184 : CollatzResearch.WordTrace tailWord_2852184 prefixEnd_2852184 325453623791860900151789 := by
  unfold tailWord_2852184
  simp only [CollatzResearch.WordTrace]
  refine ⟨52013848349515978545581803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69351797799354638060775737 52013848349515978545581803)
  ·
    refine ⟨78020772524273967818372705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52013848349515978545581803 78020772524273967818372705)
    ·
      refine ⟨58515579393205475863779529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78020772524273967818372705 58515579393205475863779529)
      ·
        refine ⟨43886684544904106897834647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58515579393205475863779529 43886684544904106897834647)
        ·
          refine ⟨65830026817356160346751971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43886684544904106897834647 65830026817356160346751971)
          ·
            refine ⟨98745040226034240520127957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65830026817356160346751971 98745040226034240520127957)
            ·
              refine ⟨2314336880297677512190499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 98745040226034240520127957 2314336880297677512190499)
              ·
                refine ⟨3471505320446516268285749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314336880297677512190499 3471505320446516268285749)
                ·
                  refine ⟨325453623791860900151789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3471505320446516268285749 325453623791860900151789)
                  ·
                    rfl

theorem cell22_2852184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 5].length) (baseStart_2852184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852184 prefixEnd_2852184 := by exact prefixLift 2852184
  have htrace : WordTrace (prefixWord ++ tailWord_2852184) baseStart_2852184 baseEnd_2852184 := by
    simpa [prefixWord, tailWord_2852184, baseEnd_2852184] using wordTrace_append hprefix tailTrace_2852184
  have hstable : (prefixWord ++ tailWord_2852184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852184).length < 2 ^ (prefixWord ++ tailWord_2852184).sum := by decide
  have hdescent : baseEnd_2852184 < baseStart_2852184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852222 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2852222 : Nat := 118140960795 + 2852222 * 2 ^ 59
def prefixEnd_2852222 : Nat := 4983230072969 + 3 ^ 40 * 2852222 * 2
def baseEnd_2852222 : Nat := 976373879552163268005251

theorem tailTrace_2852222 : CollatzResearch.WordTrace tailWord_2852222 prefixEnd_2852222 976373879552163268005251 := by
  unfold tailWord_2852222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13003635334111786197630865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69352721781929526387364613 13003635334111786197630865)
  ·
    refine ⟨9752726500583839648223149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13003635334111786197630865 9752726500583839648223149)
    ·
      refine ⟨3657272437718939868083681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9752726500583839648223149 3657272437718939868083681)
      ·
        refine ⟨2742954328289204901062761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3657272437718939868083681 2742954328289204901062761)
        ·
          refine ⟨2057215746216903675797071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2742954328289204901062761 2057215746216903675797071)
          ·
            refine ⟨3085823619325355513695607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057215746216903675797071 3085823619325355513695607)
            ·
              refine ⟨4628735428988033270543411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085823619325355513695607 4628735428988033270543411)
              ·
                refine ⟨6943103143482049905815117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628735428988033270543411 6943103143482049905815117)
                ·
                  refine ⟨2603663678805768714680669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6943103143482049905815117 2603663678805768714680669)
                  ·
                    refine ⟨976373879552163268005251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2603663678805768714680669 976373879552163268005251)
                    ·
                      rfl

theorem cell22_2852222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2852222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852222 prefixEnd_2852222 := by exact prefixLift 2852222
  have htrace : WordTrace (prefixWord ++ tailWord_2852222) baseStart_2852222 baseEnd_2852222 := by
    simpa [prefixWord, tailWord_2852222, baseEnd_2852222] using wordTrace_append hprefix tailTrace_2852222
  have hstable : (prefixWord ++ tailWord_2852222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852222).length < 2 ^ (prefixWord ++ tailWord_2852222).sum := by decide
  have hdescent : baseEnd_2852222 < baseStart_2852222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852229 : List Nat := [1, 3, 1, 1, 3, 1, 2, 6, 4]
def baseStart_2852229 : Nat := 118140960795 + 2852229 * 2 ^ 59
def prefixEnd_2852229 : Nat := 4983230072969 + 3 ^ 40 * 2852229 * 2
def baseEnd_2852229 : Nat := 325458758598405861026743

theorem tailTrace_2852229 : CollatzResearch.WordTrace tailWord_2852229 prefixEnd_2852229 325458758598405861026743 := by
  unfold tailWord_2852229
  simp only [CollatzResearch.WordTrace]
  refine ⟨104029337983868929776551741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69352891989245953184367827 104029337983868929776551741)
  ·
    refine ⟨39011001743950848666206903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104029337983868929776551741 39011001743950848666206903)
    ·
      refine ⟨58516502615926272999310355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39011001743950848666206903 58516502615926272999310355)
      ·
        refine ⟨87774753923889409498965533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58516502615926272999310355 87774753923889409498965533)
        ·
          refine ⟨32915532721458528562112075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87774753923889409498965533 32915532721458528562112075)
          ·
            refine ⟨49373299082187792843168113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32915532721458528562112075 49373299082187792843168113)
            ·
              refine ⟨37029974311640844632376085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49373299082187792843168113 37029974311640844632376085)
              ·
                refine ⟨1735780045858164592142629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37029974311640844632376085 1735780045858164592142629)
                ·
                  refine ⟨325458758598405861026743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1735780045858164592142629 325458758598405861026743)
                  ·
                    rfl

theorem cell22_2852229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_2852229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852229 prefixEnd_2852229 := by exact prefixLift 2852229
  have htrace : WordTrace (prefixWord ++ tailWord_2852229) baseStart_2852229 baseEnd_2852229 := by
    simpa [prefixWord, tailWord_2852229, baseEnd_2852229] using wordTrace_append hprefix tailTrace_2852229
  have hstable : (prefixWord ++ tailWord_2852229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852229).length < 2 ^ (prefixWord ++ tailWord_2852229).sum := by decide
  have hdescent : baseEnd_2852229 < baseStart_2852229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852248 : List Nat := [2, 1, 2, 5, 2, 2, 1, 2, 1, 4]
def baseStart_2852248 : Nat := 118140960795 + 2852248 * 2 ^ 59
def prefixEnd_2852248 : Nat := 4983230072969 + 3 ^ 40 * 2852248 * 2
def baseEnd_2852248 : Nat := 976382779883507866855171

theorem tailTrace_2852248 : CollatzResearch.WordTrace tailWord_2852248 prefixEnd_2852248 976382779883507866855171 := by
  unfold tailWord_2852248
  simp only [CollatzResearch.WordTrace]
  refine ⟨52015015485400048010746699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69353353980533397347662265 52015015485400048010746699)
  ·
    refine ⟨78022523228100072016120049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52015015485400048010746699 78022523228100072016120049)
    ·
      refine ⟨58516892421075054012090037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78022523228100072016120049 58516892421075054012090037)
      ·
        refine ⟨5485958664475786313633441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58516892421075054012090037 5485958664475786313633441)
        ·
          refine ⟨4114468998356839735225081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5485958664475786313633441 4114468998356839735225081)
          ·
            refine ⟨3085851748767629801418811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4114468998356839735225081 3085851748767629801418811)
            ·
              refine ⟨4628777623151444702128217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085851748767629801418811 4628777623151444702128217)
              ·
                refine ⟨3471583217363583526596163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4628777623151444702128217 3471583217363583526596163)
                ·
                  refine ⟨5207374826045375289894245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3471583217363583526596163 5207374826045375289894245)
                  ·
                    refine ⟨976382779883507866855171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5207374826045375289894245 976382779883507866855171)
                    ·
                      rfl

theorem cell22_2852248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_2852248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852248 prefixEnd_2852248 := by exact prefixLift 2852248
  have htrace : WordTrace (prefixWord ++ tailWord_2852248) baseStart_2852248 baseEnd_2852248 := by
    simpa [prefixWord, tailWord_2852248, baseEnd_2852248] using wordTrace_append hprefix tailTrace_2852248
  have hstable : (prefixWord ++ tailWord_2852248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852248).length < 2 ^ (prefixWord ++ tailWord_2852248).sum := by decide
  have hdescent : baseEnd_2852248 < baseStart_2852248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852259 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 2, 4]
def baseStart_2852259 : Nat := 118140960795 + 2852259 * 2 ^ 59
def prefixEnd_2852259 : Nat := 4983230072969 + 3 ^ 40 * 2852259 * 2
def baseEnd_2852259 : Nat := 976386545408307504830137

theorem tailTrace_2852259 : CollatzResearch.WordTrace tailWord_2852259 prefixEnd_2852259 976386545408307504830137 := by
  unfold tailWord_2852259
  simp only [CollatzResearch.WordTrace]
  refine ⟨104030432173760244900143831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69353621449173496600095887 104030432173760244900143831)
  ·
    refine ⟨156045648260640367350215747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104030432173760244900143831 156045648260640367350215747)
    ·
      refine ⟨234068472390960551025323621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156045648260640367350215747 234068472390960551025323621)
      ·
        refine ⟨43887838573305103317248179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234068472390960551025323621 43887838573305103317248179)
        ·
          refine ⟨65831757859957654975872269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43887838573305103317248179 65831757859957654975872269)
          ·
            refine ⟨24686909197484120615952101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65831757859957654975872269 24686909197484120615952101)
            ·
              refine ⟨4628795474528272615491019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24686909197484120615952101 4628795474528272615491019)
              ·
                refine ⟨6943193211792408923236529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628795474528272615491019 6943193211792408923236529)
                ·
                  refine ⟨5207394908844306692427397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6943193211792408923236529 5207394908844306692427397)
                  ·
                    refine ⟨976386545408307504830137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5207394908844306692427397 976386545408307504830137)
                    ·
                      rfl

theorem cell22_2852259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 4].length) (baseStart_2852259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852259 prefixEnd_2852259 := by exact prefixLift 2852259
  have htrace : WordTrace (prefixWord ++ tailWord_2852259) baseStart_2852259 baseEnd_2852259 := by
    simpa [prefixWord, tailWord_2852259, baseEnd_2852259] using wordTrace_append hprefix tailTrace_2852259
  have hstable : (prefixWord ++ tailWord_2852259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852259).length < 2 ^ (prefixWord ++ tailWord_2852259).sum := by decide
  have hdescent : baseEnd_2852259 < baseStart_2852259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852323 : List Nat := [1, 1, 1, 6, 2, 1, 1, 5, 1, 3]
def baseStart_2852323 : Nat := 118140960795 + 2852323 * 2 ^ 59
def prefixEnd_2852323 : Nat := 4983230072969 + 3 ^ 40 * 2852323 * 2
def baseEnd_2852323 : Nat := 976408453916232671229941

theorem tailTrace_2852323 : CollatzResearch.WordTrace tailWord_2852323 prefixEnd_2852323 976408453916232671229941 := by
  unfold tailWord_2852323
  simp only [CollatzResearch.WordTrace]
  refine ⟨104032766445528383830473623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69355177630352255886982415 104032766445528383830473623)
  ·
    refine ⟨156049149668292575745710435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104032766445528383830473623 156049149668292575745710435)
    ·
      refine ⟨234073724502438863618565653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156049149668292575745710435 234073724502438863618565653)
      ·
        refine ⟨10972205836051821732120265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 234073724502438863618565653 10972205836051821732120265)
        ·
          refine ⟨8229154377038866299090199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10972205836051821732120265 8229154377038866299090199)
          ·
            refine ⟨12343731565558299448635299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8229154377038866299090199 12343731565558299448635299)
            ·
              refine ⟨18515597348337449172952949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12343731565558299448635299 18515597348337449172952949)
              ·
                refine ⟨1735837251406635859964339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18515597348337449172952949 1735837251406635859964339)
                ·
                  refine ⟨2603755877109953789946509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735837251406635859964339 2603755877109953789946509)
                  ·
                    refine ⟨976408453916232671229941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2603755877109953789946509 976408453916232671229941)
                    ·
                      rfl

theorem cell22_2852323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 1, 3].length) (baseStart_2852323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852323 prefixEnd_2852323 := by exact prefixLift 2852323
  have htrace : WordTrace (prefixWord ++ tailWord_2852323) baseStart_2852323 baseEnd_2852323 := by
    simpa [prefixWord, tailWord_2852323, baseEnd_2852323] using wordTrace_append hprefix tailTrace_2852323
  have hstable : (prefixWord ++ tailWord_2852323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852323).length < 2 ^ (prefixWord ++ tailWord_2852323).sum := by decide
  have hdescent : baseEnd_2852323 < baseStart_2852323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852334 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_2852334 : Nat := 118140960795 + 2852334 * 2 ^ 59
def prefixEnd_2852334 : Nat := 4983230072969 + 3 ^ 40 * 2852334 * 2
def baseEnd_2852334 : Nat := 976412219441032309204907

theorem tailTrace_2852334 : CollatzResearch.WordTrace tailWord_2852334 prefixEnd_2852334 976412219441032309204907 := by
  unfold tailWord_2852334
  simp only [CollatzResearch.WordTrace]
  refine ⟨13004145956061066588640507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69355445098992355139416037 13004145956061066588640507)
  ·
    refine ⟨19506218934091599882960761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13004145956061066588640507 19506218934091599882960761)
    ·
      refine ⟨14629664200568699912220571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19506218934091599882960761 14629664200568699912220571)
      ·
        refine ⟨21944496300853049868330857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14629664200568699912220571 21944496300853049868330857)
        ·
          refine ⟨16458372225639787401248143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21944496300853049868330857 16458372225639787401248143)
          ·
            refine ⟨24687558338459681101872215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16458372225639787401248143 24687558338459681101872215)
            ·
              refine ⟨37031337507689521652808323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24687558338459681101872215 37031337507689521652808323)
              ·
                refine ⟨55547006261534282479212485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37031337507689521652808323 55547006261534282479212485)
                ·
                  refine ⟨10415063674037677964852341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55547006261534282479212485 10415063674037677964852341)
                  ·
                    refine ⟨976412219441032309204907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10415063674037677964852341 976412219441032309204907)
                    ·
                      rfl

theorem cell22_2852334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_2852334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852334 prefixEnd_2852334 := by exact prefixLift 2852334
  have htrace : WordTrace (prefixWord ++ tailWord_2852334) baseStart_2852334 baseEnd_2852334 := by
    simpa [prefixWord, tailWord_2852334, baseEnd_2852334] using wordTrace_append hprefix tailTrace_2852334
  have hstable : (prefixWord ++ tailWord_2852334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852334).length < 2 ^ (prefixWord ++ tailWord_2852334).sum := by decide
  have hdescent : baseEnd_2852334 < baseStart_2852334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852336 : List Nat := [2, 1, 1, 1, 3, 6, 1, 2, 5]
def baseStart_2852336 : Nat := 118140960795 + 2852336 * 2 ^ 59
def prefixEnd_2852336 : Nat := 4983230072969 + 3 ^ 40 * 2852336 * 2
def baseEnd_2852336 : Nat := 325470968027301656884967

theorem tailTrace_2852336 : CollatzResearch.WordTrace tailWord_2852336 prefixEnd_2852336 325470968027301656884967 := by
  unfold tailWord_2852336
  simp only [CollatzResearch.WordTrace]
  refine ⟨52016620297240643525348431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69355493729654191367131241 52016620297240643525348431)
  ·
    refine ⟨78024930445860965288022647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52016620297240643525348431 78024930445860965288022647)
    ·
      refine ⟨117037395668791447932033971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78024930445860965288022647 117037395668791447932033971)
      ·
        refine ⟨175556093503187171898050957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117037395668791447932033971 175556093503187171898050957)
        ·
          refine ⟨65833535063695189461769109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175556093503187171898050957 65833535063695189461769109)
          ·
            refine ⟨3085946956110712006020427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65833535063695189461769109 3085946956110712006020427)
            ·
              refine ⟨4628920434166068009030641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085946956110712006020427 4628920434166068009030641)
              ·
                refine ⟨3471690325624551006772981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4628920434166068009030641 3471690325624551006772981)
                ·
                  refine ⟨325470968027301656884967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3471690325624551006772981 325470968027301656884967)
                  ·
                    rfl

theorem cell22_2852336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 5].length) (baseStart_2852336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852336 prefixEnd_2852336 := by exact prefixLift 2852336
  have htrace : WordTrace (prefixWord ++ tailWord_2852336) baseStart_2852336 baseEnd_2852336 := by
    simpa [prefixWord, tailWord_2852336, baseEnd_2852336] using wordTrace_append hprefix tailTrace_2852336
  have hstable : (prefixWord ++ tailWord_2852336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852336).length < 2 ^ (prefixWord ++ tailWord_2852336).sum := by decide
  have hdescent : baseEnd_2852336 < baseStart_2852336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852347 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 10]
def baseStart_2852347 : Nat := 118140960795 + 2852347 * 2 ^ 59
def prefixEnd_2852347 : Nat := 4983230072969 + 3 ^ 40 * 2852347 * 2
def baseEnd_2852347 : Nat := 325472223202234869543289

theorem tailTrace_2852347 : CollatzResearch.WordTrace tailWord_2852347 prefixEnd_2852347 325472223202234869543289 := by
  unfold tailWord_2852347
  simp only [CollatzResearch.WordTrace]
  refine ⟨104033641797441435929347295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69355761198294290619564863 104033641797441435929347295)
  ·
    refine ⟨156050462696162153894020943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104033641797441435929347295 156050462696162153894020943)
    ·
      refine ⟨234075694044243230841031415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156050462696162153894020943 234075694044243230841031415)
      ·
        refine ⟨351113541066364846261547123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234075694044243230841031415 351113541066364846261547123)
        ·
          refine ⟨526670311599547269392320685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351113541066364846261547123 526670311599547269392320685)
          ·
            refine ⟨197501366849830226022120257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 526670311599547269392320685 197501366849830226022120257)
            ·
              refine ⟨148126025137372669516590193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197501366849830226022120257 148126025137372669516590193)
              ·
                refine ⟨111094518853029502137442645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148126025137372669516590193 111094518853029502137442645)
                ·
                  refine ⟨325472223202234869543289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 111094518853029502137442645 325472223202234869543289)
                  ·
                    rfl

theorem cell22_2852347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 10].length) (baseStart_2852347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852347 prefixEnd_2852347 := by exact prefixLift 2852347
  have htrace : WordTrace (prefixWord ++ tailWord_2852347) baseStart_2852347 baseEnd_2852347 := by
    simpa [prefixWord, tailWord_2852347, baseEnd_2852347] using wordTrace_append hprefix tailTrace_2852347
  have hstable : (prefixWord ++ tailWord_2852347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852347).length < 2 ^ (prefixWord ++ tailWord_2852347).sum := by decide
  have hdescent : baseEnd_2852347 < baseStart_2852347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852353 : List Nat := [1, 2, 4, 1, 4, 1, 3, 1, 5]
def baseStart_2852353 : Nat := 118140960795 + 2852353 * 2 ^ 59
def prefixEnd_2852353 : Nat := 4983230072969 + 3 ^ 40 * 2852353 * 2
def baseEnd_2852353 : Nat := 325472907843107530993283

theorem tailTrace_2852353 : CollatzResearch.WordTrace tailWord_2852353 prefixEnd_2852353 325472907843107530993283 := by
  unfold tailWord_2852353
  simp only [CollatzResearch.WordTrace]
  refine ⟨104033860635419698954065713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69355907090279799302710475 104033860635419698954065713)
  ·
    refine ⟨78025395476564774215549285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104033860635419698954065713 78025395476564774215549285)
    ·
      refine ⟨14629761651855895165415491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78025395476564774215549285 14629761651855895165415491)
      ·
        refine ⟨21944642477783842748123237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14629761651855895165415491 21944642477783842748123237)
        ·
          refine ⟨4114620464584470515273107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21944642477783842748123237 4114620464584470515273107)
          ·
            refine ⟨6171930696876705772909661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114620464584470515273107 6171930696876705772909661)
            ·
              refine ⟨2314474011328764664841123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6171930696876705772909661 2314474011328764664841123)
              ·
                refine ⟨3471711016993146997261685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314474011328764664841123 3471711016993146997261685)
                ·
                  refine ⟨325472907843107530993283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3471711016993146997261685 325472907843107530993283)
                  ·
                    rfl

theorem cell22_2852353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 5].length) (baseStart_2852353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852353 prefixEnd_2852353 := by exact prefixLift 2852353
  have htrace : WordTrace (prefixWord ++ tailWord_2852353) baseStart_2852353 baseEnd_2852353 := by
    simpa [prefixWord, tailWord_2852353, baseEnd_2852353] using wordTrace_append hprefix tailTrace_2852353
  have hstable : (prefixWord ++ tailWord_2852353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852353).length < 2 ^ (prefixWord ++ tailWord_2852353).sum := by decide
  have hdescent : baseEnd_2852353 < baseStart_2852353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852398 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_2852398 : Nat := 118140960795 + 2852398 * 2 ^ 59
def prefixEnd_2852398 : Nat := 4983230072969 + 3 ^ 40 * 2852398 * 2
def baseEnd_2852398 : Nat := 325478042649652491868237

theorem tailTrace_2852398 : CollatzResearch.WordTrace tailWord_2852398 prefixEnd_2852398 325478042649652491868237 := by
  unfold tailWord_2852398
  simp only [CollatzResearch.WordTrace]
  refine ⟨13004437740032083954931731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69357001280171114426302565 13004437740032083954931731)
  ·
    refine ⟨19506656610048125932397597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13004437740032083954931731 19506656610048125932397597)
    ·
      refine ⟨7314996228768047224649099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19506656610048125932397597 7314996228768047224649099)
      ·
        refine ⟨10972494343152070836973649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7314996228768047224649099 10972494343152070836973649)
        ·
          refine ⟨8229370757364053127730237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10972494343152070836973649 8229370757364053127730237)
          ·
            refine ⟨3086014034011519922898839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8229370757364053127730237 3086014034011519922898839)
            ·
              refine ⟨4629021051017279884348259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3086014034011519922898839 4629021051017279884348259)
              ·
                refine ⟨6943531576525919826522389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4629021051017279884348259 6943531576525919826522389)
                ·
                  refine ⟨325478042649652491868237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6943531576525919826522389 325478042649652491868237)
                  ·
                    rfl

theorem cell22_2852398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_2852398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852398 prefixEnd_2852398 := by exact prefixLift 2852398
  have htrace : WordTrace (prefixWord ++ tailWord_2852398) baseStart_2852398 baseEnd_2852398 := by
    simpa [prefixWord, tailWord_2852398, baseEnd_2852398] using wordTrace_append hprefix tailTrace_2852398
  have hstable : (prefixWord ++ tailWord_2852398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852398).length < 2 ^ (prefixWord ++ tailWord_2852398).sum := by decide
  have hdescent : baseEnd_2852398 < baseStart_2852398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852409 : List Nat := [1, 2, 1, 5, 1, 2, 1, 9]
def baseStart_2852409 : Nat := 118140960795 + 2852409 * 2 ^ 59
def prefixEnd_2852409 : Nat := 4983230072969 + 3 ^ 40 * 2852409 * 2
def baseEnd_2852409 : Nat := 108493099274861901508853

theorem tailTrace_2852409 : CollatzResearch.WordTrace tailWord_2852409 prefixEnd_2852409 108493099274861901508853 := by
  unfold tailWord_2852409
  simp only [CollatzResearch.WordTrace]
  refine ⟨104035903123216820518104281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69357268748811213678736187 104035903123216820518104281)
  ·
    refine ⟨78026927342412615388578211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104035903123216820518104281 78026927342412615388578211)
    ·
      refine ⟨117040391013618923082867317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78026927342412615388578211 117040391013618923082867317)
      ·
        refine ⟨10972536657526774039018811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117040391013618923082867317 10972536657526774039018811)
        ·
          refine ⟨16458804986290161058528217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10972536657526774039018811 16458804986290161058528217)
          ·
            refine ⟨12344103739717620793896163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16458804986290161058528217 12344103739717620793896163)
            ·
              refine ⟨18516155609576431190844245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12344103739717620793896163 18516155609576431190844245)
              ·
                refine ⟨108493099274861901508853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18516155609576431190844245 108493099274861901508853)
                ·
                  rfl

theorem cell22_2852409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 9].length) (baseStart_2852409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852409 prefixEnd_2852409 := by exact prefixLift 2852409
  have htrace : WordTrace (prefixWord ++ tailWord_2852409) baseStart_2852409 baseEnd_2852409 := by
    simpa [prefixWord, tailWord_2852409, baseEnd_2852409] using wordTrace_append hprefix tailTrace_2852409
  have hstable : (prefixWord ++ tailWord_2852409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852409).length < 2 ^ (prefixWord ++ tailWord_2852409).sum := by decide
  have hdescent : baseEnd_2852409 < baseStart_2852409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852456 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 2, 6]
def baseStart_2852456 : Nat := 118140960795 + 2852456 * 2 ^ 59
def prefixEnd_2852456 : Nat := 4983230072969 + 3 ^ 40 * 2852456 * 2
def baseEnd_2852456 : Nat := 976453982534264657654533

theorem tailTrace_2852456 : CollatzResearch.WordTrace tailWord_2852456 prefixEnd_2852456 976453982534264657654533 := by
  unfold tailWord_2852456
  simp only [CollatzResearch.WordTrace]
  refine ⟨52018808677023273772532611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69358411569364365030043481 52018808677023273772532611)
  ·
    refine ⟨78028213015534910658798917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52018808677023273772532611 78028213015534910658798917)
    ·
      refine ⟨14630289940412795748524797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78028213015534910658798917 14630289940412795748524797)
      ·
        refine ⟨5486358727654798405696799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14630289940412795748524797 5486358727654798405696799)
        ·
          refine ⟨8229538091482197608545199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5486358727654798405696799 8229538091482197608545199)
          ·
            refine ⟨12344307137223296412817799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8229538091482197608545199 12344307137223296412817799)
            ·
              refine ⟨18516460705834944619226699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12344307137223296412817799 18516460705834944619226699)
              ·
                refine ⟨27774691058752416928840049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18516460705834944619226699 27774691058752416928840049)
                ·
                  refine ⟨20831018294064312696630037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27774691058752416928840049 20831018294064312696630037)
                  ·
                    refine ⟨976453982534264657654533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20831018294064312696630037 976453982534264657654533)
                    ·
                      rfl

theorem cell22_2852456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_2852456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852456 prefixEnd_2852456 := by exact prefixLift 2852456
  have htrace : WordTrace (prefixWord ++ tailWord_2852456) baseStart_2852456 baseEnd_2852456 := by
    simpa [prefixWord, tailWord_2852456, baseEnd_2852456] using wordTrace_append hprefix tailTrace_2852456
  have hstable : (prefixWord ++ tailWord_2852456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852456).length < 2 ^ (prefixWord ++ tailWord_2852456).sum := by decide
  have hdescent : baseEnd_2852456 < baseStart_2852456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852516 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 6]
def baseStart_2852516 : Nat := 118140960795 + 2852516 * 2 ^ 59
def prefixEnd_2852516 : Nat := 4983230072969 + 3 ^ 40 * 2852516 * 2
def baseEnd_2852516 : Nat := 325491507253481500384783

theorem tailTrace_2852516 : CollatzResearch.WordTrace tailWord_2852516 prefixEnd_2852516 325491507253481500384783 := by
  unfold tailWord_2852516
  simp only [CollatzResearch.WordTrace]
  refine ⟨52019902866914588896124701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69359870489219451861499601 52019902866914588896124701)
  ·
    refine ⟨19507463575092970836046763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52019902866914588896124701 19507463575092970836046763)
    ·
      refine ⟨29261195362639456254070145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19507463575092970836046763 29261195362639456254070145)
      ·
        refine ⟨21945896521979592190552609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29261195362639456254070145 21945896521979592190552609)
        ·
          refine ⟨16459422391484694142914457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21945896521979592190552609 16459422391484694142914457)
          ·
            refine ⟨12344566793613520607185843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16459422391484694142914457 12344566793613520607185843)
            ·
              refine ⟨18516850190420280910778765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12344566793613520607185843 18516850190420280910778765)
              ·
                refine ⟨6943818821407605341542037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18516850190420280910778765 6943818821407605341542037)
                ·
                  refine ⟨325491507253481500384783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6943818821407605341542037 325491507253481500384783)
                  ·
                    rfl

theorem cell22_2852516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_2852516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852516 prefixEnd_2852516 := by exact prefixLift 2852516
  have htrace : WordTrace (prefixWord ++ tailWord_2852516) baseStart_2852516 baseEnd_2852516 := by
    simpa [prefixWord, tailWord_2852516, baseEnd_2852516] using wordTrace_append hprefix tailTrace_2852516
  have hstable : (prefixWord ++ tailWord_2852516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852516).length < 2 ^ (prefixWord ++ tailWord_2852516).sum := by decide
  have hdescent : baseEnd_2852516 < baseStart_2852516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852548 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_2852548 : Nat := 118140960795 + 2852548 * 2 ^ 59
def prefixEnd_2852548 : Nat := 4983230072969 + 3 ^ 40 * 2852548 * 2
def baseEnd_2852548 : Nat := 976485476014407084354251

theorem tailTrace_2852548 : CollatzResearch.WordTrace tailWord_2852548 prefixEnd_2852548 976485476014407084354251 := by
  unfold tailWord_2852548
  simp only [CollatzResearch.WordTrace]
  refine ⟨52020486434856623628707149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69360648579808831504942865 52020486434856623628707149)
  ·
    refine ⟨19507682413071233860765181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52020486434856623628707149 19507682413071233860765181)
    ·
      refine ⟨7315380904901712697786943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19507682413071233860765181 7315380904901712697786943)
      ·
        refine ⟨10973071357352569046680415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7315380904901712697786943 10973071357352569046680415)
        ·
          refine ⟨16459607036028853570020623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10973071357352569046680415 16459607036028853570020623)
          ·
            refine ⟨24689410554043280355030935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16459607036028853570020623 24689410554043280355030935)
            ·
              refine ⟨37034115831064920532546403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24689410554043280355030935 37034115831064920532546403)
              ·
                refine ⟨55551173746597380798819605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37034115831064920532546403 55551173746597380798819605)
                ·
                  refine ⟨2603961269371752224944669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55551173746597380798819605 2603961269371752224944669)
                  ·
                    refine ⟨976485476014407084354251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2603961269371752224944669 976485476014407084354251)
                    ·
                      rfl

theorem cell22_2852548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_2852548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852548 prefixEnd_2852548 := by exact prefixLift 2852548
  have htrace : WordTrace (prefixWord ++ tailWord_2852548) baseStart_2852548 baseEnd_2852548 := by
    simpa [prefixWord, tailWord_2852548, baseEnd_2852548] using wordTrace_append hprefix tailTrace_2852548
  have hstable : (prefixWord ++ tailWord_2852548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852548).length < 2 ^ (prefixWord ++ tailWord_2852548).sum := by decide
  have hdescent : baseEnd_2852548 < baseStart_2852548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852561 : List Nat := [1, 2, 2, 1, 2, 6, 8]
def baseStart_2852561 : Nat := 118140960795 + 2852561 * 2 ^ 59
def prefixEnd_2852561 : Nat := 4983230072969 + 3 ^ 40 * 2852561 * 2
def baseEnd_2852561 : Nat := 36166293562225162362193

theorem tailTrace_2852561 : CollatzResearch.WordTrace tailWord_2852561 prefixEnd_2852561 36166293562225162362193 := by
  unfold tailWord_2852561
  simp only [CollatzResearch.WordTrace]
  refine ⟨104041447018666150477637537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69360964679110766985091691 104041447018666150477637537)
  ·
    refine ⟨78031085263999612858228153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104041447018666150477637537 78031085263999612858228153)
    ·
      refine ⟨58523313947999709643671115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78031085263999612858228153 58523313947999709643671115)
      ·
        refine ⟨87784970921999564465506673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58523313947999709643671115 87784970921999564465506673)
        ·
          refine ⟨65838728191499673349130005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87784970921999564465506673 65838728191499673349130005)
          ·
            refine ⟨3086190383976547188240469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65838728191499673349130005 3086190383976547188240469)
            ·
              refine ⟨36166293562225162362193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3086190383976547188240469 36166293562225162362193)
              ·
                rfl

theorem cell22_2852561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 8].length) (baseStart_2852561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852561 prefixEnd_2852561 := by exact prefixLift 2852561
  have htrace : WordTrace (prefixWord ++ tailWord_2852561) baseStart_2852561 baseEnd_2852561 := by
    simpa [prefixWord, tailWord_2852561, baseEnd_2852561] using wordTrace_append hprefix tailTrace_2852561
  have hstable : (prefixWord ++ tailWord_2852561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852561).length < 2 ^ (prefixWord ++ tailWord_2852561).sum := by decide
  have hdescent : baseEnd_2852561 < baseStart_2852561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852685 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2852685 : Nat := 118140960795 + 2852685 * 2 ^ 59
def prefixEnd_2852685 : Nat := 4983230072969 + 3 ^ 40 * 2852685 * 2
def baseEnd_2852685 : Nat := 325510791304728131226277

theorem tailTrace_2852685 : CollatzResearch.WordTrace tailWord_2852685 prefixEnd_2852685 325510791304728131226277 := by
  unfold tailWord_2852685
  simp only [CollatzResearch.WordTrace]
  refine ⟨104045969670216919655151509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69363979780144613103434339 104045969670216919655151509)
  ·
    refine ⟨4877154828291418108835227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104045969670216919655151509 4877154828291418108835227)
    ·
      refine ⟨7315732242437127163252841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4877154828291418108835227 7315732242437127163252841)
      ·
        refine ⟨5486799181827845372439631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7315732242437127163252841 5486799181827845372439631)
        ·
          refine ⟨8230198772741768058659447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5486799181827845372439631 8230198772741768058659447)
          ·
            refine ⟨12345298159112652087989171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8230198772741768058659447 12345298159112652087989171)
            ·
              refine ⟨18517947238668978131983757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12345298159112652087989171 18517947238668978131983757)
              ·
                refine ⟨6944230214500866799493909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18517947238668978131983757 6944230214500866799493909)
                ·
                  refine ⟨325510791304728131226277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6944230214500866799493909 325510791304728131226277)
                  ·
                    rfl

theorem cell22_2852685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2852685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852685 prefixEnd_2852685 := by exact prefixLift 2852685
  have htrace : WordTrace (prefixWord ++ tailWord_2852685) baseStart_2852685 baseEnd_2852685 := by
    simpa [prefixWord, tailWord_2852685, baseEnd_2852685] using wordTrace_append hprefix tailTrace_2852685
  have hstable : (prefixWord ++ tailWord_2852685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852685).length < 2 ^ (prefixWord ++ tailWord_2852685).sum := by decide
  have hdescent : baseEnd_2852685 < baseStart_2852685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852796 : List Nat := [2, 2, 2, 5, 1, 1, 1, 4, 1, 3]
def baseStart_2852796 : Nat := 118140960795 + 2852796 * 2 ^ 59
def prefixEnd_2852796 : Nat := 4983230072969 + 3 ^ 40 * 2852796 * 2
def baseEnd_2852796 : Nat := 976570371482617104153491

theorem tailTrace_2852796 : CollatzResearch.WordTrace tailWord_2852796 prefixEnd_2852796 976570371482617104153491 := by
  unfold tailWord_2852796
  simp only [CollatzResearch.WordTrace]
  refine ⟨52025009086407392806221121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69366678781876523741628161 52025009086407392806221121)
  ·
    refine ⟨39018756814805544604665841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52025009086407392806221121 39018756814805544604665841)
    ·
      refine ⟨29264067611104158453499381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39018756814805544604665841 29264067611104158453499381)
      ·
        refine ⟨2743506338541014855015567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29264067611104158453499381 2743506338541014855015567)
        ·
          refine ⟨4115259507811522282523351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743506338541014855015567 4115259507811522282523351)
          ·
            refine ⟨6172889261717283423785027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115259507811522282523351 6172889261717283423785027)
            ·
              refine ⟨9259333892575925135677541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6172889261717283423785027 9259333892575925135677541)
              ·
                refine ⟨1736125104857985962939539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9259333892575925135677541 1736125104857985962939539)
                ·
                  refine ⟨2604187657286978944409309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736125104857985962939539 2604187657286978944409309)
                  ·
                    refine ⟨976570371482617104153491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2604187657286978944409309 976570371482617104153491)
                    ·
                      rfl

theorem cell22_2852796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_2852796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852796 prefixEnd_2852796 := by exact prefixLift 2852796
  have htrace : WordTrace (prefixWord ++ tailWord_2852796) baseStart_2852796 baseEnd_2852796 := by
    simpa [prefixWord, tailWord_2852796, baseEnd_2852796] using wordTrace_append hprefix tailTrace_2852796
  have hstable : (prefixWord ++ tailWord_2852796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852796).length < 2 ^ (prefixWord ++ tailWord_2852796).sum := by decide
  have hdescent : baseEnd_2852796 < baseStart_2852796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852820 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 6]
def baseStart_2852820 : Nat := 118140960795 + 2852820 * 2 ^ 59
def prefixEnd_2852820 : Nat := 4983230072969 + 3 ^ 40 * 2852820 * 2
def baseEnd_2852820 : Nat := 325526195724363013851139

theorem tailTrace_2852820 : CollatzResearch.WordTrace tailWord_2852820 prefixEnd_2852820 325526195724363013851139 := by
  unfold tailWord_2852820
  simp only [CollatzResearch.WordTrace]
  refine ⟨52025446762363918855657957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69367262349818558474210609 52025446762363918855657957)
  ·
    refine ⟨9754771267943234785435867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52025446762363918855657957 9754771267943234785435867)
    ·
      refine ⟨14632156901914852178153801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9754771267943234785435867 14632156901914852178153801)
      ·
        refine ⟨10974117676436139133615351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14632156901914852178153801 10974117676436139133615351)
        ·
          refine ⟨16461176514654208700423027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10974117676436139133615351 16461176514654208700423027)
          ·
            refine ⟨24691764771981313050634541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16461176514654208700423027 24691764771981313050634541)
            ·
              refine ⟨9259411789492992393987953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24691764771981313050634541 9259411789492992393987953)
              ·
                refine ⟨6944558842119744295490965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9259411789492992393987953 6944558842119744295490965)
                ·
                  refine ⟨325526195724363013851139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6944558842119744295490965 325526195724363013851139)
                  ·
                    rfl

theorem cell22_2852820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_2852820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852820 prefixEnd_2852820 := by exact prefixLift 2852820
  have htrace : WordTrace (prefixWord ++ tailWord_2852820) baseStart_2852820 baseEnd_2852820 := by
    simpa [prefixWord, tailWord_2852820, baseEnd_2852820] using wordTrace_append hprefix tailTrace_2852820
  have hstable : (prefixWord ++ tailWord_2852820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852820).length < 2 ^ (prefixWord ++ tailWord_2852820).sum := by decide
  have hdescent : baseEnd_2852820 < baseStart_2852820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852835 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 1, 5]
def baseStart_2852835 : Nat := 118140960795 + 2852835 * 2 ^ 59
def prefixEnd_2852835 : Nat := 4983230072969 + 3 ^ 40 * 2852835 * 2
def baseEnd_2852835 : Nat := 976583721979634002428371

theorem tailTrace_2852835 : CollatzResearch.WordTrace tailWord_2852835 prefixEnd_2852835 976583721979634002428371 := by
  unfold tailWord_2852835
  simp only [CollatzResearch.WordTrace]
  refine ⟨104051440619673495273111959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69367627079782330182074639 104051440619673495273111959)
  ·
    refine ⟨156077160929510242909667939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104051440619673495273111959 156077160929510242909667939)
    ·
      refine ⟨234115741394265364364501909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156077160929510242909667939 234115741394265364364501909)
      ·
        refine ⟨10974175377856188954586027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 234115741394265364364501909 10974175377856188954586027)
        ·
          refine ⟨16461263066784283431879041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10974175377856188954586027 16461263066784283431879041)
          ·
            refine ⟨12345947300088212573909281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16461263066784283431879041 12345947300088212573909281)
            ·
              refine ⟨9259460475066159430431961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12345947300088212573909281 9259460475066159430431961)
              ·
                refine ⟨6944595356299619572823971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9259460475066159430431961 6944595356299619572823971)
                ·
                  refine ⟨10416893034449429359235957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6944595356299619572823971 10416893034449429359235957)
                  ·
                    refine ⟨976583721979634002428371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10416893034449429359235957 976583721979634002428371)
                    ·
                      rfl

theorem cell22_2852835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 5].length) (baseStart_2852835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852835 prefixEnd_2852835 := by exact prefixLift 2852835
  have htrace : WordTrace (prefixWord ++ tailWord_2852835) baseStart_2852835 baseEnd_2852835 := by
    simpa [prefixWord, tailWord_2852835, baseEnd_2852835] using wordTrace_append hprefix tailTrace_2852835
  have hstable : (prefixWord ++ tailWord_2852835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852835).length < 2 ^ (prefixWord ++ tailWord_2852835).sum := by decide
  have hdescent : baseEnd_2852835 < baseStart_2852835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852869 : List Nat := [1, 3, 1, 1, 2, 5, 3, 1, 2, 3]
def baseStart_2852869 : Nat := 118140960795 + 2852869 * 2 ^ 59
def prefixEnd_2852869 : Nat := 4983230072969 + 3 ^ 40 * 2852869 * 2
def baseEnd_2852869 : Nat := 976595360874469247078267

theorem tailTrace_2852869 : CollatzResearch.WordTrace tailWord_2852869 prefixEnd_2852869 976595360874469247078267 := by
  unfold tailWord_2852869
  simp only [CollatzResearch.WordTrace]
  refine ⟨104052680701550319079849661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69368453801033546053233107 104052680701550319079849661)
  ·
    refine ⟨39019755263081369654943623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104052680701550319079849661 39019755263081369654943623)
    ·
      refine ⟨58529632894622054482415435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39019755263081369654943623 58529632894622054482415435)
      ·
        refine ⟨87794449341933081723623153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58529632894622054482415435 87794449341933081723623153)
        ·
          refine ⟨65845837006449811292717365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87794449341933081723623153 65845837006449811292717365)
          ·
            refine ⟨6173047219354669808692253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65845837006449811292717365 6173047219354669808692253)
            ·
              refine ⟨2314892707258001178259595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6173047219354669808692253 2314892707258001178259595)
              ·
                refine ⟨3472339060887001767389393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314892707258001178259595 3472339060887001767389393)
                ·
                  refine ⟨2604254295665251325542045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3472339060887001767389393 2604254295665251325542045)
                  ·
                    refine ⟨976595360874469247078267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2604254295665251325542045 976595360874469247078267)
                    ·
                      rfl

theorem cell22_2852869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_2852869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852869 prefixEnd_2852869 := by exact prefixLift 2852869
  have htrace : WordTrace (prefixWord ++ tailWord_2852869) baseStart_2852869 baseEnd_2852869 := by
    simpa [prefixWord, tailWord_2852869, baseEnd_2852869] using wordTrace_append hprefix tailTrace_2852869
  have hstable : (prefixWord ++ tailWord_2852869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852869).length < 2 ^ (prefixWord ++ tailWord_2852869).sum := by decide
  have hdescent : baseEnd_2852869 < baseStart_2852869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852914 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_2852914 : Nat := 118140960795 + 2852914 * 2 ^ 59
def prefixEnd_2852914 : Nat := 4983230072969 + 3 ^ 40 * 2852914 * 2
def baseEnd_2852914 : Nat := 976610765294104129703129

theorem tailTrace_2852914 : CollatzResearch.WordTrace tailWord_2852914 prefixEnd_2852914 976610765294104129703129 := by
  unfold tailWord_2852914
  simp only [CollatzResearch.WordTrace]
  refine ⟨26013580496596822941309449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69369547990924861176825197 26013580496596822941309449)
  ·
    refine ⟨19510185372447617205982087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26013580496596822941309449 19510185372447617205982087)
    ·
      refine ⟨29265278058671425808973131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19510185372447617205982087 29265278058671425808973131)
      ·
        refine ⟨43897917088007138713459697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29265278058671425808973131 43897917088007138713459697)
        ·
          refine ⟨32923437816005354035094773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43897917088007138713459697 32923437816005354035094773)
          ·
            refine ⟨3086572295250501940790135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32923437816005354035094773 3086572295250501940790135)
            ·
              refine ⟨4629858442875752911185203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3086572295250501940790135 4629858442875752911185203)
              ·
                refine ⟨6944787664313629366777805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4629858442875752911185203 6944787664313629366777805)
                ·
                  refine ⟨2604295374117611012541677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6944787664313629366777805 2604295374117611012541677)
                  ·
                    refine ⟨976610765294104129703129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2604295374117611012541677 976610765294104129703129)
                    ·
                      rfl

theorem cell22_2852914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_2852914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852914 prefixEnd_2852914 := by exact prefixLift 2852914
  have htrace : WordTrace (prefixWord ++ tailWord_2852914) baseStart_2852914 baseEnd_2852914 := by
    simpa [prefixWord, tailWord_2852914, baseEnd_2852914] using wordTrace_append hprefix tailTrace_2852914
  have hstable : (prefixWord ++ tailWord_2852914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852914).length < 2 ^ (prefixWord ++ tailWord_2852914).sum := by decide
  have hdescent : baseEnd_2852914 < baseStart_2852914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852925 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_2852925 : Nat := 118140960795 + 2852925 * 2 ^ 59
def prefixEnd_2852925 : Nat := 4983230072969 + 3 ^ 40 * 2852925 * 2
def baseEnd_2852925 : Nat := 976614530818903767678095

theorem tailTrace_2852925 : CollatzResearch.WordTrace tailWord_2852925 prefixEnd_2852925 976614530818903767678095 := by
  unfold tailWord_2852925
  simp only [CollatzResearch.WordTrace]
  refine ⟨104054723189347440643888229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69369815459564960429258819 104054723189347440643888229)
  ·
    refine ⟨19510260598002645120729043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104054723189347440643888229 19510260598002645120729043)
    ·
      refine ⟨29265390897003967681093565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19510260598002645120729043 29265390897003967681093565)
      ·
        refine ⟨10974521586376487880410087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29265390897003967681093565 10974521586376487880410087)
        ·
          refine ⟨16461782379564731820615131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10974521586376487880410087 16461782379564731820615131)
          ·
            refine ⟨24692673569347097730922697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16461782379564731820615131 24692673569347097730922697)
            ·
              refine ⟨18519505177010323298192023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24692673569347097730922697 18519505177010323298192023)
              ·
                refine ⟨27779257765515484947288035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18519505177010323298192023 27779257765515484947288035)
                ·
                  refine ⟨41668886648273227420932053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27779257765515484947288035 41668886648273227420932053)
                  ·
                    refine ⟨976614530818903767678095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41668886648273227420932053 976614530818903767678095)
                    ·
                      rfl

theorem cell22_2852925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_2852925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852925 prefixEnd_2852925 := by exact prefixLift 2852925
  have htrace : WordTrace (prefixWord ++ tailWord_2852925) baseStart_2852925 baseEnd_2852925 := by
    simpa [prefixWord, tailWord_2852925, baseEnd_2852925] using wordTrace_append hprefix tailTrace_2852925
  have hstable : (prefixWord ++ tailWord_2852925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852925).length < 2 ^ (prefixWord ++ tailWord_2852925).sum := by decide
  have hdescent : baseEnd_2852925 < baseStart_2852925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852927 : List Nat := [1, 1, 2, 2, 3, 1, 6, 1, 5]
def baseStart_2852927 : Nat := 118140960795 + 2852927 * 2 ^ 59
def prefixEnd_2852927 : Nat := 4983230072969 + 3 ^ 40 * 2852927 * 2
def baseEnd_2852927 : Nat := 325538405153258809709363

theorem tailTrace_2852927 : CollatzResearch.WordTrace tailWord_2852927 prefixEnd_2852927 325538405153258809709363 := by
  unfold tailWord_2852927
  simp only [CollatzResearch.WordTrace]
  refine ⟨104054796135340194985461035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69369864090226796656974023 104054796135340194985461035)
  ·
    refine ⟨156082194203010292478191553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104054796135340194985461035 156082194203010292478191553)
    ·
      refine ⟨117061645652257719358643665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156082194203010292478191553 117061645652257719358643665)
      ·
        refine ⟨87796234239193289518982749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117061645652257719358643665 87796234239193289518982749)
        ·
          refine ⟨32923587839697483569618531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87796234239193289518982749 32923587839697483569618531)
          ·
            refine ⟨49385381759546225354427797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32923587839697483569618531 49385381759546225354427797)
            ·
              refine ⟨2314939769978729313488803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49385381759546225354427797 2314939769978729313488803)
              ·
                refine ⟨3472409654968093970233205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314939769978729313488803 3472409654968093970233205)
                ·
                  refine ⟨325538405153258809709363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3472409654968093970233205 325538405153258809709363)
                  ·
                    rfl

theorem cell22_2852927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 5].length) (baseStart_2852927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2852927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2852927 prefixEnd_2852927 := by exact prefixLift 2852927
  have htrace : WordTrace (prefixWord ++ tailWord_2852927) baseStart_2852927 baseEnd_2852927 := by
    simpa [prefixWord, tailWord_2852927, baseEnd_2852927] using wordTrace_append hprefix tailTrace_2852927
  have hstable : (prefixWord ++ tailWord_2852927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852927).length < 2 ^ (prefixWord ++ tailWord_2852927).sum := by decide
  have hdescent : baseEnd_2852927 < baseStart_2852927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853002 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_2853002 : Nat := 118140960795 + 2853002 * 2 ^ 59
def prefixEnd_2853002 : Nat := 4983230072969 + 3 ^ 40 * 2853002 * 2
def baseEnd_2853002 : Nat := 976640889492501233502859

theorem tailTrace_2853002 : CollatzResearch.WordTrace tailWord_2853002 prefixEnd_2853002 976640889492501233502859 := by
  unfold tailWord_2853002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26014382902517120698610315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69371687740045655196294173 26014382902517120698610315)
  ·
    refine ⟨39021574353775681047915473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26014382902517120698610315 39021574353775681047915473)
    ·
      refine ⟨29266180765331760785936605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39021574353775681047915473 29266180765331760785936605)
      ·
        refine ⟨10974817786999410294726227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29266180765331760785936605 10974817786999410294726227)
        ·
          refine ⟨16462226680499115442089341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10974817786999410294726227 16462226680499115442089341)
          ·
            refine ⟨6173335005187168290783503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16462226680499115442089341 6173335005187168290783503)
            ·
              refine ⟨9260002507780752436175255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6173335005187168290783503 9260002507780752436175255)
              ·
                refine ⟨13890003761671128654262883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9260002507780752436175255 13890003761671128654262883)
                ·
                  refine ⟨20835005642506692981394325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13890003761671128654262883 20835005642506692981394325)
                  ·
                    refine ⟨976640889492501233502859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20835005642506692981394325 976640889492501233502859)
                    ·
                      rfl

theorem cell22_2853002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_2853002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853002 prefixEnd_2853002 := by exact prefixLift 2853002
  have htrace : WordTrace (prefixWord ++ tailWord_2853002) baseStart_2853002 baseEnd_2853002 := by
    simpa [prefixWord, tailWord_2853002, baseEnd_2853002] using wordTrace_append hprefix tailTrace_2853002
  have hstable : (prefixWord ++ tailWord_2853002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853002).length < 2 ^ (prefixWord ++ tailWord_2853002).sum := by decide
  have hdescent : baseEnd_2853002 < baseStart_2853002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853006 : List Nat := [4, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_2853006 : Nat := 118140960795 + 2853006 * 2 ^ 59
def prefixEnd_2853006 : Nat := 4983230072969 + 3 ^ 40 * 2853006 * 2
def baseEnd_2853006 : Nat := 325547419591415518800949

theorem tailTrace_2853006 : CollatzResearch.WordTrace tailWord_2853006 prefixEnd_2853006 325547419591415518800949 := by
  unfold tailWord_2853006
  simp only [CollatzResearch.WordTrace]
  refine ⟨13007209687756748934698359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69371785001369327651724581 13007209687756748934698359)
  ·
    refine ⟨19510814531635123402047539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13007209687756748934698359 19510814531635123402047539)
    ·
      refine ⟨29266221797452685103071309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19510814531635123402047539 29266221797452685103071309)
      ·
        refine ⟨10974833174044756913651741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29266221797452685103071309 10974833174044756913651741)
        ·
          refine ⟨4115562440266783842619403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10974833174044756913651741 4115562440266783842619403)
          ·
            refine ⟨6173343660400175763929105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115562440266783842619403 6173343660400175763929105)
            ·
              refine ⟨4630007745300131822946829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6173343660400175763929105 4630007745300131822946829)
              ·
                refine ⟨1736252904487549433605061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4630007745300131822946829 1736252904487549433605061)
                ·
                  refine ⟨325547419591415518800949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1736252904487549433605061 325547419591415518800949)
                  ·
                    rfl

theorem cell22_2853006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_2853006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853006 prefixEnd_2853006 := by exact prefixLift 2853006
  have htrace : WordTrace (prefixWord ++ tailWord_2853006) baseStart_2853006 baseEnd_2853006 := by
    simpa [prefixWord, tailWord_2853006, baseEnd_2853006] using wordTrace_append hprefix tailTrace_2853006
  have hstable : (prefixWord ++ tailWord_2853006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853006).length < 2 ^ (prefixWord ++ tailWord_2853006).sum := by decide
  have hdescent : baseEnd_2853006 < baseStart_2853006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853021 : List Nat := [1, 4, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2853021 : Nat := 118140960795 + 2853021 * 2 ^ 59
def prefixEnd_2853021 : Nat := 4983230072969 + 3 ^ 40 * 2853021 * 2
def baseEnd_2853021 : Nat := 976647393580791517277801

theorem tailTrace_2853021 : CollatzResearch.WordTrace tailWord_2853021 prefixEnd_2853021 976647393580791517277801 := by
  unfold tailWord_2853021
  simp only [CollatzResearch.WordTrace]
  refine ⟨104058224596999649039382917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69372149731333099359588611 104058224596999649039382917)
  ·
    refine ⟨19510917111937434194884297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104058224596999649039382917 19510917111937434194884297)
    ·
      refine ⟨14633187833953075646163223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19510917111937434194884297 14633187833953075646163223)
      ·
        refine ⟨21949781750929613469244835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14633187833953075646163223 21949781750929613469244835)
        ·
          refine ⟨32924672626394420203867253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21949781750929613469244835 32924672626394420203867253)
          ·
            refine ⟨3086688058724476894112555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32924672626394420203867253 3086688058724476894112555)
            ·
              refine ⟨4630032088086715341168833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3086688058724476894112555 4630032088086715341168833)
              ·
                refine ⟨3472524066065036505876625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4630032088086715341168833 3472524066065036505876625)
                ·
                  refine ⟨2604393049548777379407469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3472524066065036505876625 2604393049548777379407469)
                  ·
                    refine ⟨976647393580791517277801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2604393049548777379407469 976647393580791517277801)
                    ·
                      rfl

theorem cell22_2853021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2853021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853021 prefixEnd_2853021 := by exact prefixLift 2853021
  have htrace : WordTrace (prefixWord ++ tailWord_2853021) baseStart_2853021 baseEnd_2853021 := by
    simpa [prefixWord, tailWord_2853021, baseEnd_2853021] using wordTrace_append hprefix tailTrace_2853021
  have hstable : (prefixWord ++ tailWord_2853021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853021).length < 2 ^ (prefixWord ++ tailWord_2853021).sum := by decide
  have hdescent : baseEnd_2853021 < baseStart_2853021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853038 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2853038 : Nat := 118140960795 + 2853038 * 2 ^ 59
def prefixEnd_2853038 : Nat := 4983230072969 + 3 ^ 40 * 2853038 * 2
def baseEnd_2853038 : Nat := 976653213028209139602749

theorem tailTrace_2853038 : CollatzResearch.WordTrace tailWord_2853038 prefixEnd_2853038 976653213028209139602749 := by
  unfold tailWord_2853038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13007355579742257617843971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69372563091958707295167845 13007355579742257617843971)
  ·
    refine ⟨19511033369613386426765957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13007355579742257617843971 19511033369613386426765957)
    ·
      refine ⟨3658318756802509955018617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19511033369613386426765957 3658318756802509955018617)
      ·
        refine ⟨2743739067601882466263963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3658318756802509955018617 2743739067601882466263963)
        ·
          refine ⟨4115608601402823699395945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743739067601882466263963 4115608601402823699395945)
          ·
            refine ⟨3086706451052117774546959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4115608601402823699395945 3086706451052117774546959)
            ·
              refine ⟨4630059676578176661820439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3086706451052117774546959 4630059676578176661820439)
              ·
                refine ⟨6945089514867264992730659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4630059676578176661820439 6945089514867264992730659)
                ·
                  refine ⟨10417634272300897489095989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6945089514867264992730659 10417634272300897489095989)
                  ·
                    refine ⟨976653213028209139602749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10417634272300897489095989 976653213028209139602749)
                    ·
                      rfl

theorem cell22_2853038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2853038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853038 prefixEnd_2853038 := by exact prefixLift 2853038
  have htrace : WordTrace (prefixWord ++ tailWord_2853038) baseStart_2853038 baseEnd_2853038 := by
    simpa [prefixWord, tailWord_2853038, baseEnd_2853038] using wordTrace_append hprefix tailTrace_2853038
  have hstable : (prefixWord ++ tailWord_2853038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853038).length < 2 ^ (prefixWord ++ tailWord_2853038).sum := by decide
  have hdescent : baseEnd_2853038 < baseStart_2853038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853092 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_2853092 : Nat := 118140960795 + 2853092 * 2 ^ 59
def prefixEnd_2853092 : Nat := 4983230072969 + 3 ^ 40 * 2853092 * 2
def baseEnd_2853092 : Nat := 976671698331770998752583

theorem tailTrace_2853092 : CollatzResearch.WordTrace tailWord_2853092 prefixEnd_2853092 976671698331770998752583 := by
  unfold tailWord_2853092
  simp only [CollatzResearch.WordTrace]
  refine ⟨52030407089871214082608765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69373876119828285443478353 52030407089871214082608765)
  ·
    refine ⟨19511402658701705280978287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52030407089871214082608765 19511402658701705280978287)
    ·
      refine ⟨29267103988052557921467431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19511402658701705280978287 29267103988052557921467431)
      ·
        refine ⟨43900655982078836882201147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29267103988052557921467431 43900655982078836882201147)
        ·
          refine ⟨65850983973118255323301721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43900655982078836882201147 65850983973118255323301721)
          ·
            refine ⟨49388237979838691492476291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65850983973118255323301721 49388237979838691492476291)
            ·
              refine ⟨74082356969758037238714437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49388237979838691492476291 74082356969758037238714437)
              ·
                refine ⟨13890441931829631982258957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74082356969758037238714437 13890441931829631982258957)
                ·
                  refine ⟨5208915724436111993347109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13890441931829631982258957 5208915724436111993347109)
                  ·
                    refine ⟨976671698331770998752583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5208915724436111993347109 976671698331770998752583)
                    ·
                      rfl

theorem cell22_2853092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_2853092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853092 prefixEnd_2853092 := by exact prefixLift 2853092
  have htrace : WordTrace (prefixWord ++ tailWord_2853092) baseStart_2853092 baseEnd_2853092 := by
    simpa [prefixWord, tailWord_2853092, baseEnd_2853092] using wordTrace_append hprefix tailTrace_2853092
  have hstable : (prefixWord ++ tailWord_2853092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853092).length < 2 ^ (prefixWord ++ tailWord_2853092).sum := by decide
  have hdescent : baseEnd_2853092 < baseStart_2853092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853096 : List Nat := [2, 1, 4, 1, 2, 4, 2, 1, 5]
def baseStart_2853096 : Nat := 118140960795 + 2853096 * 2 ^ 59
def prefixEnd_2853096 : Nat := 4983230072969 + 3 ^ 40 * 2853096 * 2
def baseEnd_2853096 : Nat := 325557689204505440550857

theorem tailTrace_2853096 : CollatzResearch.WordTrace tailWord_2853096 prefixEnd_2853096 325557689204505440550857 := by
  unfold tailWord_2853096
  simp only [CollatzResearch.WordTrace]
  refine ⟨52030480035863968424181571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69373973381151957898908761 52030480035863968424181571)
  ·
    refine ⟨78045720053795952636272357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52030480035863968424181571 78045720053795952636272357)
    ·
      refine ⟨14633572510086741119301067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78045720053795952636272357 14633572510086741119301067)
      ·
        refine ⟨21950358765130111678951601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14633572510086741119301067 21950358765130111678951601)
        ·
          refine ⟨16462769073847583759213701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21950358765130111678951601 16462769073847583759213701)
          ·
            refine ⟨3086769201346421954852569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16462769073847583759213701 3086769201346421954852569)
            ·
              refine ⟨2315076901009816466139427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3086769201346421954852569 2315076901009816466139427)
              ·
                refine ⟨3472615351514724699209141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2315076901009816466139427 3472615351514724699209141)
                ·
                  refine ⟨325557689204505440550857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3472615351514724699209141 325557689204505440550857)
                  ·
                    rfl

theorem cell22_2853096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 5].length) (baseStart_2853096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853096 prefixEnd_2853096 := by exact prefixLift 2853096
  have htrace : WordTrace (prefixWord ++ tailWord_2853096) baseStart_2853096 baseEnd_2853096 := by
    simpa [prefixWord, tailWord_2853096, baseEnd_2853096] using wordTrace_append hprefix tailTrace_2853096
  have hstable : (prefixWord ++ tailWord_2853096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853096).length < 2 ^ (prefixWord ++ tailWord_2853096).sum := by decide
  have hdescent : baseEnd_2853096 < baseStart_2853096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853141 : List Nat := [1, 3, 2, 1, 2, 1, 6, 2, 4]
def baseStart_2853141 : Nat := 118140960795 + 2853141 * 2 ^ 59
def prefixEnd_2853141 : Nat := 4983230072969 + 3 ^ 40 * 2853141 * 2
def baseEnd_2853141 : Nat := 325562824011050401425811

theorem tailTrace_2853141 : CollatzResearch.WordTrace tailWord_2853141 prefixEnd_2853141 325562824011050401425811 := by
  unfold tailWord_2853141
  simp only [CollatzResearch.WordTrace]
  refine ⟨104062601356564909533751277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69375067571043273022500851 104062601356564909533751277)
  ·
    refine ⟨39023475508711841075156729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104062601356564909533751277 39023475508711841075156729)
    ·
      refine ⟨29267606631533880806367547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39023475508711841075156729 29267606631533880806367547)
      ·
        refine ⟨43901409947300821209551321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29267606631533880806367547 43901409947300821209551321)
        ·
          refine ⟨32926057460475615907163491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43901409947300821209551321 32926057460475615907163491)
          ·
            refine ⟨49389086190713423860745237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32926057460475615907163491 49389086190713423860745237)
            ·
              refine ⟨2315113415189691743472433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49389086190713423860745237 2315113415189691743472433)
              ·
                refine ⟨1736335061392268807604325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2315113415189691743472433 1736335061392268807604325)
                ·
                  refine ⟨325562824011050401425811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1736335061392268807604325 325562824011050401425811)
                  ·
                    rfl

theorem cell22_2853141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_2853141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853141 prefixEnd_2853141 := by exact prefixLift 2853141
  have htrace : WordTrace (prefixWord ++ tailWord_2853141) baseStart_2853141 baseEnd_2853141 := by
    simpa [prefixWord, tailWord_2853141, baseEnd_2853141] using wordTrace_append hprefix tailTrace_2853141
  have hstable : (prefixWord ++ tailWord_2853141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853141).length < 2 ^ (prefixWord ++ tailWord_2853141).sum := by decide
  have hdescent : baseEnd_2853141 < baseStart_2853141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853156 : List Nat := [2, 3, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_2853156 : Nat := 118140960795 + 2853156 * 2 ^ 59
def prefixEnd_2853156 : Nat := 4983230072969 + 3 ^ 40 * 2853156 * 2
def baseEnd_2853156 : Nat := 976693606839696165152387

theorem tailTrace_2853156 : CollatzResearch.WordTrace tailWord_2853156 prefixEnd_2853156 976693606839696165152387 := by
  unfold tailWord_2853156
  simp only [CollatzResearch.WordTrace]
  refine ⟨52031574225755283547773661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69375432301007044730364881 52031574225755283547773661)
  ·
    refine ⟨19511840334658231330415123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52031574225755283547773661 19511840334658231330415123)
    ·
      refine ⟨29267760501987346995622685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19511840334658231330415123 29267760501987346995622685)
      ·
        refine ⟨10975410188245255123358507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29267760501987346995622685 10975410188245255123358507)
        ·
          refine ⟨16463115282367882685037761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10975410188245255123358507 16463115282367882685037761)
          ·
            refine ⟨12347336461775912013778321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16463115282367882685037761 12347336461775912013778321)
            ·
              refine ⟨9260502346331934010333741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12347336461775912013778321 9260502346331934010333741)
              ·
                refine ⟨3472688379874475253875153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9260502346331934010333741 3472688379874475253875153)
                ·
                  refine ⟨2604516284905856440406365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3472688379874475253875153 2604516284905856440406365)
                  ·
                    refine ⟨976693606839696165152387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2604516284905856440406365 976693606839696165152387)
                    ·
                      rfl

theorem cell22_2853156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_2853156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853156 prefixEnd_2853156 := by exact prefixLift 2853156
  have htrace : WordTrace (prefixWord ++ tailWord_2853156) baseStart_2853156 baseEnd_2853156 := by
    simpa [prefixWord, tailWord_2853156, baseEnd_2853156] using wordTrace_append hprefix tailTrace_2853156
  have hstable : (prefixWord ++ tailWord_2853156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853156).length < 2 ^ (prefixWord ++ tailWord_2853156).sum := by decide
  have hdescent : baseEnd_2853156 < baseStart_2853156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853201 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 3, 3]
def baseStart_2853201 : Nat := 118140960795 + 2853201 * 2 ^ 59
def prefixEnd_2853201 : Nat := 4983230072969 + 3 ^ 40 * 2853201 * 2
def baseEnd_2853201 : Nat := 976709011259331047777249

theorem tailTrace_2853201 : CollatzResearch.WordTrace tailWord_2853201 prefixEnd_2853201 976709011259331047777249 := by
  unfold tailWord_2853201
  simp only [CollatzResearch.WordTrace]
  refine ⟨104064789736347539780935457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69376526490898359853956971 104064789736347539780935457)
  ·
    refine ⟨78048592302260654835701593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104064789736347539780935457 78048592302260654835701593)
    ·
      refine ⟨58536444226695491126776195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78048592302260654835701593 58536444226695491126776195)
      ·
        refine ⟨87804666340043236690164293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58536444226695491126776195 87804666340043236690164293)
        ·
          refine ⟨16463374938758106879405805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87804666340043236690164293 16463374938758106879405805)
          ·
            refine ⟨6173765602034290079777177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16463374938758106879405805 6173765602034290079777177)
            ·
              refine ⟨4630324201525717559832883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6173765602034290079777177 4630324201525717559832883)
              ·
                refine ⟨6945486302288576339749325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4630324201525717559832883 6945486302288576339749325)
                ·
                  refine ⟨2604557363358216127405997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6945486302288576339749325 2604557363358216127405997)
                  ·
                    refine ⟨976709011259331047777249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2604557363358216127405997 976709011259331047777249)
                    ·
                      rfl

theorem cell22_2853201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_2853201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853201 prefixEnd_2853201 := by exact prefixLift 2853201
  have htrace : WordTrace (prefixWord ++ tailWord_2853201) baseStart_2853201 baseEnd_2853201 := by
    simpa [prefixWord, tailWord_2853201, baseEnd_2853201] using wordTrace_append hprefix tailTrace_2853201
  have hstable : (prefixWord ++ tailWord_2853201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853201).length < 2 ^ (prefixWord ++ tailWord_2853201).sum := by decide
  have hdescent : baseEnd_2853201 < baseStart_2853201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853259 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 6]
def baseStart_2853259 : Nat := 118140960795 + 2853259 * 2 ^ 59
def prefixEnd_2853259 : Nat := 4983230072969 + 3 ^ 40 * 2853259 * 2
def baseEnd_2853259 : Nat := 325576288614879409942357

theorem tailTrace_2853259 : CollatzResearch.WordTrace tailWord_2853259 prefixEnd_2853259 325576288614879409942357 := by
  unfold tailWord_2853259
  simp only [CollatzResearch.WordTrace]
  refine ⟨104066905170137415686546831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69377936780091610457697887 104066905170137415686546831)
  ·
    refine ⟨156100357755206123529820247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104066905170137415686546831 156100357755206123529820247)
    ·
      refine ⟨234150536632809185294730371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156100357755206123529820247 234150536632809185294730371)
      ·
        refine ⟨351225804949213777942095557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234150536632809185294730371 351225804949213777942095557)
        ·
          refine ⟨65854838427977583364142917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 351225804949213777942095557 65854838427977583364142917)
          ·
            refine ⟨12347782205245796880776797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65854838427977583364142917 12347782205245796880776797)
            ·
              refine ⟨4630418326967173830291299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12347782205245796880776797 4630418326967173830291299)
              ·
                refine ⟨6945627490450760745436949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4630418326967173830291299 6945627490450760745436949)
                ·
                  refine ⟨325576288614879409942357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6945627490450760745436949 325576288614879409942357)
                  ·
                    rfl

theorem cell22_2853259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 6].length) (baseStart_2853259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853259 prefixEnd_2853259 := by exact prefixLift 2853259
  have htrace : WordTrace (prefixWord ++ tailWord_2853259) baseStart_2853259 baseEnd_2853259 := by
    simpa [prefixWord, tailWord_2853259, baseEnd_2853259] using wordTrace_append hprefix tailTrace_2853259
  have hstable : (prefixWord ++ tailWord_2853259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853259).length < 2 ^ (prefixWord ++ tailWord_2853259).sum := by decide
  have hdescent : baseEnd_2853259 < baseStart_2853259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853278 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2853278 : Nat := 118140960795 + 2853278 * 2 ^ 59
def prefixEnd_2853278 : Nat := 4983230072969 + 3 ^ 40 * 2853278 * 2
def baseEnd_2853278 : Nat := 976735369932928513602013

theorem tailTrace_2853278 : CollatzResearch.WordTrace tailWord_2853278 prefixEnd_2853278 976735369932928513602013 := by
  unfold tailWord_2853278
  simp only [CollatzResearch.WordTrace]
  refine ⟨13008449769633572741436061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69378398771379054620992325 13008449769633572741436061)
  ·
    refine ⟨4878168663612589778038523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13008449769633572741436061 4878168663612589778038523)
    ·
      refine ⟨7317252995418884667057785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4878168663612589778038523 7317252995418884667057785)
      ·
        refine ⟨5487939746564163500293339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7317252995418884667057785 5487939746564163500293339)
        ·
          refine ⟨8231909619846245250440009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5487939746564163500293339 8231909619846245250440009)
          ·
            refine ⟨6173932214884683937830007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8231909619846245250440009 6173932214884683937830007)
            ·
              refine ⟨9260898322327025906745011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6173932214884683937830007 9260898322327025906745011)
              ·
                refine ⟨13891347483490538860117517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9260898322327025906745011 13891347483490538860117517)
                ·
                  refine ⟨5209255306308952072544069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13891347483490538860117517 5209255306308952072544069)
                  ·
                    refine ⟨976735369932928513602013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5209255306308952072544069 976735369932928513602013)
                    ·
                      rfl

theorem cell22_2853278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2853278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853278 prefixEnd_2853278 := by exact prefixLift 2853278
  have htrace : WordTrace (prefixWord ++ tailWord_2853278) baseStart_2853278 baseEnd_2853278 := by
    simpa [prefixWord, tailWord_2853278, baseEnd_2853278] using wordTrace_append hprefix tailTrace_2853278
  have hstable : (prefixWord ++ tailWord_2853278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853278).length < 2 ^ (prefixWord ++ tailWord_2853278).sum := by decide
  have hdescent : baseEnd_2853278 < baseStart_2853278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853308 : List Nat := [2, 2, 2, 4, 1, 1, 1, 4, 2, 3]
def baseStart_2853308 : Nat := 118140960795 + 2853308 * 2 ^ 59
def prefixEnd_2853308 : Nat := 4983230072969 + 3 ^ 40 * 2853308 * 2
def baseEnd_2853308 : Nat := 976745639546018435351921

theorem tailTrace_2853308 : CollatzResearch.WordTrace tailWord_2853308 prefixEnd_2853308 976745639546018435351921 := by
  unfold tailWord_2853308
  simp only [CollatzResearch.WordTrace]
  refine ⟨52034346173479948527540289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69379128231306598036720385 52034346173479948527540289)
  ·
    refine ⟨39025759630109961395655217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52034346173479948527540289 39025759630109961395655217)
    ·
      refine ⟨29269319722582471046741413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39025759630109961395655217 29269319722582471046741413)
      ·
        refine ⟨5487997447984213321264015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29269319722582471046741413 5487997447984213321264015)
        ·
          refine ⟨8231996171976319981896023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5487997447984213321264015 8231996171976319981896023)
          ·
            refine ⟨12347994257964479972844035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8231996171976319981896023 12347994257964479972844035)
            ·
              refine ⟨18521991386946719959266053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12347994257964479972844035 18521991386946719959266053)
              ·
                refine ⟨3472873385052509992362385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18521991386946719959266053 3472873385052509992362385)
                ·
                  refine ⟨2604655038789382494271789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3472873385052509992362385 2604655038789382494271789)
                  ·
                    refine ⟨976745639546018435351921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2604655038789382494271789 976745639546018435351921)
                    ·
                      rfl

theorem cell22_2853308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_2853308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853308 prefixEnd_2853308 := by exact prefixLift 2853308
  have htrace : WordTrace (prefixWord ++ tailWord_2853308) baseStart_2853308 baseEnd_2853308 := by
    simpa [prefixWord, tailWord_2853308, baseEnd_2853308] using wordTrace_append hprefix tailTrace_2853308
  have hstable : (prefixWord ++ tailWord_2853308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853308).length < 2 ^ (prefixWord ++ tailWord_2853308).sum := by decide
  have hdescent : baseEnd_2853308 < baseStart_2853308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853366 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_2853366 : Nat := 118140960795 + 2853366 * 2 ^ 59
def prefixEnd_2853366 : Nat := 4983230072969 + 3 ^ 40 * 2853366 * 2
def baseEnd_2853366 : Nat := 325588498043775205800581

theorem tailTrace_2853366 : CollatzResearch.WordTrace tailWord_2853366 prefixEnd_2853366 325588498043775205800581 := by
  unfold tailWord_2853366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504425486296860810043247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69380538520499848640461301 6504425486296860810043247)
  ·
    refine ⟨9756638229445291215064871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6504425486296860810043247 9756638229445291215064871)
    ·
      refine ⟨14634957344167936822597307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9756638229445291215064871 14634957344167936822597307)
      ·
        refine ⟨21952436016251905233895961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14634957344167936822597307 21952436016251905233895961)
        ·
          refine ⟨16464327012188928925421971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21952436016251905233895961 16464327012188928925421971)
          ·
            refine ⟨24696490518283393388132957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16464327012188928925421971 24696490518283393388132957)
            ·
              refine ⟨9261183944356272520549859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24696490518283393388132957 9261183944356272520549859)
              ·
                refine ⟨13891775916534408780824789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9261183944356272520549859 13891775916534408780824789)
                ·
                  refine ⟨325588498043775205800581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13891775916534408780824789 325588498043775205800581)
                  ·
                    rfl

theorem cell22_2853366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_2853366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853366 prefixEnd_2853366 := by exact prefixLift 2853366
  have htrace : WordTrace (prefixWord ++ tailWord_2853366) baseStart_2853366 baseEnd_2853366 := by
    simpa [prefixWord, tailWord_2853366, baseEnd_2853366] using wordTrace_append hprefix tailTrace_2853366
  have hstable : (prefixWord ++ tailWord_2853366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853366).length < 2 ^ (prefixWord ++ tailWord_2853366).sum := by decide
  have hdescent : baseEnd_2853366 < baseStart_2853366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853421 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2853421 : Nat := 118140960795 + 2853421 * 2 ^ 59
def prefixEnd_2853421 : Nat := 4983230072969 + 3 ^ 40 * 2853421 * 2
def baseEnd_2853421 : Nat := 976784321755323807276575

theorem tailTrace_2853421 : CollatzResearch.WordTrace tailWord_2853421 prefixEnd_2853421 976784321755323807276575 := by
  unfold tailWord_2853421
  simp only [CollatzResearch.WordTrace]
  refine ⟨104072813795550517353944117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69381875863700344902629411 104072813795550517353944117)
  ·
    refine ⟨9756826293332861001932261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104072813795550517353944117 9756826293332861001932261)
    ·
      refine ⟨1829404929999911437862299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9756826293332861001932261 1829404929999911437862299)
      ·
        refine ⟨2744107394999867156793449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1829404929999911437862299 2744107394999867156793449)
        ·
          refine ⟨2058080546249900367595087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2744107394999867156793449 2058080546249900367595087)
          ·
            refine ⟨3087120819374850551392631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058080546249900367595087 3087120819374850551392631)
            ·
              refine ⟨4630681229062275827088947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3087120819374850551392631 4630681229062275827088947)
              ·
                refine ⟨6946021843593413740633421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4630681229062275827088947 6946021843593413740633421)
                ·
                  refine ⟨2604758191347530152737533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6946021843593413740633421 2604758191347530152737533)
                  ·
                    refine ⟨976784321755323807276575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2604758191347530152737533 976784321755323807276575)
                    ·
                      rfl

theorem cell22_2853421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2853421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853421 prefixEnd_2853421 := by exact prefixLift 2853421
  have htrace : WordTrace (prefixWord ++ tailWord_2853421) baseStart_2853421 baseEnd_2853421 := by
    simpa [prefixWord, tailWord_2853421, baseEnd_2853421] using wordTrace_append hprefix tailTrace_2853421
  have hstable : (prefixWord ++ tailWord_2853421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853421).length < 2 ^ (prefixWord ++ tailWord_2853421).sum := by decide
  have hdescent : baseEnd_2853421 < baseStart_2853421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853458 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_2853458 : Nat := 118140960795 + 2853458 * 2 ^ 59
def prefixEnd_2853458 : Nat := 4983230072969 + 3 ^ 40 * 2853458 * 2
def baseEnd_2853458 : Nat := 976796987611468044101461

theorem tailTrace_2853458 : CollatzResearch.WordTrace tailWord_2853458 prefixEnd_2853458 976796987611468044101461 := by
  unfold tailWord_2853458
  simp only [CollatzResearch.WordTrace]
  refine ⟨26018540824104118168260257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69382775530944315115360685 26018540824104118168260257)
  ·
    refine ⟨19513905618078088626195193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26018540824104118168260257 19513905618078088626195193)
    ·
      refine ⟨14635429213558566469646395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19513905618078088626195193 14635429213558566469646395)
      ·
        refine ⟨21953143820337849704469593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14635429213558566469646395 21953143820337849704469593)
        ·
          refine ⟨16464857865253387278352195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21953143820337849704469593 16464857865253387278352195)
          ·
            refine ⟨24697286797880080917528293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16464857865253387278352195 24697286797880080917528293)
            ·
              refine ⟨4630741274602515172036555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24697286797880080917528293 4630741274602515172036555)
              ·
                refine ⟨6946111911903772758054833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4630741274602515172036555 6946111911903772758054833)
                ·
                  refine ⟨5209583933927829568541125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6946111911903772758054833 5209583933927829568541125)
                  ·
                    refine ⟨976796987611468044101461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5209583933927829568541125 976796987611468044101461)
                    ·
                      rfl

theorem cell22_2853458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_2853458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853458 prefixEnd_2853458 := by exact prefixLift 2853458
  have htrace : WordTrace (prefixWord ++ tailWord_2853458) baseStart_2853458 baseEnd_2853458 := by
    simpa [prefixWord, tailWord_2853458, baseEnd_2853458] using wordTrace_append hprefix tailTrace_2853458
  have hstable : (prefixWord ++ tailWord_2853458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853458).length < 2 ^ (prefixWord ++ tailWord_2853458).sum := by decide
  have hdescent : baseEnd_2853458 < baseStart_2853458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853490 : List Nat := [3, 2, 1, 2, 5, 1, 1, 7]
def baseStart_2853490 : Nat := 118140960795 + 2853490 * 2 ^ 59
def prefixEnd_2853490 : Nat := 4983230072969 + 3 ^ 40 * 2853490 * 2
def baseEnd_2853490 : Nat := 108534215762825625255707

theorem tailTrace_2853490 : CollatzResearch.WordTrace tailWord_2853490 prefixEnd_2853490 108534215762825625255707 := by
  unfold tailWord_2853490
  simp only [CollatzResearch.WordTrace]
  refine ⟨26018832608075135534551481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69383553621533694758803949 26018832608075135534551481)
  ·
    refine ⟨19514124456056351650913611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26018832608075135534551481 19514124456056351650913611)
    ·
      refine ⟨29271186684084527476370417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19514124456056351650913611 29271186684084527476370417)
      ·
        refine ⟨21953390013063395607277813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29271186684084527476370417 21953390013063395607277813)
        ·
          refine ⟨2058130313724693338182295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21953390013063395607277813 2058130313724693338182295)
          ·
            refine ⟨3087195470587040007273443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058130313724693338182295 3087195470587040007273443)
            ·
              refine ⟨4630793205880560010910165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3087195470587040007273443 4630793205880560010910165)
              ·
                refine ⟨108534215762825625255707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4630793205880560010910165 108534215762825625255707)
                ·
                  rfl

theorem cell22_2853490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_2853490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853490 prefixEnd_2853490 := by exact prefixLift 2853490
  have htrace : WordTrace (prefixWord ++ tailWord_2853490) baseStart_2853490 baseEnd_2853490 := by
    simpa [prefixWord, tailWord_2853490, baseEnd_2853490] using wordTrace_append hprefix tailTrace_2853490
  have hstable : (prefixWord ++ tailWord_2853490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853490).length < 2 ^ (prefixWord ++ tailWord_2853490).sum := by decide
  have hdescent : baseEnd_2853490 < baseStart_2853490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853522 : List Nat := [3, 2, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_2853522 : Nat := 118140960795 + 2853522 * 2 ^ 59
def prefixEnd_2853522 : Nat := 4983230072969 + 3 ^ 40 * 2853522 * 2
def baseEnd_2853522 : Nat := 976818896119393210501265

theorem tailTrace_2853522 : CollatzResearch.WordTrace tailWord_2853522 prefixEnd_2853522 976818896119393210501265 := by
  unfold tailWord_2853522
  simp only [CollatzResearch.WordTrace]
  refine ⟨26019124392046152900842705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69384331712123074402247213 26019124392046152900842705)
  ·
    refine ⟨19514343294034614675632029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26019124392046152900842705 19514343294034614675632029)
    ·
      refine ⟨7317878735262980503362011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19514343294034614675632029 7317878735262980503362011)
      ·
        refine ⟨10976818102894470755043017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7317878735262980503362011 10976818102894470755043017)
        ·
          refine ⟨8232613577170853066282263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10976818102894470755043017 8232613577170853066282263)
          ·
            refine ⟨12348920365756279599423395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8232613577170853066282263 12348920365756279599423395)
            ·
              refine ⟨18523380548634419399135093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12348920365756279599423395 18523380548634419399135093)
              ·
                refine ⟨1736566926434476818668915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18523380548634419399135093 1736566926434476818668915)
                ·
                  refine ⟨2604850389651715228003373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736566926434476818668915 2604850389651715228003373)
                  ·
                    refine ⟨976818896119393210501265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2604850389651715228003373 976818896119393210501265)
                    ·
                      rfl

theorem cell22_2853522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_2853522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853522 prefixEnd_2853522 := by exact prefixLift 2853522
  have htrace : WordTrace (prefixWord ++ tailWord_2853522) baseStart_2853522 baseEnd_2853522 := by
    simpa [prefixWord, tailWord_2853522, baseEnd_2853522] using wordTrace_append hprefix tailTrace_2853522
  have hstable : (prefixWord ++ tailWord_2853522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853522).length < 2 ^ (prefixWord ++ tailWord_2853522).sum := by decide
  have hdescent : baseEnd_2853522 < baseStart_2853522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853550 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2853550 : Nat := 118140960795 + 2853550 * 2 ^ 59
def prefixEnd_2853550 : Nat := 4983230072969 + 3 ^ 40 * 2853550 * 2
def baseEnd_2853550 : Nat := 976828481091610470801179

theorem tailTrace_2853550 : CollatzResearch.WordTrace tailWord_2853550 prefixEnd_2853550 976828481091610470801179 := by
  unfold tailWord_2853550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13009689851510396548173763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69385012541388781590260069 13009689851510396548173763)
  ·
    refine ⟨19514534777265594822260645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13009689851510396548173763 19514534777265594822260645)
    ·
      refine ⟨3658975270737299029173871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19514534777265594822260645 3658975270737299029173871)
      ·
        refine ⟨5488462906105948543760807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3658975270737299029173871 5488462906105948543760807)
        ·
          refine ⟨8232694359158922815641211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5488462906105948543760807 8232694359158922815641211)
          ·
            refine ⟨12349041538738384223461817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8232694359158922815641211 12349041538738384223461817)
            ·
              refine ⟨9261781154053788167596363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12349041538738384223461817 9261781154053788167596363)
              ·
                refine ⟨13892671731080682251394545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9261781154053788167596363 13892671731080682251394545)
                ·
                  refine ⟨10419503798310511688545909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13892671731080682251394545 10419503798310511688545909)
                  ·
                    refine ⟨976828481091610470801179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10419503798310511688545909 976828481091610470801179)
                    ·
                      rfl

theorem cell22_2853550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2853550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853550 prefixEnd_2853550 := by exact prefixLift 2853550
  have htrace : WordTrace (prefixWord ++ tailWord_2853550) baseStart_2853550 baseEnd_2853550 := by
    simpa [prefixWord, tailWord_2853550, baseEnd_2853550] using wordTrace_append hprefix tailTrace_2853550
  have hstable : (prefixWord ++ tailWord_2853550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853550).length < 2 ^ (prefixWord ++ tailWord_2853550).sum := by decide
  have hdescent : baseEnd_2853550 < baseStart_2853550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853565 : List Nat := [1, 4, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_2853565 : Nat := 118140960795 + 2853565 * 2 ^ 59
def prefixEnd_2853565 : Nat := 4983230072969 + 3 ^ 40 * 2853565 * 2
def baseEnd_2853565 : Nat := 976833615898155431676133

theorem tailTrace_2853565 : CollatzResearch.WordTrace tailWord_2853565 prefixEnd_2853565 976833615898155431676133 := by
  unfold tailWord_2853565
  simp only [CollatzResearch.WordTrace]
  refine ⟨104078065907028829947186149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69385377271352553298124099 104078065907028829947186149)
  ·
    refine ⟨19514637357567905615097403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104078065907028829947186149 19514637357567905615097403)
    ·
      refine ⟨29271956036351858422646105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19514637357567905615097403 29271956036351858422646105)
      ·
        refine ⟨21953967027263893816984579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29271956036351858422646105 21953967027263893816984579)
        ·
          refine ⟨32930950540895840725476869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21953967027263893816984579 32930950540895840725476869)
          ·
            refine ⟨6174553226417970136026913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32930950540895840725476869 6174553226417970136026913)
            ·
              refine ⟨4630914919813477602020185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6174553226417970136026913 4630914919813477602020185)
              ·
                refine ⟨3473186189860108201515139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4630914919813477602020185 3473186189860108201515139)
                ·
                  refine ⟨5209779284790162302272709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3473186189860108201515139 5209779284790162302272709)
                  ·
                    refine ⟨976833615898155431676133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5209779284790162302272709 976833615898155431676133)
                    ·
                      rfl

theorem cell22_2853565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_2853565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853565 prefixEnd_2853565 := by exact prefixLift 2853565
  have htrace : WordTrace (prefixWord ++ tailWord_2853565) baseStart_2853565 baseEnd_2853565 := by
    simpa [prefixWord, tailWord_2853565, baseEnd_2853565] using wordTrace_append hprefix tailTrace_2853565
  have hstable : (prefixWord ++ tailWord_2853565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853565).length < 2 ^ (prefixWord ++ tailWord_2853565).sum := by decide
  have hdescent : baseEnd_2853565 < baseStart_2853565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853591 : List Nat := [1, 1, 3, 2, 1, 4, 10]
def baseStart_2853591 : Nat := 118140960795 + 2853591 * 2 ^ 59
def prefixEnd_2853591 : Nat := 4983230072969 + 3 ^ 40 * 2853591 * 2
def baseEnd_2853591 : Nat := 36179352452944445575039

theorem tailTrace_2853591 : CollatzResearch.WordTrace tailWord_2853591 prefixEnd_2853591 36179352452944445575039 := by
  unfold tailWord_2853591
  simp only [CollatzResearch.WordTrace]
  refine ⟨104079014204934636387632627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69386009469956424258421751 104079014204934636387632627)
  ·
    refine ⟨156118521307401954581448941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104079014204934636387632627 156118521307401954581448941)
    ·
      refine ⟨58544445490275732968043353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156118521307401954581448941 58544445490275732968043353)
      ·
        refine ⟨43908334117706799726032515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58544445490275732968043353 43908334117706799726032515)
        ·
          refine ⟨65862501176560199589048773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43908334117706799726032515 65862501176560199589048773)
          ·
            refine ⟨12349218970605037422946645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65862501176560199589048773 12349218970605037422946645)
            ·
              refine ⟨36179352452944445575039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12349218970605037422946645 36179352452944445575039)
              ·
                rfl

theorem cell22_2853591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 10].length) (baseStart_2853591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853591 prefixEnd_2853591 := by exact prefixLift 2853591
  have htrace : WordTrace (prefixWord ++ tailWord_2853591) baseStart_2853591 baseEnd_2853591 := by
    simpa [prefixWord, tailWord_2853591, baseEnd_2853591] using wordTrace_append hprefix tailTrace_2853591
  have hstable : (prefixWord ++ tailWord_2853591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853591).length < 2 ^ (prefixWord ++ tailWord_2853591).sum := by decide
  have hdescent : baseEnd_2853591 < baseStart_2853591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853593 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 2, 4]
def baseStart_2853593 : Nat := 118140960795 + 2853593 * 2 ^ 59
def prefixEnd_2853593 : Nat := 4983230072969 + 3 ^ 40 * 2853593 * 2
def baseEnd_2853593 : Nat := 976843200870372691976047

theorem tailTrace_2853593 : CollatzResearch.WordTrace tailWord_2853593 prefixEnd_2853593 976843200870372691976047 := by
  unfold tailWord_2853593
  simp only [CollatzResearch.WordTrace]
  refine ⟨104079087150927390729205433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69386058100618260486136955 104079087150927390729205433)
  ·
    refine ⟨78059315363195543046904075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104079087150927390729205433 78059315363195543046904075)
    ·
      refine ⟨117088973044793314570356113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78059315363195543046904075 117088973044793314570356113)
      ·
        refine ⟨87816729783594985927767085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117088973044793314570356113 87816729783594985927767085)
        ·
          refine ⟨32931273668848119722912657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87816729783594985927767085 32931273668848119722912657)
          ·
            refine ⟨24698455251636089792184493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32931273668848119722912657 24698455251636089792184493)
            ·
              refine ⟨9261920719363533672069185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24698455251636089792184493 9261920719363533672069185)
              ·
                refine ⟨6946440539522650254051889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9261920719363533672069185 6946440539522650254051889)
                ·
                  refine ⟨5209830404641987690538917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6946440539522650254051889 5209830404641987690538917)
                  ·
                    refine ⟨976843200870372691976047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5209830404641987690538917 976843200870372691976047)
                    ·
                      rfl

theorem cell22_2853593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_2853593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853593 prefixEnd_2853593 := by exact prefixLift 2853593
  have htrace : WordTrace (prefixWord ++ tailWord_2853593) baseStart_2853593 baseEnd_2853593 := by
    simpa [prefixWord, tailWord_2853593, baseEnd_2853593] using wordTrace_append hprefix tailTrace_2853593
  have hstable : (prefixWord ++ tailWord_2853593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853593).length < 2 ^ (prefixWord ++ tailWord_2853593).sum := by decide
  have hdescent : baseEnd_2853593 < baseStart_2853593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853623 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 5, 3]
def baseStart_2853623 : Nat := 118140960795 + 2853623 * 2 ^ 59
def prefixEnd_2853623 : Nat := 4983230072969 + 3 ^ 40 * 2853623 * 2
def baseEnd_2853623 : Nat := 976853470483462613725955

theorem tailTrace_2853623 : CollatzResearch.WordTrace tailWord_2853623 prefixEnd_2853623 976853470483462613725955 := by
  unfold tailWord_2853623
  simp only [CollatzResearch.WordTrace]
  refine ⟨104080181340818705852797523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69386787560545803901865015 104080181340818705852797523)
  ·
    refine ⟨156120272011228058779196285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104080181340818705852797523 156120272011228058779196285)
    ·
      refine ⟨58545102004210522042198607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156120272011228058779196285 58545102004210522042198607)
      ·
        refine ⟨87817653006315783063297911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58545102004210522042198607 87817653006315783063297911)
        ·
          refine ⟨131726479509473674594946867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87817653006315783063297911 131726479509473674594946867)
          ·
            refine ⟨197589719264210511892420301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131726479509473674594946867 197589719264210511892420301)
            ·
              refine ⟨74096144724078941959657613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197589719264210511892420301 74096144724078941959657613)
              ·
                refine ⟨27786054271529603234871605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74096144724078941959657613 27786054271529603234871605)
                ·
                  refine ⟨2604942587955900303269213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27786054271529603234871605 2604942587955900303269213)
                  ·
                    refine ⟨976853470483462613725955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2604942587955900303269213 976853470483462613725955)
                    ·
                      rfl

theorem cell22_2853623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_2853623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853623 prefixEnd_2853623 := by exact prefixLift 2853623
  have htrace : WordTrace (prefixWord ++ tailWord_2853623) baseStart_2853623 baseEnd_2853623 := by
    simpa [prefixWord, tailWord_2853623, baseEnd_2853623] using wordTrace_append hprefix tailTrace_2853623
  have hstable : (prefixWord ++ tailWord_2853623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853623).length < 2 ^ (prefixWord ++ tailWord_2853623).sum := by decide
  have hdescent : baseEnd_2853623 < baseStart_2853623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853674 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 3, 3]
def baseStart_2853674 : Nat := 118140960795 + 2853674 * 2 ^ 59
def prefixEnd_2853674 : Nat := 4983230072969 + 3 ^ 40 * 2853674 * 2
def baseEnd_2853674 : Nat := 976870928825715480700799

theorem tailTrace_2853674 : CollatzResearch.WordTrace tailWord_2853674 prefixEnd_2853674 976870928825715480700799 := by
  unfold tailWord_2853674
  simp only [CollatzResearch.WordTrace]
  refine ⟨26020510365908485390726019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69388027642422627708602717 26020510365908485390726019)
  ·
    refine ⟨39030765548862728086089029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26020510365908485390726019 39030765548862728086089029)
    ·
      refine ⟨7318268540411761516141693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39030765548862728086089029 7318268540411761516141693)
      ·
        refine ⟨2744350702654410568553135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7318268540411761516141693 2744350702654410568553135)
        ·
          refine ⟨4116526053981615852829703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2744350702654410568553135 4116526053981615852829703)
          ·
            refine ⟨6174789080972423779244555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4116526053981615852829703 6174789080972423779244555)
            ·
              refine ⟨9262183621458635668866833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6174789080972423779244555 9262183621458635668866833)
              ·
                refine ⟨6946637716093976751650125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9262183621458635668866833 6946637716093976751650125)
                ·
                  refine ⟨2604989143535241281868797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6946637716093976751650125 2604989143535241281868797)
                  ·
                    refine ⟨976870928825715480700799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2604989143535241281868797 976870928825715480700799)
                    ·
                      rfl

theorem cell22_2853674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_2853674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853674 prefixEnd_2853674 := by exact prefixLift 2853674
  have htrace : WordTrace (prefixWord ++ tailWord_2853674) baseStart_2853674 baseEnd_2853674 := by
    simpa [prefixWord, tailWord_2853674, baseEnd_2853674] using wordTrace_append hprefix tailTrace_2853674
  have hstable : (prefixWord ++ tailWord_2853674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853674).length < 2 ^ (prefixWord ++ tailWord_2853674).sum := by decide
  have hdescent : baseEnd_2853674 < baseStart_2853674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853728 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 3, 6]
def baseStart_2853728 : Nat := 118140960795 + 2853728 * 2 ^ 59
def prefixEnd_2853728 : Nat := 4983230072969 + 3 ^ 40 * 2853728 * 2
def baseEnd_2853728 : Nat := 976889414129277339850633

theorem tailTrace_2853728 : CollatzResearch.WordTrace tailWord_2853728 prefixEnd_2853728 976889414129277339850633 := by
  unfold tailWord_2853728
  simp only [CollatzResearch.WordTrace]
  refine ⟨52042005502719154392684919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69389340670292205856913225 52042005502719154392684919)
  ·
    refine ⟨78063008254078731589027379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52042005502719154392684919 78063008254078731589027379)
    ·
      refine ⟨117094512381118097383541069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78063008254078731589027379 117094512381118097383541069)
      ·
        refine ⟨43910442142919286518827901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117094512381118097383541069 43910442142919286518827901)
        ·
          refine ⟨16466415803594732444560463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43910442142919286518827901 16466415803594732444560463)
          ·
            refine ⟨24699623705392098666840695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16466415803594732444560463 24699623705392098666840695)
            ·
              refine ⟨37049435558088148000261043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24699623705392098666840695 37049435558088148000261043)
              ·
                refine ⟨55574153337132222000391565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37049435558088148000261043 55574153337132222000391565)
                ·
                  refine ⟨20840307501424583250146837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55574153337132222000391565 20840307501424583250146837)
                  ·
                    refine ⟨976889414129277339850633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20840307501424583250146837 976889414129277339850633)
                    ·
                      rfl

theorem cell22_2853728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_2853728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853728 prefixEnd_2853728 := by exact prefixLift 2853728
  have htrace : WordTrace (prefixWord ++ tailWord_2853728) baseStart_2853728 baseEnd_2853728 := by
    simpa [prefixWord, tailWord_2853728, baseEnd_2853728] using wordTrace_append hprefix tailTrace_2853728
  have hstable : (prefixWord ++ tailWord_2853728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853728).length < 2 ^ (prefixWord ++ tailWord_2853728).sum := by decide
  have hdescent : baseEnd_2853728 < baseStart_2853728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853749 : List Nat := [1, 3, 4, 1, 1, 4, 1, 3, 4]
def baseStart_2853749 : Nat := 118140960795 + 2853749 * 2 ^ 59
def prefixEnd_2853749 : Nat := 4983230072969 + 3 ^ 40 * 2853749 * 2
def baseEnd_2853749 : Nat := 325632200952813428358523

theorem tailTrace_2853749 : CollatzResearch.WordTrace tailWord_2853749 prefixEnd_2853749 325632200952813428358523 := by
  unfold tailWord_2853749
  simp only [CollatzResearch.WordTrace]
  refine ⟨104084776938362229371884301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69389851292241486247922867 104084776938362229371884301)
  ·
    refine ⟨39031791351885836014456613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104084776938362229371884301 39031791351885836014456613)
    ·
      refine ⟨7318460878478594252710615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39031791351885836014456613 7318460878478594252710615)
      ·
        refine ⟨10977691317717891379065923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7318460878478594252710615 10977691317717891379065923)
        ·
          refine ⟨16466536976576837068598885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10977691317717891379065923 16466536976576837068598885)
          ·
            refine ⟨3087475683108156950362291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16466536976576837068598885 3087475683108156950362291)
            ·
              refine ⟨4631213524662235425543437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3087475683108156950362291 4631213524662235425543437)
              ·
                refine ⟨1736705071748338284578789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4631213524662235425543437 1736705071748338284578789)
                ·
                  refine ⟨325632200952813428358523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1736705071748338284578789 325632200952813428358523)
                  ·
                    rfl

theorem cell22_2853749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_2853749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853749 prefixEnd_2853749 := by exact prefixLift 2853749
  have htrace : WordTrace (prefixWord ++ tailWord_2853749) baseStart_2853749 baseEnd_2853749 := by
    simpa [prefixWord, tailWord_2853749, baseEnd_2853749] using wordTrace_append hprefix tailTrace_2853749
  have hstable : (prefixWord ++ tailWord_2853749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853749).length < 2 ^ (prefixWord ++ tailWord_2853749).sum := by decide
  have hdescent : baseEnd_2853749 < baseStart_2853749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853803 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 1, 7]
def baseStart_2853803 : Nat := 118140960795 + 2853803 * 2 ^ 59
def prefixEnd_2853803 : Nat := 4983230072969 + 3 ^ 40 * 2853803 * 2
def baseEnd_2853803 : Nat := 976915088162002144225403

theorem tailTrace_2853803 : CollatzResearch.WordTrace tailWord_2853803 prefixEnd_2853803 976915088162002144225403 := by
  unfold tailWord_2853803
  simp only [CollatzResearch.WordTrace]
  refine ⟨104086746480166596594350063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69391164320111064396233375 104086746480166596594350063)
  ·
    refine ⟨156130119720249894891525095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104086746480166596594350063 156130119720249894891525095)
    ·
      refine ⟨234195179580374842337287643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156130119720249894891525095 234195179580374842337287643)
      ·
        refine ⟨351292769370562263505931465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234195179580374842337287643 351292769370562263505931465)
        ·
          refine ⟨263469577027921697629448599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351292769370562263505931465 263469577027921697629448599)
          ·
            refine ⟨395204365541882546444172899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263469577027921697629448599 395204365541882546444172899)
            ·
              refine ⟨592806548312823819666259349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395204365541882546444172899 592806548312823819666259349)
              ·
                refine ⟨27787806952163616546855907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 592806548312823819666259349 27787806952163616546855907)
                ·
                  refine ⟨41681710428245424820283861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27787806952163616546855907 41681710428245424820283861)
                  ·
                    refine ⟨976915088162002144225403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41681710428245424820283861 976915088162002144225403)
                    ·
                      rfl

theorem cell22_2853803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_2853803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853803 prefixEnd_2853803 := by exact prefixLift 2853803
  have htrace : WordTrace (prefixWord ++ tailWord_2853803) baseStart_2853803 baseEnd_2853803 := by
    simpa [prefixWord, tailWord_2853803, baseEnd_2853803] using wordTrace_append hprefix tailTrace_2853803
  have hstable : (prefixWord ++ tailWord_2853803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853803).length < 2 ^ (prefixWord ++ tailWord_2853803).sum := by decide
  have hdescent : baseEnd_2853803 < baseStart_2853803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853822 : List Nat := [4, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_2853822 : Nat := 118140960795 + 2853822 * 2 ^ 59
def prefixEnd_2853822 : Nat := 4983230072969 + 3 ^ 40 * 2853822 * 2
def baseEnd_2853822 : Nat := 325640530750097476000115

theorem tailTrace_2853822 : CollatzResearch.WordTrace tailWord_2853822 prefixEnd_2853822 325640530750097476000115 := by
  unfold tailWord_2853822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13010929933387220354911465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69391626311398508559527813 13010929933387220354911465)
  ·
    refine ⟨9758197450040415266183599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13010929933387220354911465 9758197450040415266183599)
    ·
      refine ⟨14637296175060622899275399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9758197450040415266183599 14637296175060622899275399)
      ·
        refine ⟨21955944262590934348913099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14637296175060622899275399 21955944262590934348913099)
        ·
          refine ⟨32933916393886401523369649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21955944262590934348913099 32933916393886401523369649)
          ·
            refine ⟨24700437295414801142527237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32933916393886401523369649 24700437295414801142527237)
            ·
              refine ⟨4631331992890275214223857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24700437295414801142527237 4631331992890275214223857)
              ·
                refine ⟨3473498994667706410667893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4631331992890275214223857 3473498994667706410667893)
                ·
                  refine ⟨325640530750097476000115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3473498994667706410667893 325640530750097476000115)
                  ·
                    rfl

theorem cell22_2853822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_2853822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853822 prefixEnd_2853822 := by exact prefixLift 2853822
  have htrace : WordTrace (prefixWord ++ tailWord_2853822) baseStart_2853822 baseEnd_2853822 := by
    simpa [prefixWord, tailWord_2853822, baseEnd_2853822] using wordTrace_append hprefix tailTrace_2853822
  have hstable : (prefixWord ++ tailWord_2853822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853822).length < 2 ^ (prefixWord ++ tailWord_2853822).sum := by decide
  have hdescent : baseEnd_2853822 < baseStart_2853822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853835 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 3, 4]
def baseStart_2853835 : Nat := 118140960795 + 2853835 * 2 ^ 59
def prefixEnd_2853835 : Nat := 4983230072969 + 3 ^ 40 * 2853835 * 2
def baseEnd_2853835 : Nat := 976926042415964727425305

theorem tailTrace_2853835 : CollatzResearch.WordTrace tailWord_2853835 prefixEnd_2853835 976926042415964727425305 := by
  unfold tailWord_2853835
  simp only [CollatzResearch.WordTrace]
  refine ⟨104087913616050666059514959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69391942410700444039676639 104087913616050666059514959)
  ·
    refine ⟨156131870424075999089272439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104087913616050666059514959 156131870424075999089272439)
    ·
      refine ⟨234197805636113998633908659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156131870424075999089272439 234197805636113998633908659)
      ·
        refine ⟨351296708454170997950862989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234197805636113998633908659 351296708454170997950862989)
        ·
          refine ⟨131736265670314124231573621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351296708454170997950862989 131736265670314124231573621)
          ·
            refine ⟨12350274906591949146710027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131736265670314124231573621 12350274906591949146710027)
            ·
              refine ⟨18525412359887923720065041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12350274906591949146710027 18525412359887923720065041)
              ·
                refine ⟨13894059269915942790048781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18525412359887923720065041 13894059269915942790048781)
                ·
                  refine ⟨5210272226218478546268293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13894059269915942790048781 5210272226218478546268293)
                  ·
                    refine ⟨976926042415964727425305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5210272226218478546268293 976926042415964727425305)
                    ·
                      rfl

theorem cell22_2853835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 4].length) (baseStart_2853835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853835 prefixEnd_2853835 := by exact prefixLift 2853835
  have htrace : WordTrace (prefixWord ++ tailWord_2853835) baseStart_2853835 baseEnd_2853835 := by
    simpa [prefixWord, tailWord_2853835, baseEnd_2853835] using wordTrace_append hprefix tailTrace_2853835
  have hstable : (prefixWord ++ tailWord_2853835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853835).length < 2 ^ (prefixWord ++ tailWord_2853835).sum := by decide
  have hdescent : baseEnd_2853835 < baseStart_2853835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853850 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 8]
def baseStart_2853850 : Nat := 118140960795 + 2853850 * 2 ^ 59
def prefixEnd_2853850 : Nat := 4983230072969 + 3 ^ 40 * 2853850 * 2
def baseEnd_2853850 : Nat := 325643725740836562766753

theorem tailTrace_2853850 : CollatzResearch.WordTrace tailWord_2853850 prefixEnd_2853850 325643725740836562766753 := by
  unfold tailWord_2853850
  simp only [CollatzResearch.WordTrace]
  refine ⟨26022115177749080905327751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69392307140664215747540669 26022115177749080905327751)
  ·
    refine ⟨39033172766623621357991627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26022115177749080905327751 39033172766623621357991627)
    ·
      refine ⟨58549759149935432036987441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39033172766623621357991627 58549759149935432036987441)
      ·
        refine ⟨43912319362451574027740581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58549759149935432036987441 43912319362451574027740581)
        ·
          refine ⟨8233559880459670130201359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43912319362451574027740581 8233559880459670130201359)
          ·
            refine ⟨12350339820689505195302039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8233559880459670130201359 12350339820689505195302039)
            ·
              refine ⟨18525509731034257792953059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12350339820689505195302039 18525509731034257792953059)
              ·
                refine ⟨27788264596551386689429589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18525509731034257792953059 27788264596551386689429589)
                ·
                  refine ⟨325643725740836562766753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27788264596551386689429589 325643725740836562766753)
                  ·
                    rfl

theorem cell22_2853850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_2853850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853850 prefixEnd_2853850 := by exact prefixLift 2853850
  have htrace : WordTrace (prefixWord ++ tailWord_2853850) baseStart_2853850 baseEnd_2853850 := by
    simpa [prefixWord, tailWord_2853850, baseEnd_2853850] using wordTrace_append hprefix tailTrace_2853850
  have hstable : (prefixWord ++ tailWord_2853850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853850).length < 2 ^ (prefixWord ++ tailWord_2853850).sum := by decide
  have hdescent : baseEnd_2853850 < baseStart_2853850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853880 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 4, 4]
def baseStart_2853880 : Nat := 118140960795 + 2853880 * 2 ^ 59
def prefixEnd_2853880 : Nat := 4983230072969 + 3 ^ 40 * 2853880 * 2
def baseEnd_2853880 : Nat := 976941446835599610050167

theorem tailTrace_2853880 : CollatzResearch.WordTrace tailWord_2853880 prefixEnd_2853880 976941446835599610050167 := by
  unfold tailWord_2853880
  simp only [CollatzResearch.WordTrace]
  refine ⟨52044777450443819372451547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69393036600591759163268729 52044777450443819372451547)
  ·
    refine ⟨78067166175665729058677321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52044777450443819372451547 78067166175665729058677321)
    ·
      refine ⟨58550374631749296794007991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78067166175665729058677321 58550374631749296794007991)
      ·
        refine ⟨87825561947623945191011987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58550374631749296794007991 87825561947623945191011987)
        ·
          refine ⟨131738342921435917786517981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87825561947623945191011987 131738342921435917786517981)
          ·
            refine ⟨49401878595538469169944243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131738342921435917786517981 49401878595538469169944243)
            ·
              refine ⟨74102817893307703754916365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49401878595538469169944243 74102817893307703754916365)
              ·
                refine ⟨27788556709990388908093637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74102817893307703754916365 27788556709990388908093637)
                ·
                  refine ⟨5210354383123197920267557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27788556709990388908093637 5210354383123197920267557)
                  ·
                    refine ⟨976941446835599610050167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5210354383123197920267557 976941446835599610050167)
                    ·
                      rfl

theorem cell22_2853880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_2853880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853880 prefixEnd_2853880 := by exact prefixLift 2853880
  have htrace : WordTrace (prefixWord ++ tailWord_2853880) baseStart_2853880 baseEnd_2853880 := by
    simpa [prefixWord, tailWord_2853880, baseEnd_2853880] using wordTrace_append hprefix tailTrace_2853880
  have hstable : (prefixWord ++ tailWord_2853880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853880).length < 2 ^ (prefixWord ++ tailWord_2853880).sum := by decide
  have hdescent : baseEnd_2853880 < baseStart_2853880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853895 : List Nat := [1, 1, 4, 3, 1, 1, 2, 9]
def baseStart_2853895 : Nat := 118140960795 + 2853895 * 2 ^ 59
def prefixEnd_2853895 : Nat := 4983230072969 + 3 ^ 40 * 2853895 * 2
def baseEnd_2853895 : Nat := 108549620182460507880569

theorem tailTrace_2853895 : CollatzResearch.WordTrace tailWord_2853895 prefixEnd_2853895 108549620182460507880569 := by
  unfold tailWord_2853895
  simp only [CollatzResearch.WordTrace]
  refine ⟨104090101995833296306699139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69393401330555530871132759 104090101995833296306699139)
  ·
    refine ⟨156135152993749944460048709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104090101995833296306699139 156135152993749944460048709)
    ·
      refine ⟨29275341186328114586259133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156135152993749944460048709 29275341186328114586259133)
      ·
        refine ⟨10978252944873042969847175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29275341186328114586259133 10978252944873042969847175)
        ·
          refine ⟨16467379417309564454770763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10978252944873042969847175 16467379417309564454770763)
          ·
            refine ⟨24701069125964346682156145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16467379417309564454770763 24701069125964346682156145)
            ·
              refine ⟨18525801844473260011617109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24701069125964346682156145 18525801844473260011617109)
              ·
                refine ⟨108549620182460507880569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18525801844473260011617109 108549620182460507880569)
                ·
                  rfl

theorem cell22_2853895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 9].length) (baseStart_2853895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853895 prefixEnd_2853895 := by exact prefixLift 2853895
  have htrace : WordTrace (prefixWord ++ tailWord_2853895) baseStart_2853895 baseEnd_2853895 := by
    simpa [prefixWord, tailWord_2853895, baseEnd_2853895] using wordTrace_append hprefix tailTrace_2853895
  have hstable : (prefixWord ++ tailWord_2853895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853895).length < 2 ^ (prefixWord ++ tailWord_2853895).sum := by decide
  have hdescent : baseEnd_2853895 < baseStart_2853895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853912 : List Nat := [2, 1, 2, 3, 2, 2, 4, 6]
def baseStart_2853912 : Nat := 118140960795 + 2853912 * 2 ^ 59
def prefixEnd_2853912 : Nat := 4983230072969 + 3 ^ 40 * 2853912 * 2
def baseEnd_2853912 : Nat := 108550266787729132583341

theorem tailTrace_2853912 : CollatzResearch.WordTrace tailWord_2853912 prefixEnd_2853912 108550266787729132583341 := by
  unfold tailWord_2853912
  simp only [CollatzResearch.WordTrace]
  refine ⟨52045361018385854105033995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69393814691181138806711993 52045361018385854105033995)
  ·
    refine ⟨78068041527578781157550993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52045361018385854105033995 78068041527578781157550993)
    ·
      refine ⟨58551031145684085868163245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78068041527578781157550993 58551031145684085868163245)
      ·
        refine ⟨21956636679631532200561217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58551031145684085868163245 21956636679631532200561217)
        ·
          refine ⟨16467477509723649150420913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21956636679631532200561217 16467477509723649150420913)
          ·
            refine ⟨12350608132292736862815685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16467477509723649150420913 12350608132292736862815685)
            ·
              refine ⟨2315739024804888161777941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12350608132292736862815685 2315739024804888161777941)
              ·
                refine ⟨108550266787729132583341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2315739024804888161777941 108550266787729132583341)
                ·
                  rfl

theorem cell22_2853912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 6].length) (baseStart_2853912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853912 prefixEnd_2853912 := by exact prefixLift 2853912
  have htrace : WordTrace (prefixWord ++ tailWord_2853912) baseStart_2853912 baseEnd_2853912 := by
    simpa [prefixWord, tailWord_2853912, baseEnd_2853912] using wordTrace_append hprefix tailTrace_2853912
  have hstable : (prefixWord ++ tailWord_2853912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853912).length < 2 ^ (prefixWord ++ tailWord_2853912).sum := by decide
  have hdescent : baseEnd_2853912 < baseStart_2853912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853944 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 3, 3]
def baseStart_2853944 : Nat := 118140960795 + 2853944 * 2 ^ 59
def prefixEnd_2853944 : Nat := 4983230072969 + 3 ^ 40 * 2853944 * 2
def baseEnd_2853944 : Nat := 976963355343524776449971

theorem tailTrace_2853944 : CollatzResearch.WordTrace tailWord_2853944 prefixEnd_2853944 976963355343524776449971 := by
  unfold tailWord_2853944
  simp only [CollatzResearch.WordTrace]
  refine ⟨52045944586327888837616443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69394592781770518450155257 52045944586327888837616443)
  ·
    refine ⟨78068916879491833256424665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52045944586327888837616443 78068916879491833256424665)
    ·
      refine ⟨58551687659618874942318499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78068916879491833256424665 58551687659618874942318499)
      ·
        refine ⟨87827531489428312413477749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58551687659618874942318499 87827531489428312413477749)
        ·
          refine ⟨8233831077133904288763539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87827531489428312413477749 8233831077133904288763539)
          ·
            refine ⟨12350746615700856433145309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8233831077133904288763539 12350746615700856433145309)
            ·
              refine ⟨4631529980887821162429491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12350746615700856433145309 4631529980887821162429491)
              ·
                refine ⟨6947294971331731743644237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4631529980887821162429491 6947294971331731743644237)
                ·
                  refine ⟨2605235614249399403866589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6947294971331731743644237 2605235614249399403866589)
                  ·
                    refine ⟨976963355343524776449971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2605235614249399403866589 976963355343524776449971)
                    ·
                      rfl

theorem cell22_2853944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_2853944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853944 prefixEnd_2853944 := by exact prefixLift 2853944
  have htrace : WordTrace (prefixWord ++ tailWord_2853944) baseStart_2853944 baseEnd_2853944 := by
    simpa [prefixWord, tailWord_2853944, baseEnd_2853944] using wordTrace_append hprefix tailTrace_2853944
  have hstable : (prefixWord ++ tailWord_2853944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853944).length < 2 ^ (prefixWord ++ tailWord_2853944).sum := by decide
  have hdescent : baseEnd_2853944 < baseStart_2853944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853955 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 1, 7]
def baseStart_2853955 : Nat := 118140960795 + 2853955 * 2 ^ 59
def prefixEnd_2853955 : Nat := 4983230072969 + 3 ^ 40 * 2853955 * 2
def baseEnd_2853955 : Nat := 976967120868324414424937

theorem tailTrace_2853955 : CollatzResearch.WordTrace tailWord_2853955 prefixEnd_2853955 976967120868324414424937 := by
  unfold tailWord_2853955
  simp only [CollatzResearch.WordTrace]
  refine ⟨104092290375615926553883319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69394860250410617702588879 104092290375615926553883319)
  ·
    refine ⟨156138435563423889830824979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104092290375615926553883319 156138435563423889830824979)
    ·
      refine ⟨234207653345135834746237469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156138435563423889830824979 234207653345135834746237469)
      ·
        refine ⟨87827870004425938029839051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234207653345135834746237469 87827870004425938029839051)
        ·
          refine ⟨131741805006638907044758577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87827870004425938029839051 131741805006638907044758577)
          ·
            refine ⟨98806353754979180283568933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131741805006638907044758577 98806353754979180283568933)
            ·
              refine ⟨18526191329058596303169175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98806353754979180283568933 18526191329058596303169175)
              ·
                refine ⟨27789286993587894454753763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18526191329058596303169175 27789286993587894454753763)
                ·
                  refine ⟨41683930490381841682130645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27789286993587894454753763 41683930490381841682130645)
                  ·
                    refine ⟨976967120868324414424937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41683930490381841682130645 976967120868324414424937)
                    ·
                      rfl

theorem cell22_2853955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_2853955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2853955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2853955 prefixEnd_2853955 := by exact prefixLift 2853955
  have htrace : WordTrace (prefixWord ++ tailWord_2853955) baseStart_2853955 baseEnd_2853955 := by
    simpa [prefixWord, tailWord_2853955, baseEnd_2853955] using wordTrace_append hprefix tailTrace_2853955
  have hstable : (prefixWord ++ tailWord_2853955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853955).length < 2 ^ (prefixWord ++ tailWord_2853955).sum := by decide
  have hdescent : baseEnd_2853955 < baseStart_2853955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854002 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 6]
def baseStart_2854002 : Nat := 118140960795 + 2854002 * 2 ^ 59
def prefixEnd_2854002 : Nat := 4983230072969 + 3 ^ 40 * 2854002 * 2
def baseEnd_2854002 : Nat := 325661069976277319499931

theorem tailTrace_2854002 : CollatzResearch.WordTrace tailWord_2854002 prefixEnd_2854002 325661069976277319499931 := by
  unfold tailWord_2854002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26023501151611413395211065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69396003070963769053896173 26023501151611413395211065)
  ·
    refine ⟨19517625863708560046408299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26023501151611413395211065 19517625863708560046408299)
    ·
      refine ⟨29276438795562840069612449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19517625863708560046408299 29276438795562840069612449)
      ·
        refine ⟨21957329096672130052209337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29276438795562840069612449 21957329096672130052209337)
        ·
          refine ⟨16467996822504097539157003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21957329096672130052209337 16467996822504097539157003)
          ·
            refine ⟨24701995233756146308735505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16467996822504097539157003 24701995233756146308735505)
            ·
              refine ⟨18526496425317109731551629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24701995233756146308735505 18526496425317109731551629)
              ·
                refine ⟨6947436159493916149331861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18526496425317109731551629 6947436159493916149331861)
                ·
                  refine ⟨325661069976277319499931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6947436159493916149331861 325661069976277319499931)
                  ·
                    rfl

theorem cell22_2854002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_2854002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854002 prefixEnd_2854002 := by exact prefixLift 2854002
  have htrace : WordTrace (prefixWord ++ tailWord_2854002) baseStart_2854002 baseEnd_2854002 := by
    simpa [prefixWord, tailWord_2854002, baseEnd_2854002] using wordTrace_append hprefix tailTrace_2854002
  have hstable : (prefixWord ++ tailWord_2854002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854002).length < 2 ^ (prefixWord ++ tailWord_2854002).sum := by decide
  have hdescent : baseEnd_2854002 < baseStart_2854002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854032 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 2, 4]
def baseStart_2854032 : Nat := 118140960795 + 2854032 * 2 ^ 59
def prefixEnd_2854032 : Nat := 4983230072969 + 3 ^ 40 * 2854032 * 2
def baseEnd_2854032 : Nat := 976993479541921880249701

theorem tailTrace_2854032 : CollatzResearch.WordTrace tailWord_2854032 prefixEnd_2854032 976993479541921880249701 := by
  unfold tailWord_2854032
  simp only [CollatzResearch.WordTrace]
  refine ⟨52047549398168484352218175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69396732530891312469624233 52047549398168484352218175)
  ·
    refine ⟨78071324097252726528327263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52047549398168484352218175 78071324097252726528327263)
    ·
      refine ⟨117106986145879089792490895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78071324097252726528327263 117106986145879089792490895)
      ·
        refine ⟨175660479218818634688736343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117106986145879089792490895 175660479218818634688736343)
        ·
          refine ⟨263490718828227952033104515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175660479218818634688736343 263490718828227952033104515)
          ·
            refine ⟨395236078242341928049656773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263490718828227952033104515 395236078242341928049656773)
            ·
              refine ⟨74106764670439111509310645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 395236078242341928049656773 74106764670439111509310645)
              ·
                refine ⟨6947509187853666703997873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74106764670439111509310645 6947509187853666703997873)
                ·
                  refine ⟨5210631890890250027998405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6947509187853666703997873 5210631890890250027998405)
                  ·
                    refine ⟨976993479541921880249701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5210631890890250027998405 976993479541921880249701)
                    ·
                      rfl

theorem cell22_2854032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_2854032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854032 prefixEnd_2854032 := by exact prefixLift 2854032
  have htrace : WordTrace (prefixWord ++ tailWord_2854032) baseStart_2854032 baseEnd_2854032 := by
    simpa [prefixWord, tailWord_2854032, baseEnd_2854032] using wordTrace_append hprefix tailTrace_2854032
  have hstable : (prefixWord ++ tailWord_2854032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854032).length < 2 ^ (prefixWord ++ tailWord_2854032).sum := by decide
  have hdescent : baseEnd_2854032 < baseStart_2854032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854034 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_2854034 : Nat := 118140960795 + 2854034 * 2 ^ 59
def prefixEnd_2854034 : Nat := 4983230072969 + 3 ^ 40 * 2854034 * 2
def baseEnd_2854034 : Nat := 976994164182794541699695

theorem tailTrace_2854034 : CollatzResearch.WordTrace tailWord_2854034 prefixEnd_2854034 976994164182794541699695 := by
  unfold tailWord_2854034
  simp only [CollatzResearch.WordTrace]
  refine ⟨26023792935582430761502289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69396781161553148697339437 26023792935582430761502289)
  ·
    refine ⟨19517844701686823071126717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26023792935582430761502289 19517844701686823071126717)
    ·
      refine ⟨7319191763132558651672519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19517844701686823071126717 7319191763132558651672519)
      ·
        refine ⟨10978787644698837977508779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7319191763132558651672519 10978787644698837977508779)
        ·
          refine ⟨16468181467048256966263169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10978787644698837977508779 16468181467048256966263169)
          ·
            refine ⟨12351136100286192724697377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16468181467048256966263169 12351136100286192724697377)
            ·
              refine ⟨9263352075214644543523033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12351136100286192724697377 9263352075214644543523033)
              ·
                refine ⟨6947514056410983407642275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9263352075214644543523033 6947514056410983407642275)
                ·
                  refine ⟨10421271084616475111463413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947514056410983407642275 10421271084616475111463413)
                  ·
                    refine ⟨976994164182794541699695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10421271084616475111463413 976994164182794541699695)
                    ·
                      rfl

theorem cell22_2854034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_2854034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854034 prefixEnd_2854034 := by exact prefixLift 2854034
  have htrace : WordTrace (prefixWord ++ tailWord_2854034) baseStart_2854034 baseEnd_2854034 := by
    simpa [prefixWord, tailWord_2854034, baseEnd_2854034] using wordTrace_append hprefix tailTrace_2854034
  have hstable : (prefixWord ++ tailWord_2854034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854034).length < 2 ^ (prefixWord ++ tailWord_2854034).sum := by decide
  have hdescent : baseEnd_2854034 < baseStart_2854034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854077 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2854077 : Nat := 118140960795 + 2854077 * 2 ^ 59
def prefixEnd_2854077 : Nat := 4983230072969 + 3 ^ 40 * 2854077 * 2
def baseEnd_2854077 : Nat := 977008883961556762874563

theorem tailTrace_2854077 : CollatzResearch.WordTrace tailWord_2854077 prefixEnd_2854077 977008883961556762874563 := by
  unfold tailWord_2854077
  simp only [CollatzResearch.WordTrace]
  refine ⟨104096740081173941389824485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69397826720782627593216323 104096740081173941389824485)
  ·
    refine ⟨19518138765220114010592091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104096740081173941389824485 19518138765220114010592091)
    ·
      refine ⟨29277208147830171015888137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19518138765220114010592091 29277208147830171015888137)
      ·
        refine ⟨21957906110872628261916103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29277208147830171015888137 21957906110872628261916103)
        ·
          refine ⟨32936859166308942392874155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21957906110872628261916103 32936859166308942392874155)
          ·
            refine ⟨49405288749463413589311233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32936859166308942392874155 49405288749463413589311233)
            ·
              refine ⟨37053966562097560191983425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49405288749463413589311233 37053966562097560191983425)
              ·
                refine ⟨27790474921573170143987569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37053966562097560191983425 27790474921573170143987569)
                ·
                  refine ⟨20842856191179877607990677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27790474921573170143987569 20842856191179877607990677)
                  ·
                    refine ⟨977008883961556762874563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20842856191179877607990677 977008883961556762874563)
                    ·
                      rfl

theorem cell22_2854077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2854077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854077 prefixEnd_2854077 := by exact prefixLift 2854077
  have htrace : WordTrace (prefixWord ++ tailWord_2854077) baseStart_2854077 baseEnd_2854077 := by
    simpa [prefixWord, tailWord_2854077, baseEnd_2854077] using wordTrace_append hprefix tailTrace_2854077
  have hstable : (prefixWord ++ tailWord_2854077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854077).length < 2 ^ (prefixWord ++ tailWord_2854077).sum := by decide
  have hdescent : baseEnd_2854077 < baseStart_2854077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854079 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 3, 3]
def baseStart_2854079 : Nat := 118140960795 + 2854079 * 2 ^ 59
def prefixEnd_2854079 : Nat := 4983230072969 + 3 ^ 40 * 2854079 * 2
def baseEnd_2854079 : Nat := 977009568602429424324557

theorem tailTrace_2854079 : CollatzResearch.WordTrace tailWord_2854079 prefixEnd_2854079 977009568602429424324557 := by
  unfold tailWord_2854079
  simp only [CollatzResearch.WordTrace]
  refine ⟨104096813027166695731397291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69397875351444463820931527 104096813027166695731397291)
  ·
    refine ⟨156145219540750043597095937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104096813027166695731397291 156145219540750043597095937)
    ·
      refine ⟨117108914655562532697821953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156145219540750043597095937 117108914655562532697821953)
      ·
        refine ⟨87831685991671899523366465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117108914655562532697821953 87831685991671899523366465)
        ·
          refine ⟨65873764493753924642524849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87831685991671899523366465 65873764493753924642524849)
          ·
            refine ⟨49405323370315443481893637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65873764493753924642524849 49405323370315443481893637)
            ·
              refine ⟨9263498131934145652855057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49405323370315443481893637 9263498131934145652855057)
              ·
                refine ⟨6947623598950609239641293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9263498131934145652855057 6947623598950609239641293)
                ·
                  refine ⟨2605358849606478464865485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6947623598950609239641293 2605358849606478464865485)
                  ·
                    refine ⟨977009568602429424324557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2605358849606478464865485 977009568602429424324557)
                    ·
                      rfl

theorem cell22_2854079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 3].length) (baseStart_2854079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854079 prefixEnd_2854079 := by exact prefixLift 2854079
  have htrace : WordTrace (prefixWord ++ tailWord_2854079) baseStart_2854079 baseEnd_2854079 := by
    simpa [prefixWord, tailWord_2854079, baseEnd_2854079] using wordTrace_append hprefix tailTrace_2854079
  have hstable : (prefixWord ++ tailWord_2854079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854079).length < 2 ^ (prefixWord ++ tailWord_2854079).sum := by decide
  have hdescent : baseEnd_2854079 < baseStart_2854079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854081 : List Nat := [1, 2, 6, 1, 1, 1, 4, 6]
def baseStart_2854081 : Nat := 118140960795 + 2854081 * 2 ^ 59
def prefixEnd_2854081 : Nat := 4983230072969 + 3 ^ 40 * 2854081 * 2
def baseEnd_2854081 : Nat := 108556694804811342863839

theorem tailTrace_2854081 : CollatzResearch.WordTrace tailWord_2854081 prefixEnd_2854081 108556694804811342863839 := by
  unfold tailWord_2854081
  simp only [CollatzResearch.WordTrace]
  refine ⟨104096885973159450072970097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69397923982106300048646731 104096885973159450072970097)
  ·
    refine ⟨78072664479869587554727573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104096885973159450072970097 78072664479869587554727573)
    ·
      refine ⟨3659656147493886916627855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78072664479869587554727573 3659656147493886916627855)
      ·
        refine ⟨5489484221240830374941783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3659656147493886916627855 5489484221240830374941783)
        ·
          refine ⟨8234226331861245562412675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5489484221240830374941783 8234226331861245562412675)
          ·
            refine ⟨12351339497791868343619013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8234226331861245562412675 12351339497791868343619013)
            ·
              refine ⟨2315876155835975314428565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12351339497791868343619013 2315876155835975314428565)
              ·
                refine ⟨108556694804811342863839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2315876155835975314428565 108556694804811342863839)
                ·
                  rfl

theorem cell22_2854081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 6].length) (baseStart_2854081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854081 prefixEnd_2854081 := by exact prefixLift 2854081
  have htrace : WordTrace (prefixWord ++ tailWord_2854081) baseStart_2854081 baseEnd_2854081 := by
    simpa [prefixWord, tailWord_2854081, baseEnd_2854081] using wordTrace_append hprefix tailTrace_2854081
  have hstable : (prefixWord ++ tailWord_2854081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854081).length < 2 ^ (prefixWord ++ tailWord_2854081).sum := by decide
  have hdescent : baseEnd_2854081 < baseStart_2854081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854126 : List Nat := [4, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_2854126 : Nat := 118140960795 + 2854126 * 2 ^ 59
def prefixEnd_2854126 : Nat := 4983230072969 + 3 ^ 40 * 2854126 * 2
def baseEnd_2854126 : Nat := 325675219220978989466471

theorem tailTrace_2854126 : CollatzResearch.WordTrace tailWord_2854126 prefixEnd_2854126 325675219220978989466471 := by
  unfold tailWord_2854126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13012315907249552844794779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69399018171997615172238821 13012315907249552844794779)
  ·
    refine ⟨19518473860874329267192169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13012315907249552844794779 19518473860874329267192169)
    ·
      refine ⟨14638855395655746950394127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19518473860874329267192169 14638855395655746950394127)
      ·
        refine ⟨21958283093483620425591191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14638855395655746950394127 21958283093483620425591191)
        ·
          refine ⟨32937424640225430638386787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21958283093483620425591191 32937424640225430638386787)
          ·
            refine ⟨49406136960338145957580181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32937424640225430638386787 49406136960338145957580181)
            ·
              refine ⟨2315912670015850591761571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49406136960338145957580181 2315912670015850591761571)
              ·
                refine ⟨3473869005023775887642357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2315912670015850591761571 3473869005023775887642357)
                ·
                  refine ⟨325675219220978989466471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3473869005023775887642357 325675219220978989466471)
                  ·
                    rfl

theorem cell22_2854126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_2854126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854126 prefixEnd_2854126 := by exact prefixLift 2854126
  have htrace : WordTrace (prefixWord ++ tailWord_2854126) baseStart_2854126 baseEnd_2854126 := by
    simpa [prefixWord, tailWord_2854126, baseEnd_2854126] using wordTrace_append hprefix tailTrace_2854126
  have hstable : (prefixWord ++ tailWord_2854126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854126).length < 2 ^ (prefixWord ++ tailWord_2854126).sum := by decide
  have hdescent : baseEnd_2854126 < baseStart_2854126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854137 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 8]
def baseStart_2854137 : Nat := 118140960795 + 2854137 * 2 ^ 59
def prefixEnd_2854137 : Nat := 4983230072969 + 3 ^ 40 * 2854137 * 2
def baseEnd_2854137 : Nat := 325676474395912202124793

theorem tailTrace_2854137 : CollatzResearch.WordTrace tailWord_2854137 prefixEnd_2854137 325676474395912202124793 := by
  unfold tailWord_2854137
  simp only [CollatzResearch.WordTrace]
  refine ⟨104098928460956571637008665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69399285640637714424672443 104098928460956571637008665)
  ·
    refine ⟨78074196345717428727756499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104098928460956571637008665 78074196345717428727756499)
    ·
      refine ⟨117111294518576143091634749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78074196345717428727756499 117111294518576143091634749)
      ·
        refine ⟨43916735444466053659363031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117111294518576143091634749 43916735444466053659363031)
        ·
          refine ⟨65875103166699080489044547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43916735444466053659363031 65875103166699080489044547)
          ·
            refine ⟨98812654750048620733566821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65875103166699080489044547 98812654750048620733566821)
            ·
              refine ⟨18527372765634116387543779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98812654750048620733566821 18527372765634116387543779)
              ·
                refine ⟨27791059148451174581315669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18527372765634116387543779 27791059148451174581315669)
                ·
                  refine ⟨325676474395912202124793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27791059148451174581315669 325676474395912202124793)
                  ·
                    rfl

theorem cell22_2854137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_2854137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854137 prefixEnd_2854137 := by exact prefixLift 2854137
  have htrace : WordTrace (prefixWord ++ tailWord_2854137) baseStart_2854137 baseEnd_2854137 := by
    simpa [prefixWord, tailWord_2854137, baseEnd_2854137] using wordTrace_append hprefix tailTrace_2854137
  have hstable : (prefixWord ++ tailWord_2854137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854137).length < 2 ^ (prefixWord ++ tailWord_2854137).sum := by decide
  have hdescent : baseEnd_2854137 < baseStart_2854137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854186 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2854186 : Nat := 118140960795 + 2854186 * 2 ^ 59
def prefixEnd_2854186 : Nat := 4983230072969 + 3 ^ 40 * 2854186 * 2
def baseEnd_2854186 : Nat := 977046196889116811899229

theorem tailTrace_2854186 : CollatzResearch.WordTrace tailWord_2854186 prefixEnd_2854186 977046196889116811899229 := by
  unfold tailWord_2854186
  simp only [CollatzResearch.WordTrace]
  refine ⟨26025178909444763251385603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69400477091852702003694941 26025178909444763251385603)
  ·
    refine ⟨39037768364167144877078405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26025178909444763251385603 39037768364167144877078405)
    ·
      refine ⟨7319581568281339664452201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39037768364167144877078405 7319581568281339664452201)
      ·
        refine ⟨5489686176211004748339151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7319581568281339664452201 5489686176211004748339151)
        ·
          refine ⟨8234529264316507122508727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5489686176211004748339151 8234529264316507122508727)
          ·
            refine ⟨12351793896474760683763091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8234529264316507122508727 12351793896474760683763091)
            ·
              refine ⟨18527690844712141025644637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12351793896474760683763091 18527690844712141025644637)
              ·
                refine ⟨6947884066767052884616739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18527690844712141025644637 6947884066767052884616739)
                ·
                  refine ⟨10421826100150579326925109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947884066767052884616739 10421826100150579326925109)
                  ·
                    refine ⟨977046196889116811899229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10421826100150579326925109 977046196889116811899229)
                    ·
                      rfl

theorem cell22_2854186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2854186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854186 prefixEnd_2854186 := by exact prefixLift 2854186
  have htrace : WordTrace (prefixWord ++ tailWord_2854186) baseStart_2854186 baseEnd_2854186 := by
    simpa [prefixWord, tailWord_2854186, baseEnd_2854186] using wordTrace_append hprefix tailTrace_2854186
  have hstable : (prefixWord ++ tailWord_2854186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854186).length < 2 ^ (prefixWord ++ tailWord_2854186).sum := by decide
  have hdescent : baseEnd_2854186 < baseStart_2854186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854201 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 1, 6]
def baseStart_2854201 : Nat := 118140960795 + 2854201 * 2 ^ 59
def prefixEnd_2854201 : Nat := 4983230072969 + 3 ^ 40 * 2854201 * 2
def baseEnd_2854201 : Nat := 977051331695661772774183

theorem tailTrace_2854201 : CollatzResearch.WordTrace tailWord_2854201 prefixEnd_2854201 977051331695661772774183 := by
  unfold tailWord_2854201
  simp only [CollatzResearch.WordTrace]
  refine ⟨104101262732724710567338457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69400841821816473711558971 104101262732724710567338457)
  ·
    refine ⟨78075947049543532925503843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104101262732724710567338457 78075947049543532925503843)
    ·
      refine ⟨117113920574315299388255765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78075947049543532925503843 117113920574315299388255765)
      ·
        refine ⟨5489715026921029658824489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117113920574315299388255765 5489715026921029658824489)
        ·
          refine ⟨4117286270190772244118367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5489715026921029658824489 4117286270190772244118367)
          ·
            refine ⟨6175929405286158366177551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4117286270190772244118367 6175929405286158366177551)
            ·
              refine ⟨9263894107929237549266327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6175929405286158366177551 9263894107929237549266327)
              ·
                refine ⟨13895841161893856323899491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9263894107929237549266327 13895841161893856323899491)
                ·
                  refine ⟨20843761742840784485849237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13895841161893856323899491 20843761742840784485849237)
                  ·
                    refine ⟨977051331695661772774183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20843761742840784485849237 977051331695661772774183)
                    ·
                      rfl

theorem cell22_2854201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_2854201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854201 prefixEnd_2854201 := by exact prefixLift 2854201
  have htrace : WordTrace (prefixWord ++ tailWord_2854201) baseStart_2854201 baseEnd_2854201 := by
    simpa [prefixWord, tailWord_2854201, baseEnd_2854201] using wordTrace_append hprefix tailTrace_2854201
  have hstable : (prefixWord ++ tailWord_2854201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854201).length < 2 ^ (prefixWord ++ tailWord_2854201).sum := by decide
  have hdescent : baseEnd_2854201 < baseStart_2854201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854205 : List Nat := [1, 4, 1, 5, 1, 1, 2, 3, 4]
def baseStart_2854205 : Nat := 118140960795 + 2854205 * 2 ^ 59
def prefixEnd_2854205 : Nat := 4983230072969 + 3 ^ 40 * 2854205 * 2
def baseEnd_2854205 : Nat := 325684233659135698558057

theorem tailTrace_2854205 : CollatzResearch.WordTrace tailWord_2854205 prefixEnd_2854205 325684233659135698558057 := by
  unfold tailWord_2854205
  simp only [CollatzResearch.WordTrace]
  refine ⟨104101408624710219250484069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69400939083140146166989379 104101408624710219250484069)
  ·
    refine ⟨19519014117133166109465763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104101408624710219250484069 19519014117133166109465763)
    ·
      refine ⟨29278521175699749164198645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19519014117133166109465763 29278521175699749164198645)
      ·
        refine ⟨2744861360221851484143623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29278521175699749164198645 2744861360221851484143623)
        ·
          refine ⟨4117292040332777226215435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2744861360221851484143623 4117292040332777226215435)
          ·
            refine ⟨6175938060499165839323153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4117292040332777226215435 6175938060499165839323153)
            ·
              refine ⟨4631953545374374379492365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6175938060499165839323153 4631953545374374379492365)
              ·
                refine ⟨1736982579515390392309637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4631953545374374379492365 1736982579515390392309637)
                ·
                  refine ⟨325684233659135698558057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1736982579515390392309637 325684233659135698558057)
                  ·
                    rfl

theorem cell22_2854205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_2854205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854205 prefixEnd_2854205 := by exact prefixLift 2854205
  have htrace : WordTrace (prefixWord ++ tailWord_2854205) baseStart_2854205 baseEnd_2854205 := by
    simpa [prefixWord, tailWord_2854205, baseEnd_2854205] using wordTrace_append hprefix tailTrace_2854205
  have hstable : (prefixWord ++ tailWord_2854205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854205).length < 2 ^ (prefixWord ++ tailWord_2854205).sum := by decide
  have hdescent : baseEnd_2854205 < baseStart_2854205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854231 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 3, 3]
def baseStart_2854231 : Nat := 118140960795 + 2854231 * 2 ^ 59
def prefixEnd_2854231 : Nat := 4983230072969 + 3 ^ 40 * 2854231 * 2
def baseEnd_2854231 : Nat := 977061601308751694524091

theorem tailTrace_2854231 : CollatzResearch.WordTrace tailWord_2854231 prefixEnd_2854231 977061601308751694524091 := by
  unfold tailWord_2854231
  simp only [CollatzResearch.WordTrace]
  refine ⟨104102356922616025690930547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69401571281744017127287031 104102356922616025690930547)
  ·
    refine ⟨156153535383924038536395821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104102356922616025690930547 156153535383924038536395821)
    ·
      refine ⟨58557575768971514451148433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156153535383924038536395821 58557575768971514451148433)
      ·
        refine ⟨43918181826728635838361325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58557575768971514451148433 43918181826728635838361325)
        ·
          refine ⟨16469318185023238439385497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43918181826728635838361325 16469318185023238439385497)
          ·
            refine ⟨12351988638767428829539123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16469318185023238439385497 12351988638767428829539123)
            ·
              refine ⟨18527982958151143244308685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12351988638767428829539123 18527982958151143244308685)
              ·
                refine ⟨6947993609306678716615757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18527982958151143244308685 6947993609306678716615757)
                ·
                  refine ⟨2605497603490004518730909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6947993609306678716615757 2605497603490004518730909)
                  ·
                    refine ⟨977061601308751694524091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2605497603490004518730909 977061601308751694524091)
                    ·
                      rfl

theorem cell22_2854231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_2854231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854231 prefixEnd_2854231 := by exact prefixLift 2854231
  have htrace : WordTrace (prefixWord ++ tailWord_2854231) baseStart_2854231 baseEnd_2854231 := by
    simpa [prefixWord, tailWord_2854231, baseEnd_2854231] using wordTrace_append hprefix tailTrace_2854231
  have hstable : (prefixWord ++ tailWord_2854231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854231).length < 2 ^ (prefixWord ++ tailWord_2854231).sum := by decide
  have hdescent : baseEnd_2854231 < baseStart_2854231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854237 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2854237 : Nat := 118140960795 + 2854237 * 2 ^ 59
def prefixEnd_2854237 : Nat := 4983230072969 + 3 ^ 40 * 2854237 * 2
def baseEnd_2854237 : Nat := 977063655231369678874073

theorem tailTrace_2854237 : CollatzResearch.WordTrace tailWord_2854237 prefixEnd_2854237 977063655231369678874073 := by
  unfold tailWord_2854237
  simp only [CollatzResearch.WordTrace]
  refine ⟨104102575760594288715648965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69401717173729525810432643 104102575760594288715648965)
  ·
    refine ⟨19519232955111429134184181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104102575760594288715648965 19519232955111429134184181)
    ·
      refine ⟨1829928089541696481329767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19519232955111429134184181 1829928089541696481329767)
      ·
        refine ⟨2744892134312544721994651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1829928089541696481329767 2744892134312544721994651)
        ·
          refine ⟨4117338201468817082991977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2744892134312544721994651 4117338201468817082991977)
          ·
            refine ⟨3088003651101612812243983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4117338201468817082991977 3088003651101612812243983)
            ·
              refine ⟨4632005476652419218365975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3088003651101612812243983 4632005476652419218365975)
              ·
                refine ⟨6948008214978628827548963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4632005476652419218365975 6948008214978628827548963)
                ·
                  refine ⟨10422012322467943241323445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6948008214978628827548963 10422012322467943241323445)
                  ·
                    refine ⟨977063655231369678874073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10422012322467943241323445 977063655231369678874073)
                    ·
                      rfl

theorem cell22_2854237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2854237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854237 prefixEnd_2854237 := by exact prefixLift 2854237
  have htrace : WordTrace (prefixWord ++ tailWord_2854237) baseStart_2854237 baseEnd_2854237 := by
    simpa [prefixWord, tailWord_2854237, baseEnd_2854237] using wordTrace_append hprefix tailTrace_2854237
  have hstable : (prefixWord ++ tailWord_2854237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854237).length < 2 ^ (prefixWord ++ tailWord_2854237).sum := by decide
  have hdescent : baseEnd_2854237 < baseStart_2854237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854250 : List Nat := [3, 1, 3, 3, 3, 1, 2, 6]
def baseStart_2854250 : Nat := 118140960795 + 2854250 * 2 ^ 59
def prefixEnd_2854250 : Nat := 4983230072969 + 3 ^ 40 * 2854250 * 2
def baseEnd_2854250 : Nat := 108563122821893553144337

theorem tailTrace_2854250 : CollatzResearch.WordTrace tailWord_2854250 prefixEnd_2854250 108563122821893553144337 := by
  unfold tailWord_2854250
  simp only [CollatzResearch.WordTrace]
  refine ⟨26025762477386797983968051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69402033273031461290581469 26025762477386797983968051)
  ·
    refine ⟨39038643716080196975952077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26025762477386797983968051 39038643716080196975952077)
    ·
      refine ⟨14639491393530073865982029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39038643716080196975952077 14639491393530073865982029)
      ·
        refine ⟨5489809272573777699743261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14639491393530073865982029 5489809272573777699743261)
        ·
          refine ⟨2058678477215166637403723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5489809272573777699743261 2058678477215166637403723)
          ·
            refine ⟨3088017715822749956105585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058678477215166637403723 3088017715822749956105585)
            ·
              refine ⟨2316013286867062467079189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3088017715822749956105585 2316013286867062467079189)
              ·
                refine ⟨108563122821893553144337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2316013286867062467079189 108563122821893553144337)
                ·
                  rfl

theorem cell22_2854250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_2854250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854250 prefixEnd_2854250 := by exact prefixLift 2854250
  have htrace : WordTrace (prefixWord ++ tailWord_2854250) baseStart_2854250 baseEnd_2854250 := by
    simpa [prefixWord, tailWord_2854250, baseEnd_2854250] using wordTrace_append hprefix tailTrace_2854250
  have hstable : (prefixWord ++ tailWord_2854250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854250).length < 2 ^ (prefixWord ++ tailWord_2854250).sum := by decide
  have hdescent : baseEnd_2854250 < baseStart_2854250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854319 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 1, 6]
def baseStart_2854319 : Nat := 118140960795 + 2854319 * 2 ^ 59
def prefixEnd_2854319 : Nat := 4983230072969 + 3 ^ 40 * 2854319 * 2
def baseEnd_2854319 : Nat := 977091725507148798323821

theorem tailTrace_2854319 : CollatzResearch.WordTrace tailWord_2854319 prefixEnd_2854319 977091725507148798323821 := by
  unfold tailWord_2854319
  simp only [CollatzResearch.WordTrace]
  refine ⟨104105566546297216720134011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69403711030864811146756007 104105566546297216720134011)
  ·
    refine ⟨156158349819445825080201017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104105566546297216720134011 156158349819445825080201017)
    ·
      refine ⟨117118762364584368810150763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156158349819445825080201017 117118762364584368810150763)
      ·
        refine ⟨175678143546876553215226145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117118762364584368810150763 175678143546876553215226145)
        ·
          refine ⟨131758607660157414911419609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175678143546876553215226145 131758607660157414911419609)
          ·
            refine ⟨98818955745118061183564707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131758607660157414911419609 98818955745118061183564707)
            ·
              refine ⟨148228433617677091775347061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98818955745118061183564707 148228433617677091775347061)
              ·
                refine ⟨13896415651657227353938787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148228433617677091775347061 13896415651657227353938787)
                ·
                  refine ⟨20844623477485841030908181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13896415651657227353938787 20844623477485841030908181)
                  ·
                    refine ⟨977091725507148798323821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20844623477485841030908181 977091725507148798323821)
                    ·
                      rfl

theorem cell22_2854319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_2854319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854319 prefixEnd_2854319 := by exact prefixLift 2854319
  have htrace : WordTrace (prefixWord ++ tailWord_2854319) baseStart_2854319 baseEnd_2854319 := by
    simpa [prefixWord, tailWord_2854319, baseEnd_2854319] using wordTrace_append hprefix tailTrace_2854319
  have hstable : (prefixWord ++ tailWord_2854319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854319).length < 2 ^ (prefixWord ++ tailWord_2854319).sum := by decide
  have hdescent : baseEnd_2854319 < baseStart_2854319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854321 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 1, 5]
def baseStart_2854321 : Nat := 118140960795 + 2854321 * 2 ^ 59
def prefixEnd_2854321 : Nat := 4983230072969 + 3 ^ 40 * 2854321 * 2
def baseEnd_2854321 : Nat := 977092410148021459773815

theorem tailTrace_2854321 : CollatzResearch.WordTrace tailWord_2854321 prefixEnd_2854321 977092410148021459773815 := by
  unfold tailWord_2854321
  simp only [CollatzResearch.WordTrace]
  refine ⟨104105639492289971061706817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69403759661526647374471211 104105639492289971061706817)
  ·
    refine ⟨78079229619217478296280113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104105639492289971061706817 78079229619217478296280113)
    ·
      refine ⟨58559422214413108722210085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78079229619217478296280113 58559422214413108722210085)
      ·
        refine ⟨10979891665202457885414391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58559422214413108722210085 10979891665202457885414391)
        ·
          refine ⟨16469837497803686828121587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10979891665202457885414391 16469837497803686828121587)
          ·
            refine ⟨24704756246705530242182381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16469837497803686828121587 24704756246705530242182381)
            ·
              refine ⟨9264283592514573840818393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24704756246705530242182381 9264283592514573840818393)
              ·
                refine ⟨6948212694385930380613795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9264283592514573840818393 6948212694385930380613795)
                ·
                  refine ⟨10422319041578895570920693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6948212694385930380613795 10422319041578895570920693)
                  ·
                    refine ⟨977092410148021459773815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10422319041578895570920693 977092410148021459773815)
                    ·
                      rfl

theorem cell22_2854321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_2854321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854321 prefixEnd_2854321 := by exact prefixLift 2854321
  have htrace : WordTrace (prefixWord ++ tailWord_2854321) baseStart_2854321 baseEnd_2854321 := by
    simpa [prefixWord, tailWord_2854321, baseEnd_2854321] using wordTrace_append hprefix tailTrace_2854321
  have hstable : (prefixWord ++ tailWord_2854321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854321).length < 2 ^ (prefixWord ++ tailWord_2854321).sum := by decide
  have hdescent : baseEnd_2854321 < baseStart_2854321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854325 : List Nat := [1, 3, 3, 2, 2, 2, 3, 1, 1, 4]
def baseStart_2854325 : Nat := 118140960795 + 2854325 * 2 ^ 59
def prefixEnd_2854325 : Nat := 4983230072969 + 3 ^ 40 * 2854325 * 2
def baseEnd_2854325 : Nat := 977093779429766782673803

theorem tailTrace_2854325 : CollatzResearch.WordTrace tailWord_2854325 prefixEnd_2854325 977093779429766782673803 := by
  unfold tailWord_2854325
  simp only [CollatzResearch.WordTrace]
  refine ⟨104105785384275479744852429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69403856922850319829901619 104105785384275479744852429)
  ·
    refine ⟨39039669519103304904319661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104105785384275479744852429 39039669519103304904319661)
    ·
      refine ⟨14639876069663739339119873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39039669519103304904319661 14639876069663739339119873)
      ·
        refine ⟨10979907052247804504339905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14639876069663739339119873 10979907052247804504339905)
        ·
          refine ⟨8234930289185853378254929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10979907052247804504339905 8234930289185853378254929)
          ·
            refine ⟨6176197716889390033691197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8234930289185853378254929 6176197716889390033691197)
            ·
              refine ⟨2316074143833521262634199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6176197716889390033691197 2316074143833521262634199)
              ·
                refine ⟨3474111215750281893951299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316074143833521262634199 3474111215750281893951299)
                ·
                  refine ⟨5211166823625422840926949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474111215750281893951299 5211166823625422840926949)
                  ·
                    refine ⟨977093779429766782673803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5211166823625422840926949 977093779429766782673803)
                    ·
                      rfl

theorem cell22_2854325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_2854325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854325 prefixEnd_2854325 := by exact prefixLift 2854325
  have htrace : WordTrace (prefixWord ++ tailWord_2854325) baseStart_2854325 baseEnd_2854325 := by
    simpa [prefixWord, tailWord_2854325, baseEnd_2854325] using wordTrace_append hprefix tailTrace_2854325
  have hstable : (prefixWord ++ tailWord_2854325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854325).length < 2 ^ (prefixWord ++ tailWord_2854325).sum := by decide
  have hdescent : baseEnd_2854325 < baseStart_2854325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854336 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 2, 4]
def baseStart_2854336 : Nat := 118140960795 + 2854336 * 2 ^ 59
def prefixEnd_2854336 : Nat := 4983230072969 + 3 ^ 40 * 2854336 * 2
def baseEnd_2854336 : Nat := 977097544954566420648769

theorem tailTrace_2854336 : CollatzResearch.WordTrace tailWord_2854336 prefixEnd_2854336 977097544954566420648769 := by
  unfold tailWord_2854336
  simp only [CollatzResearch.WordTrace]
  refine ⟨52053093293617814311751431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69404124391490419082335241 52053093293617814311751431)
  ·
    refine ⟨78079639940426721467627147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52053093293617814311751431 78079639940426721467627147)
    ·
      refine ⟨117119459910640082201440721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78079639940426721467627147 117119459910640082201440721)
      ·
        refine ⟨87839594932980061651080541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117119459910640082201440721 87839594932980061651080541)
        ·
          refine ⟨32939848099867523119155203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87839594932980061651080541 32939848099867523119155203)
          ·
            refine ⟨49409772149801284678732805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32939848099867523119155203 49409772149801284678732805)
            ·
              refine ⟨9264332278087740877262401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49409772149801284678732805 9264332278087740877262401)
              ·
                refine ⟨6948249208565805657946801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9264332278087740877262401 6948249208565805657946801)
                ·
                  refine ⟨5211186906424354243460101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6948249208565805657946801 5211186906424354243460101)
                  ·
                    refine ⟨977097544954566420648769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5211186906424354243460101 977097544954566420648769)
                    ·
                      rfl

theorem cell22_2854336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_2854336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854336 prefixEnd_2854336 := by exact prefixLift 2854336
  have htrace : WordTrace (prefixWord ++ tailWord_2854336) baseStart_2854336 baseEnd_2854336 := by
    simpa [prefixWord, tailWord_2854336, baseEnd_2854336] using wordTrace_append hprefix tailTrace_2854336
  have hstable : (prefixWord ++ tailWord_2854336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854336).length < 2 ^ (prefixWord ++ tailWord_2854336).sum := by decide
  have hdescent : baseEnd_2854336 < baseStart_2854336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854340 : List Nat := [2, 3, 3, 2, 1, 2, 1, 4, 4]
def baseStart_2854340 : Nat := 118140960795 + 2854340 * 2 ^ 59
def prefixEnd_2854340 : Nat := 4983230072969 + 3 ^ 40 * 2854340 * 2
def baseEnd_2854340 : Nat := 325699638078770581182919

theorem tailTrace_2854340 : CollatzResearch.WordTrace tailWord_2854340 prefixEnd_2854340 325699638078770581182919 := by
  unfold tailWord_2854340
  simp only [CollatzResearch.WordTrace]
  refine ⟨52053166239610568653324237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69404221652814091537765649 52053166239610568653324237)
  ·
    refine ⟨19519937339853963244996589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52053166239610568653324237 19519937339853963244996589)
    ·
      refine ⟨7319976502445236216873721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19519937339853963244996589 7319976502445236216873721)
      ·
        refine ⟨5489982376833927162655291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7319976502445236216873721 5489982376833927162655291)
        ·
          refine ⟨8234973565250890743982937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5489982376833927162655291 8234973565250890743982937)
          ·
            refine ⟨6176230173938168057987203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8234973565250890743982937 6176230173938168057987203)
            ·
              refine ⟨9264345260907252086980805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6176230173938168057987203 9264345260907252086980805)
              ·
                refine ⟨1737064736420109766308901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9264345260907252086980805 1737064736420109766308901)
                ·
                  refine ⟨325699638078770581182919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1737064736420109766308901 325699638078770581182919)
                  ·
                    rfl

theorem cell22_2854340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_2854340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854340 prefixEnd_2854340 := by exact prefixLift 2854340
  have htrace : WordTrace (prefixWord ++ tailWord_2854340) baseStart_2854340 baseEnd_2854340 := by
    simpa [prefixWord, tailWord_2854340, baseEnd_2854340] using wordTrace_append hprefix tailTrace_2854340
  have hstable : (prefixWord ++ tailWord_2854340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854340).length < 2 ^ (prefixWord ++ tailWord_2854340).sum := by decide
  have hdescent : baseEnd_2854340 < baseStart_2854340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854406 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2854406 : Nat := 118140960795 + 2854406 * 2 ^ 59
def prefixEnd_2854406 : Nat := 4983230072969 + 3 ^ 40 * 2854406 * 2
def baseEnd_2854406 : Nat := 977121507385109571398555

theorem tailTrace_2854406 : CollatzResearch.WordTrace tailWord_2854406 prefixEnd_2854406 977121507385109571398555 := by
  unfold tailWord_2854406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3253398115530688455579721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69405826464654687052367381 3253398115530688455579721)
  ·
    refine ⟨2440048586648016341684791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3253398115530688455579721 2440048586648016341684791)
    ·
      refine ⟨3660072879972024512527187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2440048586648016341684791 3660072879972024512527187)
      ·
        refine ⟨5490109319958036768790781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3660072879972024512527187 5490109319958036768790781)
        ·
          refine ⟨2058790994984263788296543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5490109319958036768790781 2058790994984263788296543)
          ·
            refine ⟨3088186492476395682444815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058790994984263788296543 3088186492476395682444815)
            ·
              refine ⟨4632279738714593523667223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3088186492476395682444815 4632279738714593523667223)
              ·
                refine ⟨6948419608071890285500835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4632279738714593523667223 6948419608071890285500835)
                ·
                  refine ⟨10422629412107835428251253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6948419608071890285500835 10422629412107835428251253)
                  ·
                    refine ⟨977121507385109571398555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10422629412107835428251253 977121507385109571398555)
                    ·
                      rfl

theorem cell22_2854406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2854406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854406 prefixEnd_2854406 := by exact prefixLift 2854406
  have htrace : WordTrace (prefixWord ++ tailWord_2854406) baseStart_2854406 baseEnd_2854406 := by
    simpa [prefixWord, tailWord_2854406, baseEnd_2854406] using wordTrace_append hprefix tailTrace_2854406
  have hstable : (prefixWord ++ tailWord_2854406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854406).length < 2 ^ (prefixWord ++ tailWord_2854406).sum := by decide
  have hdescent : baseEnd_2854406 < baseStart_2854406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854509 : List Nat := [1, 5, 1, 1, 4, 2, 2, 2, 4]
def baseStart_2854509 : Nat := 118140960795 + 2854509 * 2 ^ 59
def prefixEnd_2854509 : Nat := 4983230072969 + 3 ^ 40 * 2854509 * 2
def baseEnd_2854509 : Nat := 325718922130017212024413

theorem tailTrace_2854509 : CollatzResearch.WordTrace tailWord_2854509 prefixEnd_2854509 325718922130017212024413 := by
  unfold tailWord_2854509
  simp only [CollatzResearch.WordTrace]
  refine ⟨104112496415608879169550581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69408330943739252779700387 104112496415608879169550581)
  ·
    refine ⟨9760546538963332422145367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104112496415608879169550581 9760546538963332422145367)
    ·
      refine ⟨14640819808444998633218051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9760546538963332422145367 14640819808444998633218051)
      ·
        refine ⟨21961229712667497949827077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14640819808444998633218051 21961229712667497949827077)
        ·
          refine ⟨4117730571125155865592577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21961229712667497949827077 4117730571125155865592577)
          ·
            refine ⟨3088297928343866899194433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4117730571125155865592577 3088297928343866899194433)
            ·
              refine ⟨2316223446257900174395825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3088297928343866899194433 2316223446257900174395825)
              ·
                refine ⟨1737167584693425130796869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316223446257900174395825 1737167584693425130796869)
                ·
                  refine ⟨325718922130017212024413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1737167584693425130796869 325718922130017212024413)
                  ·
                    rfl

theorem cell22_2854509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_2854509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854509 prefixEnd_2854509 := by exact prefixLift 2854509
  have htrace : WordTrace (prefixWord ++ tailWord_2854509) baseStart_2854509 baseEnd_2854509 := by
    simpa [prefixWord, tailWord_2854509, baseEnd_2854509] using wordTrace_append hprefix tailTrace_2854509
  have hstable : (prefixWord ++ tailWord_2854509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854509).length < 2 ^ (prefixWord ++ tailWord_2854509).sum := by decide
  have hdescent : baseEnd_2854509 < baseStart_2854509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854531 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 9]
def baseStart_2854531 : Nat := 118140960795 + 2854531 * 2 ^ 59
def prefixEnd_2854531 : Nat := 4983230072969 + 3 ^ 40 * 2854531 * 2
def baseEnd_2854531 : Nat := 325721432479883637341057

theorem tailTrace_2854531 : CollatzResearch.WordTrace tailWord_2854531 prefixEnd_2854531 325721432479883637341057 := by
  unfold tailWord_2854531
  simp only [CollatzResearch.WordTrace]
  refine ⟨104113298821529176926851447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69408865881019451284567631 104113298821529176926851447)
  ·
    refine ⟨156169948232293765390277171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104113298821529176926851447 156169948232293765390277171)
    ·
      refine ⟨234254922348440648085415757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156169948232293765390277171 234254922348440648085415757)
      ·
        refine ⟨87845595880665243032030909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234254922348440648085415757 87845595880665243032030909)
        ·
          refine ⟨32942098455249466137011591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87845595880665243032030909 32942098455249466137011591)
          ·
            refine ⟨49413147682874199205517387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32942098455249466137011591 49413147682874199205517387)
            ·
              refine ⟨74119721524311298808276081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49413147682874199205517387 74119721524311298808276081)
              ·
                refine ⟨55589791143233474106207061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74119721524311298808276081 55589791143233474106207061)
                ·
                  refine ⟨325721432479883637341057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55589791143233474106207061 325721432479883637341057)
                  ·
                    rfl

theorem cell22_2854531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 9].length) (baseStart_2854531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854531 prefixEnd_2854531 := by exact prefixLift 2854531
  have htrace : WordTrace (prefixWord ++ tailWord_2854531) baseStart_2854531 baseEnd_2854531 := by
    simpa [prefixWord, tailWord_2854531, baseEnd_2854531] using wordTrace_append hprefix tailTrace_2854531
  have hstable : (prefixWord ++ tailWord_2854531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854531).length < 2 ^ (prefixWord ++ tailWord_2854531).sum := by decide
  have hdescent : baseEnd_2854531 < baseStart_2854531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854535 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 3, 3]
def baseStart_2854535 : Nat := 118140960795 + 2854535 * 2 ^ 59
def prefixEnd_2854535 : Nat := 4983230072969 + 3 ^ 40 * 2854535 * 2
def baseEnd_2854535 : Nat := 977165666721396234923159

theorem tailTrace_2854535 : CollatzResearch.WordTrace tailWord_2854535 prefixEnd_2854535 977165666721396234923159 := by
  unfold tailWord_2854535
  simp only [CollatzResearch.WordTrace]
  refine ⟨104113444713514685609997059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69408963142343123739998039 104113444713514685609997059)
  ·
    refine ⟨156170167070272028414995589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104113444713514685609997059 156170167070272028414995589)
    ·
      refine ⟨29281906325676005327811673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156170167070272028414995589 29281906325676005327811673)
      ·
        refine ⟨21961429744257003995858755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29281906325676005327811673 21961429744257003995858755)
        ·
          refine ⟨32942144616385505993788133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21961429744257003995858755 32942144616385505993788133)
          ·
            refine ⟨6176652115572282373835275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32942144616385505993788133 6176652115572282373835275)
            ·
              refine ⟨9264978173358423560752913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6176652115572282373835275 9264978173358423560752913)
              ·
                refine ⟨6948733630018817670564685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9264978173358423560752913 6948733630018817670564685)
                ·
                  refine ⟨2605775111257056626461757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6948733630018817670564685 2605775111257056626461757)
                  ·
                    refine ⟨977165666721396234923159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2605775111257056626461757 977165666721396234923159)
                    ·
                      rfl

theorem cell22_2854535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_2854535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854535 prefixEnd_2854535 := by exact prefixLift 2854535
  have htrace : WordTrace (prefixWord ++ tailWord_2854535) baseStart_2854535 baseEnd_2854535 := by
    simpa [prefixWord, tailWord_2854535, baseEnd_2854535] using wordTrace_append hprefix tailTrace_2854535
  have hstable : (prefixWord ++ tailWord_2854535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854535).length < 2 ^ (prefixWord ++ tailWord_2854535).sum := by decide
  have hdescent : baseEnd_2854535 < baseStart_2854535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854552 : List Nat := [2, 1, 2, 4, 1, 2, 1, 5, 1, 3]
def baseStart_2854552 : Nat := 118140960795 + 2854552 * 2 ^ 59
def prefixEnd_2854552 : Nat := 4983230072969 + 3 ^ 40 * 2854552 * 2
def baseEnd_2854552 : Nat := 977171486168813857248107

theorem tailTrace_2854552 : CollatzResearch.WordTrace tailWord_2854552 prefixEnd_2854552 977171486168813857248107 := by
  unfold tailWord_2854552
  simp only [CollatzResearch.WordTrace]
  refine ⟨52057032377226548756682955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69409376502968731675577273 52057032377226548756682955)
  ·
    refine ⟨78085548565839823135024433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52057032377226548756682955 78085548565839823135024433)
    ·
      refine ⟨58564161424379867351268325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78085548565839823135024433 58564161424379867351268325)
      ·
        refine ⟨10980780267071225128362811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58564161424379867351268325 10980780267071225128362811)
        ·
          refine ⟨16471170400606837692544217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10980780267071225128362811 16471170400606837692544217)
          ·
            refine ⟨12353377800455128269408163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16471170400606837692544217 12353377800455128269408163)
            ·
              refine ⟨18530066700682692404112245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12353377800455128269408163 18530066700682692404112245)
              ·
                refine ⟨1737193753189002412885523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18530066700682692404112245 1737193753189002412885523)
                ·
                  refine ⟨2605790629783503619328285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737193753189002412885523 2605790629783503619328285)
                  ·
                    refine ⟨977171486168813857248107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2605790629783503619328285 977171486168813857248107)
                    ·
                      rfl

theorem cell22_2854552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_2854552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854552 prefixEnd_2854552 := by exact prefixLift 2854552
  have htrace : WordTrace (prefixWord ++ tailWord_2854552) baseStart_2854552 baseEnd_2854552 := by
    simpa [prefixWord, tailWord_2854552, baseEnd_2854552] using wordTrace_append hprefix tailTrace_2854552
  have hstable : (prefixWord ++ tailWord_2854552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854552).length < 2 ^ (prefixWord ++ tailWord_2854552).sum := by decide
  have hdescent : baseEnd_2854552 < baseStart_2854552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854578 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_2854578 : Nat := 118140960795 + 2854578 * 2 ^ 59
def prefixEnd_2854578 : Nat := 4983230072969 + 3 ^ 40 * 2854578 * 2
def baseEnd_2854578 : Nat := 977180386500158456098027

theorem tailTrace_2854578 : CollatzResearch.WordTrace tailWord_2854578 prefixEnd_2854578 977180386500158456098027 := by
  unfold tailWord_2854578
  simp only [CollatzResearch.WordTrace]
  refine ⟨26028753263089725988453097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69410008701572602635874925 26028753263089725988453097)
  ·
    refine ⟨19521564947317294491339823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26028753263089725988453097 19521564947317294491339823)
    ·
      refine ⟨29282347420975941737009735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19521564947317294491339823 29282347420975941737009735)
      ·
        refine ⟨43923521131463912605514603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29282347420975941737009735 43923521131463912605514603)
        ·
          refine ⟨65885281697195868908271905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43923521131463912605514603 65885281697195868908271905)
          ·
            refine ⟨49413961272896901681203929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65885281697195868908271905 49413961272896901681203929)
            ·
              refine ⟨37060470954672676260902947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49413961272896901681203929 37060470954672676260902947)
              ·
                refine ⟨55590706432009014391354421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37060470954672676260902947 55590706432009014391354421)
                ·
                  refine ⟨5211628728000845099189477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55590706432009014391354421 5211628728000845099189477)
                  ·
                    refine ⟨977180386500158456098027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5211628728000845099189477 977180386500158456098027)
                    ·
                      rfl

theorem cell22_2854578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_2854578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854578 prefixEnd_2854578 := by exact prefixLift 2854578
  have htrace : WordTrace (prefixWord ++ tailWord_2854578) baseStart_2854578 baseEnd_2854578 := by
    simpa [prefixWord, tailWord_2854578, baseEnd_2854578] using wordTrace_append hprefix tailTrace_2854578
  have hstable : (prefixWord ++ tailWord_2854578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854578).length < 2 ^ (prefixWord ++ tailWord_2854578).sum := by decide
  have hdescent : baseEnd_2854578 < baseStart_2854578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854612 : List Nat := [2, 4, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_2854612 : Nat := 118140960795 + 2854612 * 2 ^ 59
def prefixEnd_2854612 : Nat := 4983230072969 + 3 ^ 40 * 2854612 * 2
def baseEnd_2854612 : Nat := 977192025394993700747923

theorem tailTrace_2854612 : CollatzResearch.WordTrace tailWord_2854612 prefixEnd_2854612 977192025394993700747923 := by
  unfold tailWord_2854612
  simp only [CollatzResearch.WordTrace]
  refine ⟨52058126567117863880275045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69410835422823818507033393 52058126567117863880275045)
  ·
    refine ⟨9760898731334599477551571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52058126567117863880275045 9760898731334599477551571)
    ·
      refine ⟨14641348097001899216327357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9760898731334599477551571 14641348097001899216327357)
      ·
        refine ⟨5490505536375712206122759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14641348097001899216327357 5490505536375712206122759)
        ·
          refine ⟨8235758304563568309184139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5490505536375712206122759 8235758304563568309184139)
          ·
            refine ⟨12353637456845352463776209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8235758304563568309184139 12353637456845352463776209)
            ·
              refine ⟨9265228092634014347832157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12353637456845352463776209 9265228092634014347832157)
              ·
                refine ⟨3474460534737755380437059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9265228092634014347832157 3474460534737755380437059)
                ·
                  refine ⟨5211690802106633070655589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474460534737755380437059 5211690802106633070655589)
                  ·
                    refine ⟨977192025394993700747923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5211690802106633070655589 977192025394993700747923)
                    ·
                      rfl

theorem cell22_2854612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_2854612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854612 prefixEnd_2854612 := by exact prefixLift 2854612
  have htrace : WordTrace (prefixWord ++ tailWord_2854612) baseStart_2854612 baseEnd_2854612 := by
    simpa [prefixWord, tailWord_2854612, baseEnd_2854612] using wordTrace_append hprefix tailTrace_2854612
  have hstable : (prefixWord ++ tailWord_2854612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854612).length < 2 ^ (prefixWord ++ tailWord_2854612).sum := by decide
  have hdescent : baseEnd_2854612 < baseStart_2854612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854627 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 6]
def baseStart_2854627 : Nat := 118140960795 + 2854627 * 2 ^ 59
def prefixEnd_2854627 : Nat := 4983230072969 + 3 ^ 40 * 2854627 * 2
def baseEnd_2854627 : Nat := 325732386733846220540959

theorem tailTrace_2854627 : CollatzResearch.WordTrace tailWord_2854627 prefixEnd_2854627 325732386733846220540959 := by
  unfold tailWord_2854627
  simp only [CollatzResearch.WordTrace]
  refine ⟨104116800229181385322346135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69411200152787590214897423 104116800229181385322346135)
  ·
    refine ⟨156175200343772077983519203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104116800229181385322346135 156175200343772077983519203)
    ·
      refine ⟨234262800515658116975278805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156175200343772077983519203 234262800515658116975278805)
      ·
        refine ⟨5490534387085737116608097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 234262800515658116975278805 5490534387085737116608097)
        ·
          refine ⟨4117900790314302837456073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5490534387085737116608097 4117900790314302837456073)
          ·
            refine ⟨3088425592735727128092055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4117900790314302837456073 3088425592735727128092055)
            ·
              refine ⟨4632638389103590692138083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3088425592735727128092055 4632638389103590692138083)
              ·
                refine ⟨6948957583655386038207125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4632638389103590692138083 6948957583655386038207125)
                ·
                  refine ⟨325732386733846220540959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6948957583655386038207125 325732386733846220540959)
                  ·
                    rfl

theorem cell22_2854627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 6].length) (baseStart_2854627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854627 prefixEnd_2854627 := by exact prefixLift 2854627
  have htrace : WordTrace (prefixWord ++ tailWord_2854627) baseStart_2854627 baseEnd_2854627 := by
    simpa [prefixWord, tailWord_2854627, baseEnd_2854627] using wordTrace_append hprefix tailTrace_2854627
  have hstable : (prefixWord ++ tailWord_2854627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854627).length < 2 ^ (prefixWord ++ tailWord_2854627).sum := by decide
  have hdescent : baseEnd_2854627 < baseStart_2854627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854642 : List Nat := [3, 2, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_2854642 : Nat := 118140960795 + 2854642 * 2 ^ 59
def prefixEnd_2854642 : Nat := 4983230072969 + 3 ^ 40 * 2854642 * 2
def baseEnd_2854642 : Nat := 977202295008083622497831

theorem tailTrace_2854642 : CollatzResearch.WordTrace tailWord_2854642 prefixEnd_2854642 977202295008083622497831 := by
  unfold tailWord_2854642
  simp only [CollatzResearch.WordTrace]
  refine ⟨26029336831031760721035545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69411564882751361922761453 26029336831031760721035545)
  ·
    refine ⟨19522002623273820540776659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26029336831031760721035545 19522002623273820540776659)
    ·
      refine ⟨29283003934910730811164989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19522002623273820540776659 29283003934910730811164989)
      ·
        refine ⟨10981126475591524054186871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29283003934910730811164989 10981126475591524054186871)
        ·
          refine ⟨16471689713387286081280307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10981126475591524054186871 16471689713387286081280307)
          ·
            refine ⟨24707534570080929121920461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16471689713387286081280307 24707534570080929121920461)
            ·
              refine ⟨9265325463780348420720173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24707534570080929121920461 9265325463780348420720173)
              ·
                refine ⟨3474497048917630657770065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9265325463780348420720173 3474497048917630657770065)
                ·
                  refine ⟨2605872786688222993327549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3474497048917630657770065 2605872786688222993327549)
                  ·
                    refine ⟨977202295008083622497831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2605872786688222993327549 977202295008083622497831)
                    ·
                      rfl

theorem cell22_2854642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_2854642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854642 prefixEnd_2854642 := by exact prefixLift 2854642
  have htrace : WordTrace (prefixWord ++ tailWord_2854642) baseStart_2854642 baseEnd_2854642 := by
    simpa [prefixWord, tailWord_2854642, baseEnd_2854642] using wordTrace_append hprefix tailTrace_2854642
  have hstable : (prefixWord ++ tailWord_2854642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854642).length < 2 ^ (prefixWord ++ tailWord_2854642).sum := by decide
  have hdescent : baseEnd_2854642 < baseStart_2854642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854700 : List Nat := [2, 2, 1, 1, 1, 5, 2, 3, 5]
def baseStart_2854700 : Nat := 118140960795 + 2854700 * 2 ^ 59
def prefixEnd_2854700 : Nat := 4983230072969 + 3 ^ 40 * 2854700 * 2
def baseEnd_2854700 : Nat := 325740716531130268182551

theorem tailTrace_2854700 : CollatzResearch.WordTrace tailWord_2854700 prefixEnd_2854700 325740716531130268182551 := by
  unfold tailWord_2854700
  simp only [CollatzResearch.WordTrace]
  refine ⟨52059731378958459394876777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69412975171944612526502369 52059731378958459394876777)
  ·
    refine ⟨39044798534218844546157583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52059731378958459394876777 39044798534218844546157583)
    ·
      refine ⟨58567197801328266819236375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39044798534218844546157583 58567197801328266819236375)
      ·
        refine ⟨87850796701992400228854563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58567197801328266819236375 87850796701992400228854563)
        ·
          refine ⟨131776195052988600343281845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87850796701992400228854563 131776195052988600343281845)
          ·
            refine ⟨12354018286217681282182673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131776195052988600343281845 12354018286217681282182673)
            ·
              refine ⟨9265513714663260961637005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12354018286217681282182673 9265513714663260961637005)
              ·
                refine ⟨3474567642998722860613877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9265513714663260961637005 3474567642998722860613877)
                ·
                  refine ⟨325740716531130268182551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3474567642998722860613877 325740716531130268182551)
                  ·
                    rfl

theorem cell22_2854700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_2854700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854700 prefixEnd_2854700 := by exact prefixLift 2854700
  have htrace : WordTrace (prefixWord ++ tailWord_2854700) baseStart_2854700 baseEnd_2854700 := by
    simpa [prefixWord, tailWord_2854700, baseEnd_2854700] using wordTrace_append hprefix tailTrace_2854700
  have hstable : (prefixWord ++ tailWord_2854700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854700).length < 2 ^ (prefixWord ++ tailWord_2854700).sum := by decide
  have hdescent : baseEnd_2854700 < baseStart_2854700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854745 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 6]
def baseStart_2854745 : Nat := 118140960795 + 2854745 * 2 ^ 59
def prefixEnd_2854745 : Nat := 4983230072969 + 3 ^ 40 * 2854745 * 2
def baseEnd_2854745 : Nat := 325745851337675229057505

theorem tailTrace_2854745 : CollatzResearch.WordTrace tailWord_2854745 prefixEnd_2854745 325745851337675229057505 := by
  unfold tailWord_2854745
  simp only [CollatzResearch.WordTrace]
  refine ⟨104121104042753891475141689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69414069361835927650094459 104121104042753891475141689)
  ·
    refine ⟨78090828032065418606356267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104121104042753891475141689 78090828032065418606356267)
    ·
      refine ⟨117136242048098127909534401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78090828032065418606356267 117136242048098127909534401)
      ·
        refine ⟨87852181536073595932150801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117136242048098127909534401 87852181536073595932150801)
        ·
          refine ⟨65889136152055196949113101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87852181536073595932150801 65889136152055196949113101)
          ·
            refine ⟨24708426057020698855917413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65889136152055196949113101 24708426057020698855917413)
            ·
              refine ⟨4632829885691381035484515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24708426057020698855917413 4632829885691381035484515)
              ·
                refine ⟨6949244828537071553226773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4632829885691381035484515 6949244828537071553226773)
                ·
                  refine ⟨325745851337675229057505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6949244828537071553226773 325745851337675229057505)
                  ·
                    rfl

theorem cell22_2854745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_2854745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854745 prefixEnd_2854745 := by exact prefixLift 2854745
  have htrace : WordTrace (prefixWord ++ tailWord_2854745) baseStart_2854745 baseEnd_2854745 := by
    simpa [prefixWord, tailWord_2854745, baseEnd_2854745] using wordTrace_append hprefix tailTrace_2854745
  have hstable : (prefixWord ++ tailWord_2854745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854745).length < 2 ^ (prefixWord ++ tailWord_2854745).sum := by decide
  have hdescent : baseEnd_2854745 < baseStart_2854745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854839 : List Nat := [1, 1, 3, 1, 3, 1, 1, 7, 1, 3]
def baseStart_2854839 : Nat := 118140960795 + 2854839 * 2 ^ 59
def prefixEnd_2854839 : Nat := 4983230072969 + 3 ^ 40 * 2854839 * 2
def baseEnd_2854839 : Nat := 977269732134040775322227

theorem tailTrace_2854839 : CollatzResearch.WordTrace tailWord_2854839 prefixEnd_2854839 977269732134040775322227 := by
  unfold tailWord_2854839
  simp only [CollatzResearch.WordTrace]
  refine ⟨104124532504413345529063571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69416355002942230352709047 104124532504413345529063571)
  ·
    refine ⟨156186798756620018293595357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104124532504413345529063571 156186798756620018293595357)
    ·
      refine ⟨58570049533732506860098259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156186798756620018293595357 58570049533732506860098259)
      ·
        refine ⟨87855074300598760290147389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58570049533732506860098259 87855074300598760290147389)
        ·
          refine ⟨32945652862724535108805271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87855074300598760290147389 32945652862724535108805271)
          ·
            refine ⟨49418479294086802663207907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32945652862724535108805271 49418479294086802663207907)
            ·
              refine ⟨74127718941130203994811861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49418479294086802663207907 74127718941130203994811861)
              ·
                refine ⟨1737368412682739156128403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 74127718941130203994811861 1737368412682739156128403)
                ·
                  refine ⟨2606052619024108734192605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737368412682739156128403 2606052619024108734192605)
                  ·
                    refine ⟨977269732134040775322227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2606052619024108734192605 977269732134040775322227)
                    ·
                      rfl

theorem cell22_2854839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_2854839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854839 prefixEnd_2854839 := by exact prefixLift 2854839
  have htrace : WordTrace (prefixWord ++ tailWord_2854839) baseStart_2854839 baseEnd_2854839 := by
    simpa [prefixWord, tailWord_2854839, baseEnd_2854839] using wordTrace_append hprefix tailTrace_2854839
  have hstable : (prefixWord ++ tailWord_2854839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854839).length < 2 ^ (prefixWord ++ tailWord_2854839).sum := by decide
  have hdescent : baseEnd_2854839 < baseStart_2854839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854856 : List Nat := [2, 1, 3, 1, 4, 2, 1, 4, 1, 3]
def baseStart_2854856 : Nat := 118140960795 + 2854856 * 2 ^ 59
def prefixEnd_2854856 : Nat := 4983230072969 + 3 ^ 40 * 2854856 * 2
def baseEnd_2854856 : Nat := 977275551581458397647175

theorem tailTrace_2854856 : CollatzResearch.WordTrace tailWord_2854856 prefixEnd_2854856 977275551581458397647175 := by
  unfold tailWord_2854856
  simp only [CollatzResearch.WordTrace]
  refine ⟨52062576272675878716216211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69416768363567838288288281 52062576272675878716216211)
  ·
    refine ⟨78093864409013818074324317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52062576272675878716216211 78093864409013818074324317)
    ·
      refine ⟨29285199153380181777871619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78093864409013818074324317 29285199153380181777871619)
      ·
        refine ⟨43927798730070272666807429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29285199153380181777871619 43927798730070272666807429)
        ·
          refine ⟨8236462261888176125026393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43927798730070272666807429 8236462261888176125026393)
          ·
            refine ⟨6177346696416132093769795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8236462261888176125026393 6177346696416132093769795)
            ·
              refine ⟨9266020044624198140654693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6177346696416132093769795 9266020044624198140654693)
              ·
                refine ⟨1737378758367037151372755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9266020044624198140654693 1737378758367037151372755)
                ·
                  refine ⟨2606068137550555727059133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737378758367037151372755 2606068137550555727059133)
                  ·
                    refine ⟨977275551581458397647175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2606068137550555727059133 977275551581458397647175)
                    ·
                      rfl

theorem cell22_2854856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_2854856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854856 prefixEnd_2854856 := by exact prefixLift 2854856
  have htrace : WordTrace (prefixWord ++ tailWord_2854856) baseStart_2854856 baseEnd_2854856 := by
    simpa [prefixWord, tailWord_2854856, baseEnd_2854856] using wordTrace_append hprefix tailTrace_2854856
  have hstable : (prefixWord ++ tailWord_2854856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854856).length < 2 ^ (prefixWord ++ tailWord_2854856).sum := by decide
  have hdescent : baseEnd_2854856 < baseStart_2854856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854948 : List Nat := [2, 3, 1, 4, 2, 2, 1, 3, 4]
def baseStart_2854948 : Nat := 118140960795 + 2854948 * 2 ^ 59
def prefixEnd_2854948 : Nat := 4983230072969 + 3 ^ 40 * 2854948 * 2
def baseEnd_2854948 : Nat := 325769015020533608115631

theorem tailTrace_2854948 : CollatzResearch.WordTrace tailWord_2854948 prefixEnd_2854948 325769015020533608115631 := by
  unfold tailWord_2854948
  simp only [CollatzResearch.WordTrace]
  refine ⟨52064254030509228572390749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69419005374012304763187665 52064254030509228572390749)
  ·
    refine ⟨19524095261440960714646531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52064254030509228572390749 19524095261440960714646531)
    ·
      refine ⟨29286142892161441071969797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19524095261440960714646531 29286142892161441071969797)
      ·
        refine ⟨5491151792280270200994337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29286142892161441071969797 5491151792280270200994337)
        ·
          refine ⟨4118363844210202650745753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5491151792280270200994337 4118363844210202650745753)
          ·
            refine ⟨3088772883157651988059315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4118363844210202650745753 3088772883157651988059315)
            ·
              refine ⟨4633159324736477982088973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3088772883157651988059315 4633159324736477982088973)
              ·
                refine ⟨1737434746776179243283365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4633159324736477982088973 1737434746776179243283365)
                ·
                  refine ⟨325769015020533608115631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1737434746776179243283365 325769015020533608115631)
                  ·
                    rfl

theorem cell22_2854948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_2854948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854948 prefixEnd_2854948 := by exact prefixLift 2854948
  have htrace : WordTrace (prefixWord ++ tailWord_2854948) baseStart_2854948 baseEnd_2854948 := by
    simpa [prefixWord, tailWord_2854948, baseEnd_2854948] using wordTrace_append hprefix tailTrace_2854948
  have hstable : (prefixWord ++ tailWord_2854948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854948).length < 2 ^ (prefixWord ++ tailWord_2854948).sum := by decide
  have hdescent : baseEnd_2854948 < baseStart_2854948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854972 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_2854972 : Nat := 118140960795 + 2854972 * 2 ^ 59
def prefixEnd_2854972 : Nat := 4983230072969 + 3 ^ 40 * 2854972 * 2
def baseEnd_2854972 : Nat := 977315260752072761746819

theorem tailTrace_2854972 : CollatzResearch.WordTrace tailWord_2854972 prefixEnd_2854972 977315260752072761746819 := by
  unfold tailWord_2854972
  simp only [CollatzResearch.WordTrace]
  refine ⟨52064691706465754621827585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69419588941954339495770113 52064691706465754621827585)
  ·
    refine ⟨39048518779849315966370689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52064691706465754621827585 39048518779849315966370689)
    ·
      refine ⟨29286389084886986974778017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39048518779849315966370689 29286389084886986974778017)
      ·
        refine ⟨21964791813665240231083513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29286389084886986974778017 21964791813665240231083513)
        ·
          refine ⟨16473593860248930173312635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21964791813665240231083513 16473593860248930173312635)
          ·
            refine ⟨24710390790373395259968953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16473593860248930173312635 24710390790373395259968953)
            ·
              refine ⟨18532793092780046444976715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24710390790373395259968953 18532793092780046444976715)
              ·
                refine ⟨27799189639170069667465073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18532793092780046444976715 27799189639170069667465073)
                ·
                  refine ⟨20849392229377552250598805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27799189639170069667465073 20849392229377552250598805)
                  ·
                    refine ⟨977315260752072761746819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20849392229377552250598805 977315260752072761746819)
                    ·
                      rfl

theorem cell22_2854972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_2854972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854972 prefixEnd_2854972 := by exact prefixLift 2854972
  have htrace : WordTrace (prefixWord ++ tailWord_2854972) baseStart_2854972 baseEnd_2854972 := by
    simpa [prefixWord, tailWord_2854972, baseEnd_2854972] using wordTrace_append hprefix tailTrace_2854972
  have hstable : (prefixWord ++ tailWord_2854972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854972).length < 2 ^ (prefixWord ++ tailWord_2854972).sum := by decide
  have hdescent : baseEnd_2854972 < baseStart_2854972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854987 : List Nat := [1, 1, 1, 1, 3, 1, 2, 7, 5]
def baseStart_2854987 : Nat := 118140960795 + 2854987 * 2 ^ 59
def prefixEnd_2854987 : Nat := 4983230072969 + 3 ^ 40 * 2854987 * 2
def baseEnd_2854987 : Nat := 325773465186205907540591

theorem tailTrace_2854987 : CollatzResearch.WordTrace tailWord_2854987 prefixEnd_2854987 325773465186205907540591 := by
  unfold tailWord_2854987
  simp only [CollatzResearch.WordTrace]
  refine ⟨104129930507877166805451215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69419953671918111203634143 104129930507877166805451215)
  ·
    refine ⟨156194895761815750208176823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104129930507877166805451215 156194895761815750208176823)
    ·
      refine ⟨234292343642723625312265235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156194895761815750208176823 234292343642723625312265235)
      ·
        refine ⟨351438515464085437968397853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234292343642723625312265235 351438515464085437968397853)
        ·
          refine ⟨131789443299032039238149195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351438515464085437968397853 131789443299032039238149195)
          ·
            refine ⟨197684164948548058857223793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131789443299032039238149195 197684164948548058857223793)
            ·
              refine ⟨148263123711411044142917845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197684164948548058857223793 148263123711411044142917845)
              ·
                refine ⟨3474916961986196347099637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 148263123711411044142917845 3474916961986196347099637)
                ·
                  refine ⟨325773465186205907540591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3474916961986196347099637 325773465186205907540591)
                  ·
                    rfl

theorem cell22_2854987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 5].length) (baseStart_2854987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2854987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2854987 prefixEnd_2854987 := by exact prefixLift 2854987
  have htrace : WordTrace (prefixWord ++ tailWord_2854987) baseStart_2854987 baseEnd_2854987 := by
    simpa [prefixWord, tailWord_2854987, baseEnd_2854987] using wordTrace_append hprefix tailTrace_2854987
  have hstable : (prefixWord ++ tailWord_2854987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854987).length < 2 ^ (prefixWord ++ tailWord_2854987).sum := by decide
  have hdescent : baseEnd_2854987 < baseStart_2854987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855032 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 6]
def baseStart_2855032 : Nat := 118140960795 + 2855032 * 2 ^ 59
def prefixEnd_2855032 : Nat := 4983230072969 + 3 ^ 40 * 2855032 * 2
def baseEnd_2855032 : Nat := 325778599992750868415545

theorem tailTrace_2855032 : CollatzResearch.WordTrace tailWord_2855032 prefixEnd_2855032 325778599992750868415545 := by
  unfold tailWord_2855032
  simp only [CollatzResearch.WordTrace]
  refine ⟨52065785896357069745419675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69421047861809426327226233 52065785896357069745419675)
  ·
    refine ⟨78098678844535604618129513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52065785896357069745419675 78098678844535604618129513)
    ·
      refine ⟨58574009133401703463597135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78098678844535604618129513 58574009133401703463597135)
      ·
        refine ⟨87861013700102555195395703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58574009133401703463597135 87861013700102555195395703)
        ·
          refine ⟨131791520550153832793093555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87861013700102555195395703 131791520550153832793093555)
          ·
            refine ⟨197687280825230749189640333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131791520550153832793093555 197687280825230749189640333)
            ·
              refine ⟨74132730309461530946115125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197687280825230749189640333 74132730309461530946115125)
              ·
                refine ⟨6949943466512018526198293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74132730309461530946115125 6949943466512018526198293)
                ·
                  refine ⟨325778599992750868415545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6949943466512018526198293 325778599992750868415545)
                  ·
                    rfl

theorem cell22_2855032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_2855032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855032 prefixEnd_2855032 := by exact prefixLift 2855032
  have htrace : WordTrace (prefixWord ++ tailWord_2855032) baseStart_2855032 baseEnd_2855032 := by
    simpa [prefixWord, tailWord_2855032, baseEnd_2855032] using wordTrace_append hprefix tailTrace_2855032
  have hstable : (prefixWord ++ tailWord_2855032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855032).length < 2 ^ (prefixWord ++ tailWord_2855032).sum := by decide
  have hdescent : baseEnd_2855032 < baseStart_2855032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855077 : List Nat := [1, 3, 1, 2, 1, 3, 11]
def baseStart_2855077 : Nat := 118140960795 + 2855077 * 2 ^ 59
def prefixEnd_2855077 : Nat := 4983230072969 + 3 ^ 40 * 2855077 * 2
def baseEnd_2855077 : Nat := 36198192755477314365611

theorem tailTrace_2855077 : CollatzResearch.WordTrace tailWord_2855077 prefixEnd_2855077 36198192755477314365611 := by
  unfold tailWord_2855077
  simp only [CollatzResearch.WordTrace]
  refine ⟨104133213077551112176227485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69422142051700741450818323 104133213077551112176227485)
  ·
    refine ⟨39049954904081667066085307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104133213077551112176227485 39049954904081667066085307)
    ·
      refine ⟨58574932356122500599127961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39049954904081667066085307 58574932356122500599127961)
      ·
        refine ⟨43931199267091875449345971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58574932356122500599127961 43931199267091875449345971)
        ·
          refine ⟨65896798900637813174018957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43931199267091875449345971 65896798900637813174018957)
          ·
            refine ⟨24711299587739179940257109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65896798900637813174018957 24711299587739179940257109)
            ·
              refine ⟨36198192755477314365611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24711299587739179940257109 36198192755477314365611)
              ·
                rfl

theorem cell22_2855077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 11].length) (baseStart_2855077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855077 prefixEnd_2855077 := by exact prefixLift 2855077
  have htrace : WordTrace (prefixWord ++ tailWord_2855077) baseStart_2855077 baseEnd_2855077 := by
    simpa [prefixWord, tailWord_2855077, baseEnd_2855077] using wordTrace_append hprefix tailTrace_2855077
  have hstable : (prefixWord ++ tailWord_2855077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855077).length < 2 ^ (prefixWord ++ tailWord_2855077).sum := by decide
  have hdescent : baseEnd_2855077 < baseStart_2855077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855107 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 3, 8]
def baseStart_2855107 : Nat := 118140960795 + 2855107 * 2 ^ 59
def prefixEnd_2855107 : Nat := 4983230072969 + 3 ^ 40 * 2855107 * 2
def baseEnd_2855107 : Nat := 977361474010977409621405

theorem tailTrace_2855107 : CollatzResearch.WordTrace tailWord_2855107 prefixEnd_2855107 977361474010977409621405 := by
  unfold tailWord_2855107
  simp only [CollatzResearch.WordTrace]
  refine ⟨104134307267442427299819575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69422871511628284866546383 104134307267442427299819575)
  ·
    refine ⟨156201460901163640949729363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104134307267442427299819575 156201460901163640949729363)
    ·
      refine ⟨234302191351745461424594045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156201460901163640949729363 234302191351745461424594045)
      ·
        refine ⟨87863321756904548034222767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234302191351745461424594045 87863321756904548034222767)
        ·
          refine ⟨131794982635356822051334151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87863321756904548034222767 131794982635356822051334151)
          ·
            refine ⟨197692473953035233077001227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131794982635356822051334151 197692473953035233077001227)
            ·
              refine ⟨296538710929552849615501841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197692473953035233077001227 296538710929552849615501841)
              ·
                refine ⟨222404033197164637211626381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296538710929552849615501841 222404033197164637211626381)
                ·
                  refine ⟨83401512448936738954359893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222404033197164637211626381 83401512448936738954359893)
                  ·
                    refine ⟨977361474010977409621405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83401512448936738954359893 977361474010977409621405)
                    ·
                      rfl

theorem cell22_2855107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_2855107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855107 prefixEnd_2855107 := by exact prefixLift 2855107
  have htrace : WordTrace (prefixWord ++ tailWord_2855107) baseStart_2855107 baseEnd_2855107 := by
    simpa [prefixWord, tailWord_2855107, baseEnd_2855107] using wordTrace_append hprefix tailTrace_2855107
  have hstable : (prefixWord ++ tailWord_2855107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855107).length < 2 ^ (prefixWord ++ tailWord_2855107).sum := by decide
  have hdescent : baseEnd_2855107 < baseStart_2855107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855143 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 3, 3]
def baseStart_2855143 : Nat := 118140960795 + 2855143 * 2 ^ 59
def prefixEnd_2855143 : Nat := 4983230072969 + 3 ^ 40 * 2855143 * 2
def baseEnd_2855143 : Nat := 977373797546685315721295

theorem tailTrace_2855143 : CollatzResearch.WordTrace tailWord_2855143 prefixEnd_2855143 977373797546685315721295 := by
  unfold tailWord_2855143
  simp only [CollatzResearch.WordTrace]
  refine ⟨104135620295312005448130083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69423746863541336965420055 104135620295312005448130083)
  ·
    refine ⟨156203430442968008172195125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104135620295312005448130083 156203430442968008172195125)
    ·
      refine ⟨14644071604028250766143293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156203430442968008172195125 14644071604028250766143293)
      ·
        refine ⟨5491526851510594037303735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14644071604028250766143293 5491526851510594037303735)
        ·
          refine ⟨8237290277265891055955603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491526851510594037303735 8237290277265891055955603)
          ·
            refine ⟨12355935415898836583933405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8237290277265891055955603 12355935415898836583933405)
            ·
              refine ⟨4633475780962063718975027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12355935415898836583933405 4633475780962063718975027)
              ·
                refine ⟨6950213671443095578462541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4633475780962063718975027 6950213671443095578462541)
                ·
                  refine ⟨2606330126791160841923453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6950213671443095578462541 2606330126791160841923453)
                  ·
                    refine ⟨977373797546685315721295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2606330126791160841923453 977373797546685315721295)
                    ·
                      rfl

theorem cell22_2855143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_2855143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855143 prefixEnd_2855143 := by exact prefixLift 2855143
  have htrace : WordTrace (prefixWord ++ tailWord_2855143) baseStart_2855143 baseEnd_2855143 := by
    simpa [prefixWord, tailWord_2855143, baseEnd_2855143] using wordTrace_append hprefix tailTrace_2855143
  have hstable : (prefixWord ++ tailWord_2855143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855143).length < 2 ^ (prefixWord ++ tailWord_2855143).sum := by decide
  have hdescent : baseEnd_2855143 < baseStart_2855143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855194 : List Nat := [3, 1, 1, 3, 5, 1, 2, 2, 1, 3]
def baseStart_2855194 : Nat := 118140960795 + 2855194 * 2 ^ 59
def prefixEnd_2855194 : Nat := 4983230072969 + 3 ^ 40 * 2855194 * 2
def baseEnd_2855194 : Nat := 977391255888938182696139

theorem tailTrace_2855194 : CollatzResearch.WordTrace tailWord_2855194 prefixEnd_2855194 977391255888938182696139 := by
  unfold tailWord_2855194
  simp only [CollatzResearch.WordTrace]
  refine ⟨26034370104531810289559159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69424986945418160772157757 26034370104531810289559159)
  ·
    refine ⟨39051555156797715434338739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26034370104531810289559159 39051555156797715434338739)
    ·
      refine ⟨58577332735196573151508109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39051555156797715434338739 58577332735196573151508109)
      ·
        refine ⟨21966499775698714931815541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58577332735196573151508109 21966499775698714931815541)
        ·
          refine ⟨2059359353971754524857707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21966499775698714931815541 2059359353971754524857707)
          ·
            refine ⟨3089039030957631787286561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059359353971754524857707 3089039030957631787286561)
            ·
              refine ⟨2316779273218223840464921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089039030957631787286561 2316779273218223840464921)
              ·
                refine ⟨1737584454913667880348691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316779273218223840464921 1737584454913667880348691)
                ·
                  refine ⟨2606376682370501820523037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737584454913667880348691 2606376682370501820523037)
                  ·
                    refine ⟨977391255888938182696139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2606376682370501820523037 977391255888938182696139)
                    ·
                      rfl

theorem cell22_2855194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_2855194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855194 prefixEnd_2855194 := by exact prefixLift 2855194
  have htrace : WordTrace (prefixWord ++ tailWord_2855194) baseStart_2855194 baseEnd_2855194 := by
    simpa [prefixWord, tailWord_2855194, baseEnd_2855194] using wordTrace_append hprefix tailTrace_2855194
  have hstable : (prefixWord ++ tailWord_2855194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855194).length < 2 ^ (prefixWord ++ tailWord_2855194).sum := by decide
  have hdescent : baseEnd_2855194 < baseStart_2855194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855318 : List Nat := [5, 3, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2855318 : Nat := 118140960795 + 2855318 * 2 ^ 59
def prefixEnd_2855318 : Nat := 4983230072969 + 3 ^ 40 * 2855318 * 2
def baseEnd_2855318 : Nat := 977433703623043192595759

theorem tailTrace_2855318 : CollatzResearch.WordTrace tailWord_2855318 prefixEnd_2855318 977433703623043192595759 := by
  unfold tailWord_2855318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6508875191854875645984413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69428002046452006890500405 6508875191854875645984413)
  ·
    refine ⟨2440828196945578367244155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6508875191854875645984413 2440828196945578367244155)
    ·
      refine ⟨3661242295418367550866233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2440828196945578367244155 3661242295418367550866233)
      ·
        refine ⟨2745931721563775663149675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3661242295418367550866233 2745931721563775663149675)
        ·
          refine ⟨4118897582345663494724513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2745931721563775663149675 4118897582345663494724513)
          ·
            refine ⟨3089173186759247621043385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4118897582345663494724513 3089173186759247621043385)
            ·
              refine ⟨2316879890069435715782539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089173186759247621043385 2316879890069435715782539)
              ·
                refine ⟨3475319835104153573673809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316879890069435715782539 3475319835104153573673809)
                ·
                  refine ⟨2606489876328115180255357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3475319835104153573673809 2606489876328115180255357)
                  ·
                    refine ⟨977433703623043192595759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2606489876328115180255357 977433703623043192595759)
                    ·
                      rfl

theorem cell22_2855318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2855318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855318 prefixEnd_2855318 := by exact prefixLift 2855318
  have htrace : WordTrace (prefixWord ++ tailWord_2855318) baseStart_2855318 baseEnd_2855318 := by
    simpa [prefixWord, tailWord_2855318, baseEnd_2855318] using wordTrace_append hprefix tailTrace_2855318
  have hstable : (prefixWord ++ tailWord_2855318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855318).length < 2 ^ (prefixWord ++ tailWord_2855318).sum := by decide
  have hdescent : baseEnd_2855318 < baseStart_2855318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855321 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 3, 4]
def baseStart_2855321 : Nat := 118140960795 + 2855321 * 2 ^ 59
def prefixEnd_2855321 : Nat := 4983230072969 + 3 ^ 40 * 2855321 * 2
def baseEnd_2855321 : Nat := 977434730584352184770749

theorem tailTrace_2855321 : CollatzResearch.WordTrace tailWord_2855321 prefixEnd_2855321 977434730584352184770749 := by
  unfold tailWord_2855321
  simp only [CollatzResearch.WordTrace]
  refine ⟨104142112488667141848109817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69428074992444761232073211 104142112488667141848109817)
  ·
    refine ⟨78106584366500356386082363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104142112488667141848109817 78106584366500356386082363)
    ·
      refine ⟨117159876549750534579123545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78106584366500356386082363 117159876549750534579123545)
      ·
        refine ⟨87869907412312900934342659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117159876549750534579123545 87869907412312900934342659)
        ·
          refine ⟨131804861118469351401513989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87869907412312900934342659 131804861118469351401513989)
          ·
            refine ⟨24713411459713003387783873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131804861118469351401513989 24713411459713003387783873)
            ·
              refine ⟨18535058594784752540837905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24713411459713003387783873 18535058594784752540837905)
              ·
                refine ⟨13901293946088564405628429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18535058594784752540837905 13901293946088564405628429)
                ·
                  refine ⟨5212985229783211652110661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13901293946088564405628429 5212985229783211652110661)
                  ·
                    refine ⟨977434730584352184770749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5212985229783211652110661 977434730584352184770749)
                    ·
                      rfl

theorem cell22_2855321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_2855321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855321 prefixEnd_2855321 := by exact prefixLift 2855321
  have htrace : WordTrace (prefixWord ++ tailWord_2855321) baseStart_2855321 baseEnd_2855321 := by
    simpa [prefixWord, tailWord_2855321, baseEnd_2855321] using wordTrace_append hprefix tailTrace_2855321
  have hstable : (prefixWord ++ tailWord_2855321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855321).length < 2 ^ (prefixWord ++ tailWord_2855321).sum := by decide
  have hdescent : baseEnd_2855321 < baseStart_2855321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855351 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 3, 5]
def baseStart_2855351 : Nat := 118140960795 + 2855351 * 2 ^ 59
def prefixEnd_2855351 : Nat := 4983230072969 + 3 ^ 40 * 2855351 * 2
def baseEnd_2855351 : Nat := 977445000197442106520657

theorem tailTrace_2855351 : CollatzResearch.WordTrace tailWord_2855351 prefixEnd_2855351 977445000197442106520657 := by
  unfold tailWord_2855351
  simp only [CollatzResearch.WordTrace]
  refine ⟨104143206678558456971701907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69428804452372304647801271 104143206678558456971701907)
  ·
    refine ⟨156214810017837685457552861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104143206678558456971701907 156214810017837685457552861)
    ·
      refine ⟨58580553756689132046582323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156214810017837685457552861 58580553756689132046582323)
      ·
        refine ⟨87870830635033698069873485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58580553756689132046582323 87870830635033698069873485)
        ·
          refine ⟨32951561488137636776202557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87870830635033698069873485 32951561488137636776202557)
          ·
            refine ⟨12356835558051613791075959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32951561488137636776202557 12356835558051613791075959)
            ·
              refine ⟨18535253337077420686613939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12356835558051613791075959 18535253337077420686613939)
              ·
                refine ⟨27802880005616131029920909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18535253337077420686613939 27802880005616131029920909)
                ·
                  refine ⟨10426080002106049136220341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27802880005616131029920909 10426080002106049136220341)
                  ·
                    refine ⟨977445000197442106520657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10426080002106049136220341 977445000197442106520657)
                    ·
                      rfl

theorem cell22_2855351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_2855351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855351 prefixEnd_2855351 := by exact prefixLift 2855351
  have htrace : WordTrace (prefixWord ++ tailWord_2855351) baseStart_2855351 baseEnd_2855351 := by
    simpa [prefixWord, tailWord_2855351, baseEnd_2855351] using wordTrace_append hprefix tailTrace_2855351
  have hstable : (prefixWord ++ tailWord_2855351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855351).length < 2 ^ (prefixWord ++ tailWord_2855351).sum := by decide
  have hdescent : baseEnd_2855351 < baseStart_2855351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855400 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 2, 4]
def baseStart_2855400 : Nat := 118140960795 + 2855400 * 2 ^ 59
def prefixEnd_2855400 : Nat := 4983230072969 + 3 ^ 40 * 2855400 * 2
def baseEnd_2855400 : Nat := 977461773898822312045507

theorem tailTrace_2855400 : CollatzResearch.WordTrace tailWord_2855400 prefixEnd_2855400 977461773898822312045507 := by
  unfold tailWord_2855400
  simp only [CollatzResearch.WordTrace]
  refine ⟨52072496927690469170117827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69429995903587292226823769 52072496927690469170117827)
  ·
    refine ⟨78108745391535703755176741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52072496927690469170117827 78108745391535703755176741)
    ·
      refine ⟨14645389760912944454095639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78108745391535703755176741 14645389760912944454095639)
      ·
        refine ⟨21968084641369416681143459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14645389760912944454095639 21968084641369416681143459)
        ·
          refine ⟨32952126962054125021715189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21968084641369416681143459 32952126962054125021715189)
          ·
            refine ⟨3089261902692574220785799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32952126962054125021715189 3089261902692574220785799)
            ·
              refine ⟨4633892854038861331178699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089261902692574220785799 4633892854038861331178699)
              ·
                refine ⟨6950839281058291996768049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4633892854038861331178699 6950839281058291996768049)
                ·
                  refine ⟨5213129460793718997576037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6950839281058291996768049 5213129460793718997576037)
                  ·
                    refine ⟨977461773898822312045507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5213129460793718997576037 977461773898822312045507)
                    ·
                      rfl

theorem cell22_2855400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_2855400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855400 prefixEnd_2855400 := by exact prefixLift 2855400
  have htrace : WordTrace (prefixWord ++ tailWord_2855400) baseStart_2855400 baseEnd_2855400 := by
    simpa [prefixWord, tailWord_2855400, baseEnd_2855400] using wordTrace_append hprefix tailTrace_2855400
  have hstable : (prefixWord ++ tailWord_2855400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855400).length < 2 ^ (prefixWord ++ tailWord_2855400).sum := by decide
  have hdescent : baseEnd_2855400 < baseStart_2855400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855441 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 1, 7]
def baseStart_2855441 : Nat := 118140960795 + 2855441 * 2 ^ 59
def prefixEnd_2855441 : Nat := 4983230072969 + 3 ^ 40 * 2855441 * 2
def baseEnd_2855441 : Nat := 977475809036711871770381

theorem tailTrace_2855441 : CollatzResearch.WordTrace tailWord_2855441 prefixEnd_2855441 977475809036711871770381 := by
  unfold tailWord_2855441
  simp only [CollatzResearch.WordTrace]
  refine ⟨104146489248232402342478177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69430992832154934894985451 104146489248232402342478177)
  ·
    refine ⟨78109866936174301756858633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104146489248232402342478177 78109866936174301756858633)
    ·
      refine ⟨58582400202130726317643975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78109866936174301756858633 58582400202130726317643975)
      ·
        refine ⟨87873600303196089476465963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58582400202130726317643975 87873600303196089476465963)
        ·
          refine ⟨131810400454794134214698945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87873600303196089476465963 131810400454794134214698945)
          ·
            refine ⟨98857800341095600661024209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131810400454794134214698945 98857800341095600661024209)
            ·
              refine ⟨74143350255821700495768157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98857800341095600661024209 74143350255821700495768157)
              ·
                refine ⟨27803756345933137685913059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74143350255821700495768157 27803756345933137685913059)
                ·
                  refine ⟨41705634518899706528869589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27803756345933137685913059 41705634518899706528869589)
                  ·
                    refine ⟨977475809036711871770381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41705634518899706528869589 977475809036711871770381)
                    ·
                      rfl

theorem cell22_2855441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_2855441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855441 prefixEnd_2855441 := by exact prefixLift 2855441
  have htrace : WordTrace (prefixWord ++ tailWord_2855441) baseStart_2855441 baseEnd_2855441 := by
    simpa [prefixWord, tailWord_2855441, baseEnd_2855441] using wordTrace_append hprefix tailTrace_2855441
  have hstable : (prefixWord ++ tailWord_2855441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855441).length < 2 ^ (prefixWord ++ tailWord_2855441).sum := by decide
  have hdescent : baseEnd_2855441 < baseStart_2855441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855464 : List Nat := [2, 1, 5, 2, 1, 1, 3, 3, 1, 3]
def baseStart_2855464 : Nat := 118140960795 + 2855464 * 2 ^ 59
def prefixEnd_2855464 : Nat := 4983230072969 + 3 ^ 40 * 2855464 * 2
def baseEnd_2855464 : Nat := 977483682406747478445311

theorem tailTrace_2855464 : CollatzResearch.WordTrace tailWord_2855464 prefixEnd_2855464 977483682406747478445311 := by
  unfold tailWord_2855464
  simp only [CollatzResearch.WordTrace]
  refine ⟨52073664063574538635282723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69431552084766051513710297 52073664063574538635282723)
  ·
    refine ⟨78110496095361807952924085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52073664063574538635282723 78110496095361807952924085)
    ·
      refine ⟨7322859008940169495586633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78110496095361807952924085 7322859008940169495586633)
      ·
        refine ⟨5492144256705127121689975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7322859008940169495586633 5492144256705127121689975)
        ·
          refine ⟨8238216385057690682534963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5492144256705127121689975 8238216385057690682534963)
          ·
            refine ⟨12357324577586536023802445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8238216385057690682534963 12357324577586536023802445)
            ·
              refine ⟨4633996716594951008925917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12357324577586536023802445 4633996716594951008925917)
              ·
                refine ⟨1737748768723106628347219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4633996716594951008925917 1737748768723106628347219)
                ·
                  refine ⟨2606623153084659942520829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737748768723106628347219 2606623153084659942520829)
                  ·
                    refine ⟨977483682406747478445311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2606623153084659942520829 977483682406747478445311)
                    ·
                      rfl

theorem cell22_2855464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_2855464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855464 prefixEnd_2855464 := by exact prefixLift 2855464
  have htrace : WordTrace (prefixWord ++ tailWord_2855464) baseStart_2855464 baseEnd_2855464 := by
    simpa [prefixWord, tailWord_2855464, baseEnd_2855464] using wordTrace_append hprefix tailTrace_2855464
  have hstable : (prefixWord ++ tailWord_2855464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855464).length < 2 ^ (prefixWord ++ tailWord_2855464).sum := by decide
  have hdescent : baseEnd_2855464 < baseStart_2855464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855488 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 6]
def baseStart_2855488 : Nat := 118140960795 + 2855488 * 2 ^ 59
def prefixEnd_2855488 : Nat := 4983230072969 + 3 ^ 40 * 2855488 * 2
def baseEnd_2855488 : Nat := 325830632699073138615079

theorem tailTrace_2855488 : CollatzResearch.WordTrace tailWord_2855488 prefixEnd_2855488 325830632699073138615079 := by
  unfold tailWord_2855488
  simp only [CollatzResearch.WordTrace]
  refine ⟨52074101739531064684719559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69432135652708086246292745 52074101739531064684719559)
  ·
    refine ⟨78111152609296597027079339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52074101739531064684719559 78111152609296597027079339)
    ·
      refine ⟨117166728913944895540619009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78111152609296597027079339 117166728913944895540619009)
      ·
        refine ⟨87875046685458671655464257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117166728913944895540619009 87875046685458671655464257)
        ·
          refine ⟨65906285014094003741598193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87875046685458671655464257 65906285014094003741598193)
          ·
            refine ⟨49429713760570502806198645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65906285014094003741598193 49429713760570502806198645)
            ·
              refine ⟨4634035665053484638081123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49429713760570502806198645 4634035665053484638081123)
              ·
                refine ⟨6951053497580226957121685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4634035665053484638081123 6951053497580226957121685)
                ·
                  refine ⟨325830632699073138615079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6951053497580226957121685 325830632699073138615079)
                  ·
                    rfl

theorem cell22_2855488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_2855488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855488 prefixEnd_2855488 := by exact prefixLift 2855488
  have htrace : WordTrace (prefixWord ++ tailWord_2855488) baseStart_2855488 baseEnd_2855488 := by
    simpa [prefixWord, tailWord_2855488, baseEnd_2855488] using wordTrace_append hprefix tailTrace_2855488
  have hstable : (prefixWord ++ tailWord_2855488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855488).length < 2 ^ (prefixWord ++ tailWord_2855488).sum := by decide
  have hdescent : baseEnd_2855488 < baseStart_2855488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855494 : List Nat := [6, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_2855494 : Nat := 118140960795 + 2855494 * 2 ^ 59
def prefixEnd_2855494 : Nat := 4983230072969 + 3 ^ 40 * 2855494 * 2
def baseEnd_2855494 : Nat := 325831317339945800065073

theorem tailTrace_2855494 : CollatzResearch.WordTrace tailWord_2855494 prefixEnd_2855494 325831317339945800065073 := by
  unfold tailWord_2855494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254638197407512262317423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69432281544693594929438357 3254638197407512262317423)
  ·
    refine ⟨4881957296111268393476135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3254638197407512262317423 4881957296111268393476135)
    ·
      refine ⟨7322935944166902590214203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4881957296111268393476135 7322935944166902590214203)
      ·
        refine ⟨10984403916250353885321305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7322935944166902590214203 10984403916250353885321305)
        ·
          refine ⟨8238302937187765413990979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10984403916250353885321305 8238302937187765413990979)
          ·
            refine ⟨12357454405781648120986469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8238302937187765413990979 12357454405781648120986469)
            ·
              refine ⟨2317022701084059022684963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12357454405781648120986469 2317022701084059022684963)
              ·
                refine ⟨3475534051626088534027445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317022701084059022684963 3475534051626088534027445)
                ·
                  refine ⟨325831317339945800065073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3475534051626088534027445 325831317339945800065073)
                  ·
                    rfl

theorem cell22_2855494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_2855494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855494 prefixEnd_2855494 := by exact prefixLift 2855494
  have htrace : WordTrace (prefixWord ++ tailWord_2855494) baseStart_2855494 baseEnd_2855494 := by
    simpa [prefixWord, tailWord_2855494, baseEnd_2855494] using wordTrace_append hprefix tailTrace_2855494
  have hstable : (prefixWord ++ tailWord_2855494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855494).length < 2 ^ (prefixWord ++ tailWord_2855494).sum := by decide
  have hdescent : baseEnd_2855494 < baseStart_2855494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855533 : List Nat := [1, 5, 1, 1, 3, 11]
def baseStart_2855533 : Nat := 118140960795 + 2855533 * 2 ^ 59
def prefixEnd_2855533 : Nat := 4983230072969 + 3 ^ 40 * 2855533 * 2
def baseEnd_2855533 : Nat := 12067991389096966647779

theorem tailTrace_2855533 : CollatzResearch.WordTrace tailWord_2855533 prefixEnd_2855533 12067991389096966647779 := by
  unfold tailWord_2855533
  simp only [CollatzResearch.WordTrace]
  refine ⟨104149844763899102054827253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69433229842599401369884835 104149844763899102054827253)
  ·
    refine ⟨9764047946615540817640055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104149844763899102054827253 9764047946615540817640055)
    ·
      refine ⟨14646071919923311226460083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9764047946615540817640055 14646071919923311226460083)
      ·
        refine ⟨21969107879884966839690125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14646071919923311226460083 21969107879884966839690125)
        ·
          refine ⟨8238415454956862564883797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21969107879884966839690125 8238415454956862564883797)
          ·
            refine ⟨12067991389096966647779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8238415454956862564883797 12067991389096966647779)
            ·
              rfl

theorem cell22_2855533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 11].length) (baseStart_2855533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855533 prefixEnd_2855533 := by exact prefixLift 2855533
  have htrace : WordTrace (prefixWord ++ tailWord_2855533) baseStart_2855533 baseEnd_2855533 := by
    simpa [prefixWord, tailWord_2855533, baseEnd_2855533] using wordTrace_append hprefix tailTrace_2855533
  have hstable : (prefixWord ++ tailWord_2855533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855533).length < 2 ^ (prefixWord ++ tailWord_2855533).sum := by decide
  have hdescent : baseEnd_2855533 < baseStart_2855533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855582 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_2855582 : Nat := 118140960795 + 2855582 * 2 ^ 59
def prefixEnd_2855582 : Nat := 4983230072969 + 3 ^ 40 * 2855582 * 2
def baseEnd_2855582 : Nat := 977524076218234503994949

theorem tailTrace_2855582 : CollatzResearch.WordTrace tailWord_2855582 prefixEnd_2855582 977524076218234503994949 := by
  unfold tailWord_2855582
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018953992590197927920125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69434421293814388948907333 13018953992590197927920125)
  ·
    refine ⟨4882107747221324222970047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13018953992590197927920125 4882107747221324222970047)
    ·
      refine ⟨7323161620831986334455071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4882107747221324222970047 7323161620831986334455071)
      ·
        refine ⟨10984742431247979501682607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7323161620831986334455071 10984742431247979501682607)
        ·
          refine ⟨16477113646871969252523911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10984742431247979501682607 16477113646871969252523911)
          ·
            refine ⟨24715670470307953878785867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16477113646871969252523911 24715670470307953878785867)
            ·
              refine ⟨37073505705461930818178801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24715670470307953878785867 37073505705461930818178801)
              ·
                refine ⟨27805129279096448113634101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37073505705461930818178801 27805129279096448113634101)
                ·
                  refine ⟨2606730869915292010653197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27805129279096448113634101 2606730869915292010653197)
                  ·
                    refine ⟨977524076218234503994949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2606730869915292010653197 977524076218234503994949)
                    ·
                      rfl

theorem cell22_2855582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_2855582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855582 prefixEnd_2855582 := by exact prefixLift 2855582
  have htrace : WordTrace (prefixWord ++ tailWord_2855582) baseStart_2855582 baseEnd_2855582 := by
    simpa [prefixWord, tailWord_2855582, baseEnd_2855582] using wordTrace_append hprefix tailTrace_2855582
  have hstable : (prefixWord ++ tailWord_2855582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855582).length < 2 ^ (prefixWord ++ tailWord_2855582).sum := by decide
  have hdescent : baseEnd_2855582 < baseStart_2855582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855593 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 2, 5]
def baseStart_2855593 : Nat := 118140960795 + 2855593 * 2 ^ 59
def prefixEnd_2855593 : Nat := 4983230072969 + 3 ^ 40 * 2855593 * 2
def baseEnd_2855593 : Nat := 977527841743034141969915

theorem tailTrace_2855593 : CollatzResearch.WordTrace tailWord_2855593 prefixEnd_2855593 977527841743034141969915 := by
  unfold tailWord_2855593
  simp only [CollatzResearch.WordTrace]
  refine ⟨104152033143681732302011433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69434688762454488201340955 104152033143681732302011433)
  ·
    refine ⟨78114024857761299226508575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104152033143681732302011433 78114024857761299226508575)
    ·
      refine ⟨117171037286641948839762863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78114024857761299226508575 117171037286641948839762863)
      ·
        refine ⟨175756555929962923259644295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117171037286641948839762863 175756555929962923259644295)
        ·
          refine ⟨263634833894944384889466443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175756555929962923259644295 263634833894944384889466443)
          ·
            refine ⟨395452250842416577334199665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263634833894944384889466443 395452250842416577334199665)
            ·
              refine ⟨296589188131812433000649749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395452250842416577334199665 296589188131812433000649749)
              ·
                refine ⟨13902618193678707796905457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 296589188131812433000649749 13902618193678707796905457)
                ·
                  refine ⟨10426963645259030847679093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13902618193678707796905457 10426963645259030847679093)
                  ·
                    refine ⟨977527841743034141969915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10426963645259030847679093 977527841743034141969915)
                    ·
                      rfl

theorem cell22_2855593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_2855593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855593 prefixEnd_2855593 := by exact prefixLift 2855593
  have htrace : WordTrace (prefixWord ++ tailWord_2855593) baseStart_2855593 baseEnd_2855593 := by
    simpa [prefixWord, tailWord_2855593, baseEnd_2855593] using wordTrace_append hprefix tailTrace_2855593
  have hstable : (prefixWord ++ tailWord_2855593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855593).length < 2 ^ (prefixWord ++ tailWord_2855593).sum := by decide
  have hdescent : baseEnd_2855593 < baseStart_2855593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855612 : List Nat := [2, 2, 2, 3, 1, 1, 5, 1, 5]
def baseStart_2855612 : Nat := 118140960795 + 2855612 * 2 ^ 59
def prefixEnd_2855612 : Nat := 4983230072969 + 3 ^ 40 * 2855612 * 2
def baseEnd_2855612 : Nat := 325844781943774808581619

theorem tailTrace_2855612 : CollatzResearch.WordTrace tailWord_2855612 prefixEnd_2855612 325844781943774808581619 := by
  unfold tailWord_2855612
  simp only [CollatzResearch.WordTrace]
  refine ⟨52076363065306449273476545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69435150753741932364635393 52076363065306449273476545)
  ·
    refine ⟨39057272298979836955107409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52076363065306449273476545 39057272298979836955107409)
    ·
      refine ⟨29292954224234877716330557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39057272298979836955107409 29292954224234877716330557)
      ·
        refine ⟨10984857834088079143623959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29292954224234877716330557 10984857834088079143623959)
        ·
          refine ⟨16477286751132118715435939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10984857834088079143623959 16477286751132118715435939)
          ·
            refine ⟨24715930126698178073153909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16477286751132118715435939 24715930126698178073153909)
            ·
              refine ⟨2317118449377954194358179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24715930126698178073153909 2317118449377954194358179)
              ·
                refine ⟨3475677674066931291537269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317118449377954194358179 3475677674066931291537269)
                ·
                  refine ⟨325844781943774808581619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3475677674066931291537269 325844781943774808581619)
                  ·
                    rfl

theorem cell22_2855612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_2855612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855612 prefixEnd_2855612 := by exact prefixLift 2855612
  have htrace : WordTrace (prefixWord ++ tailWord_2855612) baseStart_2855612 baseEnd_2855612 := by
    simpa [prefixWord, tailWord_2855612, baseEnd_2855612] using wordTrace_append hprefix tailTrace_2855612
  have hstable : (prefixWord ++ tailWord_2855612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855612).length < 2 ^ (prefixWord ++ tailWord_2855612).sum := by decide
  have hdescent : baseEnd_2855612 < baseStart_2855612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855623 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 8]
def baseStart_2855623 : Nat := 118140960795 + 2855623 * 2 ^ 59
def prefixEnd_2855623 : Nat := 4983230072969 + 3 ^ 40 * 2855623 * 2
def baseEnd_2855623 : Nat := 325846037118708021239941

theorem tailTrace_2855623 : CollatzResearch.WordTrace tailWord_2855623 prefixEnd_2855623 325846037118708021239941 := by
  unfold tailWord_2855623
  simp only [CollatzResearch.WordTrace]
  refine ⟨104153127333573047425603523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69435418222382031617069015 104153127333573047425603523)
  ·
    refine ⟨156229691000359571138405285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104153127333573047425603523 156229691000359571138405285)
    ·
      refine ⟨29293067062567419588450991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156229691000359571138405285 29293067062567419588450991)
      ·
        refine ⟨43939600593851129382676487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29293067062567419588450991 43939600593851129382676487)
        ·
          refine ⟨65909400890776694074014731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43939600593851129382676487 65909400890776694074014731)
          ·
            refine ⟨98864101336165041111022097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65909400890776694074014731 98864101336165041111022097)
            ·
              refine ⟨74148076002123780833266573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98864101336165041111022097 74148076002123780833266573)
              ·
                refine ⟨27805528500796417812474965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74148076002123780833266573 27805528500796417812474965)
                ·
                  refine ⟨325846037118708021239941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27805528500796417812474965 325846037118708021239941)
                  ·
                    rfl

theorem cell22_2855623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 8].length) (baseStart_2855623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855623 prefixEnd_2855623 := by exact prefixLift 2855623
  have htrace : WordTrace (prefixWord ++ tailWord_2855623) baseStart_2855623 baseEnd_2855623 := by
    simpa [prefixWord, tailWord_2855623, baseEnd_2855623] using wordTrace_append hprefix tailTrace_2855623
  have hstable : (prefixWord ++ tailWord_2855623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855623).length < 2 ^ (prefixWord ++ tailWord_2855623).sum := by decide
  have hdescent : baseEnd_2855623 < baseStart_2855623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855672 : List Nat := [2, 1, 2, 1, 1, 2, 5, 3, 2, 3]
def baseStart_2855672 : Nat := 118140960795 + 2855672 * 2 ^ 59
def prefixEnd_2855672 : Nat := 4983230072969 + 3 ^ 40 * 2855672 * 2
def baseEnd_2855672 : Nat := 977554885057504269244673

theorem tailTrace_2855672 : CollatzResearch.WordTrace tailWord_2855672 prefixEnd_2855672 977554885057504269244673 := by
  unfold tailWord_2855672
  simp only [CollatzResearch.WordTrace]
  refine ⟨52077457255197764397068635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69436609673597019196091513 52077457255197764397068635)
  ·
    refine ⟨78116185882796646595602953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52077457255197764397068635 78116185882796646595602953)
    ·
      refine ⟨58587139412097484946702215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78116185882796646595602953 58587139412097484946702215)
      ·
        refine ⟨87880709118146227420053323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58587139412097484946702215 87880709118146227420053323)
        ·
          refine ⟨131821063677219341130079985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87880709118146227420053323 131821063677219341130079985)
          ·
            refine ⟨98865797757914505847559989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131821063677219341130079985 98865797757914505847559989)
            ·
              refine ⟨9268668539804484923208749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98865797757914505847559989 9268668539804484923208749)
              ·
                refine ⟨3475750702426681846203281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9268668539804484923208749 3475750702426681846203281)
                ·
                  refine ⟨2606813026820011384652461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3475750702426681846203281 2606813026820011384652461)
                  ·
                    refine ⟨977554885057504269244673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2606813026820011384652461 977554885057504269244673)
                    ·
                      rfl

theorem cell22_2855672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_2855672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855672 prefixEnd_2855672 := by exact prefixLift 2855672
  have htrace : WordTrace (prefixWord ++ tailWord_2855672) baseStart_2855672 baseEnd_2855672 := by
    simpa [prefixWord, tailWord_2855672, baseEnd_2855672] using wordTrace_append hprefix tailTrace_2855672
  have hstable : (prefixWord ++ tailWord_2855672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855672).length < 2 ^ (prefixWord ++ tailWord_2855672).sum := by decide
  have hdescent : baseEnd_2855672 < baseStart_2855672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855687 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 2, 4]
def baseStart_2855687 : Nat := 118140960795 + 2855687 * 2 ^ 59
def prefixEnd_2855687 : Nat := 4983230072969 + 3 ^ 40 * 2855687 * 2
def baseEnd_2855687 : Nat := 977560019864049230119627

theorem tailTrace_2855687 : CollatzResearch.WordTrace tailWord_2855687 prefixEnd_2855687 977560019864049230119627 := by
  unfold tailWord_2855687
  simp only [CollatzResearch.WordTrace]
  refine ⟨104155461605341186355933315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69436974403560790903955543 104155461605341186355933315)
  ·
    refine ⟨156233192408011779533899973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104155461605341186355933315 156233192408011779533899973)
    ·
      refine ⟨29293723576502208662606245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156233192408011779533899973 29293723576502208662606245)
      ·
        refine ⟨5492573170594164124238671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29293723576502208662606245 5492573170594164124238671)
        ·
          refine ⟨8238859755891246186358007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5492573170594164124238671 8238859755891246186358007)
          ·
            refine ⟨12358289633836869279537011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8238859755891246186358007 12358289633836869279537011)
            ·
              refine ⟨18537434450755303919305517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12358289633836869279537011 18537434450755303919305517)
              ·
                refine ⟨6951537919033238969739569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18537434450755303919305517 6951537919033238969739569)
                ·
                  refine ⟨5213653439274929227304677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6951537919033238969739569 5213653439274929227304677)
                  ·
                    refine ⟨977560019864049230119627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5213653439274929227304677 977560019864049230119627)
                    ·
                      rfl

theorem cell22_2855687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_2855687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855687 prefixEnd_2855687 := by exact prefixLift 2855687
  have htrace : WordTrace (prefixWord ++ tailWord_2855687) baseStart_2855687 baseEnd_2855687 := by
    simpa [prefixWord, tailWord_2855687, baseEnd_2855687] using wordTrace_append hprefix tailTrace_2855687
  have hstable : (prefixWord ++ tailWord_2855687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855687).length < 2 ^ (prefixWord ++ tailWord_2855687).sum := by decide
  have hdescent : baseEnd_2855687 < baseStart_2855687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855717 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 3, 3]
def baseStart_2855717 : Nat := 118140960795 + 2855717 * 2 ^ 59
def prefixEnd_2855717 : Nat := 4983230072969 + 3 ^ 40 * 2855717 * 2
def baseEnd_2855717 : Nat := 977570289477139151869535

theorem tailTrace_2855717 : CollatzResearch.WordTrace tailWord_2855717 prefixEnd_2855717 977570289477139151869535 := by
  unfold tailWord_2855717
  simp only [CollatzResearch.WordTrace]
  refine ⟨104156555795232501479525405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69437703863488334319683603 104156555795232501479525405)
  ·
    refine ⟨39058708423212188054822027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104156555795232501479525405 39058708423212188054822027)
    ·
      refine ⟨58588062634818282082233041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39058708423212188054822027 58588062634818282082233041)
      ·
        refine ⟨43941046976113711561674781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58588062634818282082233041 43941046976113711561674781)
        ·
          refine ⟨16477892616042641835628043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43941046976113711561674781 16477892616042641835628043)
          ·
            refine ⟨24716838924063962753442065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16477892616042641835628043 24716838924063962753442065)
            ·
              refine ⟨18537629193047972065081549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24716838924063962753442065 18537629193047972065081549)
              ·
                refine ⟨6951610947392989524405581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18537629193047972065081549 6951610947392989524405581)
                ·
                  refine ⟨2606854105272371071652093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6951610947392989524405581 2606854105272371071652093)
                  ·
                    refine ⟨977570289477139151869535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2606854105272371071652093 977570289477139151869535)
                    ·
                      rfl

theorem cell22_2855717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_2855717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855717 prefixEnd_2855717 := by exact prefixLift 2855717
  have htrace : WordTrace (prefixWord ++ tailWord_2855717) baseStart_2855717 baseEnd_2855717 := by
    simpa [prefixWord, tailWord_2855717, baseEnd_2855717] using wordTrace_append hprefix tailTrace_2855717
  have hstable : (prefixWord ++ tailWord_2855717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855717).length < 2 ^ (prefixWord ++ tailWord_2855717).sum := by decide
  have hdescent : baseEnd_2855717 < baseStart_2855717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855807 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 4, 3]
def baseStart_2855807 : Nat := 118140960795 + 2855807 * 2 ^ 59
def prefixEnd_2855807 : Nat := 4983230072969 + 3 ^ 40 * 2855807 * 2
def baseEnd_2855807 : Nat := 977601098316408917119259

theorem tailTrace_2855807 : CollatzResearch.WordTrace tailWord_2855807 prefixEnd_2855807 977601098316408917119259 := by
  unfold tailWord_2855807
  simp only [CollatzResearch.WordTrace]
  refine ⟨104159838364906446850301675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69439892243270964566867783 104159838364906446850301675)
  ·
    refine ⟨156239757547359670275452513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104159838364906446850301675 156239757547359670275452513)
    ·
      refine ⟨117179818160519752706589385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156239757547359670275452513 117179818160519752706589385)
      ·
        refine ⟨87884863620389814529942039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117179818160519752706589385 87884863620389814529942039)
        ·
          refine ⟨131827295430584721794913059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87884863620389814529942039 131827295430584721794913059)
          ·
            refine ⟨197740943145877082692369589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131827295430584721794913059 197740943145877082692369589)
            ·
              refine ⟨18538213419925976502409649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197740943145877082692369589 18538213419925976502409649)
              ·
                refine ⟨13903660064944482376807237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18538213419925976502409649 13903660064944482376807237)
                ·
                  refine ⟨2606936262177090445651357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13903660064944482376807237 2606936262177090445651357)
                  ·
                    refine ⟨977601098316408917119259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2606936262177090445651357 977601098316408917119259)
                    ·
                      rfl

theorem cell22_2855807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 3].length) (baseStart_2855807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855807 prefixEnd_2855807 := by exact prefixLift 2855807
  have htrace : WordTrace (prefixWord ++ tailWord_2855807) baseStart_2855807 baseEnd_2855807 := by
    simpa [prefixWord, tailWord_2855807, baseEnd_2855807] using wordTrace_append hprefix tailTrace_2855807
  have hstable : (prefixWord ++ tailWord_2855807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855807).length < 2 ^ (prefixWord ++ tailWord_2855807).sum := by decide
  have hdescent : baseEnd_2855807 < baseStart_2855807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855820 : List Nat := [2, 2, 1, 2, 1, 2, 12]
def baseStart_2855820 : Nat := 118140960795 + 2855820 * 2 ^ 59
def prefixEnd_2855820 : Nat := 4983230072969 + 3 ^ 40 * 2855820 * 2
def baseEnd_2855820 : Nat := 36207612906743748760897

theorem tailTrace_2855820 : CollatzResearch.WordTrace tailWord_2855820 prefixEnd_2855820 36207612906743748760897 := by
  unfold tailWord_2855820
  simp only [CollatzResearch.WordTrace]
  refine ⟨52080156256929675035262457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69440208342572900047016609 52080156256929675035262457)
  ·
    refine ⟨39060117192697256276446843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52080156256929675035262457 39060117192697256276446843)
    ·
      refine ⟨58590175789045884414670265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39060117192697256276446843 58590175789045884414670265)
      ·
        refine ⟨43942631841784413311002699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58590175789045884414670265 43942631841784413311002699)
        ·
          refine ⟨65913947762676619966504049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43942631841784413311002699 65913947762676619966504049)
          ·
            refine ⟨49435460822007464974878037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65913947762676619966504049 49435460822007464974878037)
            ·
              refine ⟨36207612906743748760897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 49435460822007464974878037 36207612906743748760897)
              ·
                rfl

theorem cell22_2855820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 12].length) (baseStart_2855820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855820 prefixEnd_2855820 := by exact prefixLift 2855820
  have htrace : WordTrace (prefixWord ++ tailWord_2855820) baseStart_2855820 baseEnd_2855820 := by
    simpa [prefixWord, tailWord_2855820, baseEnd_2855820] using wordTrace_append hprefix tailTrace_2855820
  have hstable : (prefixWord ++ tailWord_2855820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855820).length < 2 ^ (prefixWord ++ tailWord_2855820).sum := by decide
  have hdescent : baseEnd_2855820 < baseStart_2855820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855826 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 6]
def baseStart_2855826 : Nat := 118140960795 + 2855826 * 2 ^ 59
def prefixEnd_2855826 : Nat := 4983230072969 + 3 ^ 40 * 2855826 * 2
def baseEnd_2855826 : Nat := 325869200801566400298067

theorem tailTrace_2855826 : CollatzResearch.WordTrace tailWord_2855826 prefixEnd_2855826 325869200801566400298067 := by
  unfold tailWord_2855826
  simp only [CollatzResearch.WordTrace]
  refine ⟨26040132837959403273810833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69440354234558408730162221 26040132837959403273810833)
  ·
    refine ⟨19530099628469552455358125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26040132837959403273810833 19530099628469552455358125)
    ·
      refine ⟨7323787360676082170759297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19530099628469552455358125 7323787360676082170759297)
      ·
        refine ⟨5492840520507061628069473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7323787360676082170759297 5492840520507061628069473)
        ·
          refine ⟨4119630390380296221052105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5492840520507061628069473 4119630390380296221052105)
          ·
            refine ⟨3089722792785222165789079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4119630390380296221052105 3089722792785222165789079)
            ·
              refine ⟨4634584189177833248683619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089722792785222165789079 4634584189177833248683619)
              ·
                refine ⟨6951876283766749873025429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4634584189177833248683619 6951876283766749873025429)
                ·
                  refine ⟨325869200801566400298067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6951876283766749873025429 325869200801566400298067)
                  ·
                    rfl

theorem cell22_2855826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_2855826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855826 prefixEnd_2855826 := by exact prefixLift 2855826
  have htrace : WordTrace (prefixWord ++ tailWord_2855826) baseStart_2855826 baseEnd_2855826 := by
    simpa [prefixWord, tailWord_2855826, baseEnd_2855826] using wordTrace_append hprefix tailTrace_2855826
  have hstable : (prefixWord ++ tailWord_2855826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855826).length < 2 ^ (prefixWord ++ tailWord_2855826).sum := by decide
  have hdescent : baseEnd_2855826 < baseStart_2855826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855837 : List Nat := [1, 4, 2, 1, 2, 1, 4, 7]
def baseStart_2855837 : Nat := 118140960795 + 2855837 * 2 ^ 59
def prefixEnd_2855837 : Nat := 4983230072969 + 3 ^ 40 * 2855837 * 2
def baseEnd_2855837 : Nat := 108623485325499870985463

theorem tailTrace_2855837 : CollatzResearch.WordTrace tailWord_2855837 prefixEnd_2855837 108623485325499870985463 := by
  unfold tailWord_2855837
  simp only [CollatzResearch.WordTrace]
  refine ⟨104160932554797761973893765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69440621703198507982595843 104160932554797761973893765)
  ·
    refine ⟨19530174854024580370105081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104160932554797761973893765 19530174854024580370105081)
    ·
      refine ⟨14647631140518435277578811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19530174854024580370105081 14647631140518435277578811)
      ·
        refine ⟨21971446710777652916368217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14647631140518435277578811 21971446710777652916368217)
        ·
          refine ⟨16478585033083239687276163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21971446710777652916368217 16478585033083239687276163)
          ·
            refine ⟨24717877549624859530914245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16478585033083239687276163 24717877549624859530914245)
            ·
              refine ⟨4634602040554661162046421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24717877549624859530914245 4634602040554661162046421)
              ·
                refine ⟨108623485325499870985463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4634602040554661162046421 108623485325499870985463)
                ·
                  rfl

theorem cell22_2855837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 7].length) (baseStart_2855837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855837 prefixEnd_2855837 := by exact prefixLift 2855837
  have htrace : WordTrace (prefixWord ++ tailWord_2855837) baseStart_2855837 baseEnd_2855837 := by
    simpa [prefixWord, tailWord_2855837, baseEnd_2855837] using wordTrace_append hprefix tailTrace_2855837
  have hstable : (prefixWord ++ tailWord_2855837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855837).length < 2 ^ (prefixWord ++ tailWord_2855837).sum := by decide
  have hdescent : baseEnd_2855837 < baseStart_2855837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855841 : List Nat := [1, 2, 3, 4, 1, 2, 1, 3, 2, 3]
def baseStart_2855841 : Nat := 118140960795 + 2855841 * 2 ^ 59
def prefixEnd_2855841 : Nat := 4983230072969 + 3 ^ 40 * 2855841 * 2
def baseEnd_2855841 : Nat := 977612737211244161769155

theorem tailTrace_2855841 : CollatzResearch.WordTrace tailWord_2855841 prefixEnd_2855841 977612737211244161769155 := by
  unfold tailWord_2855841
  simp only [CollatzResearch.WordTrace]
  refine ⟨104161078446783270657039377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69440718964522180438026251 104161078446783270657039377)
  ·
    refine ⟨78120808835087452992779533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104161078446783270657039377 78120808835087452992779533)
    ·
      refine ⟨29295303313157794872292325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78120808835087452992779533 29295303313157794872292325)
      ·
        refine ⟨5492869371217086538554811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29295303313157794872292325 5492869371217086538554811)
        ·
          refine ⟨8239304056825629807832217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5492869371217086538554811 8239304056825629807832217)
          ·
            refine ⟨6179478042619222355874163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8239304056825629807832217 6179478042619222355874163)
            ·
              refine ⟨9269217063928833533811245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6179478042619222355874163 9269217063928833533811245)
              ·
                refine ⟨3475956398973312575179217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9269217063928833533811245 3475956398973312575179217)
                ·
                  refine ⟨2606967299229984431384413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3475956398973312575179217 2606967299229984431384413)
                  ·
                    refine ⟨977612737211244161769155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2606967299229984431384413 977612737211244161769155)
                    ·
                      rfl

theorem cell22_2855841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_2855841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855841 prefixEnd_2855841 := by exact prefixLift 2855841
  have htrace : WordTrace (prefixWord ++ tailWord_2855841) baseStart_2855841 baseEnd_2855841 := by
    simpa [prefixWord, tailWord_2855841, baseEnd_2855841] using wordTrace_append hprefix tailTrace_2855841
  have hstable : (prefixWord ++ tailWord_2855841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855841).length < 2 ^ (prefixWord ++ tailWord_2855841).sum := by decide
  have hdescent : baseEnd_2855841 < baseStart_2855841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855862 : List Nat := [5, 1, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2855862 : Nat := 118140960795 + 2855862 * 2 ^ 59
def prefixEnd_2855862 : Nat := 4983230072969 + 3 ^ 40 * 2855862 * 2
def baseEnd_2855862 : Nat := 977619925940407106994091

theorem tailTrace_2855862 : CollatzResearch.WordTrace tailWord_2855862 prefixEnd_2855862 977619925940407106994091 := by
  unfold tailWord_2855862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6510115273731699452722115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69441229586471460829035893 6510115273731699452722115)
  ·
    refine ⟨9765172910597549179083173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6510115273731699452722115 9765172910597549179083173)
    ·
      refine ⟨1830969920737040471078095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9765172910597549179083173 1830969920737040471078095)
      ·
        refine ⟨2746454881105560706617143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1830969920737040471078095 2746454881105560706617143)
        ·
          refine ⟨4119682321658341059925715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2746454881105560706617143 4119682321658341059925715)
          ·
            refine ⟨6179523482487511589888573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4119682321658341059925715 6179523482487511589888573)
            ·
              refine ⟨2317321305932816846208215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6179523482487511589888573 2317321305932816846208215)
              ·
                refine ⟨3475981958899225269312323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317321305932816846208215 3475981958899225269312323)
                ·
                  refine ⟨5213972938348837903968485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475981958899225269312323 5213972938348837903968485)
                  ·
                    refine ⟨977619925940407106994091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5213972938348837903968485 977619925940407106994091)
                    ·
                      rfl

theorem cell22_2855862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2855862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855862 prefixEnd_2855862 := by exact prefixLift 2855862
  have htrace : WordTrace (prefixWord ++ tailWord_2855862) baseStart_2855862 baseEnd_2855862 := by
    simpa [prefixWord, tailWord_2855862, baseEnd_2855862] using wordTrace_append hprefix tailTrace_2855862
  have hstable : (prefixWord ++ tailWord_2855862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855862).length < 2 ^ (prefixWord ++ tailWord_2855862).sum := by decide
  have hdescent : baseEnd_2855862 < baseStart_2855862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855897 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 1, 7]
def baseStart_2855897 : Nat := 118140960795 + 2855897 * 2 ^ 59
def prefixEnd_2855897 : Nat := 4983230072969 + 3 ^ 40 * 2855897 * 2
def baseEnd_2855897 : Nat := 977631907155678682368983

theorem tailTrace_2855897 : CollatzResearch.WordTrace tailWord_2855897 prefixEnd_2855897 977631907155678682368983 := by
  unfold tailWord_2855897
  simp only [CollatzResearch.WordTrace]
  refine ⟨104163120934580392221077945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69442080623053594814051963 104163120934580392221077945)
  ·
    refine ⟨78122340700935294165808459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104163120934580392221077945 78122340700935294165808459)
    ·
      refine ⟨117183511051402941248712689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78122340700935294165808459 117183511051402941248712689)
      ·
        refine ⟨87887633288552205936534517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117183511051402941248712689 87887633288552205936534517)
        ·
          refine ⟨8239465620801769306550111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87887633288552205936534517 8239465620801769306550111)
          ·
            refine ⟨12359198431202653959825167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8239465620801769306550111 12359198431202653959825167)
            ·
              refine ⟨18538797646803980939737751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12359198431202653959825167 18538797646803980939737751)
              ·
                refine ⟨27808196470205971409606627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18538797646803980939737751 27808196470205971409606627)
                ·
                  refine ⟨41712294705308957114409941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27808196470205971409606627 41712294705308957114409941)
                  ·
                    refine ⟨977631907155678682368983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41712294705308957114409941 977631907155678682368983)
                    ·
                      rfl

theorem cell22_2855897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_2855897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855897 prefixEnd_2855897 := by exact prefixLift 2855897
  have htrace : WordTrace (prefixWord ++ tailWord_2855897) baseStart_2855897 baseEnd_2855897 := by
    simpa [prefixWord, tailWord_2855897, baseEnd_2855897] using wordTrace_append hprefix tailTrace_2855897
  have hstable : (prefixWord ++ tailWord_2855897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855897).length < 2 ^ (prefixWord ++ tailWord_2855897).sum := by decide
  have hdescent : baseEnd_2855897 < baseStart_2855897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855929 : List Nat := [1, 2, 1, 3, 1, 3, 3, 3, 1, 4]
def baseStart_2855929 : Nat := 118140960795 + 2855929 * 2 ^ 59
def prefixEnd_2855929 : Nat := 4983230072969 + 3 ^ 40 * 2855929 * 2
def baseEnd_2855929 : Nat := 977642861409641265568885

theorem tailTrace_2855929 : CollatzResearch.WordTrace tailWord_2855929 prefixEnd_2855929 977642861409641265568885 := by
  unfold tailWord_2855929
  simp only [CollatzResearch.WordTrace]
  refine ⟨104164288070464461686242841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69442858713642974457495227 104164288070464461686242841)
  ·
    refine ⟨78123216052848346264682131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104164288070464461686242841 78123216052848346264682131)
    ·
      refine ⟨117184824079272519397023197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78123216052848346264682131 117184824079272519397023197)
      ·
        refine ⟨43944309029727194773883699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117184824079272519397023197 43944309029727194773883699)
        ·
          refine ⟨65916463544590792160825549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43944309029727194773883699 65916463544590792160825549)
          ·
            refine ⟨24718673829221547060309581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65916463544590792160825549 24718673829221547060309581)
            ·
              refine ⟨9269502685958080147616093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24718673829221547060309581 9269502685958080147616093)
              ·
                refine ⟨3476063507234280055356035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9269502685958080147616093 3476063507234280055356035)
                ·
                  refine ⟨5214095260851420083034053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3476063507234280055356035 5214095260851420083034053)
                  ·
                    refine ⟨977642861409641265568885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5214095260851420083034053 977642861409641265568885)
                    ·
                      rfl

theorem cell22_2855929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_2855929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855929 prefixEnd_2855929 := by exact prefixLift 2855929
  have htrace : WordTrace (prefixWord ++ tailWord_2855929) baseStart_2855929 baseEnd_2855929 := by
    simpa [prefixWord, tailWord_2855929, baseEnd_2855929] using wordTrace_append hprefix tailTrace_2855929
  have hstable : (prefixWord ++ tailWord_2855929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855929).length < 2 ^ (prefixWord ++ tailWord_2855929).sum := by decide
  have hdescent : baseEnd_2855929 < baseStart_2855929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855944 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 6]
def baseStart_2855944 : Nat := 118140960795 + 2855944 * 2 ^ 59
def prefixEnd_2855944 : Nat := 4983230072969 + 3 ^ 40 * 2855944 * 2
def baseEnd_2855944 : Nat := 325882665405395408814613

theorem tailTrace_2855944 : CollatzResearch.WordTrace tailWord_2855944 prefixEnd_2855944 325882665405395408814613 := by
  unfold tailWord_2855944
  simp only [CollatzResearch.WordTrace]
  refine ⟨52082417582705059624019443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69443223443606746165359257 52082417582705059624019443)
  ·
    refine ⟨78123626374057589436029165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52082417582705059624019443 78123626374057589436029165)
    ·
      refine ⟨29296359890271596038510937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78123626374057589436029165 29296359890271596038510937)
      ·
        refine ⟨21972269917703697028883203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29296359890271596038510937 21972269917703697028883203)
        ·
          refine ⟨32958404876555545543324805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21972269917703697028883203 32958404876555545543324805)
          ·
            refine ⟨6179700914354164789373401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32958404876555545543324805 6179700914354164789373401)
            ·
              refine ⟨4634775685765623592030051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6179700914354164789373401 4634775685765623592030051)
              ·
                refine ⟨6952163528648435388045077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4634775685765623592030051 6952163528648435388045077)
                ·
                  refine ⟨325882665405395408814613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6952163528648435388045077 325882665405395408814613)
                  ·
                    rfl

theorem cell22_2855944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_2855944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2855944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2855944 prefixEnd_2855944 := by exact prefixLift 2855944
  have htrace : WordTrace (prefixWord ++ tailWord_2855944) baseStart_2855944 baseEnd_2855944 := by
    simpa [prefixWord, tailWord_2855944, baseEnd_2855944] using wordTrace_append hprefix tailTrace_2855944
  have hstable : (prefixWord ++ tailWord_2855944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855944).length < 2 ^ (prefixWord ++ tailWord_2855944).sum := by decide
  have hdescent : baseEnd_2855944 < baseStart_2855944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856006 : List Nat := [6, 1, 1, 1, 1, 2, 1, 9]
def baseStart_2856006 : Nat := 118140960795 + 2856006 * 2 ^ 59
def prefixEnd_2856006 : Nat := 4983230072969 + 3 ^ 40 * 2856006 * 2
def baseEnd_2856006 : Nat := 108629913342582081265961

theorem tailTrace_2856006 : CollatzResearch.WordTrace tailWord_2856006 prefixEnd_2856006 108629913342582081265961 := by
  unfold tailWord_2856006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3255221765349546994899871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69444730994123669224530581 3255221765349546994899871)
  ·
    refine ⟨4882832648024320492349807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3255221765349546994899871 4882832648024320492349807)
    ·
      refine ⟨7324248972036480738524711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4882832648024320492349807 7324248972036480738524711)
      ·
        refine ⟨10986373458054721107787067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7324248972036480738524711 10986373458054721107787067)
        ·
          refine ⟨16479560187082081661680601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10986373458054721107787067 16479560187082081661680601)
          ·
            refine ⟨12359670140311561246260451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16479560187082081661680601 12359670140311561246260451)
            ·
              refine ⟨18539505210467341869390677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12359670140311561246260451 18539505210467341869390677)
              ·
                refine ⟨108629913342582081265961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18539505210467341869390677 108629913342582081265961)
                ·
                  rfl

theorem cell22_2856006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_2856006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856006 prefixEnd_2856006 := by exact prefixLift 2856006
  have htrace : WordTrace (prefixWord ++ tailWord_2856006) baseStart_2856006 baseEnd_2856006 := by
    simpa [prefixWord, tailWord_2856006, baseEnd_2856006] using wordTrace_append hprefix tailTrace_2856006
  have hstable : (prefixWord ++ tailWord_2856006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856006).length < 2 ^ (prefixWord ++ tailWord_2856006).sum := by decide
  have hdescent : baseEnd_2856006 < baseStart_2856006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856064 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 3, 4]
def baseStart_2856064 : Nat := 118140960795 + 2856064 * 2 ^ 59
def prefixEnd_2856064 : Nat := 4983230072969 + 3 ^ 40 * 2856064 * 2
def baseEnd_2856064 : Nat := 977689074668545913443471

theorem tailTrace_2856064 : CollatzResearch.WordTrace tailWord_2856064 prefixEnd_2856064 977689074668545913443471 := by
  unfold tailWord_2856064
  simp only [CollatzResearch.WordTrace]
  refine ⟨52084605962487689871203623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69446141283316919828271497 52084605962487689871203623)
  ·
    refine ⟨78126908943731534806805435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52084605962487689871203623 78126908943731534806805435)
    ·
      refine ⟨117190363415597302210208153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78126908943731534806805435 117190363415597302210208153)
      ·
        refine ⟨87892772561697976657656115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117190363415597302210208153 87892772561697976657656115)
        ·
          refine ⟨131839158842546964986484173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87892772561697976657656115 131839158842546964986484173)
          ·
            refine ⟨49439684565955111869931565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131839158842546964986484173 49439684565955111869931565)
            ·
              refine ⟨18539881712233166951224337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49439684565955111869931565 18539881712233166951224337)
              ·
                refine ⟨13904911284174875213418253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18539881712233166951224337 13904911284174875213418253)
                ·
                  refine ⟨5214341731565578205031845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13904911284174875213418253 5214341731565578205031845)
                  ·
                    refine ⟨977689074668545913443471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5214341731565578205031845 977689074668545913443471)
                    ·
                      rfl

theorem cell22_2856064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_2856064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856064 prefixEnd_2856064 := by exact prefixLift 2856064
  have htrace : WordTrace (prefixWord ++ tailWord_2856064) baseStart_2856064 baseEnd_2856064 := by
    simpa [prefixWord, tailWord_2856064, baseEnd_2856064] using wordTrace_append hprefix tailTrace_2856064
  have hstable : (prefixWord ++ tailWord_2856064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856064).length < 2 ^ (prefixWord ++ tailWord_2856064).sum := by decide
  have hdescent : baseEnd_2856064 < baseStart_2856064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856113 : List Nat := [1, 2, 2, 5, 1, 1, 2, 4, 4]
def baseStart_2856113 : Nat := 118140960795 + 2856113 * 2 ^ 59
def prefixEnd_2856113 : Nat := 4983230072969 + 3 ^ 40 * 2856113 * 2
def baseEnd_2856113 : Nat := 325901949456642039656107

theorem tailTrace_2856113 : CollatzResearch.WordTrace tailWord_2856113 prefixEnd_2856113 325901949456642039656107 := by
  unfold tailWord_2856113
  simp only [CollatzResearch.WordTrace]
  refine ⟨104170999101797861110940993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69447332734531907407293995 104170999101797861110940993)
  ·
    refine ⟨78128249326348395833205745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104170999101797861110940993 78128249326348395833205745)
    ·
      refine ⟨58596186994761296874904309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78128249326348395833205745 58596186994761296874904309)
      ·
        refine ⟨5493392530758871582022279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58596186994761296874904309 5493392530758871582022279)
        ·
          refine ⟨8240088796138307373033419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5493392530758871582022279 8240088796138307373033419)
          ·
            refine ⟨12360133194207461059550129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8240088796138307373033419 12360133194207461059550129)
            ·
              refine ⟨9270099895655595794662597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12360133194207461059550129 9270099895655595794662597)
              ·
                refine ⟨1738143730435424211499237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9270099895655595794662597 1738143730435424211499237)
                ·
                  refine ⟨325901949456642039656107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1738143730435424211499237 325901949456642039656107)
                  ·
                    rfl

theorem cell22_2856113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 4].length) (baseStart_2856113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856113 prefixEnd_2856113 := by exact prefixLift 2856113
  have htrace : WordTrace (prefixWord ++ tailWord_2856113) baseStart_2856113 baseEnd_2856113 := by
    simpa [prefixWord, tailWord_2856113, baseEnd_2856113] using wordTrace_append hprefix tailTrace_2856113
  have hstable : (prefixWord ++ tailWord_2856113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856113).length < 2 ^ (prefixWord ++ tailWord_2856113).sum := by decide
  have hdescent : baseEnd_2856113 < baseStart_2856113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856126 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_2856126 : Nat := 118140960795 + 2856126 * 2 ^ 59
def prefixEnd_2856126 : Nat := 4983230072969 + 3 ^ 40 * 2856126 * 2
def baseEnd_2856126 : Nat := 977710298535598418393281

theorem tailTrace_2856126 : CollatzResearch.WordTrace tailWord_2856126 prefixEnd_2856126 977710298535598418393281 := by
  unfold tailWord_2856126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13021434156343845541395529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69447648833833842887442821 13021434156343845541395529)
  ·
    refine ⟨9766075617257884156046647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13021434156343845541395529 9766075617257884156046647)
    ·
      refine ⟨14649113425886826234069971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9766075617257884156046647 14649113425886826234069971)
      ·
        refine ⟨21973670138830239351104957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14649113425886826234069971 21973670138830239351104957)
        ·
          refine ⟨8240126302061339756664359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21973670138830239351104957 8240126302061339756664359)
          ·
            refine ⟨12360189453092009634996539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8240126302061339756664359 12360189453092009634996539)
            ·
              refine ⟨18540284179638014452494809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12360189453092009634996539 18540284179638014452494809)
              ·
                refine ⟨13905213134728510839371107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18540284179638014452494809 13905213134728510839371107)
                ·
                  refine ⟨20857819702092766259056661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13905213134728510839371107 20857819702092766259056661)
                  ·
                    refine ⟨977710298535598418393281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20857819702092766259056661 977710298535598418393281)
                    ·
                      rfl

theorem cell22_2856126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_2856126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856126 prefixEnd_2856126 := by exact prefixLift 2856126
  have htrace : WordTrace (prefixWord ++ tailWord_2856126) baseStart_2856126 baseEnd_2856126 := by
    simpa [prefixWord, tailWord_2856126, baseEnd_2856126] using wordTrace_append hprefix tailTrace_2856126
  have hstable : (prefixWord ++ tailWord_2856126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856126).length < 2 ^ (prefixWord ++ tailWord_2856126).sum := by decide
  have hdescent : baseEnd_2856126 < baseStart_2856126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856128 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 1, 5]
def baseStart_2856128 : Nat := 118140960795 + 2856128 * 2 ^ 59
def prefixEnd_2856128 : Nat := 4983230072969 + 3 ^ 40 * 2856128 * 2
def baseEnd_2856128 : Nat := 977710983176471079843275

theorem tailTrace_2856128 : CollatzResearch.WordTrace tailWord_2856128 prefixEnd_2856128 977710983176471079843275 := by
  unfold tailWord_2856128
  simp only [CollatzResearch.WordTrace]
  refine ⟨52085773098371759336368519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69447697464495679115158025 52085773098371759336368519)
  ·
    refine ⟨78128659647557639004552779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52085773098371759336368519 78128659647557639004552779)
    ·
      refine ⟨117192989471336458506829169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78128659647557639004552779 117192989471336458506829169)
      ·
        refine ⟨87894742103502343880121877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117192989471336458506829169 87894742103502343880121877)
        ·
          refine ⟨4120066036101672369380713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87894742103502343880121877 4120066036101672369380713)
          ·
            refine ⟨3090049527076254277035535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4120066036101672369380713 3090049527076254277035535)
            ·
              refine ⟨4635074290614381415553303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3090049527076254277035535 4635074290614381415553303)
              ·
                refine ⟨6952611435921572123329955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4635074290614381415553303 6952611435921572123329955)
                ·
                  refine ⟨10428917153882358184994933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6952611435921572123329955 10428917153882358184994933)
                  ·
                    refine ⟨977710983176471079843275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10428917153882358184994933 977710983176471079843275)
                    ·
                      rfl

theorem cell22_2856128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 5].length) (baseStart_2856128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856128 prefixEnd_2856128 := by exact prefixLift 2856128
  have htrace : WordTrace (prefixWord ++ tailWord_2856128) baseStart_2856128 baseEnd_2856128 := by
    simpa [prefixWord, tailWord_2856128, baseEnd_2856128] using wordTrace_append hprefix tailTrace_2856128
  have hstable : (prefixWord ++ tailWord_2856128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856128).length < 2 ^ (prefixWord ++ tailWord_2856128).sum := by decide
  have hdescent : baseEnd_2856128 < baseStart_2856128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856154 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_2856154 : Nat := 118140960795 + 2856154 * 2 ^ 59
def prefixEnd_2856154 : Nat := 4983230072969 + 3 ^ 40 * 2856154 * 2
def baseEnd_2856154 : Nat := 977719883507815678693195

theorem tailTrace_2856154 : CollatzResearch.WordTrace tailWord_2856154 prefixEnd_2856154 977719883507815678693195 := by
  unfold tailWord_2856154
  simp only [CollatzResearch.WordTrace]
  refine ⟨26043123623662331278295879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69448329663099550075455677 26043123623662331278295879)
  ·
    refine ⟨39064685435493496917443819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26043123623662331278295879 39064685435493496917443819)
    ·
      refine ⟨58597028153240245376165729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39064685435493496917443819 58597028153240245376165729)
      ·
        refine ⟨43947771114930184032124297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58597028153240245376165729 43947771114930184032124297)
        ·
          refine ⟨32960828336197638024093223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43947771114930184032124297 32960828336197638024093223)
          ·
            refine ⟨49441242504296457036139835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32960828336197638024093223 49441242504296457036139835)
            ·
              refine ⟨74161863756444685554209753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49441242504296457036139835 74161863756444685554209753)
              ·
                refine ⟨55621397817333514165657315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74161863756444685554209753 55621397817333514165657315)
                ·
                  refine ⟨83432096726000271248485973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55621397817333514165657315 83432096726000271248485973)
                  ·
                    refine ⟨977719883507815678693195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83432096726000271248485973 977719883507815678693195)
                    ·
                      rfl

theorem cell22_2856154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_2856154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856154 prefixEnd_2856154 := by exact prefixLift 2856154
  have htrace : WordTrace (prefixWord ++ tailWord_2856154) baseStart_2856154 baseEnd_2856154 := by
    simpa [prefixWord, tailWord_2856154, baseEnd_2856154] using wordTrace_append hprefix tailTrace_2856154
  have hstable : (prefixWord ++ tailWord_2856154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856154).length < 2 ^ (prefixWord ++ tailWord_2856154).sum := by decide
  have hdescent : baseEnd_2856154 < baseStart_2856154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856186 : List Nat := [3, 1, 1, 1, 1, 4, 3, 3, 5]
def baseStart_2856186 : Nat := 118140960795 + 2856186 * 2 ^ 59
def prefixEnd_2856186 : Nat := 4983230072969 + 3 ^ 40 * 2856186 * 2
def baseEnd_2856186 : Nat := 325910279253926087297699

theorem tailTrace_2856186 : CollatzResearch.WordTrace tailWord_2856186 prefixEnd_2856186 325910279253926087297699 := by
  unfold tailWord_2856186
  simp only [CollatzResearch.WordTrace]
  refine ⟨26043415407633348644587103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69449107753688929718898941 26043415407633348644587103)
  ·
    refine ⟨39065123111450022966880655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26043415407633348644587103 39065123111450022966880655)
    ·
      refine ⟨58597684667175034450320983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39065123111450022966880655 58597684667175034450320983)
      ·
        refine ⟨87896527000762551675481475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58597684667175034450320983 87896527000762551675481475)
        ·
          refine ⟨131844790501143827513222213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87896527000762551675481475 131844790501143827513222213)
          ·
            refine ⟨24720898218964467658729165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131844790501143827513222213 24720898218964467658729165)
            ·
              refine ⟨9270336832111675372023437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24720898218964467658729165 9270336832111675372023437)
              ·
                refine ⟨3476376312041878264508789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9270336832111675372023437 3476376312041878264508789)
                ·
                  refine ⟨325910279253926087297699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3476376312041878264508789 325910279253926087297699)
                  ·
                    rfl

theorem cell22_2856186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_2856186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856186 prefixEnd_2856186 := by exact prefixLift 2856186
  have htrace : WordTrace (prefixWord ++ tailWord_2856186) baseStart_2856186 baseEnd_2856186 := by
    simpa [prefixWord, tailWord_2856186, baseEnd_2856186] using wordTrace_append hprefix tailTrace_2856186
  have hstable : (prefixWord ++ tailWord_2856186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856186).length < 2 ^ (prefixWord ++ tailWord_2856186).sum := by decide
  have hdescent : baseEnd_2856186 < baseStart_2856186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856224 : List Nat := [2, 1, 1, 5, 3, 2, 2, 2, 1, 3]
def baseStart_2856224 : Nat := 118140960795 + 2856224 * 2 ^ 59
def prefixEnd_2856224 : Nat := 4983230072969 + 3 ^ 40 * 2856224 * 2
def baseEnd_2856224 : Nat := 977743845938358829442981

theorem tailTrace_2856224 : CollatzResearch.WordTrace tailWord_2856224 prefixEnd_2856224 977743845938358829442981 := by
  unfold tailWord_2856224
  simp only [CollatzResearch.WordTrace]
  refine ⟨52087523802197863534115863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69450031736263818045487817 52087523802197863534115863)
  ·
    refine ⟨78131285703296795301173795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52087523802197863534115863 78131285703296795301173795)
    ·
      refine ⟨117196928554945192951760693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78131285703296795301173795 117196928554945192951760693)
      ·
        refine ⟨10987212052026111839227565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117196928554945192951760693 10987212052026111839227565)
        ·
          refine ⟨4120204519509791939710337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10987212052026111839227565 4120204519509791939710337)
          ·
            refine ⟨3090153389632343954782753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4120204519509791939710337 3090153389632343954782753)
            ·
              refine ⟨2317615042224257966087065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3090153389632343954782753 2317615042224257966087065)
              ·
                refine ⟨1738211281668193474565299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317615042224257966087065 1738211281668193474565299)
                ·
                  refine ⟨2607316922502290211847949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1738211281668193474565299 2607316922502290211847949)
                  ·
                    refine ⟨977743845938358829442981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2607316922502290211847949 977743845938358829442981)
                    ·
                      rfl

theorem cell22_2856224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 1, 3].length) (baseStart_2856224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856224 prefixEnd_2856224 := by exact prefixLift 2856224
  have htrace : WordTrace (prefixWord ++ tailWord_2856224) baseStart_2856224 baseEnd_2856224 := by
    simpa [prefixWord, tailWord_2856224, baseEnd_2856224] using wordTrace_append hprefix tailTrace_2856224
  have hstable : (prefixWord ++ tailWord_2856224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856224).length < 2 ^ (prefixWord ++ tailWord_2856224).sum := by decide
  have hdescent : baseEnd_2856224 < baseStart_2856224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856276 : List Nat := [2, 4, 1, 1, 2, 1, 11]
def baseStart_2856276 : Nat := 118140960795 + 2856276 * 2 ^ 59
def prefixEnd_2856276 : Nat := 4983230072969 + 3 ^ 40 * 2856276 * 2
def baseEnd_2856276 : Nat := 36213394318557334338623

theorem tailTrace_2856276 : CollatzResearch.WordTrace tailWord_2856276 prefixEnd_2856276 36213394318557334338623 := by
  unfold tailWord_2856276
  simp only [CollatzResearch.WordTrace]
  refine ⟨52088472100103669974562341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69451296133471559966083121 52088472100103669974562341)
  ·
    refine ⟨9766588518769438120230439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52088472100103669974562341 9766588518769438120230439)
    ·
      refine ⟨14649882778154157180345659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9766588518769438120230439 14649882778154157180345659)
      ·
        refine ⟨21974824167231235770518489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14649882778154157180345659 21974824167231235770518489)
        ·
          refine ⟨16481118125423426827888867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21974824167231235770518489 16481118125423426827888867)
          ·
            refine ⟨24721677188135140241833301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16481118125423426827888867 24721677188135140241833301)
            ·
              refine ⟨36213394318557334338623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24721677188135140241833301 36213394318557334338623)
              ·
                rfl

theorem cell22_2856276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 11].length) (baseStart_2856276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856276 prefixEnd_2856276 := by exact prefixLift 2856276
  have htrace : WordTrace (prefixWord ++ tailWord_2856276) baseStart_2856276 baseEnd_2856276 := by
    simpa [prefixWord, tailWord_2856276, baseEnd_2856276] using wordTrace_append hprefix tailTrace_2856276
  have hstable : (prefixWord ++ tailWord_2856276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856276).length < 2 ^ (prefixWord ++ tailWord_2856276).sum := by decide
  have hdescent : baseEnd_2856276 < baseStart_2856276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856368 : List Nat := [2, 1, 1, 1, 2, 1, 1, 8, 1, 4]
def baseStart_2856368 : Nat := 118140960795 + 2856368 * 2 ^ 59
def prefixEnd_2856368 : Nat := 4983230072969 + 3 ^ 40 * 2856368 * 2
def baseEnd_2856368 : Nat := 977793140081190453842539

theorem tailTrace_2856368 : CollatzResearch.WordTrace tailWord_2856368 prefixEnd_2856368 977793140081190453842539 := by
  unfold tailWord_2856368
  simp only [CollatzResearch.WordTrace]
  refine ⟨52090149857937019830736879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69453533143916026440982505 52090149857937019830736879)
  ·
    refine ⟨78135224786905529746105319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52090149857937019830736879 78135224786905529746105319)
    ·
      refine ⟨117202837180358294619157979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78135224786905529746105319 117202837180358294619157979)
      ·
        refine ⟨175804255770537441928736969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117202837180358294619157979 175804255770537441928736969)
        ·
          refine ⟨131853191827903081446552727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175804255770537441928736969 131853191827903081446552727)
          ·
            refine ⟨197779787741854622169829091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131853191827903081446552727 197779787741854622169829091)
            ·
              refine ⟨296669681612781933254743637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197779787741854622169829091 296669681612781933254743637)
              ·
                refine ⟨3476597831399788280329027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 296669681612781933254743637 3476597831399788280329027)
                ·
                  refine ⟨5214896747099682420493541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3476597831399788280329027 5214896747099682420493541)
                  ·
                    refine ⟨977793140081190453842539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5214896747099682420493541 977793140081190453842539)
                    ·
                      rfl

theorem cell22_2856368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_2856368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856368 prefixEnd_2856368 := by exact prefixLift 2856368
  have htrace : WordTrace (prefixWord ++ tailWord_2856368) baseStart_2856368 baseEnd_2856368 := by
    simpa [prefixWord, tailWord_2856368, baseEnd_2856368] using wordTrace_append hprefix tailTrace_2856368
  have hstable : (prefixWord ++ tailWord_2856368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856368).length < 2 ^ (prefixWord ++ tailWord_2856368).sum := by decide
  have hdescent : baseEnd_2856368 < baseStart_2856368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856415 : List Nat := [1, 1, 2, 3, 3, 1, 1, 5, 2, 3]
def baseStart_2856415 : Nat := 118140960795 + 2856415 * 2 ^ 59
def prefixEnd_2856415 : Nat := 4983230072969 + 3 ^ 40 * 2856415 * 2
def baseEnd_2856415 : Nat := 977809229141697997917395

theorem tailTrace_2856415 : CollatzResearch.WordTrace tailWord_2856415 prefixEnd_2856415 977809229141697997917395 := by
  unfold tailWord_2856415
  simp only [CollatzResearch.WordTrace]
  refine ⟨104182013946703766688434699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69454675964469177792289799 104182013946703766688434699)
  ·
    refine ⟨156273020920055650032652049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104182013946703766688434699 156273020920055650032652049)
    ·
      refine ⟨117204765690041737524489037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156273020920055650032652049 117204765690041737524489037)
      ·
        refine ⟨43951787133765651571683389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117204765690041737524489037 43951787133765651571683389)
        ·
          refine ⟨16481920175162119339381271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43951787133765651571683389 16481920175162119339381271)
          ·
            refine ⟨24722880262743179009071907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16481920175162119339381271 24722880262743179009071907)
            ·
              refine ⟨37084320394114768513607861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24722880262743179009071907 37084320394114768513607861)
              ·
                refine ⟨3476655036948259548150737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37084320394114768513607861 3476655036948259548150737)
                ·
                  refine ⟨2607491277711194661113053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3476655036948259548150737 2607491277711194661113053)
                  ·
                    refine ⟨977809229141697997917395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2607491277711194661113053 977809229141697997917395)
                    ·
                      rfl

theorem cell22_2856415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 3].length) (baseStart_2856415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856415 prefixEnd_2856415 := by exact prefixLift 2856415
  have htrace : WordTrace (prefixWord ++ tailWord_2856415) baseStart_2856415 baseEnd_2856415 := by
    simpa [prefixWord, tailWord_2856415, baseEnd_2856415] using wordTrace_append hprefix tailTrace_2856415
  have hstable : (prefixWord ++ tailWord_2856415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856415).length < 2 ^ (prefixWord ++ tailWord_2856415).sum := by decide
  have hdescent : baseEnd_2856415 < baseStart_2856415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856449 : List Nat := [1, 2, 4, 1, 4, 2, 1, 2, 2, 3]
def baseStart_2856449 : Nat := 118140960795 + 2856449 * 2 ^ 59
def prefixEnd_2856449 : Nat := 4983230072969 + 3 ^ 40 * 2856449 * 2
def baseEnd_2856449 : Nat := 977820868036533242567291

theorem tailTrace_2856449 : CollatzResearch.WordTrace tailWord_2856449 prefixEnd_2856449 977820868036533242567291 := by
  unfold tailWord_2856449
  simp only [CollatzResearch.WordTrace]
  refine ⟨104183254028580590495172401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69455502685720393663448267 104183254028580590495172401)
  ·
    refine ⟨78137440521435442871379301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104183254028580590495172401 78137440521435442871379301)
    ·
      refine ⟨14650770097769145538383619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78137440521435442871379301 14650770097769145538383619)
      ·
        refine ⟨21976155146653718307575429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14650770097769145538383619 21976155146653718307575429)
        ·
          refine ⟨4120529089997572182670393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21976155146653718307575429 4120529089997572182670393)
          ·
            refine ⟨3090396817498179137002795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4120529089997572182670393 3090396817498179137002795)
            ·
              refine ⟨4635595226247268705504193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3090396817498179137002795 4635595226247268705504193)
              ·
                refine ⟨3476696419685451529128145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4635595226247268705504193 3476696419685451529128145)
                ·
                  refine ⟨2607522314764088646846109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3476696419685451529128145 2607522314764088646846109)
                  ·
                    refine ⟨977820868036533242567291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2607522314764088646846109 977820868036533242567291)
                    ·
                      rfl

theorem cell22_2856449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_2856449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856449 prefixEnd_2856449 := by exact prefixLift 2856449
  have htrace : WordTrace (prefixWord ++ tailWord_2856449) baseStart_2856449 baseEnd_2856449 := by
    simpa [prefixWord, tailWord_2856449, baseEnd_2856449] using wordTrace_append hprefix tailTrace_2856449
  have hstable : (prefixWord ++ tailWord_2856449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856449).length < 2 ^ (prefixWord ++ tailWord_2856449).sum := by decide
  have hdescent : baseEnd_2856449 < baseStart_2856449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856554 : List Nat := [3, 1, 3, 2, 1, 3, 3, 1, 1, 4]
def baseStart_2856554 : Nat := 118140960795 + 2856554 * 2 ^ 59
def prefixEnd_2856554 : Nat := 4983230072969 + 3 ^ 40 * 2856554 * 2
def baseEnd_2856554 : Nat := 977856811682347968691969

theorem tailTrace_2856554 : CollatzResearch.WordTrace tailWord_2856554 prefixEnd_2856554 977856811682347968691969 := by
  unfold tailWord_2856554
  simp only [CollatzResearch.WordTrace]
  refine ⟨26046770923300048356936179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69458055795466795618496477 26046770923300048356936179)
  ·
    refine ⟨39070156384950072535404269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26046770923300048356936179 39070156384950072535404269)
    ·
      refine ⟨14651308644356277200776601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39070156384950072535404269 14651308644356277200776601)
      ·
        refine ⟨10988481483267207900582451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14651308644356277200776601 10988481483267207900582451)
        ·
          refine ⟨16482722224900811850873677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10988481483267207900582451 16482722224900811850873677)
          ·
            refine ⟨6181020834337804444077629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16482722224900811850873677 6181020834337804444077629)
            ·
              refine ⟨2317882812876676666529111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6181020834337804444077629 2317882812876676666529111)
              ·
                refine ⟨3476824219315014999793667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317882812876676666529111 3476824219315014999793667)
                ·
                  refine ⟨5215236328972522499690501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3476824219315014999793667 5215236328972522499690501)
                  ·
                    refine ⟨977856811682347968691969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5215236328972522499690501 977856811682347968691969)
                    ·
                      rfl

theorem cell22_2856554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_2856554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856554 prefixEnd_2856554 := by exact prefixLift 2856554
  have htrace : WordTrace (prefixWord ++ tailWord_2856554) baseStart_2856554 baseEnd_2856554 := by
    simpa [prefixWord, tailWord_2856554, baseEnd_2856554] using wordTrace_append hprefix tailTrace_2856554
  have hstable : (prefixWord ++ tailWord_2856554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856554).length < 2 ^ (prefixWord ++ tailWord_2856554).sum := by decide
  have hdescent : baseEnd_2856554 < baseStart_2856554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856584 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 1, 5]
def baseStart_2856584 : Nat := 118140960795 + 2856584 * 2 ^ 59
def prefixEnd_2856584 : Nat := 4983230072969 + 3 ^ 40 * 2856584 * 2
def baseEnd_2856584 : Nat := 977867081295437890441877

theorem tailTrace_2856584 : CollatzResearch.WordTrace tailWord_2856584 prefixEnd_2856584 977867081295437890441877 := by
  unfold tailWord_2856584
  simp only [CollatzResearch.WordTrace]
  refine ⟨52094088941545754275668403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69458785255394339034224537 52094088941545754275668403)
  ·
    refine ⟨78141133412318631413502605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52094088941545754275668403 78141133412318631413502605)
    ·
      refine ⟨29302925029619486780063477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78141133412318631413502605 29302925029619486780063477)
      ·
        refine ⟨2747149221526826885630951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29302925029619486780063477 2747149221526826885630951)
        ·
          refine ⟨4120723832290240328446427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747149221526826885630951 4120723832290240328446427)
          ·
            refine ⟨6181085748435360492669641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4120723832290240328446427 6181085748435360492669641)
            ·
              refine ⟨4635814311326520369502231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6181085748435360492669641 4635814311326520369502231)
              ·
                refine ⟨6953721466989780554253347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4635814311326520369502231 6953721466989780554253347)
                ·
                  refine ⟨10430582200484670831380021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6953721466989780554253347 10430582200484670831380021)
                  ·
                    refine ⟨977867081295437890441877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10430582200484670831380021 977867081295437890441877)
                    ·
                      rfl

theorem cell22_2856584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_2856584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856584 prefixEnd_2856584 := by exact prefixLift 2856584
  have htrace : WordTrace (prefixWord ++ tailWord_2856584) baseStart_2856584 baseEnd_2856584 := by
    simpa [prefixWord, tailWord_2856584, baseEnd_2856584] using wordTrace_append hprefix tailTrace_2856584
  have hstable : (prefixWord ++ tailWord_2856584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856584).length < 2 ^ (prefixWord ++ tailWord_2856584).sum := by decide
  have hdescent : baseEnd_2856584 < baseStart_2856584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856640 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 2, 5]
def baseStart_2856640 : Nat := 118140960795 + 2856640 * 2 ^ 59
def prefixEnd_2856640 : Nat := 4983230072969 + 3 ^ 40 * 2856640 * 2
def baseEnd_2856640 : Nat := 977886251239872411041705

theorem tailTrace_2856640 : CollatzResearch.WordTrace tailWord_2856640 prefixEnd_2856640 977886251239872411041705 := by
  unfold tailWord_2856640
  simp only [CollatzResearch.WordTrace]
  refine ⟨52095110185444315057687687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69460146913925753410250249 52095110185444315057687687)
  ·
    refine ⟨78142665278166472586531531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52095110185444315057687687 78142665278166472586531531)
    ·
      refine ⟨117213997917249708879797297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78142665278166472586531531 117213997917249708879797297)
      ·
        refine ⟨87910498437937281659847973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117213997917249708879797297 87910498437937281659847973)
        ·
          refine ⟨16483218457113240311221495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87910498437937281659847973 16483218457113240311221495)
          ·
            refine ⟨24724827685669860466832243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16483218457113240311221495 24724827685669860466832243)
            ·
              refine ⟨37087241528504790700248365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24724827685669860466832243 37087241528504790700248365)
              ·
                refine ⟨13907715573189296512593137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37087241528504790700248365 13907715573189296512593137)
                ·
                  refine ⟨10430786679891972384444853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13907715573189296512593137 10430786679891972384444853)
                  ·
                    refine ⟨977886251239872411041705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10430786679891972384444853 977886251239872411041705)
                    ·
                      rfl

theorem cell22_2856640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_2856640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856640 prefixEnd_2856640 := by exact prefixLift 2856640
  have htrace : WordTrace (prefixWord ++ tailWord_2856640) baseStart_2856640 baseEnd_2856640 := by
    simpa [prefixWord, tailWord_2856640, baseEnd_2856640] using wordTrace_append hprefix tailTrace_2856640
  have hstable : (prefixWord ++ tailWord_2856640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856640).length < 2 ^ (prefixWord ++ tailWord_2856640).sum := by decide
  have hdescent : baseEnd_2856640 < baseStart_2856640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856655 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 3, 4]
def baseStart_2856655 : Nat := 118140960795 + 2856655 * 2 ^ 59
def prefixEnd_2856655 : Nat := 4983230072969 + 3 ^ 40 * 2856655 * 2
def baseEnd_2856655 : Nat := 977891386046417371916659

theorem tailTrace_2856655 : CollatzResearch.WordTrace tailWord_2856655 prefixEnd_2856655 977891386046417371916659 := by
  unfold tailWord_2856655
  simp only [CollatzResearch.WordTrace]
  refine ⟨104190767465834287677171419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69460511643889525118114279 104190767465834287677171419)
  ·
    refine ⟨156286151198751431515757129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104190767465834287677171419 156286151198751431515757129)
    ·
      refine ⟨117214613399063573636817847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156286151198751431515757129 117214613399063573636817847)
      ·
        refine ⟨175821920098595360455226771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117214613399063573636817847 175821920098595360455226771)
        ·
          refine ⟨263732880147893040682840157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175821920098595360455226771 263732880147893040682840157)
          ·
            refine ⟨98899830055459890256065059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263732880147893040682840157 98899830055459890256065059)
            ·
              refine ⟨148349745083189835384097589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98899830055459890256065059 148349745083189835384097589)
              ·
                refine ⟨13907788601549047067259149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148349745083189835384097589 13907788601549047067259149)
                ·
                  refine ⟨5215420725580892650222181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13907788601549047067259149 5215420725580892650222181)
                  ·
                    refine ⟨977891386046417371916659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5215420725580892650222181 977891386046417371916659)
                    ·
                      rfl

theorem cell22_2856655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_2856655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2856655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2856655 prefixEnd_2856655 := by exact prefixLift 2856655
  have htrace : WordTrace (prefixWord ++ tailWord_2856655) baseStart_2856655 baseEnd_2856655 := by
    simpa [prefixWord, tailWord_2856655, baseEnd_2856655] using wordTrace_append hprefix tailTrace_2856655
  have hstable : (prefixWord ++ tailWord_2856655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856655).length < 2 ^ (prefixWord ++ tailWord_2856655).sum := by decide
  have hdescent : baseEnd_2856655 < baseStart_2856655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
