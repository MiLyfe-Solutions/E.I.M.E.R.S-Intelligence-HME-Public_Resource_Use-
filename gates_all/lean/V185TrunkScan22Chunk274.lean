import V185TrunkScan22Chunk273

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2442819 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 1, 10]
def baseStart_2442819 : Nat := 118140960795 + 2442819 * 2 ^ 59
def prefixEnd_2442819 : Nat := 4983230072969 + 3 ^ 40 * 2442819 * 2
def baseEnd_2442819 : Nat := 836226865957055462085457

theorem tailTrace_2442819 : CollatzResearch.WordTrace tailWord_2442819 prefixEnd_2442819 836226865957055462085457 := by
  unfold tailWord_2442819
  simp only [CollatzResearch.WordTrace]
  refine ⟨89096928537091438115299511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59397952358060958743533007 89096928537091438115299511)
  ·
    refine ⟨133645392805637157172949267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89096928537091438115299511 133645392805637157172949267)
    ·
      refine ⟨200468089208455735759423901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133645392805637157172949267 200468089208455735759423901)
      ·
        refine ⟨75175533453170900909783963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200468089208455735759423901 75175533453170900909783963)
        ·
          refine ⟨112763300179756351364675945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75175533453170900909783963 112763300179756351364675945)
          ·
            refine ⟨84572475134817263523506959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112763300179756351364675945 84572475134817263523506959)
            ·
              refine ⟨126858712702225895285260439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84572475134817263523506959 126858712702225895285260439)
              ·
                refine ⟨190288069053338842927890659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126858712702225895285260439 190288069053338842927890659)
                ·
                  refine ⟨285432103580008264391835989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190288069053338842927890659 285432103580008264391835989)
                  ·
                    refine ⟨836226865957055462085457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 285432103580008264391835989 836226865957055462085457)
                    ·
                      rfl

theorem cell22_2442819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_2442819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442819 prefixEnd_2442819 := by exact prefixLift 2442819
  have htrace : WordTrace (prefixWord ++ tailWord_2442819) baseStart_2442819 baseEnd_2442819 := by
    simpa [prefixWord, tailWord_2442819, baseEnd_2442819] using wordTrace_append hprefix tailTrace_2442819
  have hstable : (prefixWord ++ tailWord_2442819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442819).length < 2 ^ (prefixWord ++ tailWord_2442819).sum := by decide
  have hdescent : baseEnd_2442819 < baseStart_2442819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442823 : List Nat := [1, 1, 4, 1, 5, 1, 1, 3, 5]
def baseStart_2442823 : Nat := 118140960795 + 2442823 * 2 ^ 59
def prefixEnd_2442823 : Nat := 4983230072969 + 3 ^ 40 * 2442823 * 2
def baseEnd_2442823 : Nat := 278742745079600261661815

theorem tailTrace_2442823 : CollatzResearch.WordTrace tailWord_2442823 prefixEnd_2442823 278742745079600261661815 := by
  unfold tailWord_2442823
  simp only [CollatzResearch.WordTrace]
  refine ⟨89097074429076946798445123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59398049619384631198963415 89097074429076946798445123)
  ·
    refine ⟨133645611643615420197667685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89097074429076946798445123 133645611643615420197667685)
    ·
      refine ⟨25058552183177891287062691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133645611643615420197667685 25058552183177891287062691)
      ·
        refine ⟨37587828274766836930594037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25058552183177891287062691 37587828274766836930594037)
        ·
          refine ⟨3523858900759390962243191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37587828274766836930594037 3523858900759390962243191)
          ·
            refine ⟨5285788351139086443364787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523858900759390962243191 5285788351139086443364787)
            ·
              refine ⟨7928682526708629665047181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285788351139086443364787 7928682526708629665047181)
              ·
                refine ⟨2973255947515736124392693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7928682526708629665047181 2973255947515736124392693)
                ·
                  refine ⟨278742745079600261661815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2973255947515736124392693 278742745079600261661815)
                  ·
                    rfl

theorem cell22_2442823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 5].length) (baseStart_2442823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442823 prefixEnd_2442823 := by exact prefixLift 2442823
  have htrace : WordTrace (prefixWord ++ tailWord_2442823) baseStart_2442823 baseEnd_2442823 := by
    simpa [prefixWord, tailWord_2442823, baseEnd_2442823] using wordTrace_append hprefix tailTrace_2442823
  have hstable : (prefixWord ++ tailWord_2442823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442823).length < 2 ^ (prefixWord ++ tailWord_2442823).sum := by decide
  have hdescent : baseEnd_2442823 < baseStart_2442823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442861 : List Nat := [1, 5, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_2442861 : Nat := 118140960795 + 2442861 * 2 ^ 59
def prefixEnd_2442861 : Nat := 4983230072969 + 3 ^ 40 * 2442861 * 2
def baseEnd_2442861 : Nat := 836241243415381352535329

theorem tailTrace_2442861 : CollatzResearch.WordTrace tailWord_2442861 prefixEnd_2442861 836241243415381352535329 := by
  unfold tailWord_2442861
  simp only [CollatzResearch.WordTrace]
  refine ⟨89098460402939279288328437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59398973601959519525552291 89098460402939279288328437)
  ·
    refine ⟨8352980662775557433280791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89098460402939279288328437 8352980662775557433280791)
    ·
      refine ⟨12529470994163336149921187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8352980662775557433280791 12529470994163336149921187)
      ·
        refine ⟨18794206491245004224881781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12529470994163336149921187 18794206491245004224881781)
        ·
          refine ⟨1761956858554219146082667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18794206491245004224881781 1761956858554219146082667)
          ·
            refine ⟨2642935287831328719124001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761956858554219146082667 2642935287831328719124001)
            ·
              refine ⟨1982201465873496539343001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2642935287831328719124001 1982201465873496539343001)
              ·
                refine ⟨1486651099405122404507251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1982201465873496539343001 1486651099405122404507251)
                ·
                  refine ⟨2229976649107683606760877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486651099405122404507251 2229976649107683606760877)
                  ·
                    refine ⟨836241243415381352535329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229976649107683606760877 836241243415381352535329)
                    ·
                      rfl

theorem cell22_2442861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_2442861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442861 prefixEnd_2442861 := by exact prefixLift 2442861
  have htrace : WordTrace (prefixWord ++ tailWord_2442861) baseStart_2442861 baseEnd_2442861 := by
    simpa [prefixWord, tailWord_2442861, baseEnd_2442861] using wordTrace_append hprefix tailTrace_2442861
  have hstable : (prefixWord ++ tailWord_2442861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442861).length < 2 ^ (prefixWord ++ tailWord_2442861).sum := by decide
  have hdescent : baseEnd_2442861 < baseStart_2442861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442928 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 3, 3]
def baseStart_2442928 : Nat := 118140960795 + 2442928 * 2 ^ 59
def prefixEnd_2442928 : Nat := 4983230072969 + 3 ^ 40 * 2442928 * 2
def baseEnd_2442928 : Nat := 836264178884615511110123

theorem tailTrace_2442928 : CollatzResearch.WordTrace tailWord_2442928 prefixEnd_2442928 836264178884615511110123 := by
  unfold tailWord_2442928
  simp only [CollatzResearch.WordTrace]
  refine ⟨44550452046848274865508719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59400602729131033154011625 44550452046848274865508719)
  ·
    refine ⟨66825678070272412298263079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44550452046848274865508719 66825678070272412298263079)
    ·
      refine ⟨100238517105408618447394619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66825678070272412298263079 100238517105408618447394619)
      ·
        refine ⟨150357775658112927671091929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100238517105408618447394619 150357775658112927671091929)
        ·
          refine ⟨112768331743584695753318947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150357775658112927671091929 112768331743584695753318947)
          ·
            refine ⟨169152497615377043629978421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112768331743584695753318947 169152497615377043629978421)
            ·
              refine ⟨15858046651441597840310477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169152497615377043629978421 15858046651441597840310477)
              ·
                refine ⟨5946767494290599190116429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15858046651441597840310477 5946767494290599190116429)
                ·
                  refine ⟨2230037810358974696293661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5946767494290599190116429 2230037810358974696293661)
                  ·
                    refine ⟨836264178884615511110123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2230037810358974696293661 836264178884615511110123)
                    ·
                      rfl

theorem cell22_2442928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 3, 3].length) (baseStart_2442928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442928 prefixEnd_2442928 := by exact prefixLift 2442928
  have htrace : WordTrace (prefixWord ++ tailWord_2442928) baseStart_2442928 baseEnd_2442928 := by
    simpa [prefixWord, tailWord_2442928, baseEnd_2442928] using wordTrace_append hprefix tailTrace_2442928
  have hstable : (prefixWord ++ tailWord_2442928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442928).length < 2 ^ (prefixWord ++ tailWord_2442928).sum := by decide
  have hdescent : baseEnd_2442928 < baseStart_2442928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442979 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 3, 3]
def baseStart_2442979 : Nat := 118140960795 + 2442979 * 2 ^ 59
def prefixEnd_2442979 : Nat := 4983230072969 + 3 ^ 40 * 2442979 * 2
def baseEnd_2442979 : Nat := 836281637226868378084967

theorem tailTrace_2442979 : CollatzResearch.WordTrace tailWord_2442979 prefixEnd_2442979 836281637226868378084967 := by
  unfold tailWord_2442979
  simp only [CollatzResearch.WordTrace]
  refine ⟨89102764216511785441123991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59401842811007856960749327 89102764216511785441123991)
  ·
    refine ⟨133654146324767678161685987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89102764216511785441123991 133654146324767678161685987)
    ·
      refine ⟨200481219487151517242528981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133654146324767678161685987 200481219487151517242528981)
      ·
        refine ⟨4698778581730113685371773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 200481219487151517242528981 4698778581730113685371773)
        ·
          refine ⟨1762041968148792632014415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4698778581730113685371773 1762041968148792632014415)
          ·
            refine ⟨2643062952223188948021623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1762041968148792632014415 2643062952223188948021623)
            ·
              refine ⟨3964594428334783422032435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2643062952223188948021623 3964594428334783422032435)
              ·
                refine ⟨5946891642502175133048653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964594428334783422032435 5946891642502175133048653)
                ·
                  refine ⟨2230084365938315674893245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5946891642502175133048653 2230084365938315674893245)
                  ·
                    refine ⟨836281637226868378084967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2230084365938315674893245 836281637226868378084967)
                    ·
                      rfl

theorem cell22_2442979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 3, 3].length) (baseStart_2442979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442979 prefixEnd_2442979 := by exact prefixLift 2442979
  have htrace : WordTrace (prefixWord ++ tailWord_2442979) baseStart_2442979 baseEnd_2442979 := by
    simpa [prefixWord, tailWord_2442979, baseEnd_2442979] using wordTrace_append hprefix tailTrace_2442979
  have hstable : (prefixWord ++ tailWord_2442979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442979).length < 2 ^ (prefixWord ++ tailWord_2442979).sum := by decide
  have hdescent : baseEnd_2442979 < baseStart_2442979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443018 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_2443018 : Nat := 118140960795 + 2443018 * 2 ^ 59
def prefixEnd_2443018 : Nat := 4983230072969 + 3 ^ 40 * 2443018 * 2
def baseEnd_2443018 : Nat := 836294987723885276359847

theorem tailTrace_2443018 : CollatzResearch.WordTrace tailWord_2443018 prefixEnd_2443018 836294987723885276359847 := by
  unfold tailWord_2443018
  simp only [CollatzResearch.WordTrace]
  refine ⟨22276046665842623775448427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59402791108913663401195805 22276046665842623775448427)
  ·
    refine ⟨33414069998763935663172641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22276046665842623775448427 33414069998763935663172641)
    ·
      refine ⟨25060552499072951747379481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33414069998763935663172641 25060552499072951747379481)
      ·
        refine ⟨18795414374304713810534611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25060552499072951747379481 18795414374304713810534611)
        ·
          refine ⟨28193121561457070715801917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18795414374304713810534611 28193121561457070715801917)
          ·
            refine ⟨10572420585546401518425719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28193121561457070715801917 10572420585546401518425719)
            ·
              refine ⟨15858630878319602277638579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10572420585546401518425719 15858630878319602277638579)
              ·
                refine ⟨23787946317479403416457869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15858630878319602277638579 23787946317479403416457869)
                ·
                  refine ⟨8920479869054776281171701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23787946317479403416457869 8920479869054776281171701)
                  ·
                    refine ⟨836294987723885276359847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8920479869054776281171701 836294987723885276359847)
                    ·
                      rfl

theorem cell22_2443018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_2443018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443018 prefixEnd_2443018 := by exact prefixLift 2443018
  have htrace : WordTrace (prefixWord ++ tailWord_2443018) baseStart_2443018 baseEnd_2443018 := by
    simpa [prefixWord, tailWord_2443018, baseEnd_2443018] using wordTrace_append hprefix tailTrace_2443018
  have hstable : (prefixWord ++ tailWord_2443018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443018).length < 2 ^ (prefixWord ++ tailWord_2443018).sum := by decide
  have hdescent : baseEnd_2443018 < baseStart_2443018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443097 : List Nat := [1, 2, 1, 2, 2, 3, 1, 6, 1, 3]
def baseStart_2443097 : Nat := 118140960795 + 2443097 * 2 ^ 59
def prefixEnd_2443097 : Nat := 4983230072969 + 3 ^ 40 * 2443097 * 2
def baseEnd_2443097 : Nat := 836322031038355403634605

theorem tailTrace_2443097 : CollatzResearch.WordTrace tailWord_2443097 prefixEnd_2443097 836322031038355403634605 := by
  unfold tailWord_2443097
  simp only [CollatzResearch.WordTrace]
  refine ⟨89107068030084291593919545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59404712020056194395946363 89107068030084291593919545)
  ·
    refine ⟨66830301022563218695439659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89107068030084291593919545 66830301022563218695439659)
    ·
      refine ⟨100245451533844828043159489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66830301022563218695439659 100245451533844828043159489)
      ·
        refine ⟨75184088650383621032369617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100245451533844828043159489 75184088650383621032369617)
        ·
          refine ⟨56388066487787715774277213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75184088650383621032369617 56388066487787715774277213)
          ·
            refine ⟨21145524932920393415353955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56388066487787715774277213 21145524932920393415353955)
            ·
              refine ⟨31718287399380590123030933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21145524932920393415353955 31718287399380590123030933)
              ·
                refine ⟨1486794721845965162017075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31718287399380590123030933 1486794721845965162017075)
                ·
                  refine ⟨2230192082768947743025613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486794721845965162017075 2230192082768947743025613)
                  ·
                    refine ⟨836322031038355403634605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2230192082768947743025613 836322031038355403634605)
                    ·
                      rfl

theorem cell22_2443097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 1, 3].length) (baseStart_2443097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443097 prefixEnd_2443097 := by exact prefixLift 2443097
  have htrace : WordTrace (prefixWord ++ tailWord_2443097) baseStart_2443097 baseEnd_2443097 := by
    simpa [prefixWord, tailWord_2443097, baseEnd_2443097] using wordTrace_append hprefix tailTrace_2443097
  have hstable : (prefixWord ++ tailWord_2443097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443097).length < 2 ^ (prefixWord ++ tailWord_2443097).sum := by decide
  have hdescent : baseEnd_2443097 < baseStart_2443097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443183 : List Nat := [1, 1, 2, 1, 2, 2, 3, 10]
def baseStart_2443183 : Nat := 118140960795 + 2443183 * 2 ^ 59
def prefixEnd_2443183 : Nat := 4983230072969 + 3 ^ 40 * 2443183 * 2
def baseEnd_2443183 : Nat := 92927941177319982887149

theorem tailTrace_2443183 : CollatzResearch.WordTrace tailWord_2443183 prefixEnd_2443183 92927941177319982887149 := by
  unfold tailWord_2443183
  simp only [CollatzResearch.WordTrace]
  refine ⟨89110204707772728281550203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59406803138515152187700135 89110204707772728281550203)
  ·
    refine ⟨133665307061659092422325305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89110204707772728281550203 133665307061659092422325305)
    ·
      refine ⟨100248980296244319316743979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133665307061659092422325305 100248980296244319316743979)
      ·
        refine ⟨150373470444366478975115969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100248980296244319316743979 150373470444366478975115969)
        ·
          refine ⟨112780102833274859231336977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150373470444366478975115969 112780102833274859231336977)
          ·
            refine ⟨84585077124956144423502733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112780102833274859231336977 84585077124956144423502733)
            ·
              refine ⟨31719403921858554158813525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84585077124956144423502733 31719403921858554158813525)
              ·
                refine ⟨92927941177319982887149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31719403921858554158813525 92927941177319982887149)
                ·
                  rfl

theorem cell22_2443183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 10].length) (baseStart_2443183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443183 prefixEnd_2443183 := by exact prefixLift 2443183
  have htrace : WordTrace (prefixWord ++ tailWord_2443183) baseStart_2443183 baseEnd_2443183 := by
    simpa [prefixWord, tailWord_2443183, baseEnd_2443183] using wordTrace_append hprefix tailTrace_2443183
  have hstable : (prefixWord ++ tailWord_2443183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443183).length < 2 ^ (prefixWord ++ tailWord_2443183).sum := by decide
  have hdescent : baseEnd_2443183 < baseStart_2443183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443260 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_2443260 : Nat := 118140960795 + 2443260 * 2 ^ 59
def prefixEnd_2443260 : Nat := 4983230072969 + 3 ^ 40 * 2443260 * 2
def baseEnd_2443260 : Nat := 836377829269477311809105

theorem tailTrace_2443260 : CollatzResearch.WordTrace tailWord_2443260 prefixEnd_2443260 836377829269477311809105 := by
  unfold tailWord_2443260
  simp only [CollatzResearch.WordTrace]
  refine ⟨44556506564246885216051617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59408675418995846954735489 44556506564246885216051617)
  ·
    refine ⟨33417379923185163912038713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44556506564246885216051617 33417379923185163912038713)
    ·
      refine ⟨25063034942388872934029035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33417379923185163912038713 25063034942388872934029035)
      ·
        refine ⟨37594552413583309401043553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25063034942388872934029035 37594552413583309401043553)
        ·
          refine ⟨28195914310187482050782665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37594552413583309401043553 28195914310187482050782665)
          ·
            refine ⟨21146935732640611538086999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28195914310187482050782665 21146935732640611538086999)
            ·
              refine ⟨31720403598960917307130499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21146935732640611538086999 31720403598960917307130499)
              ·
                refine ⟨47580605398441375960695749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31720403598960917307130499 47580605398441375960695749)
                ·
                  refine ⟨8921363512207757992630453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47580605398441375960695749 8921363512207757992630453)
                  ·
                    refine ⟨836377829269477311809105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8921363512207757992630453 836377829269477311809105)
                    ·
                      rfl

theorem cell22_2443260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2443260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443260 prefixEnd_2443260 := by exact prefixLift 2443260
  have htrace : WordTrace (prefixWord ++ tailWord_2443260) baseStart_2443260 baseEnd_2443260 := by
    simpa [prefixWord, tailWord_2443260, baseEnd_2443260] using wordTrace_append hprefix tailTrace_2443260
  have hstable : (prefixWord ++ tailWord_2443260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443260).length < 2 ^ (prefixWord ++ tailWord_2443260).sum := by decide
  have hdescent : baseEnd_2443260 < baseStart_2443260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443300 : List Nat := [2, 3, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_2443300 : Nat := 118140960795 + 2443300 * 2 ^ 59
def prefixEnd_2443300 : Nat := 4983230072969 + 3 ^ 40 * 2443300 * 2
def baseEnd_2443300 : Nat := 836391522086930540808983

theorem tailTrace_2443300 : CollatzResearch.WordTrace tailWord_2443300 prefixEnd_2443300 836391522086930540808983 := by
  unfold tailWord_2443300
  simp only [CollatzResearch.WordTrace]
  refine ⟨44557236024174428631779677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59409648032232571509039569 44557236024174428631779677)
  ·
    refine ⟨16708963509065410736917379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44557236024174428631779677 16708963509065410736917379)
    ·
      refine ⟨25063445263598116105376069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16708963509065410736917379 25063445263598116105376069)
      ·
        refine ⟨4699395986924646769758013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25063445263598116105376069 4699395986924646769758013)
        ·
          refine ⟨1762273495096742538659255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4699395986924646769758013 1762273495096742538659255)
          ·
            refine ⟨2643410242645113807988883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1762273495096742538659255 2643410242645113807988883)
            ·
              refine ⟨3965115363967670711983325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2643410242645113807988883 3965115363967670711983325)
              ·
                refine ⟨1486918261487876516993747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3965115363967670711983325 1486918261487876516993747)
                ·
                  refine ⟨2230377392231814775490621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486918261487876516993747 2230377392231814775490621)
                  ·
                    refine ⟨836391522086930540808983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2230377392231814775490621 836391522086930540808983)
                    ·
                      rfl

theorem cell22_2443300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_2443300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443300 prefixEnd_2443300 := by exact prefixLift 2443300
  have htrace : WordTrace (prefixWord ++ tailWord_2443300) baseStart_2443300 baseEnd_2443300 := by
    simpa [prefixWord, tailWord_2443300, baseEnd_2443300] using wordTrace_append hprefix tailTrace_2443300
  have hstable : (prefixWord ++ tailWord_2443300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443300).length < 2 ^ (prefixWord ++ tailWord_2443300).sum := by decide
  have hdescent : baseEnd_2443300 < baseStart_2443300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443307 : List Nat := [1, 1, 1, 1, 2, 1, 4, 7, 4]
def baseStart_2443307 : Nat := 118140960795 + 2443307 * 2 ^ 59
def prefixEnd_2443307 : Nat := 4983230072969 + 3 ^ 40 * 2443307 * 2
def baseEnd_2443307 : Nat := 278797972776661618627987

theorem tailTrace_2443307 : CollatzResearch.WordTrace tailWord_2443307 prefixEnd_2443307 278797972776661618627987 := by
  unfold tailWord_2443307
  simp only [CollatzResearch.WordTrace]
  refine ⟨89114727359323497459064175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59409818239548998306042783 89114727359323497459064175)
  ·
    refine ⟨133672091038985246188596263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89114727359323497459064175 133672091038985246188596263)
    ·
      refine ⟨200508136558477869282894395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133672091038985246188596263 200508136558477869282894395)
      ·
        refine ⟨300762204837716803924341593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200508136558477869282894395 300762204837716803924341593)
        ·
          refine ⟨225571653628287602943256195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300762204837716803924341593 225571653628287602943256195)
          ·
            refine ⟨338357480442431404414884293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225571653628287602943256195 338357480442431404414884293)
            ·
              refine ⟨63442027582955888327790805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 338357480442431404414884293 63442027582955888327790805)
              ·
                refine ⟨1486922521475528632682597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 63442027582955888327790805 1486922521475528632682597)
                ·
                  refine ⟨278797972776661618627987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1486922521475528632682597 278797972776661618627987)
                  ·
                    rfl

theorem cell22_2443307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 4].length) (baseStart_2443307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443307 prefixEnd_2443307 := by exact prefixLift 2443307
  have htrace : WordTrace (prefixWord ++ tailWord_2443307) baseStart_2443307 baseEnd_2443307 := by
    simpa [prefixWord, tailWord_2443307, baseEnd_2443307] using wordTrace_append hprefix tailTrace_2443307
  have hstable : (prefixWord ++ tailWord_2443307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443307).length < 2 ^ (prefixWord ++ tailWord_2443307).sum := by decide
  have hdescent : baseEnd_2443307 < baseStart_2443307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443472 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 8, 4]
def baseStart_2443472 : Nat := 118140960795 + 2443472 * 2 ^ 59
def prefixEnd_2443472 : Nat := 4983230072969 + 3 ^ 40 * 2443472 * 2
def baseEnd_2443472 : Nat := 836450401201979425508455

theorem tailTrace_2443472 : CollatzResearch.WordTrace tailWord_2443472 prefixEnd_2443472 836450401201979425508455 := by
  unfold tailWord_2443472
  simp only [CollatzResearch.WordTrace]
  refine ⟨44560372701862865319410335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59413830269150487092547113 44560372701862865319410335)
  ·
    refine ⟨66840559052794297979115503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44560372701862865319410335 66840559052794297979115503)
    ·
      refine ⟨100260838579191446968673255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66840559052794297979115503 100260838579191446968673255)
      ·
        refine ⟨150391257868787170453009883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100260838579191446968673255 150391257868787170453009883)
        ·
          refine ⟨225586886803180755679514825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150391257868787170453009883 225586886803180755679514825)
          ·
            refine ⟨169190165102385566759636119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225586886803180755679514825 169190165102385566759636119)
            ·
              refine ⟨253785247653578350139454179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169190165102385566759636119 253785247653578350139454179)
              ·
                refine ⟨380677871480367525209181269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253785247653578350139454179 380677871480367525209181269)
                ·
                  refine ⟨4461068806410556936045093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 380677871480367525209181269 4461068806410556936045093)
                  ·
                    refine ⟨836450401201979425508455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4461068806410556936045093 836450401201979425508455)
                    ·
                      rfl

theorem cell22_2443472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_2443472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443472 prefixEnd_2443472 := by exact prefixLift 2443472
  have htrace : WordTrace (prefixWord ++ tailWord_2443472) baseStart_2443472 baseEnd_2443472 := by
    simpa [prefixWord, tailWord_2443472, baseEnd_2443472] using wordTrace_append hprefix tailTrace_2443472
  have hstable : (prefixWord ++ tailWord_2443472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443472).length < 2 ^ (prefixWord ++ tailWord_2443472).sum := by decide
  have hdescent : baseEnd_2443472 < baseStart_2443472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443478 : List Nat := [5, 2, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2443478 : Nat := 118140960795 + 2443478 * 2 ^ 59
def prefixEnd_2443478 : Nat := 4983230072969 + 3 ^ 40 * 2443478 * 2
def baseEnd_2443478 : Nat := 836452455124597409858437

theorem tailTrace_2443478 : CollatzResearch.WordTrace tailWord_2443478 prefixEnd_2443478 836452455124597409858437 := by
  unfold tailWord_2443478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570060265106499603971193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59413976161135995775692725 5570060265106499603971193)
  ·
    refine ⟨4177545198829874702978395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5570060265106499603971193 4177545198829874702978395)
    ·
      refine ⟨6266317798244812054467593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4177545198829874702978395 6266317798244812054467593)
      ·
        refine ⟨4699738348683609040850695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6266317798244812054467593 4699738348683609040850695)
        ·
          refine ⟨7049607523025413561276043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4699738348683609040850695 7049607523025413561276043)
          ·
            refine ⟨10574411284538120341914065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7049607523025413561276043 10574411284538120341914065)
            ·
              refine ⟨7930808463403590256435549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10574411284538120341914065 7930808463403590256435549)
              ·
                refine ⟨2974053173776346346163331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7930808463403590256435549 2974053173776346346163331)
                ·
                  refine ⟨4461079760664519519244997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2974053173776346346163331 4461079760664519519244997)
                  ·
                    refine ⟨836452455124597409858437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4461079760664519519244997 836452455124597409858437)
                    ·
                      rfl

theorem cell22_2443478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2443478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443478 prefixEnd_2443478 := by exact prefixLift 2443478
  have htrace : WordTrace (prefixWord ++ tailWord_2443478) baseStart_2443478 baseEnd_2443478 := by
    simpa [prefixWord, tailWord_2443478, baseEnd_2443478] using wordTrace_append hprefix tailTrace_2443478
  have hstable : (prefixWord ++ tailWord_2443478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443478).length < 2 ^ (prefixWord ++ tailWord_2443478).sum := by decide
  have hdescent : baseEnd_2443478 < baseStart_2443478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443489 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 2, 4]
def baseStart_2443489 : Nat := 118140960795 + 2443489 * 2 ^ 59
def prefixEnd_2443489 : Nat := 4983230072969 + 3 ^ 40 * 2443489 * 2
def baseEnd_2443489 : Nat := 836456220649397047833403

theorem tailTrace_2443489 : CollatzResearch.WordTrace tailWord_2443489 prefixEnd_2443489 836456220649397047833403 := by
  unfold tailWord_2443489
  simp only [CollatzResearch.WordTrace]
  refine ⟨89121365444664142542189521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59414243629776095028126347 89121365444664142542189521)
  ·
    refine ⟨66841024083498106906642141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89121365444664142542189521 66841024083498106906642141)
    ·
      refine ⟨25065384031311790089990803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66841024083498106906642141 25065384031311790089990803)
      ·
        refine ⟨37598076046967685134986205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25065384031311790089990803 37598076046967685134986205)
        ·
          refine ⟨14099278517612881925619827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37598076046967685134986205 14099278517612881925619827)
          ·
            refine ⟨21148917776419322888429741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14099278517612881925619827 21148917776419322888429741)
            ·
              refine ⟨7930844166157246083161153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21148917776419322888429741 7930844166157246083161153)
              ·
                refine ⟨5948133124617934562370865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7930844166157246083161153 5948133124617934562370865)
                ·
                  refine ⟨4461099843463450921778149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5948133124617934562370865 4461099843463450921778149)
                  ·
                    refine ⟨836456220649397047833403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4461099843463450921778149 836456220649397047833403)
                    ·
                      rfl

theorem cell22_2443489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_2443489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443489 prefixEnd_2443489 := by exact prefixLift 2443489
  have htrace : WordTrace (prefixWord ++ tailWord_2443489) baseStart_2443489 baseEnd_2443489 := by
    simpa [prefixWord, tailWord_2443489, baseEnd_2443489] using wordTrace_append hprefix tailTrace_2443489
  have hstable : (prefixWord ++ tailWord_2443489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443489).length < 2 ^ (prefixWord ++ tailWord_2443489).sum := by decide
  have hdescent : baseEnd_2443489 < baseStart_2443489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443493 : List Nat := [1, 3, 1, 4, 2, 2, 3, 2, 4]
def baseStart_2443493 : Nat := 118140960795 + 2443493 * 2 ^ 59
def prefixEnd_2443493 : Nat := 4983230072969 + 3 ^ 40 * 2443493 * 2
def baseEnd_2443493 : Nat := 278819196643714123577797

theorem tailTrace_2443493 : CollatzResearch.WordTrace tailWord_2443493 prefixEnd_2443493 278819196643714123577797 := by
  unfold tailWord_2443493
  simp only [CollatzResearch.WordTrace]
  refine ⟨89121511336649651225335133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59414340891099767483556755 89121511336649651225335133)
  ·
    refine ⟨33420566751243619209500675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89121511336649651225335133 33420566751243619209500675)
    ·
      refine ⟨50130850126865428814251013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33420566751243619209500675 50130850126865428814251013)
      ·
        refine ⟨9399534398787267902672065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50130850126865428814251013 9399534398787267902672065)
        ·
          refine ⟨7049650799090450927004049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9399534398787267902672065 7049650799090450927004049)
          ·
            refine ⟨5287238099317838195253037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7049650799090450927004049 5287238099317838195253037)
            ·
              refine ⟨1982714287244189323219889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5287238099317838195253037 1982714287244189323219889)
              ·
                refine ⟨1487035715433141992414917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1982714287244189323219889 1487035715433141992414917)
                ·
                  refine ⟨278819196643714123577797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487035715433141992414917 278819196643714123577797)
                  ·
                    rfl

theorem cell22_2443493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_2443493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443493 prefixEnd_2443493 := by exact prefixLift 2443493
  have htrace : WordTrace (prefixWord ++ tailWord_2443493) baseStart_2443493 baseEnd_2443493 := by
    simpa [prefixWord, tailWord_2443493, baseEnd_2443493] using wordTrace_append hprefix tailTrace_2443493
  have hstable : (prefixWord ++ tailWord_2443493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443493).length < 2 ^ (prefixWord ++ tailWord_2443493).sum := by decide
  have hdescent : baseEnd_2443493 < baseStart_2443493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443519 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 5, 3]
def baseStart_2443519 : Nat := 118140960795 + 2443519 * 2 ^ 59
def prefixEnd_2443519 : Nat := 4983230072969 + 3 ^ 40 * 2443519 * 2
def baseEnd_2443519 : Nat := 836466490262486969583311

theorem tailTrace_2443519 : CollatzResearch.WordTrace tailWord_2443519 prefixEnd_2443519 836466490262486969583311 := by
  unfold tailWord_2443519
  simp only [CollatzResearch.WordTrace]
  refine ⟨89122459634555457665781611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59414973089703638443854407 89122459634555457665781611)
  ·
    refine ⟨133683689451833186498672417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89122459634555457665781611 133683689451833186498672417)
    ·
      refine ⟨100262767088874889874004313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133683689451833186498672417 100262767088874889874004313)
      ·
        refine ⟨75197075316656167405503235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100262767088874889874004313 75197075316656167405503235)
        ·
          refine ⟨112795612974984251108254853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75197075316656167405503235 112795612974984251108254853)
          ·
            refine ⟨21149177432809547082797785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112795612974984251108254853 21149177432809547082797785)
            ·
              refine ⟨15861883074607160312098339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21149177432809547082797785 15861883074607160312098339)
              ·
                refine ⟨23792824611910740468147509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15861883074607160312098339 23792824611910740468147509)
                ·
                  refine ⟨2230577307366631918888829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23792824611910740468147509 2230577307366631918888829)
                  ·
                    refine ⟨836466490262486969583311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2230577307366631918888829 836466490262486969583311)
                    ·
                      rfl

theorem cell22_2443519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 3].length) (baseStart_2443519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443519 prefixEnd_2443519 := by exact prefixLift 2443519
  have htrace : WordTrace (prefixWord ++ tailWord_2443519) baseStart_2443519 baseEnd_2443519 := by
    simpa [prefixWord, tailWord_2443519, baseEnd_2443519] using wordTrace_append hprefix tailTrace_2443519
  have hstable : (prefixWord ++ tailWord_2443519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443519).length < 2 ^ (prefixWord ++ tailWord_2443519).sum := by decide
  have hdescent : baseEnd_2443519 < baseStart_2443519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443596 : List Nat := [2, 2, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_2443596 : Nat := 118140960795 + 2443596 * 2 ^ 59
def prefixEnd_2443596 : Nat := 4983230072969 + 3 ^ 40 * 2443596 * 2
def baseEnd_2443596 : Nat := 836492848936084435408075

theorem tailTrace_2443596 : CollatzResearch.WordTrace tailWord_2443596 prefixEnd_2443596 836492848936084435408075 := by
  unfold tailWord_2443596
  simp only [CollatzResearch.WordTrace]
  refine ⟨44562634027638249908167321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59416845370184333210889761 44562634027638249908167321)
  ·
    refine ⟨33421975520728687431125491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44562634027638249908167321 33421975520728687431125491)
    ·
      refine ⟨50132963281093031146688237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33421975520728687431125491 50132963281093031146688237)
      ·
        refine ⟨18799861230409886680008089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50132963281093031146688237 18799861230409886680008089)
        ·
          refine ⟨14099895922807415010006067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18799861230409886680008089 14099895922807415010006067)
          ·
            refine ⟨21149843884211122515009101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14099895922807415010006067 21149843884211122515009101)
            ·
              refine ⟨7931191456579170943128413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21149843884211122515009101 7931191456579170943128413)
              ·
                refine ⟨2974196796217189103673155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7931191456579170943128413 2974196796217189103673155)
                ·
                  refine ⟨4461295194325783655509733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2974196796217189103673155 4461295194325783655509733)
                  ·
                    refine ⟨836492848936084435408075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4461295194325783655509733 836492848936084435408075)
                    ·
                      rfl

theorem cell22_2443596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_2443596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443596 prefixEnd_2443596 := by exact prefixLift 2443596
  have htrace : WordTrace (prefixWord ++ tailWord_2443596) baseStart_2443596 baseEnd_2443596 := by
    simpa [prefixWord, tailWord_2443596, baseEnd_2443596] using wordTrace_append hprefix tailTrace_2443596
  have hstable : (prefixWord ++ tailWord_2443596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443596).length < 2 ^ (prefixWord ++ tailWord_2443596).sum := by decide
  have hdescent : baseEnd_2443596 < baseStart_2443596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443669 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_2443669 : Nat := 118140960795 + 2443669 * 2 ^ 59
def prefixEnd_2443669 : Nat := 4983230072969 + 3 ^ 40 * 2443669 * 2
def baseEnd_2443669 : Nat := 836517838327936578332851

theorem tailTrace_2443669 : CollatzResearch.WordTrace tailWord_2443669 prefixEnd_2443669 836517838327936578332851 := by
  unfold tailWord_2443669
  simp only [CollatzResearch.WordTrace]
  refine ⟨89127930584012033283742061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59418620389341355522494707 89127930584012033283742061)
  ·
    refine ⟨33422973969004512481403273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89127930584012033283742061 33422973969004512481403273)
    ·
      refine ⟨25067230476753384361052455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33422973969004512481403273 25067230476753384361052455)
      ·
        refine ⟨37600845715130076541578683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25067230476753384361052455 37600845715130076541578683)
        ·
          refine ⟨56401268572695114812368025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37600845715130076541578683 56401268572695114812368025)
          ·
            refine ⟨42300951429521336109276019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56401268572695114812368025 42300951429521336109276019)
            ·
              refine ⟨63451427144282004163914029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42300951429521336109276019 63451427144282004163914029)
              ·
                refine ⟨23794285179105751561467761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63451427144282004163914029 23794285179105751561467761)
                ·
                  refine ⟨17845713884329313671100821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23794285179105751561467761 17845713884329313671100821)
                  ·
                    refine ⟨836517838327936578332851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17845713884329313671100821 836517838327936578332851)
                    ·
                      rfl

theorem cell22_2443669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_2443669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443669 prefixEnd_2443669 := by exact prefixLift 2443669
  have htrace : WordTrace (prefixWord ++ tailWord_2443669) baseStart_2443669 baseEnd_2443669 := by
    simpa [prefixWord, tailWord_2443669, baseEnd_2443669] using wordTrace_append hprefix tailTrace_2443669
  have hstable : (prefixWord ++ tailWord_2443669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443669).length < 2 ^ (prefixWord ++ tailWord_2443669).sum := by decide
  have hdescent : baseEnd_2443669 < baseStart_2443669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443677 : List Nat := [1, 4, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_2443677 : Nat := 118140960795 + 2443677 * 2 ^ 59
def prefixEnd_2443677 : Nat := 4983230072969 + 3 ^ 40 * 2443677 * 2
def baseEnd_2443677 : Nat := 836520576891427224132827

theorem tailTrace_2443677 : CollatzResearch.WordTrace tailWord_2443677 prefixEnd_2443677 836520576891427224132827 := by
  unfold tailWord_2443677
  simp only [CollatzResearch.WordTrace]
  refine ⟨89128222367983050650033285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59418814911988700433355523 89128222367983050650033285)
  ·
    refine ⟨16711541693996821996881241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89128222367983050650033285 16711541693996821996881241)
    ·
      refine ⟨12533656270497616497660931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16711541693996821996881241 12533656270497616497660931)
      ·
        refine ⟨18800484405746424746491397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12533656270497616497660931 18800484405746424746491397)
        ·
          refine ⟨3525090826077454639967137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18800484405746424746491397 3525090826077454639967137)
          ·
            refine ⟨2643818119558090979975353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3525090826077454639967137 2643818119558090979975353)
            ·
              refine ⟨1982863589668568234981515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2643818119558090979975353 1982863589668568234981515)
              ·
                refine ⟨2974295384502852352472273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982863589668568234981515 2974295384502852352472273)
                ·
                  refine ⟨2230721538377139264354205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974295384502852352472273 2230721538377139264354205)
                  ·
                    refine ⟨836520576891427224132827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2230721538377139264354205 836520576891427224132827)
                    ·
                      rfl

theorem cell22_2443677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_2443677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443677 prefixEnd_2443677 := by exact prefixLift 2443677
  have htrace : WordTrace (prefixWord ++ tailWord_2443677) baseStart_2443677 baseEnd_2443677 := by
    simpa [prefixWord, tailWord_2443677, baseEnd_2443677] using wordTrace_append hprefix tailTrace_2443677
  have hstable : (prefixWord ++ tailWord_2443677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443677).length < 2 ^ (prefixWord ++ tailWord_2443677).sum := by decide
  have hdescent : baseEnd_2443677 < baseStart_2443677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443699 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 6, 5]
def baseStart_2443699 : Nat := 118140960795 + 2443699 * 2 ^ 59
def prefixEnd_2443699 : Nat := 4983230072969 + 3 ^ 40 * 2443699 * 2
def baseEnd_2443699 : Nat := 836528107941026500082759

theorem tailTrace_2443699 : CollatzResearch.WordTrace tailWord_2443699 prefixEnd_2443699 836528107941026500082759 := by
  unfold tailWord_2443699
  simp only [CollatzResearch.WordTrace]
  refine ⟨89129024773903348407334151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59419349849268898938222767 89129024773903348407334151)
  ·
    refine ⟨133693537160855022611001227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89129024773903348407334151 133693537160855022611001227)
    ·
      refine ⟨200540305741282533916501841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133693537160855022611001227 200540305741282533916501841)
      ·
        refine ⟨150405229305961900437376381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200540305741282533916501841 150405229305961900437376381)
        ·
          refine ⟨56401960989735712664016143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150405229305961900437376381 56401960989735712664016143)
          ·
            refine ⟨84602941484603568996024215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56401960989735712664016143 84602941484603568996024215)
            ·
              refine ⟨126904412226905353494036323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84602941484603568996024215 126904412226905353494036323)
              ·
                refine ⟨190356618340358030241054485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126904412226905353494036323 190356618340358030241054485)
                ·
                  refine ⟨8922966484704282667549429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 190356618340358030241054485 8922966484704282667549429)
                  ·
                    refine ⟨836528107941026500082759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8922966484704282667549429 836528107941026500082759)
                    ·
                      rfl

theorem cell22_2443699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_2443699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443699 prefixEnd_2443699 := by exact prefixLift 2443699
  have htrace : WordTrace (prefixWord ++ tailWord_2443699) baseStart_2443699 baseEnd_2443699 := by
    simpa [prefixWord, tailWord_2443699, baseEnd_2443699] using wordTrace_append hprefix tailTrace_2443699
  have hstable : (prefixWord ++ tailWord_2443699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443699).length < 2 ^ (prefixWord ++ tailWord_2443699).sum := by decide
  have hdescent : baseEnd_2443699 < baseStart_2443699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443729 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 10]
def baseStart_2443729 : Nat := 118140960795 + 2443729 * 2 ^ 59
def prefixEnd_2443729 : Nat := 4983230072969 + 3 ^ 40 * 2443729 * 2
def baseEnd_2443729 : Nat := 278846125851372140610889

theorem tailTrace_2443729 : CollatzResearch.WordTrace tailWord_2443729 prefixEnd_2443729 278846125851372140610889 := by
  unfold tailWord_2443729
  simp only [CollatzResearch.WordTrace]
  refine ⟨89130118963794663530926241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59420079309196442353950827 89130118963794663530926241)
  ·
    refine ⟨66847589222845997648194681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89130118963794663530926241 66847589222845997648194681)
    ·
      refine ⟨50135691917134498236146011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66847589222845997648194681 50135691917134498236146011)
      ·
        refine ⟨75203537875701747354219017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50135691917134498236146011 75203537875701747354219017)
        ·
          refine ⟨56402653406776310515664263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75203537875701747354219017 56402653406776310515664263)
          ·
            refine ⟨84603980110164465773496395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56402653406776310515664263 84603980110164465773496395)
            ·
              refine ⟨126905970165246698660244593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84603980110164465773496395 126905970165246698660244593)
              ·
                refine ⟨95179477623935023995183445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126905970165246698660244593 95179477623935023995183445)
                ·
                  refine ⟨278846125851372140610889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 95179477623935023995183445 278846125851372140610889)
                  ·
                    rfl

theorem cell22_2443729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_2443729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443729 prefixEnd_2443729 := by exact prefixLift 2443729
  have htrace : WordTrace (prefixWord ++ tailWord_2443729) baseStart_2443729 baseEnd_2443729 := by
    simpa [prefixWord, tailWord_2443729, baseEnd_2443729] using wordTrace_append hprefix tailTrace_2443729
  have hstable : (prefixWord ++ tailWord_2443729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443729).length < 2 ^ (prefixWord ++ tailWord_2443729).sum := by decide
  have hdescent : baseEnd_2443729 < baseStart_2443729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443761 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 1, 5]
def baseStart_2443761 : Nat := 118140960795 + 2443761 * 2 ^ 59
def prefixEnd_2443761 : Nat := 4983230072969 + 3 ^ 40 * 2443761 * 2
def baseEnd_2443761 : Nat := 836549331808079005032569

theorem tailTrace_2443761 : CollatzResearch.WordTrace tailWord_2443761 prefixEnd_2443761 836549331808079005032569 := by
  unfold tailWord_2443761
  simp only [CollatzResearch.WordTrace]
  refine ⟨89131286099678732996091137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59420857399785821997394091 89131286099678732996091137)
  ·
    refine ⟨66848464574759049747068353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89131286099678732996091137 66848464574759049747068353)
    ·
      refine ⟨50136348431069287310301265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66848464574759049747068353 50136348431069287310301265)
      ·
        refine ⟨37602261323301965482725949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50136348431069287310301265 37602261323301965482725949)
        ·
          refine ⟨14100847996238237056022231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37602261323301965482725949 14100847996238237056022231)
          ·
            refine ⟨21151271994357355584033347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14100847996238237056022231 21151271994357355584033347)
            ·
              refine ⟨31726907991536033376050021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21151271994357355584033347 31726907991536033376050021)
              ·
                refine ⟨5948795248413006258009379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31726907991536033376050021 5948795248413006258009379)
                ·
                  refine ⟨8923192872619509387014069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5948795248413006258009379 8923192872619509387014069)
                  ·
                    refine ⟨836549331808079005032569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8923192872619509387014069 836549331808079005032569)
                    ·
                      rfl

theorem cell22_2443761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_2443761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443761 prefixEnd_2443761 := by exact prefixLift 2443761
  have htrace : WordTrace (prefixWord ++ tailWord_2443761) baseStart_2443761 baseEnd_2443761 := by
    simpa [prefixWord, tailWord_2443761, baseEnd_2443761] using wordTrace_append hprefix tailTrace_2443761
  have hstable : (prefixWord ++ tailWord_2443761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443761).length < 2 ^ (prefixWord ++ tailWord_2443761).sum := by decide
  have hdescent : baseEnd_2443761 < baseStart_2443761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443763 : List Nat := [1, 1, 1, 2, 2, 2, 6, 3, 4]
def baseStart_2443763 : Nat := 118140960795 + 2443763 * 2 ^ 59
def prefixEnd_2443763 : Nat := 4983230072969 + 3 ^ 40 * 2443763 * 2
def baseEnd_2443763 : Nat := 278850005482983888827521

theorem tailTrace_2443763 : CollatzResearch.WordTrace tailWord_2443763 prefixEnd_2443763 278850005482983888827521 := by
  unfold tailWord_2443763
  simp only [CollatzResearch.WordTrace]
  refine ⟨89131359045671487337663943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59420906030447658225109295 89131359045671487337663943)
  ·
    refine ⟨133697038568507231006495915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89131359045671487337663943 133697038568507231006495915)
    ·
      refine ⟨200545557852760846509743873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133697038568507231006495915 200545557852760846509743873)
      ·
        refine ⟨150409168389570634882307905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200545557852760846509743873 150409168389570634882307905)
        ·
          refine ⟨112806876292177976161730929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150409168389570634882307905 112806876292177976161730929)
          ·
            refine ⟨84605157219133482121298197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112806876292177976161730929 84605157219133482121298197)
            ·
              refine ⟨3965866744646881974435853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84605157219133482121298197 3965866744646881974435853)
              ·
                refine ⟨1487200029242580740413445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3965866744646881974435853 1487200029242580740413445)
                ·
                  refine ⟨278850005482983888827521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487200029242580740413445 278850005482983888827521)
                  ·
                    rfl

theorem cell22_2443763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 4].length) (baseStart_2443763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443763 prefixEnd_2443763 := by exact prefixLift 2443763
  have htrace : WordTrace (prefixWord ++ tailWord_2443763) baseStart_2443763 baseEnd_2443763 := by
    simpa [prefixWord, tailWord_2443763, baseEnd_2443763] using wordTrace_append hprefix tailTrace_2443763
  have hstable : (prefixWord ++ tailWord_2443763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443763).length < 2 ^ (prefixWord ++ tailWord_2443763).sum := by decide
  have hdescent : baseEnd_2443763 < baseStart_2443763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443780 : List Nat := [2, 3, 2, 3, 1, 1, 2, 4, 4]
def baseStart_2443780 : Nat := 118140960795 + 2443780 * 2 ^ 59
def prefixEnd_2443780 : Nat := 4983230072969 + 3 ^ 40 * 2443780 * 2
def baseEnd_2443780 : Nat := 278851945298789762935837

theorem tailTrace_2443780 : CollatzResearch.WordTrace tailWord_2443780 prefixEnd_2443780 278851945298789762935837 := by
  unfold tailWord_2443780
  simp only [CollatzResearch.WordTrace]
  refine ⟨44565989543304949620516397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59421319391073266160688529 44565989543304949620516397)
  ·
    refine ⟨16712246078739356107693649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44565989543304949620516397 16712246078739356107693649)
    ·
      refine ⟨12534184559054517080770237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16712246078739356107693649 12534184559054517080770237)
      ·
        refine ⟨4700319209645443905288839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12534184559054517080770237 4700319209645443905288839)
        ·
          refine ⟨7050478814468165857933259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4700319209645443905288839 7050478814468165857933259)
          ·
            refine ⟨10575718221702248786899889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7050478814468165857933259 10575718221702248786899889)
            ·
              refine ⟨7931788666276686590174917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10575718221702248786899889 7931788666276686590174917)
              ·
                refine ⟨1487210374926878735657797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7931788666276686590174917 1487210374926878735657797)
                ·
                  refine ⟨278851945298789762935837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487210374926878735657797 278851945298789762935837)
                  ·
                    rfl

theorem cell22_2443780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_2443780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443780 prefixEnd_2443780 := by exact prefixLift 2443780
  have htrace : WordTrace (prefixWord ++ tailWord_2443780) baseStart_2443780 baseEnd_2443780 := by
    simpa [prefixWord, tailWord_2443780, baseEnd_2443780] using wordTrace_append hprefix tailTrace_2443780
  have hstable : (prefixWord ++ tailWord_2443780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443780).length < 2 ^ (prefixWord ++ tailWord_2443780).sum := by decide
  have hdescent : baseEnd_2443780 < baseStart_2443780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443795 : List Nat := [1, 1, 1, 2, 1, 5, 5, 1, 2, 3]
def baseStart_2443795 : Nat := 118140960795 + 2443795 * 2 ^ 59
def prefixEnd_2443795 : Nat := 4983230072969 + 3 ^ 40 * 2443795 * 2
def baseEnd_2443795 : Nat := 836560970702914249682465

theorem tailTrace_2443795 : CollatzResearch.WordTrace tailWord_2443795 prefixEnd_2443795 836560970702914249682465 := by
  unfold tailWord_2443795
  simp only [CollatzResearch.WordTrace]
  refine ⟨89132526181555556802828839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59421684121037037868552559 89132526181555556802828839)
  ·
    refine ⟨133698789272333335204243259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89132526181555556802828839 133698789272333335204243259)
    ·
      refine ⟨200548183908500002806364889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133698789272333335204243259 200548183908500002806364889)
      ·
        refine ⟨150411137931375002104773667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200548183908500002806364889 150411137931375002104773667)
        ·
          refine ⟨225616706897062503157160501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150411137931375002104773667 225616706897062503157160501)
          ·
            refine ⟨21151566271599609670983797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 225616706897062503157160501 21151566271599609670983797)
            ·
              refine ⟨1982959337962463406654731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21151566271599609670983797 1982959337962463406654731)
              ·
                refine ⟨2974439006943695109982097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982959337962463406654731 2974439006943695109982097)
                ·
                  refine ⟨2230829255207771332486573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974439006943695109982097 2230829255207771332486573)
                  ·
                    refine ⟨836560970702914249682465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2230829255207771332486573 836560970702914249682465)
                    ·
                      rfl

theorem cell22_2443795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 2, 3].length) (baseStart_2443795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443795 prefixEnd_2443795 := by exact prefixLift 2443795
  have htrace : WordTrace (prefixWord ++ tailWord_2443795) baseStart_2443795 baseEnd_2443795 := by
    simpa [prefixWord, tailWord_2443795, baseEnd_2443795] using wordTrace_append hprefix tailTrace_2443795
  have hstable : (prefixWord ++ tailWord_2443795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443795).length < 2 ^ (prefixWord ++ tailWord_2443795).sum := by decide
  have hdescent : baseEnd_2443795 < baseStart_2443795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443808 : List Nat := [2, 1, 1, 6, 2, 1, 1, 8]
def baseStart_2443808 : Nat := 118140960795 + 2443808 * 2 ^ 59
def prefixEnd_2443808 : Nat := 4983230072969 + 3 ^ 40 * 2443808 * 2
def baseEnd_2443808 : Nat := 92951713429842949900825

theorem tailTrace_2443808 : CollatzResearch.WordTrace tailWord_2443808 prefixEnd_2443808 92951713429842949900825 := by
  unfold tailWord_2443808
  simp only [CollatzResearch.WordTrace]
  refine ⟨44566500165254230011526039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59422000220338973348701385 44566500165254230011526039)
  ·
    refine ⟨66849750247881345017289059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44566500165254230011526039 66849750247881345017289059)
    ·
      refine ⟨100274625371822017525933589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66849750247881345017289059 100274625371822017525933589)
      ·
        refine ⟨4700373064304157071528137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100274625371822017525933589 4700373064304157071528137)
        ·
          refine ⟨3525279798228117803646103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4700373064304157071528137 3525279798228117803646103)
          ·
            refine ⟨5287919697342176705469155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3525279798228117803646103 5287919697342176705469155)
            ·
              refine ⟨7931879546013265058203733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5287919697342176705469155 7931879546013265058203733)
              ·
                refine ⟨92951713429842949900825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7931879546013265058203733 92951713429842949900825)
                ·
                  rfl

theorem cell22_2443808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 8].length) (baseStart_2443808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443808 prefixEnd_2443808 := by exact prefixLift 2443808
  have htrace : WordTrace (prefixWord ++ tailWord_2443808) baseStart_2443808 baseEnd_2443808 := by
    simpa [prefixWord, tailWord_2443808, baseEnd_2443808] using wordTrace_append hprefix tailTrace_2443808
  have hstable : (prefixWord ++ tailWord_2443808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443808).length < 2 ^ (prefixWord ++ tailWord_2443808).sum := by decide
  have hdescent : baseEnd_2443808 < baseStart_2443808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443840 : List Nat := [2, 1, 1, 2, 2, 2, 2, 6, 1, 3]
def baseStart_2443840 : Nat := 118140960795 + 2443840 * 2 ^ 59
def prefixEnd_2443840 : Nat := 4983230072969 + 3 ^ 40 * 2443840 * 2
def baseEnd_2443840 : Nat := 836576375122549132307327

theorem tailTrace_2443840 : CollatzResearch.WordTrace tailWord_2443840 prefixEnd_2443840 836576375122549132307327 := by
  unfold tailWord_2443840
  simp only [CollatzResearch.WordTrace]
  refine ⟨44567083733196264744108487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59422778310928352992144649 44567083733196264744108487)
  ·
    refine ⟨66850625599794397116162731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44567083733196264744108487 66850625599794397116162731)
    ·
      refine ⟨100275938399691595674244097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66850625599794397116162731 100275938399691595674244097)
      ·
        refine ⟨75206953799768696755683073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100275938399691595674244097 75206953799768696755683073)
        ·
          refine ⟨56405215349826522566762305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75206953799768696755683073 56405215349826522566762305)
          ·
            refine ⟨42303911512369891925071729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56405215349826522566762305 42303911512369891925071729)
            ·
              refine ⟨31727933634277418943803797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42303911512369891925071729 31727933634277418943803797)
              ·
                refine ⟨1487246889106754012990803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31727933634277418943803797 1487246889106754012990803)
                ·
                  refine ⟨2230870333660131019486205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487246889106754012990803 2230870333660131019486205)
                  ·
                    refine ⟨836576375122549132307327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2230870333660131019486205 836576375122549132307327)
                    ·
                      rfl

theorem cell22_2443840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 1, 3].length) (baseStart_2443840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443840 prefixEnd_2443840 := by exact prefixLift 2443840
  have htrace : WordTrace (prefixWord ++ tailWord_2443840) baseStart_2443840 baseEnd_2443840 := by
    simpa [prefixWord, tailWord_2443840, baseEnd_2443840] using wordTrace_append hprefix tailTrace_2443840
  have hstable : (prefixWord ++ tailWord_2443840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443840).length < 2 ^ (prefixWord ++ tailWord_2443840).sum := by decide
  have hdescent : baseEnd_2443840 < baseStart_2443840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443846 : List Nat := [6, 1, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_2443846 : Nat := 118140960795 + 2443846 * 2 ^ 59
def prefixEnd_2443846 : Nat := 4983230072969 + 3 ^ 40 * 2443846 * 2
def baseEnd_2443846 : Nat := 836578429045167116657309

theorem tailTrace_2443846 : CollatzResearch.WordTrace tailWord_2443846 prefixEnd_2443846 836578429045167116657309 := by
  unfold tailWord_2443846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2785449572011587266029231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59422924202913861675290261 2785449572011587266029231)
  ·
    refine ⟨4178174358017380899043847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2785449572011587266029231 4178174358017380899043847)
    ·
      refine ⟨6267261537026071348565771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4178174358017380899043847 6267261537026071348565771)
      ·
        refine ⟨9400892305539107022848657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6267261537026071348565771 9400892305539107022848657)
        ·
          refine ⟨7050669229154330267136493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9400892305539107022848657 7050669229154330267136493)
          ·
            refine ⟨2644000960932873850176185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7050669229154330267136493 2644000960932873850176185)
            ·
              refine ⟨1983000720699655387632139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2644000960932873850176185 1983000720699655387632139)
              ·
                refine ⟨2974501081049483081448209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983000720699655387632139 2974501081049483081448209)
                ·
                  refine ⟨2230875810787112311086157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974501081049483081448209 2230875810787112311086157)
                  ·
                    refine ⟨836578429045167116657309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2230875810787112311086157 836578429045167116657309)
                    ·
                      rfl

theorem cell22_2443846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_2443846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443846 prefixEnd_2443846 := by exact prefixLift 2443846
  have htrace : WordTrace (prefixWord ++ tailWord_2443846) baseStart_2443846 baseEnd_2443846 := by
    simpa [prefixWord, tailWord_2443846, baseEnd_2443846] using wordTrace_append hprefix tailTrace_2443846
  have hstable : (prefixWord ++ tailWord_2443846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443846).length < 2 ^ (prefixWord ++ tailWord_2443846).sum := by decide
  have hdescent : baseEnd_2443846 < baseStart_2443846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443851 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 2, 5]
def baseStart_2443851 : Nat := 118140960795 + 2443851 * 2 ^ 59
def prefixEnd_2443851 : Nat := 4983230072969 + 3 ^ 40 * 2443851 * 2
def baseEnd_2443851 : Nat := 836580140647348770282293

theorem tailTrace_2443851 : CollatzResearch.WordTrace tailWord_2443851 prefixEnd_2443851 836580140647348770282293 := by
  unfold tailWord_2443851
  simp only [CollatzResearch.WordTrace]
  refine ⟨89134568669352678366867407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59423045779568452244578271 89134568669352678366867407)
  ·
    refine ⟨133701853004029017550301111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89134568669352678366867407 133701853004029017550301111)
    ·
      refine ⟨200552779506043526325451667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133701853004029017550301111 200552779506043526325451667)
      ·
        refine ⟨300829169259065289488177501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200552779506043526325451667 300829169259065289488177501)
        ·
          refine ⟨112810938472149483558066563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300829169259065289488177501 112810938472149483558066563)
          ·
            refine ⟨169216407708224225337099845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112810938472149483558066563 169216407708224225337099845)
            ·
              refine ⟨31728076445292042250706221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169216407708224225337099845 31728076445292042250706221)
              ·
                refine ⟨11898028666984515844014833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31728076445292042250706221 11898028666984515844014833)
                ·
                  refine ⟨8923521500238386883011125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11898028666984515844014833 8923521500238386883011125)
                  ·
                    refine ⟨836580140647348770282293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8923521500238386883011125 836580140647348770282293)
                    ·
                      rfl

theorem cell22_2443851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_2443851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443851 prefixEnd_2443851 := by exact prefixLift 2443851
  have htrace : WordTrace (prefixWord ++ tailWord_2443851) baseStart_2443851 baseEnd_2443851 := by
    simpa [prefixWord, tailWord_2443851, baseEnd_2443851] using wordTrace_append hprefix tailTrace_2443851
  have hstable : (prefixWord ++ tailWord_2443851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443851).length < 2 ^ (prefixWord ++ tailWord_2443851).sum := by decide
  have hdescent : baseEnd_2443851 < baseStart_2443851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443913 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 6, 3]
def baseStart_2443913 : Nat := 118140960795 + 2443913 * 2 ^ 59
def prefixEnd_2443913 : Nat := 4983230072969 + 3 ^ 40 * 2443913 * 2
def baseEnd_2443913 : Nat := 836601364514401275232103

theorem tailTrace_2443913 : CollatzResearch.WordTrace tailWord_2443913 prefixEnd_2443913 836601364514401275232103 := by
  unfold tailWord_2443913
  simp only [CollatzResearch.WordTrace]
  refine ⟨89136829995128062955624393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59424553330085375303749595 89136829995128062955624393)
  ·
    refine ⟨66852622496346047216718295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89136829995128062955624393 66852622496346047216718295)
    ·
      refine ⟨100278933744519070825077443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66852622496346047216718295 100278933744519070825077443)
      ·
        refine ⟨150418400616778606237616165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100278933744519070825077443 150418400616778606237616165)
        ·
          refine ⟨28203450115645988669553031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150418400616778606237616165 28203450115645988669553031)
          ·
            refine ⟨42305175173468983004329547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28203450115645988669553031 42305175173468983004329547)
            ·
              refine ⟨63457762760203474506494321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42305175173468983004329547 63457762760203474506494321)
              ·
                refine ⟨47593322070152605879870741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63457762760203474506494321 47593322070152605879870741)
                ·
                  refine ⟨2230936972038403400618941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47593322070152605879870741 2230936972038403400618941)
                  ·
                    refine ⟨836601364514401275232103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2230936972038403400618941 836601364514401275232103)
                    ·
                      rfl

theorem cell22_2443913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 3].length) (baseStart_2443913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443913 prefixEnd_2443913 := by exact prefixLift 2443913
  have htrace : WordTrace (prefixWord ++ tailWord_2443913) baseStart_2443913 baseEnd_2443913 := by
    simpa [prefixWord, tailWord_2443913, baseEnd_2443913] using wordTrace_append hprefix tailTrace_2443913
  have hstable : (prefixWord ++ tailWord_2443913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443913).length < 2 ^ (prefixWord ++ tailWord_2443913).sum := by decide
  have hdescent : baseEnd_2443913 < baseStart_2443913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443928 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 1, 6]
def baseStart_2443928 : Nat := 118140960795 + 2443928 * 2 ^ 59
def prefixEnd_2443928 : Nat := 4983230072969 + 3 ^ 40 * 2443928 * 2
def baseEnd_2443928 : Nat := 836606499320946236107057

theorem tailTrace_2443928 : CollatzResearch.WordTrace tailWord_2443928 prefixEnd_2443928 836606499320946236107057 := by
  unfold tailWord_2443928
  simp only [CollatzResearch.WordTrace]
  refine ⟨44568688545036860258710219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59424918060049147011613625 44568688545036860258710219)
  ·
    refine ⟨66853032817555290388065329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44568688545036860258710219 66853032817555290388065329)
    ·
      refine ⟨50139774613166467791048997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66853032817555290388065329 50139774613166467791048997)
      ·
        refine ⟨9401207739968712710821687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50139774613166467791048997 9401207739968712710821687)
        ·
          refine ⟨14101811609953069066232531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9401207739968712710821687 14101811609953069066232531)
          ·
            refine ⟨21152717414929603599348797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14101811609953069066232531 21152717414929603599348797)
            ·
              refine ⟨7932269030598601349755799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21152717414929603599348797 7932269030598601349755799)
              ·
                refine ⟨11898403545897902024633699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7932269030598601349755799 11898403545897902024633699)
                ·
                  refine ⟨17847605318846853036950549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11898403545897902024633699 17847605318846853036950549)
                  ·
                    refine ⟨836606499320946236107057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17847605318846853036950549 836606499320946236107057)
                    ·
                      rfl

theorem cell22_2443928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_2443928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443928 prefixEnd_2443928 := by exact prefixLift 2443928
  have htrace : WordTrace (prefixWord ++ tailWord_2443928) baseStart_2443928 baseEnd_2443928 := by
    simpa [prefixWord, tailWord_2443928, baseEnd_2443928] using wordTrace_append hprefix tailTrace_2443928
  have hstable : (prefixWord ++ tailWord_2443928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443928).length < 2 ^ (prefixWord ++ tailWord_2443928).sum := by decide
  have hdescent : baseEnd_2443928 < baseStart_2443928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443932 : List Nat := [2, 2, 3, 2, 2, 2, 2, 3, 4]
def baseStart_2443932 : Nat := 118140960795 + 2443932 * 2 ^ 59
def prefixEnd_2443932 : Nat := 4983230072969 + 3 ^ 40 * 2443932 * 2
def baseEnd_2443932 : Nat := 278869289534230519669015

theorem tailTrace_2443932 : CollatzResearch.WordTrace tailWord_2443932 prefixEnd_2443932 278869289534230519669015 := by
  unfold tailWord_2443932
  simp only [CollatzResearch.WordTrace]
  refine ⟨44568761491029614600283025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59425015321372819467044033 44568761491029614600283025)
  ·
    refine ⟨33426571118272210950212269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44568761491029614600283025 33426571118272210950212269)
    ·
      refine ⟨12534964169352079106329601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33426571118272210950212269 12534964169352079106329601)
      ·
        refine ⟨9401223127014059329747201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12534964169352079106329601 9401223127014059329747201)
        ·
          refine ⟨7050917345260544497310401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9401223127014059329747201 7050917345260544497310401)
          ·
            refine ⟨5288188008945408372982801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7050917345260544497310401 5288188008945408372982801)
            ·
              refine ⟨3966141006709056279737101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5288188008945408372982801 3966141006709056279737101)
              ·
                refine ⟨1487302877515896104901413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3966141006709056279737101 1487302877515896104901413)
                ·
                  refine ⟨278869289534230519669015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487302877515896104901413 278869289534230519669015)
                  ·
                    rfl

theorem cell22_2443932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_2443932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2443932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2443932 prefixEnd_2443932 := by exact prefixLift 2443932
  have htrace : WordTrace (prefixWord ++ tailWord_2443932) baseStart_2443932 baseEnd_2443932 := by
    simpa [prefixWord, tailWord_2443932, baseEnd_2443932] using wordTrace_append hprefix tailTrace_2443932
  have hstable : (prefixWord ++ tailWord_2443932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443932).length < 2 ^ (prefixWord ++ tailWord_2443932).sum := by decide
  have hdescent : baseEnd_2443932 < baseStart_2443932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444033 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 8]
def baseStart_2444033 : Nat := 118140960795 + 2444033 * 2 ^ 59
def prefixEnd_2444033 : Nat := 4983230072969 + 3 ^ 40 * 2444033 * 2
def baseEnd_2444033 : Nat := 278880814322253654077245

theorem tailTrace_2444033 : CollatzResearch.WordTrace tailWord_2444033 prefixEnd_2444033 278880814322253654077245 := by
  unfold tailWord_2444033
  simp only [CollatzResearch.WordTrace]
  refine ⟨89141206754693323449992753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59427471169795548966661835 89141206754693323449992753)
  ·
    refine ⟨66855905066019992587494565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89141206754693323449992753 66855905066019992587494565)
    ·
      refine ⟨12535482199878748610155231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66855905066019992587494565 12535482199878748610155231)
      ·
        refine ⟨18803223299818122915232847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12535482199878748610155231 18803223299818122915232847)
        ·
          refine ⟨28204834949727184372849271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18803223299818122915232847 28204834949727184372849271)
          ·
            refine ⟨42307252424590776559273907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28204834949727184372849271 42307252424590776559273907)
            ·
              refine ⟨63460878636886164838910861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42307252424590776559273907 63460878636886164838910861)
              ·
                refine ⟨23797829488832311814591573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63460878636886164838910861 23797829488832311814591573)
                ·
                  refine ⟨278880814322253654077245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23797829488832311814591573 278880814322253654077245)
                  ·
                    rfl

theorem cell22_2444033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_2444033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444033 prefixEnd_2444033 := by exact prefixLift 2444033
  have htrace : WordTrace (prefixWord ++ tailWord_2444033) baseStart_2444033 baseEnd_2444033 := by
    simpa [prefixWord, tailWord_2444033, baseEnd_2444033] using wordTrace_append hprefix tailTrace_2444033
  have hstable : (prefixWord ++ tailWord_2444033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444033).length < 2 ^ (prefixWord ++ tailWord_2444033).sum := by decide
  have hdescent : baseEnd_2444033 < baseStart_2444033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444082 : List Nat := [3, 2, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_2444082 : Nat := 118140960795 + 2444082 * 2 ^ 59
def prefixEnd_2444082 : Nat := 4983230072969 + 3 ^ 40 * 2444082 * 2
def baseEnd_2444082 : Nat := 836659216668141167756585

theorem tailTrace_2444082 : CollatzResearch.WordTrace tailWord_2444082 prefixEnd_2444082 836659216668141167756585 := by
  unfold tailWord_2444082
  simp only [CollatzResearch.WordTrace]
  refine ⟨22285748482878951204631625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59428662621010536545684333 22285748482878951204631625)
  ·
    refine ⟨16714311362159213403473719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22285748482878951204631625 16714311362159213403473719)
    ·
      refine ⟨25071467043238820105210579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16714311362159213403473719 25071467043238820105210579)
      ·
        refine ⟨37607200564858230157815869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25071467043238820105210579 37607200564858230157815869)
        ·
          refine ⟨14102700211821836309180951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37607200564858230157815869 14102700211821836309180951)
          ·
            refine ⟨21154050317732754463771427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14102700211821836309180951 21154050317732754463771427)
            ·
              refine ⟨31731075476599131695657141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21154050317732754463771427 31731075476599131695657141)
              ·
                refine ⟨2974788325931168596467857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31731075476599131695657141 2974788325931168596467857)
                ·
                  refine ⟨2231091244448376447350893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974788325931168596467857 2231091244448376447350893)
                  ·
                    refine ⟨836659216668141167756585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2231091244448376447350893 836659216668141167756585)
                    ·
                      rfl

theorem cell22_2444082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_2444082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444082 prefixEnd_2444082 := by exact prefixLift 2444082
  have htrace : WordTrace (prefixWord ++ tailWord_2444082) baseStart_2444082 baseEnd_2444082 := by
    simpa [prefixWord, tailWord_2444082, baseEnd_2444082] using wordTrace_append hprefix tailTrace_2444082
  have hstable : (prefixWord ++ tailWord_2444082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444082).length < 2 ^ (prefixWord ++ tailWord_2444082).sum := by decide
  have hdescent : baseEnd_2444082 < baseStart_2444082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444116 : List Nat := [2, 4, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_2444116 : Nat := 118140960795 + 2444116 * 2 ^ 59
def prefixEnd_2444116 : Nat := 4983230072969 + 3 ^ 40 * 2444116 * 2
def baseEnd_2444116 : Nat := 836670855562976412406481

theorem tailTrace_2444116 : CollatzResearch.WordTrace tailWord_2444116 prefixEnd_2444116 836670855562976412406481 := by
  unfold tailWord_2444116
  simp only [CollatzResearch.WordTrace]
  refine ⟨44572117006696314312632101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59429489342261752416842801 44572117006696314312632101)
  ·
    refine ⟨8357271938755558933618519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44572117006696314312632101 8357271938755558933618519)
    ·
      refine ⟨12535907908133338400427779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8357271938755558933618519 12535907908133338400427779)
      ·
        refine ⟨18803861862200007600641669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12535907908133338400427779 18803861862200007600641669)
        ·
          refine ⟨3525724099162501425120313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18803861862200007600641669 3525724099162501425120313)
          ·
            refine ⟨2644293074371876068840235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3525724099162501425120313 2644293074371876068840235)
            ·
              refine ⟨3966439611557814103260353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644293074371876068840235 3966439611557814103260353)
              ·
                refine ⟨2974829708668360577445265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966439611557814103260353 2974829708668360577445265)
                ·
                  refine ⟨2231122281501270433083949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974829708668360577445265 2231122281501270433083949)
                  ·
                    refine ⟨836670855562976412406481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2231122281501270433083949 836670855562976412406481)
                    ·
                      rfl

theorem cell22_2444116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_2444116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444116 prefixEnd_2444116 := by exact prefixLift 2444116
  have htrace : WordTrace (prefixWord ++ tailWord_2444116) baseStart_2444116 baseEnd_2444116 := by
    simpa [prefixWord, tailWord_2444116, baseEnd_2444116] using wordTrace_append hprefix tailTrace_2444116
  have hstable : (prefixWord ++ tailWord_2444116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444116).length < 2 ^ (prefixWord ++ tailWord_2444116).sum := by decide
  have hdescent : baseEnd_2444116 < baseStart_2444116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444127 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 3, 3]
def baseStart_2444127 : Nat := 118140960795 + 2444127 * 2 ^ 59
def prefixEnd_2444127 : Nat := 4983230072969 + 3 ^ 40 * 2444127 * 2
def baseEnd_2444127 : Nat := 836674621087776050381447

theorem tailTrace_2444127 : CollatzResearch.WordTrace tailWord_2444127 prefixEnd_2444127 836674621087776050381447 := by
  unfold tailWord_2444127
  simp only [CollatzResearch.WordTrace]
  refine ⟨89144635216352777503914635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59429756810901851669276423 89144635216352777503914635)
  ·
    refine ⟨133716952824529166255871953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89144635216352777503914635 133716952824529166255871953)
    ·
      refine ⟨100287714618396874691903965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133716952824529166255871953 100287714618396874691903965)
      ·
        refine ⟨37607892981898828009463987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100287714618396874691903965 37607892981898828009463987)
        ·
          refine ⟨56411839472848242014195981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37607892981898828009463987 56411839472848242014195981)
          ·
            refine ⟨21154439802318090755323493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56411839472848242014195981 21154439802318090755323493)
            ·
              refine ⟨3966457462934642016623155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21154439802318090755323493 3966457462934642016623155)
              ·
                refine ⟨5949686194401963024934733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3966457462934642016623155 5949686194401963024934733)
                ·
                  refine ⟨2231132322900736134350525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5949686194401963024934733 2231132322900736134350525)
                  ·
                    refine ⟨836674621087776050381447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2231132322900736134350525 836674621087776050381447)
                    ·
                      rfl

theorem cell22_2444127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 3].length) (baseStart_2444127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444127 prefixEnd_2444127 := by exact prefixLift 2444127
  have htrace : WordTrace (prefixWord ++ tailWord_2444127) baseStart_2444127 baseEnd_2444127 := by
    simpa [prefixWord, tailWord_2444127, baseEnd_2444127] using wordTrace_append hprefix tailTrace_2444127
  have hstable : (prefixWord ++ tailWord_2444127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444127).length < 2 ^ (prefixWord ++ tailWord_2444127).sum := by decide
  have hdescent : baseEnd_2444127 < baseStart_2444127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444178 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_2444178 : Nat := 118140960795 + 2444178 * 2 ^ 59
def prefixEnd_2444178 : Nat := 4983230072969 + 3 ^ 40 * 2444178 * 2
def baseEnd_2444178 : Nat := 836692079430028917356291

theorem tailTrace_2444178 : CollatzResearch.WordTrace tailWord_2444178 prefixEnd_2444178 836692079430028917356291 := by
  unfold tailWord_2444178
  simp only [CollatzResearch.WordTrace]
  refine ⟨22286623834792003303505297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59430996892778675476014125 22286623834792003303505297)
  ·
    refine ⟨16714967876094002477628973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22286623834792003303505297 16714967876094002477628973)
    ·
      refine ⟨6268112953535250929110865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16714967876094002477628973 6268112953535250929110865)
      ·
        refine ⟨4701084715151438196833149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6268112953535250929110865 4701084715151438196833149)
        ·
          refine ⟨1762906768181789323812431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4701084715151438196833149 1762906768181789323812431)
          ·
            refine ⟨2644360152272683985718647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1762906768181789323812431 2644360152272683985718647)
            ·
              refine ⟨3966540228409025978577971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644360152272683985718647 3966540228409025978577971)
              ·
                refine ⟨5949810342613538967866957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3966540228409025978577971 5949810342613538967866957)
                ·
                  refine ⟨2231178878480077112950109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5949810342613538967866957 2231178878480077112950109)
                  ·
                    refine ⟨836692079430028917356291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2231178878480077112950109 836692079430028917356291)
                    ·
                      rfl

theorem cell22_2444178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_2444178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444178 prefixEnd_2444178 := by exact prefixLift 2444178
  have htrace : WordTrace (prefixWord ++ tailWord_2444178) baseStart_2444178 baseEnd_2444178 := by
    simpa [prefixWord, tailWord_2444178, baseEnd_2444178] using wordTrace_append hprefix tailTrace_2444178
  have hstable : (prefixWord ++ tailWord_2444178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444178).length < 2 ^ (prefixWord ++ tailWord_2444178).sum := by decide
  have hdescent : baseEnd_2444178 < baseStart_2444178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444215 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 1, 6]
def baseStart_2444215 : Nat := 118140960795 + 2444215 * 2 ^ 59
def prefixEnd_2444215 : Nat := 4983230072969 + 3 ^ 40 * 2444215 * 2
def baseEnd_2444215 : Nat := 836704745286173154181177

theorem tailTrace_2444215 : CollatzResearch.WordTrace tailWord_2444215 prefixEnd_2444215 836704745286173154181177 := by
  unfold tailWord_2444215
  simp only [CollatzResearch.WordTrace]
  refine ⟨89147844840033968533118099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59431896560022645688745399 89147844840033968533118099)
  ·
    refine ⟨133721767260050952799677149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89147844840033968533118099 133721767260050952799677149)
    ·
      refine ⟨50145662722519107299878931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133721767260050952799677149 50145662722519107299878931)
      ·
        refine ⟨75218494083778660949818397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50145662722519107299878931 75218494083778660949818397)
        ·
          refine ⟨28206935281416997856181899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75218494083778660949818397 28206935281416997856181899)
          ·
            refine ⟨42310402922125496784272849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28206935281416997856181899 42310402922125496784272849)
            ·
              refine ⟨31732802191594122588204637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42310402922125496784272849 31732802191594122588204637)
              ·
                refine ⟨11899800821847795970576739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31732802191594122588204637 11899800821847795970576739)
                ·
                  refine ⟨17849701232771693955865109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11899800821847795970576739 17849701232771693955865109)
                  ·
                    refine ⟨836704745286173154181177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17849701232771693955865109 836704745286173154181177)
                    ·
                      rfl

theorem cell22_2444215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_2444215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444215 prefixEnd_2444215 := by exact prefixLift 2444215
  have htrace : WordTrace (prefixWord ++ tailWord_2444215) baseStart_2444215 baseEnd_2444215 := by
    simpa [prefixWord, tailWord_2444215, baseEnd_2444215] using wordTrace_append hprefix tailTrace_2444215
  have hstable : (prefixWord ++ tailWord_2444215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444215).length < 2 ^ (prefixWord ++ tailWord_2444215).sum := by decide
  have hdescent : baseEnd_2444215 < baseStart_2444215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444217 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 1, 5]
def baseStart_2444217 : Nat := 118140960795 + 2444217 * 2 ^ 59
def prefixEnd_2444217 : Nat := 4983230072969 + 3 ^ 40 * 2444217 * 2
def baseEnd_2444217 : Nat := 836705429927045815631171

theorem tailTrace_2444217 : CollatzResearch.WordTrace tailWord_2444217 prefixEnd_2444217 836705429927045815631171 := by
  unfold tailWord_2444217
  simp only [CollatzResearch.WordTrace]
  refine ⟨89147917786026722874690905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59431945190684481916460603 89147917786026722874690905)
  ·
    refine ⟨66860938339520042156018179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89147917786026722874690905 66860938339520042156018179)
    ·
      refine ⟨100291407509280063234027269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66860938339520042156018179 100291407509280063234027269)
      ·
        refine ⟨18804638907990011856380113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100291407509280063234027269 18804638907990011856380113)
        ·
          refine ⟨14103479180992508892285085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18804638907990011856380113 14103479180992508892285085)
          ·
            refine ⟨5288804692872190834606907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14103479180992508892285085 5288804692872190834606907)
            ·
              refine ⟨7933207039308286251910361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5288804692872190834606907 7933207039308286251910361)
              ·
                refine ⟨5949905279481214688932771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7933207039308286251910361 5949905279481214688932771)
                ·
                  refine ⟨8924857919221822033399157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5949905279481214688932771 8924857919221822033399157)
                  ·
                    refine ⟨836705429927045815631171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8924857919221822033399157 836705429927045815631171)
                    ·
                      rfl

theorem cell22_2444217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_2444217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444217 prefixEnd_2444217 := by exact prefixLift 2444217
  have htrace : WordTrace (prefixWord ++ tailWord_2444217) baseStart_2444217 baseEnd_2444217 := by
    simpa [prefixWord, tailWord_2444217, baseEnd_2444217] using wordTrace_append hprefix tailTrace_2444217
  have hstable : (prefixWord ++ tailWord_2444217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444217).length < 2 ^ (prefixWord ++ tailWord_2444217).sum := by decide
  have hdescent : baseEnd_2444217 < baseStart_2444217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444221 : List Nat := [1, 4, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_2444221 : Nat := 118140960795 + 2444221 * 2 ^ 59
def prefixEnd_2444221 : Nat := 4983230072969 + 3 ^ 40 * 2444221 * 2
def baseEnd_2444221 : Nat := 836706799208791138531159

theorem tailTrace_2444221 : CollatzResearch.WordTrace tailWord_2444221 prefixEnd_2444221 836706799208791138531159 := by
  unfold tailWord_2444221
  simp only [CollatzResearch.WordTrace]
  refine ⟨89148063678012231557836517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59432042452008154371891011 89148063678012231557836517)
  ·
    refine ⟨16715261939627293417094347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89148063678012231557836517 16715261939627293417094347)
    ·
      refine ⟨25072892909440940125641521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16715261939627293417094347 25072892909440940125641521)
      ·
        refine ⟨18804669682080705094231141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25072892909440940125641521 18804669682080705094231141)
        ·
          refine ⟨3525875565390132205168339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18804669682080705094231141 3525875565390132205168339)
          ·
            refine ⟨5288813348085198307752509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3525875565390132205168339 5288813348085198307752509)
            ·
              refine ⟨1983305005531949365407191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5288813348085198307752509 1983305005531949365407191)
              ·
                refine ⟨2974957508297924048110787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983305005531949365407191 2974957508297924048110787)
                ·
                  refine ⟨4462436262446886072166181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2974957508297924048110787 4462436262446886072166181)
                  ·
                    refine ⟨836706799208791138531159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4462436262446886072166181 836706799208791138531159)
                    ·
                      rfl

theorem cell22_2444221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_2444221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444221 prefixEnd_2444221 := by exact prefixLift 2444221
  have htrace : WordTrace (prefixWord ++ tailWord_2444221) baseStart_2444221 baseEnd_2444221 := by
    simpa [prefixWord, tailWord_2444221, baseEnd_2444221] using wordTrace_append hprefix tailTrace_2444221
  have hstable : (prefixWord ++ tailWord_2444221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444221).length < 2 ^ (prefixWord ++ tailWord_2444221).sum := by decide
  have hdescent : baseEnd_2444221 < baseStart_2444221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444296 : List Nat := [2, 1, 3, 2, 1, 3, 2, 4, 1, 3]
def baseStart_2444296 : Nat := 118140960795 + 2444296 * 2 ^ 59
def prefixEnd_2444296 : Nat := 4983230072969 + 3 ^ 40 * 2444296 * 2
def baseEnd_2444296 : Nat := 836732473241515942905929

theorem tailTrace_2444296 : CollatzResearch.WordTrace tailWord_2444296 prefixEnd_2444296 836732473241515942905929 := by
  unfold tailWord_2444296
  simp only [CollatzResearch.WordTrace]
  refine ⟨44575399576370259683408371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59433866101827012911211161 44575399576370259683408371)
  ·
    refine ⟨66863099364555389525112557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44575399576370259683408371 66863099364555389525112557)
    ·
      refine ⟨25073662261708271071917209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66863099364555389525112557 25073662261708271071917209)
      ·
        refine ⟨18805246696281203303937907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25073662261708271071917209 18805246696281203303937907)
        ·
          refine ⟨28207870044421804955906861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18805246696281203303937907 28207870044421804955906861)
          ·
            refine ⟨10577951266658176858465073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28207870044421804955906861 10577951266658176858465073)
            ·
              refine ⟨7933463449993632643848805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10577951266658176858465073 7933463449993632643848805)
              ·
                refine ⟨1487524396873806120721651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7933463449993632643848805 1487524396873806120721651)
                ·
                  refine ⟨2231286595310709181082477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487524396873806120721651 2231286595310709181082477)
                  ·
                    refine ⟨836732473241515942905929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2231286595310709181082477 836732473241515942905929)
                    ·
                      rfl

theorem cell22_2444296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_2444296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444296 prefixEnd_2444296 := by exact prefixLift 2444296
  have htrace : WordTrace (prefixWord ++ tailWord_2444296) baseStart_2444296 baseEnd_2444296 := by
    simpa [prefixWord, tailWord_2444296, baseEnd_2444296] using wordTrace_append hprefix tailTrace_2444296
  have hstable : (prefixWord ++ tailWord_2444296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444296).length < 2 ^ (prefixWord ++ tailWord_2444296).sum := by decide
  have hdescent : baseEnd_2444296 < baseStart_2444296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444330 : List Nat := [3, 1, 4, 1, 3, 2, 1, 3, 1, 3]
def baseStart_2444330 : Nat := 118140960795 + 2444330 * 2 ^ 59
def prefixEnd_2444330 : Nat := 4983230072969 + 3 ^ 40 * 2444330 * 2
def baseEnd_2444330 : Nat := 836744112136351187555825

theorem tailTrace_2444330 : CollatzResearch.WordTrace tailWord_2444330 prefixEnd_2444330 836744112136351187555825 := by
  unfold tailWord_2444330
  simp only [CollatzResearch.WordTrace]
  refine ⟨22288009808654335793388611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59434692823078228782369629 22288009808654335793388611)
  ·
    refine ⟨33432014712981503690082917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22288009808654335793388611 33432014712981503690082917)
    ·
      refine ⟨6268502758684031941890547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33432014712981503690082917 6268502758684031941890547)
      ·
        refine ⟨9402754138026047912835821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6268502758684031941890547 9402754138026047912835821)
        ·
          refine ⟨3526032801759767967313433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9402754138026047912835821 3526032801759767967313433)
          ·
            refine ⟨2644524601319825975485075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3526032801759767967313433 2644524601319825975485075)
            ·
              refine ⟨3966786901979738963227613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644524601319825975485075 3966786901979738963227613)
              ·
                refine ⟨1487545088242402111210355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3966786901979738963227613 1487545088242402111210355)
                ·
                  refine ⟨2231317632363603166815533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487545088242402111210355 2231317632363603166815533)
                  ·
                    refine ⟨836744112136351187555825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2231317632363603166815533 836744112136351187555825)
                    ·
                      rfl

theorem cell22_2444330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_2444330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444330 prefixEnd_2444330 := by exact prefixLift 2444330
  have htrace : WordTrace (prefixWord ++ tailWord_2444330) baseStart_2444330 baseEnd_2444330 := by
    simpa [prefixWord, tailWord_2444330, baseEnd_2444330] using wordTrace_append hprefix tailTrace_2444330
  have hstable : (prefixWord ++ tailWord_2444330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444330).length < 2 ^ (prefixWord ++ tailWord_2444330).sum := by decide
  have hdescent : baseEnd_2444330 < baseStart_2444330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444384 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 2, 4]
def baseStart_2444384 : Nat := 118140960795 + 2444384 * 2 ^ 59
def prefixEnd_2444384 : Nat := 4983230072969 + 3 ^ 40 * 2444384 * 2
def baseEnd_2444384 : Nat := 836762597439913046705659

theorem tailTrace_2444384 : CollatzResearch.WordTrace tailWord_2444384 prefixEnd_2444384 836762597439913046705659 := by
  unfold tailWord_2444384
  simp only [CollatzResearch.WordTrace]
  refine ⟨44577004388210855198010103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59436005850947806930680137 44577004388210855198010103)
  ·
    refine ⟨66865506582316282797015155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44577004388210855198010103 66865506582316282797015155)
    ·
      refine ⟨100298259873474424195522733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66865506582316282797015155 100298259873474424195522733)
      ·
        refine ⟨37611847452552909073321025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100298259873474424195522733 37611847452552909073321025)
        ·
          refine ⟨28208885589414681804990769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37611847452552909073321025 28208885589414681804990769)
          ·
            refine ⟨21156664192061011353743077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28208885589414681804990769 21156664192061011353743077)
            ·
              refine ⟨3966874536011439628826827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21156664192061011353743077 3966874536011439628826827)
              ·
                refine ⟨5950311804017159443240241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3966874536011439628826827 5950311804017159443240241)
                ·
                  refine ⟨4462733853012869582430181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5950311804017159443240241 4462733853012869582430181)
                  ·
                    refine ⟨836762597439913046705659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4462733853012869582430181 836762597439913046705659)
                    ·
                      rfl

theorem cell22_2444384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_2444384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444384 prefixEnd_2444384 := by exact prefixLift 2444384
  have htrace : WordTrace (prefixWord ++ tailWord_2444384) baseStart_2444384 baseEnd_2444384 := by
    simpa [prefixWord, tailWord_2444384, baseEnd_2444384] using wordTrace_append hprefix tailTrace_2444384
  have hstable : (prefixWord ++ tailWord_2444384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444384).length < 2 ^ (prefixWord ++ tailWord_2444384).sum := by decide
  have hdescent : baseEnd_2444384 < baseStart_2444384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444386 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2444386 : Nat := 118140960795 + 2444386 * 2 ^ 59
def prefixEnd_2444386 : Nat := 4983230072969 + 3 ^ 40 * 2444386 * 2
def baseEnd_2444386 : Nat := 836763282080785708155653

theorem tailTrace_2444386 : CollatzResearch.WordTrace tailWord_2444386 prefixEnd_2444386 836763282080785708155653 := by
  unfold tailWord_2444386
  simp only [CollatzResearch.WordTrace]
  refine ⟨22288520430603616184398253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59436054481609643158395341 22288520430603616184398253)
  ·
    refine ⟨8358195161476356069149345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22288520430603616184398253 8358195161476356069149345)
    ·
      refine ⟨6268646371107267051862009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8358195161476356069149345 6268646371107267051862009)
      ·
        refine ⟨4701484778330450288896507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6268646371107267051862009 4701484778330450288896507)
        ·
          refine ⟨7052227167495675433344761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4701484778330450288896507 7052227167495675433344761)
          ·
            refine ⟨5289170375621756575008571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7052227167495675433344761 5289170375621756575008571)
            ·
              refine ⟨7933755563432634862512857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5289170375621756575008571 7933755563432634862512857)
              ·
                refine ⟨5950316672574476146884643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7933755563432634862512857 5950316672574476146884643)
                ·
                  refine ⟨8925475008861714220326965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5950316672574476146884643 8925475008861714220326965)
                  ·
                    refine ⟨836763282080785708155653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8925475008861714220326965 836763282080785708155653)
                    ·
                      rfl

theorem cell22_2444386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2444386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444386 prefixEnd_2444386 := by exact prefixLift 2444386
  have htrace : WordTrace (prefixWord ++ tailWord_2444386) baseStart_2444386 baseEnd_2444386 := by
    simpa [prefixWord, tailWord_2444386, baseEnd_2444386] using wordTrace_append hprefix tailTrace_2444386
  have hstable : (prefixWord ++ tailWord_2444386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444386).length < 2 ^ (prefixWord ++ tailWord_2444386).sum := by decide
  have hdescent : baseEnd_2444386 < baseStart_2444386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444412 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_2444412 : Nat := 118140960795 + 2444412 * 2 ^ 59
def prefixEnd_2444412 : Nat := 4983230072969 + 3 ^ 40 * 2444412 * 2
def baseEnd_2444412 : Nat := 836772182412130307005573

theorem tailTrace_2444412 : CollatzResearch.WordTrace tailWord_2444412 prefixEnd_2444412 836772182412130307005573 := by
  unfold tailWord_2444412
  simp only [CollatzResearch.WordTrace]
  refine ⟨44577515010160135589019745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59436686680213514118692993 44577515010160135589019745)
  ·
    refine ⟨33433136257620101691764809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44577515010160135589019745 33433136257620101691764809)
    ·
      refine ⟨25074852193215076268823607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33433136257620101691764809 25074852193215076268823607)
      ·
        refine ⟨37612278289822614403235411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25074852193215076268823607 37612278289822614403235411)
        ·
          refine ⟨56418417434733921604853117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37612278289822614403235411 56418417434733921604853117)
          ·
            refine ⟨21156906538025220601819919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56418417434733921604853117 21156906538025220601819919)
            ·
              refine ⟨31735359807037830902729879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21156906538025220601819919 31735359807037830902729879)
              ·
                refine ⟨47603039710556746354094819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31735359807037830902729879 47603039710556746354094819)
                ·
                  refine ⟨71404559565835119531142229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47603039710556746354094819 71404559565835119531142229)
                  ·
                    refine ⟨836772182412130307005573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71404559565835119531142229 836772182412130307005573)
                    ·
                      rfl

theorem cell22_2444412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_2444412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444412 prefixEnd_2444412 := by exact prefixLift 2444412
  have htrace : WordTrace (prefixWord ++ tailWord_2444412) baseStart_2444412 baseEnd_2444412 := by
    simpa [prefixWord, tailWord_2444412, baseEnd_2444412] using wordTrace_append hprefix tailTrace_2444412
  have hstable : (prefixWord ++ tailWord_2444412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444412).length < 2 ^ (prefixWord ++ tailWord_2444412).sum := by decide
  have hdescent : baseEnd_2444412 < baseStart_2444412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444448 : List Nat := [2, 1, 1, 4, 2, 1, 4, 3, 1, 3]
def baseStart_2444448 : Nat := 118140960795 + 2444448 * 2 ^ 59
def prefixEnd_2444448 : Nat := 4983230072969 + 3 ^ 40 * 2444448 * 2
def baseEnd_2444448 : Nat := 836784505947838213105463

theorem tailTrace_2444448 : CollatzResearch.WordTrace tailWord_2444448 prefixEnd_2444448 836784505947838213105463 := by
  unfold tailWord_2444448
  simp only [CollatzResearch.WordTrace]
  refine ⟨44578171524094924663174999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59437562032126566217566665 44578171524094924663174999)
  ·
    refine ⟨66867257286142386994762499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44578171524094924663174999 66867257286142386994762499)
    ·
      refine ⟨100300885929213580492143749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66867257286142386994762499 100300885929213580492143749)
      ·
        refine ⟨18806416111727546342276953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100300885929213580492143749 18806416111727546342276953)
        ·
          refine ⟨14104812083795659756707715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18806416111727546342276953 14104812083795659756707715)
          ·
            refine ⟨21157218125693489635061573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14104812083795659756707715 21157218125693489635061573)
            ·
              refine ⟨3966978398567529306574045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21157218125693489635061573 3966978398567529306574045)
              ·
                refine ⟨1487616899462823489965267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3966978398567529306574045 1487616899462823489965267)
                ·
                  refine ⟨2231425349194235234947901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487616899462823489965267 2231425349194235234947901)
                  ·
                    refine ⟨836784505947838213105463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2231425349194235234947901 836784505947838213105463)
                    ·
                      rfl

theorem cell22_2444448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 1, 3].length) (baseStart_2444448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444448 prefixEnd_2444448 := by exact prefixLift 2444448
  have htrace : WordTrace (prefixWord ++ tailWord_2444448) baseStart_2444448 baseEnd_2444448 := by
    simpa [prefixWord, tailWord_2444448, baseEnd_2444448] using wordTrace_append hprefix tailTrace_2444448
  have hstable : (prefixWord ++ tailWord_2444448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444448).length < 2 ^ (prefixWord ++ tailWord_2444448).sum := by decide
  have hdescent : baseEnd_2444448 < baseStart_2444448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444461 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 7]
def baseStart_2444461 : Nat := 118140960795 + 2444461 * 2 ^ 59
def prefixEnd_2444461 : Nat := 4983230072969 + 3 ^ 40 * 2444461 * 2
def baseEnd_2444461 : Nat := 278929652037836837510141

theorem tailTrace_2444461 : CollatzResearch.WordTrace tailWord_2444461 prefixEnd_2444461 278929652037836837510141 := by
  unfold tailWord_2444461
  simp only [CollatzResearch.WordTrace]
  refine ⟨89156817197142752546573237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59437878131428501697715491 89156817197142752546573237)
  ·
    refine ⟨8358451612232133051241241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89156817197142752546573237 8358451612232133051241241)
    ·
      refine ⟨6268838709174099788430931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8358451612232133051241241 6268838709174099788430931)
      ·
        refine ⟨9403258063761149682646397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6268838709174099788430931 9403258063761149682646397)
        ·
          refine ⟨3526221773910431130992399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9403258063761149682646397 3526221773910431130992399)
          ·
            refine ⟨5289332660865646696488599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3526221773910431130992399 5289332660865646696488599)
            ·
              refine ⟨7933998991298470044732899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5289332660865646696488599 7933998991298470044732899)
              ·
                refine ⟨11900998486947705067099349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7933998991298470044732899 11900998486947705067099349)
                ·
                  refine ⟨278929652037836837510141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11900998486947705067099349 278929652037836837510141)
                  ·
                    rfl

theorem cell22_2444461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_2444461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444461 prefixEnd_2444461 := by exact prefixLift 2444461
  have htrace : WordTrace (prefixWord ++ tailWord_2444461) baseStart_2444461 baseEnd_2444461 := by
    simpa [prefixWord, tailWord_2444461, baseEnd_2444461] using wordTrace_append hprefix tailTrace_2444461
  have hstable : (prefixWord ++ tailWord_2444461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444461).length < 2 ^ (prefixWord ++ tailWord_2444461).sum := by decide
  have hdescent : baseEnd_2444461 < baseStart_2444461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444478 : List Nat := [4, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_2444478 : Nat := 118140960795 + 2444478 * 2 ^ 59
def prefixEnd_2444478 : Nat := 4983230072969 + 3 ^ 40 * 2444478 * 2
def baseEnd_2444478 : Nat := 278931591853642711618457

theorem tailTrace_2444478 : CollatzResearch.WordTrace tailWord_2444478 prefixEnd_2444478 278931591853642711618457 := by
  unfold tailWord_2444478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11144679654760145556242761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59438291492054109633294725 11144679654760145556242761)
  ·
    refine ⟨8358509741070109167182071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11144679654760145556242761 8358509741070109167182071)
    ·
      refine ⟨12537764611605163750773107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8358509741070109167182071 12537764611605163750773107)
      ·
        refine ⟨18806646917407745626159661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12537764611605163750773107 18806646917407745626159661)
        ·
          refine ⟨7052492594027904609809873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18806646917407745626159661 7052492594027904609809873)
          ·
            refine ⟨5289369445520928457357405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7052492594027904609809873 5289369445520928457357405)
            ·
              refine ⟨1983513542070348171509027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5289369445520928457357405 1983513542070348171509027)
              ·
                refine ⟨2975270313105522257263541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983513542070348171509027 2975270313105522257263541)
                ·
                  refine ⟨278931591853642711618457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2975270313105522257263541 278931591853642711618457)
                  ·
                    rfl

theorem cell22_2444478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_2444478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444478 prefixEnd_2444478 := by exact prefixLift 2444478
  have htrace : WordTrace (prefixWord ++ tailWord_2444478) baseStart_2444478 baseEnd_2444478 := by
    simpa [prefixWord, tailWord_2444478, baseEnd_2444478] using wordTrace_append hprefix tailTrace_2444478
  have hstable : (prefixWord ++ tailWord_2444478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444478).length < 2 ^ (prefixWord ++ tailWord_2444478).sum := by decide
  have hdescent : baseEnd_2444478 < baseStart_2444478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444523 : List Nat := [1, 1, 1, 1, 2, 7, 3, 2, 4]
def baseStart_2444523 : Nat := 118140960795 + 2444523 * 2 ^ 59
def prefixEnd_2444523 : Nat := 4983230072969 + 3 ^ 40 * 2444523 * 2
def baseEnd_2444523 : Nat := 278936726660187672493411

theorem tailTrace_2444523 : CollatzResearch.WordTrace tailWord_2444523 prefixEnd_2444523 278936726660187672493411 := by
  unfold tailWord_2444523
  simp only [CollatzResearch.WordTrace]
  refine ⟨89159078522918137135330223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59439385681945424756886815 89159078522918137135330223)
  ·
    refine ⟨133738617784377205702995335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89159078522918137135330223 133738617784377205702995335)
    ·
      refine ⟨200607926676565808554493003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133738617784377205702995335 200607926676565808554493003)
      ·
        refine ⟨300911890014848712831739505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200607926676565808554493003 300911890014848712831739505)
        ·
          refine ⟨225683917511136534623804629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300911890014848712831739505 225683917511136534623804629)
          ·
            refine ⟨5289466816667262530245421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 225683917511136534623804629 5289466816667262530245421)
            ·
              refine ⟨1983550056250223448842033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5289466816667262530245421 1983550056250223448842033)
              ·
                refine ⟨1487662542187667586631525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1983550056250223448842033 1487662542187667586631525)
                ·
                  refine ⟨278936726660187672493411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487662542187667586631525 278936726660187672493411)
                  ·
                    rfl

theorem cell22_2444523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 4].length) (baseStart_2444523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444523 prefixEnd_2444523 := by exact prefixLift 2444523
  have htrace : WordTrace (prefixWord ++ tailWord_2444523) baseStart_2444523 baseEnd_2444523 := by
    simpa [prefixWord, tailWord_2444523, baseEnd_2444523] using wordTrace_append hprefix tailTrace_2444523
  have hstable : (prefixWord ++ tailWord_2444523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444523).length < 2 ^ (prefixWord ++ tailWord_2444523).sum := by decide
  have hdescent : baseEnd_2444523 < baseStart_2444523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444574 : List Nat := [4, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_2444574 : Nat := 118140960795 + 2444574 * 2 ^ 59
def prefixEnd_2444574 : Nat := 4983230072969 + 3 ^ 40 * 2444574 * 2
def baseEnd_2444574 : Nat := 278942546107605294818359

theorem tailTrace_2444574 : CollatzResearch.WordTrace tailWord_2444574 prefixEnd_2444574 278942546107605294818359 := by
  unfold tailWord_2444574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11145117330716671605679597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59440625763822248563624517 11145117330716671605679597)
  ·
    refine ⟨4179418999018751852129849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11145117330716671605679597 4179418999018751852129849)
    ·
      refine ⟨3134564249264063889097387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4179418999018751852129849 3134564249264063889097387)
      ·
        refine ⟨4701846373896095833646081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3134564249264063889097387 4701846373896095833646081)
        ·
          refine ⟨3526384780422071875234561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4701846373896095833646081 3526384780422071875234561)
          ·
            refine ⟨2644788585316553906425921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3526384780422071875234561 2644788585316553906425921)
            ·
              refine ⟨1983591438987415429819441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2644788585316553906425921 1983591438987415429819441)
              ·
                refine ⟨1487693579240561572364581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1983591438987415429819441 1487693579240561572364581)
                ·
                  refine ⟨278942546107605294818359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487693579240561572364581 278942546107605294818359)
                  ·
                    rfl

theorem cell22_2444574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_2444574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444574 prefixEnd_2444574 := by exact prefixLift 2444574
  have htrace : WordTrace (prefixWord ++ tailWord_2444574) baseStart_2444574 baseEnd_2444574 := by
    simpa [prefixWord, tailWord_2444574, baseEnd_2444574] using wordTrace_append hprefix tailTrace_2444574
  have hstable : (prefixWord ++ tailWord_2444574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444574).length < 2 ^ (prefixWord ++ tailWord_2444574).sum := by decide
  have hdescent : baseEnd_2444574 < baseStart_2444574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444624 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 8]
def baseStart_2444624 : Nat := 118140960795 + 2444624 * 2 ^ 59
def prefixEnd_2444624 : Nat := 4983230072969 + 3 ^ 40 * 2444624 * 2
def baseEnd_2444624 : Nat := 278948251448210806901641

theorem tailTrace_2444624 : CollatzResearch.WordTrace tailWord_2444624 prefixEnd_2444624 278948251448210806901641 := by
  unfold tailWord_2444624
  simp only [CollatzResearch.WordTrace]
  refine ⟨44581381147776115692378463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59441841530368154256504617 44581381147776115692378463)
  ·
    refine ⟨66872071721664173538567695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44581381147776115692378463 66872071721664173538567695)
    ·
      refine ⟨100308107582496260307851543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66872071721664173538567695 100308107582496260307851543)
      ·
        refine ⟨150462161373744390461777315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100308107582496260307851543 150462161373744390461777315)
        ·
          refine ⟨225693242060616585692665973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150462161373744390461777315 225693242060616585692665973)
          ·
            refine ⟨21158741443182804908687435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 225693242060616585692665973 21158741443182804908687435)
            ·
              refine ⟨31738112164774207363031153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21158741443182804908687435 31738112164774207363031153)
              ·
                refine ⟨23803584123580655522273365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31738112164774207363031153 23803584123580655522273365)
                ·
                  refine ⟨278948251448210806901641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23803584123580655522273365 278948251448210806901641)
                  ·
                    rfl

theorem cell22_2444624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_2444624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444624 prefixEnd_2444624 := by exact prefixLift 2444624
  have htrace : WordTrace (prefixWord ++ tailWord_2444624) baseStart_2444624 baseEnd_2444624 := by
    simpa [prefixWord, tailWord_2444624, baseEnd_2444624] using wordTrace_append hprefix tailTrace_2444624
  have hstable : (prefixWord ++ tailWord_2444624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444624).length < 2 ^ (prefixWord ++ tailWord_2444624).sum := by decide
  have hdescent : baseEnd_2444624 < baseStart_2444624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444675 : List Nat := [1, 1, 1, 3, 5, 3, 1, 3, 4]
def baseStart_2444675 : Nat := 118140960795 + 2444675 * 2 ^ 59
def prefixEnd_2444675 : Nat := 4983230072969 + 3 ^ 40 * 2444675 * 2
def baseEnd_2444675 : Nat := 278954070895628429226589

theorem tailTrace_2444675 : CollatzResearch.WordTrace tailWord_2444675 prefixEnd_2444675 278954070895628429226589 := by
  unfold tailWord_2444675
  simp only [CollatzResearch.WordTrace]
  refine ⟨89164622418367467094863479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59443081612244978063242319 89164622418367467094863479)
  ·
    refine ⟨133746933627551200642295219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89164622418367467094863479 133746933627551200642295219)
    ·
      refine ⟨200620400441326800963442829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133746933627551200642295219 200620400441326800963442829)
      ·
        refine ⟨75232650165497550361291061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200620400441326800963442829 75232650165497550361291061)
        ·
          refine ⟨7053060953015395346371037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75232650165497550361291061 7053060953015395346371037)
          ·
            refine ⟨2644897857380773254889139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7053060953015395346371037 2644897857380773254889139)
            ·
              refine ⟨3967346786071159882333709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644897857380773254889139 3967346786071159882333709)
              ·
                refine ⟨1487755044776684955875141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3967346786071159882333709 1487755044776684955875141)
                ·
                  refine ⟨278954070895628429226589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487755044776684955875141 278954070895628429226589)
                  ·
                    rfl

theorem cell22_2444675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 4].length) (baseStart_2444675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444675 prefixEnd_2444675 := by exact prefixLift 2444675
  have htrace : WordTrace (prefixWord ++ tailWord_2444675) baseStart_2444675 baseEnd_2444675 := by
    simpa [prefixWord, tailWord_2444675, baseEnd_2444675] using wordTrace_append hprefix tailTrace_2444675
  have hstable : (prefixWord ++ tailWord_2444675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444675).length < 2 ^ (prefixWord ++ tailWord_2444675).sum := by decide
  have hdescent : baseEnd_2444675 < baseStart_2444675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444692 : List Nat := [2, 4, 2, 1, 2, 2, 3, 2, 4]
def baseStart_2444692 : Nat := 118140960795 + 2444692 * 2 ^ 59
def prefixEnd_2444692 : Nat := 4983230072969 + 3 ^ 40 * 2444692 * 2
def baseEnd_2444692 : Nat := 278956010711434303334905

theorem tailTrace_2444692 : CollatzResearch.WordTrace tailWord_2444692 prefixEnd_2444692 278956010711434303334905 := by
  unfold tailWord_2444692
  simp only [CollatzResearch.WordTrace]
  refine ⟨44582621229652939499116165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59443494972870585998821553 44582621229652939499116165)
  ·
    refine ⟨8359241480559926156084281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44582621229652939499116165 8359241480559926156084281)
    ·
      refine ⟨6269431110419944617063211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8359241480559926156084281 6269431110419944617063211)
      ·
        refine ⟨9404146665629916925594817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6269431110419944617063211 9404146665629916925594817)
        ·
          refine ⟨7053109999222437694196113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9404146665629916925594817 7053109999222437694196113)
          ·
            refine ⟨5289832499416828270647085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7053109999222437694196113 5289832499416828270647085)
            ·
              refine ⟨1983687187281310601492657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5289832499416828270647085 1983687187281310601492657)
              ·
                refine ⟨1487765390460982951119493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1983687187281310601492657 1487765390460982951119493)
                ·
                  refine ⟨278956010711434303334905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487765390460982951119493 278956010711434303334905)
                  ·
                    rfl

theorem cell22_2444692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_2444692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444692 prefixEnd_2444692 := by exact prefixLift 2444692
  have htrace : WordTrace (prefixWord ++ tailWord_2444692) baseStart_2444692 baseEnd_2444692 := by
    simpa [prefixWord, tailWord_2444692, baseEnd_2444692] using wordTrace_append hprefix tailTrace_2444692
  have hstable : (prefixWord ++ tailWord_2444692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444692).length < 2 ^ (prefixWord ++ tailWord_2444692).sum := by decide
  have hdescent : baseEnd_2444692 < baseStart_2444692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444748 : List Nat := [2, 2, 1, 4, 2, 1, 1, 4, 5]
def baseStart_2444748 : Nat := 118140960795 + 2444748 * 2 ^ 59
def prefixEnd_2444748 : Nat := 4983230072969 + 3 ^ 40 * 2444748 * 2
def baseEnd_2444748 : Nat := 278962400692912476868181

theorem tailTrace_2444748 : CollatzResearch.WordTrace tailWord_2444748 prefixEnd_2444748 278962400692912476868181 := by
  unfold tailWord_2444748
  simp only [CollatzResearch.WordTrace]
  refine ⟨44583642473551500281135449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59444856631402000374847265 44583642473551500281135449)
  ·
    refine ⟨33437731855163625210851587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44583642473551500281135449 33437731855163625210851587)
    ·
      refine ⟨50156597782745437816277381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33437731855163625210851587 50156597782745437816277381)
      ·
        refine ⟨9404362084264769590552009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50156597782745437816277381 9404362084264769590552009)
        ·
          refine ⟨7053271563198577192914007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9404362084264769590552009 7053271563198577192914007)
          ·
            refine ⟨10579907344797865789371011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7053271563198577192914007 10579907344797865789371011)
            ·
              refine ⟨15869861017196798684056517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10579907344797865789371011 15869861017196798684056517)
              ·
                refine ⟨2975598940724399753260597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15869861017196798684056517 2975598940724399753260597)
                ·
                  refine ⟨278962400692912476868181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2975598940724399753260597 278962400692912476868181)
                  ·
                    rfl

theorem cell22_2444748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_2444748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444748 prefixEnd_2444748 := by exact prefixLift 2444748
  have htrace : WordTrace (prefixWord ++ tailWord_2444748) baseStart_2444748 baseEnd_2444748 := by
    simpa [prefixWord, tailWord_2444748, baseEnd_2444748] using wordTrace_append hprefix tailTrace_2444748
  have hstable : (prefixWord ++ tailWord_2444748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444748).length < 2 ^ (prefixWord ++ tailWord_2444748).sum := by decide
  have hdescent : baseEnd_2444748 < baseStart_2444748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444791 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 3, 5]
def baseStart_2444791 : Nat := 118140960795 + 2444791 * 2 ^ 59
def prefixEnd_2444791 : Nat := 4983230072969 + 3 ^ 40 * 2444791 * 2
def baseEnd_2444791 : Nat := 836901921857499651779411

theorem tailTrace_2444791 : CollatzResearch.WordTrace tailWord_2444791 prefixEnd_2444791 836901921857499651779411 := by
  unfold tailWord_2444791
  simp only [CollatzResearch.WordTrace]
  refine ⟨89168853285947218906086227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59445902190631479270724151 89168853285947218906086227)
  ·
    refine ⟨133753279928920828359129341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89168853285947218906086227 133753279928920828359129341)
    ·
      refine ⟨50157479973345310634673503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133753279928920828359129341 50157479973345310634673503)
      ·
        refine ⟨75236219960017965952010255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50157479973345310634673503 75236219960017965952010255)
        ·
          refine ⟨112854329940026948928015383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75236219960017965952010255 112854329940026948928015383)
          ·
            refine ⟨169281494910040423392023075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112854329940026948928015383 169281494910040423392023075)
            ·
              refine ⟨253922242365060635088034613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169281494910040423392023075 253922242365060635088034613)
              ·
                refine ⟨23805210221724434539503245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 253922242365060635088034613 23805210221724434539503245)
                ·
                  refine ⟨8926953833146662952313717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23805210221724434539503245 8926953833146662952313717)
                  ·
                    refine ⟨836901921857499651779411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8926953833146662952313717 836901921857499651779411)
                    ·
                      rfl

theorem cell22_2444791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_2444791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444791 prefixEnd_2444791 := by exact prefixLift 2444791
  have htrace : WordTrace (prefixWord ++ tailWord_2444791) baseStart_2444791 baseEnd_2444791 := by
    simpa [prefixWord, tailWord_2444791, baseEnd_2444791] using wordTrace_append hprefix tailTrace_2444791
  have hstable : (prefixWord ++ tailWord_2444791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444791).length < 2 ^ (prefixWord ++ tailWord_2444791).sum := by decide
  have hdescent : baseEnd_2444791 < baseStart_2444791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444810 : List Nat := [3, 1, 2, 2, 2, 2, 2, 4, 4]
def baseStart_2444810 : Nat := 118140960795 + 2444810 * 2 ^ 59
def prefixEnd_2444810 : Nat := 4983230072969 + 3 ^ 40 * 2444810 * 2
def baseEnd_2444810 : Nat := 278969475315263311851451

theorem tailTrace_2444810 : CollatzResearch.WordTrace tailWord_2444810 prefixEnd_2444810 278969475315263311851451 := by
  unfold tailWord_2444810
  simp only [CollatzResearch.WordTrace]
  refine ⟨22292386568219596287756971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59446364181918923434018589 22292386568219596287756971)
  ·
    refine ⟨33438579852329394431635457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22292386568219596287756971 33438579852329394431635457)
    ·
      refine ⟨25078934889247045823726593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33438579852329394431635457 25078934889247045823726593)
      ·
        refine ⟨18809201166935284367794945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25078934889247045823726593 18809201166935284367794945)
        ·
          refine ⟨14106900875201463275846209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18809201166935284367794945 14106900875201463275846209)
          ·
            refine ⟨10580175656401097456884657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14106900875201463275846209 10580175656401097456884657)
            ·
              refine ⟨7935131742300823092663493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10580175656401097456884657 7935131742300823092663493)
              ·
                refine ⟨1487837201681404329874405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7935131742300823092663493 1487837201681404329874405)
                ·
                  refine ⟨278969475315263311851451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487837201681404329874405 278969475315263311851451)
                  ·
                    rfl

theorem cell22_2444810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_2444810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444810 prefixEnd_2444810 := by exact prefixLift 2444810
  have htrace : WordTrace (prefixWord ++ tailWord_2444810) baseStart_2444810 baseEnd_2444810 := by
    simpa [prefixWord, tailWord_2444810, baseEnd_2444810] using wordTrace_append hprefix tailTrace_2444810
  have hstable : (prefixWord ++ tailWord_2444810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444810).length < 2 ^ (prefixWord ++ tailWord_2444810).sum := by decide
  have hdescent : baseEnd_2444810 < baseStart_2444810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444917 : List Nat := [1, 3, 4, 2, 1, 2, 2, 2, 5]
def baseStart_2444917 : Nat := 118140960795 + 2444917 * 2 ^ 59
def prefixEnd_2444917 : Nat := 4983230072969 + 3 ^ 40 * 2444917 * 2
def baseEnd_2444917 : Nat := 278981684744159107709675

theorem tailTrace_2444917 : CollatzResearch.WordTrace tailWord_2444917 prefixEnd_2444917 278981684744159107709675 := by
  unfold tailWord_2444917
  simp only [CollatzResearch.WordTrace]
  refine ⟨89173448883490742425173005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59448965922327161616782003 89173448883490742425173005)
  ·
    refine ⟨33440043331309028409439877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89173448883490742425173005 33440043331309028409439877)
    ·
      refine ⟨6270008124620442826769977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33440043331309028409439877 6270008124620442826769977)
      ·
        refine ⟨4702506093465332120077483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6270008124620442826769977 4702506093465332120077483)
        ·
          refine ⟨7053759140197998180116225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4702506093465332120077483 7053759140197998180116225)
          ·
            refine ⟨5290319355148498635087169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7053759140197998180116225 5290319355148498635087169)
            ·
              refine ⟨3967739516361373976315377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5290319355148498635087169 3967739516361373976315377)
              ·
                refine ⟨2975804637271030482236533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3967739516361373976315377 2975804637271030482236533)
                ·
                  refine ⟨278981684744159107709675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2975804637271030482236533 278981684744159107709675)
                  ·
                    rfl

theorem cell22_2444917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_2444917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444917 prefixEnd_2444917 := by exact prefixLift 2444917
  have htrace : WordTrace (prefixWord ++ tailWord_2444917) baseStart_2444917 baseEnd_2444917 := by
    simpa [prefixWord, tailWord_2444917, baseEnd_2444917] using wordTrace_append hprefix tailTrace_2444917
  have hstable : (prefixWord ++ tailWord_2444917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444917).length < 2 ^ (prefixWord ++ tailWord_2444917).sum := by decide
  have hdescent : baseEnd_2444917 < baseStart_2444917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444928 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 6]
def baseStart_2444928 : Nat := 118140960795 + 2444928 * 2 ^ 59
def prefixEnd_2444928 : Nat := 4983230072969 + 3 ^ 40 * 2444928 * 2
def baseEnd_2444928 : Nat := 278982939919092320367997

theorem tailTrace_2444928 : CollatzResearch.WordTrace tailWord_2444928 prefixEnd_2444928 278982939919092320367997 := by
  unfold tailWord_2444928
  simp only [CollatzResearch.WordTrace]
  refine ⟨44586925043225445651911719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59449233390967260869215625 44586925043225445651911719)
  ·
    refine ⟨66880387564838168477867579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44586925043225445651911719 66880387564838168477867579)
    ·
      refine ⟨100320581347257252716801369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66880387564838168477867579 100320581347257252716801369)
      ·
        refine ⟨75240436010442939537601027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100320581347257252716801369 75240436010442939537601027)
        ·
          refine ⟨112860654015664409306401541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75240436010442939537601027 112860654015664409306401541)
          ·
            refine ⟨21161372627937076744950289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112860654015664409306401541 21161372627937076744950289)
            ·
              refine ⟨15871029470952807558712717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21161372627937076744950289 15871029470952807558712717)
              ·
                refine ⟨5951636051607302834517269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15871029470952807558712717 5951636051607302834517269)
                ·
                  refine ⟨278982939919092320367997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5951636051607302834517269 278982939919092320367997)
                  ·
                    rfl

theorem cell22_2444928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_2444928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444928 prefixEnd_2444928 := by exact prefixLift 2444928
  have htrace : WordTrace (prefixWord ++ tailWord_2444928) baseStart_2444928 baseEnd_2444928 := by
    simpa [prefixWord, tailWord_2444928, baseEnd_2444928] using wordTrace_append hprefix tailTrace_2444928
  have hstable : (prefixWord ++ tailWord_2444928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444928).length < 2 ^ (prefixWord ++ tailWord_2444928).sum := by decide
  have hdescent : baseEnd_2444928 < baseStart_2444928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444960 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 1, 5]
def baseStart_2444960 : Nat := 118140960795 + 2444960 * 2 ^ 59
def prefixEnd_2444960 : Nat := 4983230072969 + 3 ^ 40 * 2444960 * 2
def baseEnd_2444960 : Nat := 836959774011239544303893

theorem tailTrace_2444960 : CollatzResearch.WordTrace tailWord_2444960 prefixEnd_2444960 836959774011239544303893 := by
  unfold tailWord_2444960
  simp only [CollatzResearch.WordTrace]
  refine ⟨44587508611167480384494167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59450011481556640512658889 44587508611167480384494167)
  ·
    refine ⟨66881262916751220576741251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44587508611167480384494167 66881262916751220576741251)
    ·
      refine ⟨100321894375126830865111877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66881262916751220576741251 100321894375126830865111877)
      ·
        refine ⟨18810355195336280787208477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100321894375126830865111877 18810355195336280787208477)
        ·
          refine ⟨7053883198251105295203179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18810355195336280787208477 7053883198251105295203179)
          ·
            refine ⟨10580824797376657942804769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7053883198251105295203179 10580824797376657942804769)
            ·
              refine ⟨7935618598032493457103577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10580824797376657942804769 7935618598032493457103577)
              ·
                refine ⟨5951713948524370092827683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7935618598032493457103577 5951713948524370092827683)
                ·
                  refine ⟨8927570922786555139241525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5951713948524370092827683 8927570922786555139241525)
                  ·
                    refine ⟨836959774011239544303893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8927570922786555139241525 836959774011239544303893)
                    ·
                      rfl

theorem cell22_2444960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_2444960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444960 prefixEnd_2444960 := by exact prefixLift 2444960
  have htrace : WordTrace (prefixWord ++ tailWord_2444960) baseStart_2444960 baseEnd_2444960 := by
    simpa [prefixWord, tailWord_2444960, baseEnd_2444960] using wordTrace_append hprefix tailTrace_2444960
  have hstable : (prefixWord ++ tailWord_2444960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444960).length < 2 ^ (prefixWord ++ tailWord_2444960).sum := by decide
  have hdescent : baseEnd_2444960 < baseStart_2444960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444964 : List Nat := [2, 3, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_2444964 : Nat := 118140960795 + 2444964 * 2 ^ 59
def prefixEnd_2444964 : Nat := 4983230072969 + 3 ^ 40 * 2444964 * 2
def baseEnd_2444964 : Nat := 836961143292984867203881

theorem tailTrace_2444964 : CollatzResearch.WordTrace tailWord_2444964 prefixEnd_2444964 836961143292984867203881 := by
  unfold tailWord_2444964
  simp only [CollatzResearch.WordTrace]
  refine ⟨44587581557160234726066973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59450108742880312968089297 44587581557160234726066973)
  ·
    refine ⟨16720343083935088022275115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44587581557160234726066973 16720343083935088022275115)
    ·
      refine ⟨25080514625902632033412673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16720343083935088022275115 25080514625902632033412673)
      ·
        refine ⟨18810385969426974025059505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25080514625902632033412673 18810385969426974025059505)
        ·
          refine ⟨14107789477070230518794629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18810385969426974025059505 14107789477070230518794629)
          ·
            refine ⟨2645210526950668222273993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14107789477070230518794629 2645210526950668222273993)
            ·
              refine ⟨1983907895213001166705495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2645210526950668222273993 1983907895213001166705495)
              ·
                refine ⟨2975861842819501750058243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983907895213001166705495 2975861842819501750058243)
                ·
                  refine ⟨4463792764229252625087365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2975861842819501750058243 4463792764229252625087365)
                  ·
                    refine ⟨836961143292984867203881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4463792764229252625087365 836961143292984867203881)
                    ·
                      rfl

theorem cell22_2444964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_2444964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444964 prefixEnd_2444964 := by exact prefixLift 2444964
  have htrace : WordTrace (prefixWord ++ tailWord_2444964) baseStart_2444964 baseEnd_2444964 := by
    simpa [prefixWord, tailWord_2444964, baseEnd_2444964] using wordTrace_append hprefix tailTrace_2444964
  have hstable : (prefixWord ++ tailWord_2444964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444964).length < 2 ^ (prefixWord ++ tailWord_2444964).sum := by decide
  have hdescent : baseEnd_2444964 < baseStart_2444964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444968 : List Nat := [2, 1, 7, 1, 2, 1, 1, 2, 5]
def baseStart_2444968 : Nat := 118140960795 + 2444968 * 2 ^ 59
def prefixEnd_2444968 : Nat := 4983230072969 + 3 ^ 40 * 2444968 * 2
def baseEnd_2444968 : Nat := 278987504191576730034623

theorem tailTrace_2444968 : CollatzResearch.WordTrace tailWord_2444968 prefixEnd_2444968 278987504191576730034623 := by
  unfold tailWord_2444968
  simp only [CollatzResearch.WordTrace]
  refine ⟨44587654503152989067639779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59450206004203985423519705 44587654503152989067639779)
  ·
    refine ⟨66881481754729483601459669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44587654503152989067639779 66881481754729483601459669)
    ·
      refine ⟨1567534728626472271909211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 66881481754729483601459669 1567534728626472271909211)
      ·
        refine ⟨2351302092939708407863817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567534728626472271909211 2351302092939708407863817)
        ·
          refine ⟨1763476569704781305897863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351302092939708407863817 1763476569704781305897863)
          ·
            refine ⟨2645214854557171958846795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763476569704781305897863 2645214854557171958846795)
            ·
              refine ⟨3967822281835757938270193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645214854557171958846795 3967822281835757938270193)
              ·
                refine ⟨2975866711376818453702645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3967822281835757938270193 2975866711376818453702645)
                ·
                  refine ⟨278987504191576730034623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2975866711376818453702645 278987504191576730034623)
                  ·
                    rfl

theorem cell22_2444968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 5].length) (baseStart_2444968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2444968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2444968 prefixEnd_2444968 := by exact prefixLift 2444968
  have htrace : WordTrace (prefixWord ++ tailWord_2444968) baseStart_2444968 baseEnd_2444968 := by
    simpa [prefixWord, tailWord_2444968, baseEnd_2444968] using wordTrace_append hprefix tailTrace_2444968
  have hstable : (prefixWord ++ tailWord_2444968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444968).length < 2 ^ (prefixWord ++ tailWord_2444968).sum := by decide
  have hdescent : baseEnd_2444968 < baseStart_2444968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445003 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 2, 6]
def baseStart_2445003 : Nat := 118140960795 + 2445003 * 2 ^ 59
def prefixEnd_2445003 : Nat := 4983230072969 + 3 ^ 40 * 2445003 * 2
def baseEnd_2445003 : Nat := 836974493790001765478761

theorem tailTrace_2445003 : CollatzResearch.WordTrace tailWord_2445003 prefixEnd_2445003 836974493790001765478761 := by
  unfold tailWord_2445003
  simp only [CollatzResearch.WordTrace]
  refine ⟨89176585561179179112803663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59451057040786119408535775 89176585561179179112803663)
  ·
    refine ⟨133764878341768768669205495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89176585561179179112803663 133764878341768768669205495)
    ·
      refine ⟨200647317512653153003808243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133764878341768768669205495 200647317512653153003808243)
      ·
        refine ⟨300970976268979729505712365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200647317512653153003808243 300970976268979729505712365)
        ·
          refine ⟨112864116100867398564642137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300970976268979729505712365 112864116100867398564642137)
          ·
            refine ⟨84648087075650548923481603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112864116100867398564642137 84648087075650548923481603)
            ·
              refine ⟨126972130613475823385222405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84648087075650548923481603 126972130613475823385222405)
              ·
                refine ⟨23807274490026716884729201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126972130613475823385222405 23807274490026716884729201)
                ·
                  refine ⟨17855455867520037663546901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23807274490026716884729201 17855455867520037663546901)
                  ·
                    refine ⟨836974493790001765478761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17855455867520037663546901 836974493790001765478761)
                    ·
                      rfl

theorem cell22_2445003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_2445003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445003 prefixEnd_2445003 := by exact prefixLift 2445003
  have htrace : WordTrace (prefixWord ++ tailWord_2445003) baseStart_2445003 baseEnd_2445003 := by
    simpa [prefixWord, tailWord_2445003, baseEnd_2445003] using wordTrace_append hprefix tailTrace_2445003
  have hstable : (prefixWord ++ tailWord_2445003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445003).length < 2 ^ (prefixWord ++ tailWord_2445003).sum := by decide
  have hdescent : baseEnd_2445003 < baseStart_2445003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445112 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 1, 5]
def baseStart_2445112 : Nat := 118140960795 + 2445112 * 2 ^ 59
def prefixEnd_2445112 : Nat := 4983230072969 + 3 ^ 40 * 2445112 * 2
def baseEnd_2445112 : Nat := 837011806717561814503427

theorem tailTrace_2445112 : CollatzResearch.WordTrace tailWord_2445112 prefixEnd_2445112 837011806717561814503427 := by
  unfold tailWord_2445112
  simp only [CollatzResearch.WordTrace]
  refine ⟨44590280558892145364260795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59453707411856193819014393 44590280558892145364260795)
  ·
    refine ⟨66885420838338218046391193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44590280558892145364260795 66885420838338218046391193)
    ·
      refine ⟨50164065628753663534793395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66885420838338218046391193 50164065628753663534793395)
      ·
        refine ⟨75246098443130495302190093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50164065628753663534793395 75246098443130495302190093)
        ·
          refine ⟨28217286916173935738321285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75246098443130495302190093 28217286916173935738321285)
          ·
            refine ⟨5290741296782612950935241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28217286916173935738321285 5290741296782612950935241)
            ·
              refine ⟨3968055972586959713201431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5290741296782612950935241 3968055972586959713201431)
              ·
                refine ⟨5952083958880439569802147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3968055972586959713201431 5952083958880439569802147)
                ·
                  refine ⟨8928125938320659354703221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5952083958880439569802147 8928125938320659354703221)
                  ·
                    refine ⟨837011806717561814503427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8928125938320659354703221 837011806717561814503427)
                    ·
                      rfl

theorem cell22_2445112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_2445112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445112 prefixEnd_2445112 := by exact prefixLift 2445112
  have htrace : WordTrace (prefixWord ++ tailWord_2445112) baseStart_2445112 baseEnd_2445112 := by
    simpa [prefixWord, tailWord_2445112, baseEnd_2445112] using wordTrace_append hprefix tailTrace_2445112
  have hstable : (prefixWord ++ tailWord_2445112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445112).length < 2 ^ (prefixWord ++ tailWord_2445112).sum := by decide
  have hdescent : baseEnd_2445112 < baseStart_2445112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445127 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2445127 : Nat := 118140960795 + 2445127 * 2 ^ 59
def prefixEnd_2445127 : Nat := 4983230072969 + 3 ^ 40 * 2445127 * 2
def baseEnd_2445127 : Nat := 837016941524106775378381

theorem tailTrace_2445127 : CollatzResearch.WordTrace tailWord_2445127 prefixEnd_2445127 837016941524106775378381 := by
  unfold tailWord_2445127
  simp only [CollatzResearch.WordTrace]
  refine ⟨89181108212729948290317635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59454072141819965526878423 89181108212729948290317635)
  ·
    refine ⟨133771662319094922435476453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89181108212729948290317635 133771662319094922435476453)
    ·
      refine ⟨25082186684830297956651835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133771662319094922435476453 25082186684830297956651835)
      ·
        refine ⟨37623280027245446934977753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25082186684830297956651835 37623280027245446934977753)
        ·
          refine ⟨28217460020434085201233315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37623280027245446934977753 28217460020434085201233315)
          ·
            refine ⟨42326190030651127801849973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28217460020434085201233315 42326190030651127801849973)
            ·
              refine ⟨3968080315373543231423435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42326190030651127801849973 3968080315373543231423435)
              ·
                refine ⟨5952120473060314847135153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3968080315373543231423435 5952120473060314847135153)
                ·
                  refine ⟨4464090354795236135351365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5952120473060314847135153 4464090354795236135351365)
                  ·
                    refine ⟨837016941524106775378381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4464090354795236135351365 837016941524106775378381)
                    ·
                      rfl

theorem cell22_2445127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2445127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445127 prefixEnd_2445127 := by exact prefixLift 2445127
  have htrace : WordTrace (prefixWord ++ tailWord_2445127) baseStart_2445127 baseEnd_2445127 := by
    simpa [prefixWord, tailWord_2445127, baseEnd_2445127] using wordTrace_append hprefix tailTrace_2445127
  have hstable : (prefixWord ++ tailWord_2445127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445127).length < 2 ^ (prefixWord ++ tailWord_2445127).sum := by decide
  have hdescent : baseEnd_2445127 < baseStart_2445127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445133 : List Nat := [1, 6, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_2445133 : Nat := 118140960795 + 2445133 * 2 ^ 59
def prefixEnd_2445133 : Nat := 4983230072969 + 3 ^ 40 * 2445133 * 2
def baseEnd_2445133 : Nat := 837018995446724759728363

theorem tailTrace_2445133 : CollatzResearch.WordTrace tailWord_2445133 prefixEnd_2445133 837018995446724759728363 := by
  unfold tailWord_2445133
  simp only [CollatzResearch.WordTrace]
  refine ⟨89181327050708211315036053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59454218033805474210024035 89181327050708211315036053)
  ·
    refine ⟨4180374705501947405392315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89181327050708211315036053 4180374705501947405392315)
    ·
      refine ⟨6270562058252921108088473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4180374705501947405392315 6270562058252921108088473)
      ·
        refine ⟨4702921543689690831066355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6270562058252921108088473 4702921543689690831066355)
        ·
          refine ⟨7054382315534536246599533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4702921543689690831066355 7054382315534536246599533)
          ·
            refine ⟨2645393368325451092474825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7054382315534536246599533 2645393368325451092474825)
            ·
              refine ⟨1984045026244088319356119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2645393368325451092474825 1984045026244088319356119)
              ·
                refine ⟨2976067539366132479034179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984045026244088319356119 2976067539366132479034179)
                ·
                  refine ⟨4464101309049198718551269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976067539366132479034179 4464101309049198718551269)
                  ·
                    refine ⟨837018995446724759728363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4464101309049198718551269 837018995446724759728363)
                    ·
                      rfl

theorem cell22_2445133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_2445133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445133 prefixEnd_2445133 := by exact prefixLift 2445133
  have htrace : WordTrace (prefixWord ++ tailWord_2445133) baseStart_2445133 baseEnd_2445133 := by
    simpa [prefixWord, tailWord_2445133, baseEnd_2445133] using wordTrace_append hprefix tailTrace_2445133
  have hstable : (prefixWord ++ tailWord_2445133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445133).length < 2 ^ (prefixWord ++ tailWord_2445133).sum := by decide
  have hdescent : baseEnd_2445133 < baseStart_2445133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445208 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 3, 3]
def baseStart_2445208 : Nat := 118140960795 + 2445208 * 2 ^ 59
def prefixEnd_2445208 : Nat := 4983230072969 + 3 ^ 40 * 2445208 * 2
def baseEnd_2445208 : Nat := 837044669479449564103133

theorem tailTrace_2445208 : CollatzResearch.WordTrace tailWord_2445208 prefixEnd_2445208 837044669479449564103133 := by
  unfold tailWord_2445208
  simp only [CollatzResearch.WordTrace]
  refine ⟨44592031262718249562008139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59456041683624332749344185 44592031262718249562008139)
  ·
    refine ⟨66888046894077374343012209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44592031262718249562008139 66888046894077374343012209)
    ·
      refine ⟨50166035170558030757259157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66888046894077374343012209 50166035170558030757259157)
      ·
        refine ⟨2351532898619907691746523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50166035170558030757259157 2351532898619907691746523)
        ·
          refine ⟨3527299347929861537619785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351532898619907691746523 3527299347929861537619785)
          ·
            refine ⟨2645474510947396153214839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3527299347929861537619785 2645474510947396153214839)
            ·
              refine ⟨3968211766421094229822259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645474510947396153214839 3968211766421094229822259)
              ·
                refine ⟨5952317649631641344733389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3968211766421094229822259 5952317649631641344733389)
                ·
                  refine ⟨2232119118611865504275021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5952317649631641344733389 2232119118611865504275021)
                  ·
                    refine ⟨837044669479449564103133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2232119118611865504275021 837044669479449564103133)
                    ·
                      rfl

theorem cell22_2445208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_2445208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445208 prefixEnd_2445208 := by exact prefixLift 2445208
  have htrace : WordTrace (prefixWord ++ tailWord_2445208) baseStart_2445208 baseEnd_2445208 := by
    simpa [prefixWord, tailWord_2445208, baseEnd_2445208] using wordTrace_append hprefix tailTrace_2445208
  have hstable : (prefixWord ++ tailWord_2445208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445208).length < 2 ^ (prefixWord ++ tailWord_2445208).sum := by decide
  have hdescent : baseEnd_2445208 < baseStart_2445208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445247 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 1, 5]
def baseStart_2445247 : Nat := 118140960795 + 2445247 * 2 ^ 59
def prefixEnd_2445247 : Nat := 4983230072969 + 3 ^ 40 * 2445247 * 2
def baseEnd_2445247 : Nat := 837058019976466462378013

theorem tailTrace_2445247 : CollatzResearch.WordTrace tailWord_2445247 prefixEnd_2445247 837058019976466462378013 := by
  unfold tailWord_2445247
  simp only [CollatzResearch.WordTrace]
  refine ⟨89185484972295208784685995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59456989981530139189790663 89185484972295208784685995)
  ·
    refine ⟨133778227458442813177028993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89185484972295208784685995 133778227458442813177028993)
    ·
      refine ⟨100333670593832109882771745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133778227458442813177028993 100333670593832109882771745)
      ·
        refine ⟨75250252945374082412078809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100333670593832109882771745 75250252945374082412078809)
        ·
          refine ⟨56437689709030561809059107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75250252945374082412078809 56437689709030561809059107)
          ·
            refine ⟨84656534563545842713588661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56437689709030561809059107 84656534563545842713588661)
            ·
              refine ⟨7936550115332422754398937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84656534563545842713588661 7936550115332422754398937)
              ·
                refine ⟨5952412586499317065799203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7936550115332422754398937 5952412586499317065799203)
                ·
                  refine ⟨8928618879748975598698805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5952412586499317065799203 8928618879748975598698805)
                  ·
                    refine ⟨837058019976466462378013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8928618879748975598698805 837058019976466462378013)
                    ·
                      rfl

theorem cell22_2445247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_2445247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445247 prefixEnd_2445247 := by exact prefixLift 2445247
  have htrace : WordTrace (prefixWord ++ tailWord_2445247) baseStart_2445247 baseEnd_2445247 := by
    simpa [prefixWord, tailWord_2445247, baseEnd_2445247] using wordTrace_append hprefix tailTrace_2445247
  have hstable : (prefixWord ++ tailWord_2445247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445247).length < 2 ^ (prefixWord ++ tailWord_2445247).sum := by decide
  have hdescent : baseEnd_2445247 < baseStart_2445247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445264 : List Nat := [2, 1, 1, 1, 1, 2, 5, 4, 2, 3]
def baseStart_2445264 : Nat := 118140960795 + 2445264 * 2 ^ 59
def prefixEnd_2445264 : Nat := 4983230072969 + 3 ^ 40 * 2445264 * 2
def baseEnd_2445264 : Nat := 837063839423884084702961

theorem tailTrace_2445264 : CollatzResearch.WordTrace tailWord_2445264 prefixEnd_2445264 837063839423884084702961 := by
  unfold tailWord_2445264
  simp only [CollatzResearch.WordTrace]
  refine ⟨44593052506616810344027423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59457403342155747125369897 44593052506616810344027423)
  ·
    refine ⟨66889578759925215516041135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44593052506616810344027423 66889578759925215516041135)
    ·
      refine ⟨100334368139887823274061703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66889578759925215516041135 100334368139887823274061703)
      ·
        refine ⟨150501552209831734911092555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100334368139887823274061703 150501552209831734911092555)
        ·
          refine ⟨225752328314747602366638833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150501552209831734911092555 225752328314747602366638833)
          ·
            refine ⟨169314246236060701774979125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225752328314747602366638833 169314246236060701774979125)
            ·
              refine ⟨15873210584630690791404293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169314246236060701774979125 15873210584630690791404293)
              ·
                refine ⟨2976226984618254523388305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15873210584630690791404293 2976226984618254523388305)
                ·
                  refine ⟨2232170238463690892541229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2976226984618254523388305 2232170238463690892541229)
                  ·
                    refine ⟨837063839423884084702961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2232170238463690892541229 837063839423884084702961)
                    ·
                      rfl

theorem cell22_2445264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 2, 3].length) (baseStart_2445264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445264 prefixEnd_2445264 := by exact prefixLift 2445264
  have htrace : WordTrace (prefixWord ++ tailWord_2445264) baseStart_2445264 baseEnd_2445264 := by
    simpa [prefixWord, tailWord_2445264, baseEnd_2445264] using wordTrace_append hprefix tailTrace_2445264
  have hstable : (prefixWord ++ tailWord_2445264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445264).length < 2 ^ (prefixWord ++ tailWord_2445264).sum := by decide
  have hdescent : baseEnd_2445264 < baseStart_2445264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445326 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_2445326 : Nat := 118140960795 + 2445326 * 2 ^ 59
def prefixEnd_2445326 : Nat := 4983230072969 + 3 ^ 40 * 2445326 * 2
def baseEnd_2445326 : Nat := 837085063290936589652771

theorem tailTrace_2445326 : CollatzResearch.WordTrace tailWord_2445326 prefixEnd_2445326 837085063290936589652771 := by
  unfold tailWord_2445326
  simp only [CollatzResearch.WordTrace]
  refine ⟨11148545792376125659601479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59458910892672670184541221 11148545792376125659601479)
  ·
    refine ⟨16722818688564188489402219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11148545792376125659601479 16722818688564188489402219)
    ·
      refine ⟨25084228032846282734103329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16722818688564188489402219 25084228032846282734103329)
      ·
        refine ⟨18813171024634712050577497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25084228032846282734103329 18813171024634712050577497)
        ·
          refine ⟨14109878268476034037933123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18813171024634712050577497 14109878268476034037933123)
          ·
            refine ⟨21164817402714051056899685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14109878268476034037933123 21164817402714051056899685)
            ·
              refine ⟨3968403263008884573168691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21164817402714051056899685 3968403263008884573168691)
              ·
                refine ⟨5952604894513326859753037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3968403263008884573168691 5952604894513326859753037)
                ·
                  refine ⟨2232226835442497572407389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5952604894513326859753037 2232226835442497572407389)
                  ·
                    refine ⟨837085063290936589652771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2232226835442497572407389 837085063290936589652771)
                    ·
                      rfl

theorem cell22_2445326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_2445326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445326 prefixEnd_2445326 := by exact prefixLift 2445326
  have htrace : WordTrace (prefixWord ++ tailWord_2445326) baseStart_2445326 baseEnd_2445326 := by
    simpa [prefixWord, tailWord_2445326, baseEnd_2445326] using wordTrace_append hprefix tailTrace_2445326
  have hstable : (prefixWord ++ tailWord_2445326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445326).length < 2 ^ (prefixWord ++ tailWord_2445326).sum := by decide
  have hdescent : baseEnd_2445326 < baseStart_2445326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445332 : List Nat := [2, 4, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2445332 : Nat := 118140960795 + 2445332 * 2 ^ 59
def prefixEnd_2445332 : Nat := 4983230072969 + 3 ^ 40 * 2445332 * 2
def baseEnd_2445332 : Nat := 837087117213554574002753

theorem tailTrace_2445332 : CollatzResearch.WordTrace tailWord_2445332 prefixEnd_2445332 837087117213554574002753 := by
  unfold tailWord_2445332
  simp only [CollatzResearch.WordTrace]
  refine ⟨44594292588493634150765125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59459056784658178867686833 44594292588493634150765125)
  ·
    refine ⟨8361429860342556403268461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44594292588493634150765125 8361429860342556403268461)
    ·
      refine ⟨3135536197628458651225673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8361429860342556403268461 3135536197628458651225673)
      ·
        refine ⟨2351652148221343988419255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3135536197628458651225673 2351652148221343988419255)
        ·
          refine ⟨3527478222332015982628883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351652148221343988419255 3527478222332015982628883)
          ·
            refine ⟨5291217333498023973943325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527478222332015982628883 5291217333498023973943325)
            ·
              refine ⟨1984206500061758990228747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5291217333498023973943325 1984206500061758990228747)
              ·
                refine ⟨2976309750092638485343121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984206500061758990228747 2976309750092638485343121)
                ·
                  refine ⟨2232232312569478864007341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2976309750092638485343121 2232232312569478864007341)
                  ·
                    refine ⟨837087117213554574002753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2232232312569478864007341 837087117213554574002753)
                    ·
                      rfl

theorem cell22_2445332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2445332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445332 prefixEnd_2445332 := by exact prefixLift 2445332
  have htrace : WordTrace (prefixWord ++ tailWord_2445332) baseStart_2445332 baseEnd_2445332 := by
    simpa [prefixWord, tailWord_2445332, baseEnd_2445332] using wordTrace_append hprefix tailTrace_2445332
  have hstable : (prefixWord ++ tailWord_2445332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445332).length < 2 ^ (prefixWord ++ tailWord_2445332).sum := by decide
  have hdescent : baseEnd_2445332 < baseStart_2445332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445367 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 8]
def baseStart_2445367 : Nat := 118140960795 + 2445367 * 2 ^ 59
def prefixEnd_2445367 : Nat := 4983230072969 + 3 ^ 40 * 2445367 * 2
def baseEnd_2445367 : Nat := 279033032809608716459215

theorem tailTrace_2445367 : CollatzResearch.WordTrace tailWord_2445367 prefixEnd_2445367 279033032809608716459215 := by
  unfold tailWord_2445367
  simp only [CollatzResearch.WordTrace]
  refine ⟨89189861731860469279054355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59459907821240312852702903 89189861731860469279054355)
  ·
    refine ⟨133784792597790703918581533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89189861731860469279054355 133784792597790703918581533)
    ·
      refine ⟨50169297224171513969468075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133784792597790703918581533 50169297224171513969468075)
      ·
        refine ⟨75253945836257270954202113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50169297224171513969468075 75253945836257270954202113)
        ·
          refine ⟨56440459377192953215651585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75253945836257270954202113 56440459377192953215651585)
          ·
            refine ⟨42330344532894714911738689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56440459377192953215651585 42330344532894714911738689)
            ·
              refine ⟨31747758399671036183804017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42330344532894714911738689 31747758399671036183804017)
              ·
                refine ⟨23810818799753277137853013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31747758399671036183804017 23810818799753277137853013)
                ·
                  refine ⟨279033032809608716459215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23810818799753277137853013 279033032809608716459215)
                  ·
                    rfl

theorem cell22_2445367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 8].length) (baseStart_2445367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445367 prefixEnd_2445367 := by exact prefixLift 2445367
  have htrace : WordTrace (prefixWord ++ tailWord_2445367) baseStart_2445367 baseEnd_2445367 := by
    simpa [prefixWord, tailWord_2445367, baseEnd_2445367] using wordTrace_append hprefix tailTrace_2445367
  have hstable : (prefixWord ++ tailWord_2445367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445367).length < 2 ^ (prefixWord ++ tailWord_2445367).sum := by decide
  have hdescent : baseEnd_2445367 < baseStart_2445367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445433 : List Nat := [1, 2, 1, 3, 4, 2, 2, 2, 2, 3]
def baseStart_2445433 : Nat := 118140960795 + 2445433 * 2 ^ 59
def prefixEnd_2445433 : Nat := 4983230072969 + 3 ^ 40 * 2445433 * 2
def baseEnd_2445433 : Nat := 837121691577623977227443

theorem tailTrace_2445433 : CollatzResearch.WordTrace tailWord_2445433 prefixEnd_2445433 837121691577623977227443 := by
  unfold tailWord_2445433
  simp only [CollatzResearch.WordTrace]
  refine ⟨89192268949621362550956953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59461512633080908367304635 89192268949621362550956953)
  ·
    refine ⟨66894201712216021913217715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89192268949621362550956953 66894201712216021913217715)
    ·
      refine ⟨100341302568324032869826573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66894201712216021913217715 100341302568324032869826573)
      ·
        refine ⟨37627988463121512326184965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100341302568324032869826573 37627988463121512326184965)
        ·
          refine ⟨7055247836835283561159681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37627988463121512326184965 7055247836835283561159681)
          ·
            refine ⟨5291435877626462670869761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7055247836835283561159681 5291435877626462670869761)
            ·
              refine ⟨3968576908219847003152321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5291435877626462670869761 3968576908219847003152321)
              ·
                refine ⟨2976432681164885252364241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3968576908219847003152321 2976432681164885252364241)
                ·
                  refine ⟨2232324510873663939273181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2976432681164885252364241 2232324510873663939273181)
                  ·
                    refine ⟨837121691577623977227443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2232324510873663939273181 837121691577623977227443)
                    ·
                      rfl

theorem cell22_2445433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 3].length) (baseStart_2445433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445433 prefixEnd_2445433 := by exact prefixLift 2445433
  have htrace : WordTrace (prefixWord ++ tailWord_2445433) baseStart_2445433 baseEnd_2445433 := by
    simpa [prefixWord, tailWord_2445433, baseEnd_2445433] using wordTrace_append hprefix tailTrace_2445433
  have hstable : (prefixWord ++ tailWord_2445433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445433).length < 2 ^ (prefixWord ++ tailWord_2445433).sum := by decide
  have hdescent : baseEnd_2445433 < baseStart_2445433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445461 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 3, 3]
def baseStart_2445461 : Nat := 118140960795 + 2445461 * 2 ^ 59
def prefixEnd_2445461 : Nat := 4983230072969 + 3 ^ 40 * 2445461 * 2
def baseEnd_2445461 : Nat := 837131276549841237527357

theorem tailTrace_2445461 : CollatzResearch.WordTrace tailWord_2445461 prefixEnd_2445461 837131276549841237527357 := by
  unfold tailWord_2445461
  simp only [CollatzResearch.WordTrace]
  refine ⟨89193290193519923332976237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59462193462346615555317491 89193290193519923332976237)
  ·
    refine ⟨33447483822569971249866089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89193290193519923332976237 33447483822569971249866089)
    ·
      refine ⟨25085612866927478437399567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33447483822569971249866089 25085612866927478437399567)
      ·
        refine ⟨37628419300391217656099351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25085612866927478437399567 37628419300391217656099351)
        ·
          refine ⟨56442628950586826484149027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37628419300391217656099351 56442628950586826484149027)
          ·
            refine ⟨84663943425880239726223541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56442628950586826484149027 84663943425880239726223541)
            ·
              refine ⟨7937244696176272474333457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84663943425880239726223541 7937244696176272474333457)
              ·
                refine ⟨5952933522132204355750093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7937244696176272474333457 5952933522132204355750093)
                ·
                  refine ⟨2232350070799576633406285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5952933522132204355750093 2232350070799576633406285)
                  ·
                    refine ⟨837131276549841237527357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2232350070799576633406285 837131276549841237527357)
                    ·
                      rfl

theorem cell22_2445461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_2445461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445461 prefixEnd_2445461 := by exact prefixLift 2445461
  have htrace : WordTrace (prefixWord ++ tailWord_2445461) baseStart_2445461 baseEnd_2445461 := by
    simpa [prefixWord, tailWord_2445461, baseEnd_2445461] using wordTrace_append hprefix tailTrace_2445461
  have hstable : (prefixWord ++ tailWord_2445461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445461).length < 2 ^ (prefixWord ++ tailWord_2445461).sum := by decide
  have hdescent : baseEnd_2445461 < baseStart_2445461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445519 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 6]
def baseStart_2445519 : Nat := 118140960795 + 2445519 * 2 ^ 59
def prefixEnd_2445519 : Nat := 4983230072969 + 3 ^ 40 * 2445519 * 2
def baseEnd_2445519 : Nat := 279050377045049473192393

theorem tailTrace_2445519 : CollatzResearch.WordTrace tailWord_2445519 prefixEnd_2445519 279050377045049473192393 := by
  unfold tailWord_2445519
  simp only [CollatzResearch.WordTrace]
  refine ⟨89195405627309799238587611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59463603751539866159058407 89195405627309799238587611)
  ·
    refine ⟨133793108440964698857881417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89195405627309799238587611 133793108440964698857881417)
    ·
      refine ⟨100344831330723524143411063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133793108440964698857881417 100344831330723524143411063)
      ·
        refine ⟨150517246996085286215116595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100344831330723524143411063 150517246996085286215116595)
        ·
          refine ⟨225775870494127929322674893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150517246996085286215116595 225775870494127929322674893)
          ·
            refine ⟨84665951435297973496003085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225775870494127929322674893 84665951435297973496003085)
            ·
              refine ⟨31749731788236740061001157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84665951435297973496003085 31749731788236740061001157)
              ·
                refine ⟨5953074710294388761437717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31749731788236740061001157 5953074710294388761437717)
                ·
                  refine ⟨279050377045049473192393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5953074710294388761437717 279050377045049473192393)
                  ·
                    rfl

theorem cell22_2445519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 6].length) (baseStart_2445519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445519 prefixEnd_2445519 := by exact prefixLift 2445519
  have htrace : WordTrace (prefixWord ++ tailWord_2445519) baseStart_2445519 baseEnd_2445519 := by
    simpa [prefixWord, tailWord_2445519, baseEnd_2445519] using wordTrace_append hprefix tailTrace_2445519
  have hstable : (prefixWord ++ tailWord_2445519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445519).length < 2 ^ (prefixWord ++ tailWord_2445519).sum := by decide
  have hdescent : baseEnd_2445519 < baseStart_2445519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445521 : List Nat := [1, 2, 2, 1, 2, 2, 3, 4, 1, 4]
def baseStart_2445521 : Nat := 118140960795 + 2445521 * 2 ^ 59
def prefixEnd_2445521 : Nat := 4983230072969 + 3 ^ 40 * 2445521 * 2
def baseEnd_2445521 : Nat := 837151815776021081027173

theorem tailTrace_2445521 : CollatzResearch.WordTrace tailWord_2445521 prefixEnd_2445521 837151815776021081027173 := by
  unfold tailWord_2445521
  simp only [CollatzResearch.WordTrace]
  refine ⟨89195478573302553580160417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59463652382201702386773611 89195478573302553580160417)
  ·
    refine ⟨66896608929976915185120313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89195478573302553580160417 66896608929976915185120313)
    ·
      refine ⟨50172456697482686388840235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66896608929976915185120313 50172456697482686388840235)
      ·
        refine ⟨75258685046224029583260353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50172456697482686388840235 75258685046224029583260353)
        ·
          refine ⟨56444013784668022187445265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75258685046224029583260353 56444013784668022187445265)
          ·
            refine ⟨42333010338501016640583949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56444013784668022187445265 42333010338501016640583949)
            ·
              refine ⟨15874878876937881240218981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42333010338501016640583949 15874878876937881240218981)
              ·
                refine ⟨2976539789425852732541059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15874878876937881240218981 2976539789425852732541059)
                ·
                  refine ⟨4464809684138779098811589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976539789425852732541059 4464809684138779098811589)
                  ·
                    refine ⟨837151815776021081027173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4464809684138779098811589 837151815776021081027173)
                    ·
                      rfl

theorem cell22_2445521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_2445521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445521 prefixEnd_2445521 := by exact prefixLift 2445521
  have htrace : WordTrace (prefixWord ++ tailWord_2445521) baseStart_2445521 baseEnd_2445521 := by
    simpa [prefixWord, tailWord_2445521, baseEnd_2445521] using wordTrace_append hprefix tailTrace_2445521
  have hstable : (prefixWord ++ tailWord_2445521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445521).length < 2 ^ (prefixWord ++ tailWord_2445521).sum := by decide
  have hdescent : baseEnd_2445521 < baseStart_2445521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445572 : List Nat := [2, 3, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_2445572 : Nat := 118140960795 + 2445572 * 2 ^ 59
def prefixEnd_2445572 : Nat := 4983230072969 + 3 ^ 40 * 2445572 * 2
def baseEnd_2445572 : Nat := 837169274118273948002017

theorem tailTrace_2445572 : CollatzResearch.WordTrace tailWord_2445572 prefixEnd_2445572 837169274118273948002017 := by
  unfold tailWord_2445572
  simp only [CollatzResearch.WordTrace]
  refine ⟨44598669348058894645133485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59464892464078526193511313 44598669348058894645133485)
  ·
    refine ⟨16724501005522085491925057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44598669348058894645133485 16724501005522085491925057)
    ·
      refine ⟨12543375754141564118943793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16724501005522085491925057 12543375754141564118943793)
      ·
        refine ⟨9407531815606173089207845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12543375754141564118943793 9407531815606173089207845)
        ·
          refine ⟨1763912215426157454226471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9407531815606173089207845 1763912215426157454226471)
          ·
            refine ⟨2645868323139236181339707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763912215426157454226471 2645868323139236181339707)
            ·
              refine ⟨3968802484708854272009561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645868323139236181339707 3968802484708854272009561)
              ·
                refine ⟨2976601863531640704007171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3968802484708854272009561 2976601863531640704007171)
                ·
                  refine ⟨4464902795297461056010757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976601863531640704007171 4464902795297461056010757)
                  ·
                    refine ⟨837169274118273948002017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4464902795297461056010757 837169274118273948002017)
                    ·
                      rfl

theorem cell22_2445572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_2445572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445572 prefixEnd_2445572 := by exact prefixLift 2445572
  have htrace : WordTrace (prefixWord ++ tailWord_2445572) baseStart_2445572 baseEnd_2445572 := by
    simpa [prefixWord, tailWord_2445572, baseEnd_2445572] using wordTrace_append hprefix tailTrace_2445572
  have hstable : (prefixWord ++ tailWord_2445572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445572).length < 2 ^ (prefixWord ++ tailWord_2445572).sum := by decide
  have hdescent : baseEnd_2445572 < baseStart_2445572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445598 : List Nat := [4, 3, 2, 1, 1, 11]
def baseStart_2445598 : Nat := 118140960795 + 2445598 * 2 ^ 59
def prefixEnd_2445598 : Nat := 4983230072969 + 3 ^ 40 * 2445598 * 2
def baseEnd_2445598 : Nat := 10335533017896525269777

theorem tailTrace_2445598 : CollatzResearch.WordTrace tailWord_2445598 prefixEnd_2445598 10335533017896525269777 := by
  unfold tailWord_2445598
  simp only [CollatzResearch.WordTrace]
  refine ⟨11149785874252949466339181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59465524662682397153808965 11149785874252949466339181)
  ·
    refine ⟨4181169702844856049877193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11149785874252949466339181 4181169702844856049877193)
    ·
      refine ⟨3135877277133642037407895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4181169702844856049877193 3135877277133642037407895)
      ·
        refine ⟨4703815915700463056111843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3135877277133642037407895 4703815915700463056111843)
        ·
          refine ⟨7055723873550694584167765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703815915700463056111843 7055723873550694584167765)
          ·
            refine ⟨10335533017896525269777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7055723873550694584167765 10335533017896525269777)
            ·
              rfl

theorem cell22_2445598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 11].length) (baseStart_2445598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445598 prefixEnd_2445598 := by exact prefixLift 2445598
  have htrace : WordTrace (prefixWord ++ tailWord_2445598) baseStart_2445598 baseEnd_2445598 := by
    simpa [prefixWord, tailWord_2445598, baseEnd_2445598] using wordTrace_append hprefix tailTrace_2445598
  have hstable : (prefixWord ++ tailWord_2445598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445598).length < 2 ^ (prefixWord ++ tailWord_2445598).sum := by decide
  have hdescent : baseEnd_2445598 < baseStart_2445598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445630 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_2445630 : Nat := 118140960795 + 2445630 * 2 ^ 59
def prefixEnd_2445630 : Nat := 4983230072969 + 3 ^ 40 * 2445630 * 2
def baseEnd_2445630 : Nat := 837189128703581130051839

theorem tailTrace_2445630 : CollatzResearch.WordTrace tailWord_2445630 prefixEnd_2445630 837189128703581130051839 := by
  unfold tailWord_2445630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11149931766238458149484793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59466302753271776797252229 11149931766238458149484793)
  ·
    refine ⟨8362448824678843612113595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11149931766238458149484793 8362448824678843612113595)
    ·
      refine ⟨12543673237018265418170393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8362448824678843612113595 12543673237018265418170393)
      ·
        refine ⟨9407754927763699063627795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12543673237018265418170393 9407754927763699063627795)
        ·
          refine ⟨14111632391645548595441693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9407754927763699063627795 14111632391645548595441693)
          ·
            refine ⟨5291862146867080723290635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14111632391645548595441693 5291862146867080723290635)
            ·
              refine ⟨7937793220300621084935953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5291862146867080723290635 7937793220300621084935953)
              ·
                refine ⟨5953344915225465813701965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7937793220300621084935953 5953344915225465813701965)
                ·
                  refine ⟨2232504343209549680138237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5953344915225465813701965 2232504343209549680138237)
                  ·
                    refine ⟨837189128703581130051839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2232504343209549680138237 837189128703581130051839)
                    ·
                      rfl

theorem cell22_2445630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_2445630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445630 prefixEnd_2445630 := by exact prefixLift 2445630
  have htrace : WordTrace (prefixWord ++ tailWord_2445630) baseStart_2445630 baseEnd_2445630 := by
    simpa [prefixWord, tailWord_2445630, baseEnd_2445630] using wordTrace_append hprefix tailTrace_2445630
  have hstable : (prefixWord ++ tailWord_2445630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445630).length < 2 ^ (prefixWord ++ tailWord_2445630).sum := by decide
  have hdescent : baseEnd_2445630 < baseStart_2445630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445656 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 5, 4]
def baseStart_2445656 : Nat := 118140960795 + 2445656 * 2 ^ 59
def prefixEnd_2445656 : Nat := 4983230072969 + 3 ^ 40 * 2445656 * 2
def baseEnd_2445656 : Nat := 837198029034925728901759

theorem tailTrace_2445656 : CollatzResearch.WordTrace tailWord_2445656 prefixEnd_2445656 837198029034925728901759 := by
  unfold tailWord_2445656
  simp only [CollatzResearch.WordTrace]
  refine ⟨44600201213906735818162411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59466934951875647757549881 44600201213906735818162411)
  ·
    refine ⟨66900301820860103727243617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44600201213906735818162411 66900301820860103727243617)
    ·
      refine ⟨50175226365645077795432713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66900301820860103727243617 50175226365645077795432713)
      ·
        refine ⟨37631419774233808346574535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50175226365645077795432713 37631419774233808346574535)
        ·
          refine ⟨56447129661350712519861803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37631419774233808346574535 56447129661350712519861803)
          ·
            refine ⟨84670694492026068779792705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56447129661350712519861803 84670694492026068779792705)
            ·
              refine ⟨63503020869019551584844529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84670694492026068779792705 63503020869019551584844529)
              ·
                refine ⟨47627265651764663688633397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63503020869019551584844529 47627265651764663688633397)
                ·
                  refine ⟨4465056154852937220809381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47627265651764663688633397 4465056154852937220809381)
                  ·
                    refine ⟨837198029034925728901759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4465056154852937220809381 837198029034925728901759)
                    ·
                      rfl

theorem cell22_2445656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_2445656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445656 prefixEnd_2445656 := by exact prefixLift 2445656
  have htrace : WordTrace (prefixWord ++ tailWord_2445656) baseStart_2445656 baseEnd_2445656 := by
    simpa [prefixWord, tailWord_2445656, baseEnd_2445656] using wordTrace_append hprefix tailTrace_2445656
  have hstable : (prefixWord ++ tailWord_2445656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445656).length < 2 ^ (prefixWord ++ tailWord_2445656).sum := by decide
  have hdescent : baseEnd_2445656 < baseStart_2445656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445660 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 7]
def baseStart_2445660 : Nat := 118140960795 + 2445660 * 2 ^ 59
def prefixEnd_2445660 : Nat := 4983230072969 + 3 ^ 40 * 2445660 * 2
def baseEnd_2445660 : Nat := 279066466105557017267249

theorem tailTrace_2445660 : CollatzResearch.WordTrace tailWord_2445660 prefixEnd_2445660 279066466105557017267249 := by
  unfold tailWord_2445660
  simp only [CollatzResearch.WordTrace]
  refine ⟨44600274159899490159735217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59467032213199320212980289 44600274159899490159735217)
  ·
    refine ⟨33450205619924617619801413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44600274159899490159735217 33450205619924617619801413)
    ·
      refine ⟨6271913553735865803712765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33450205619924617619801413 6271913553735865803712765)
      ·
        refine ⟨2351967582650949676392287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6271913553735865803712765 2351967582650949676392287)
        ·
          refine ⟨3527951373976424514588431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351967582650949676392287 3527951373976424514588431)
          ·
            refine ⟨5291927060964636771882647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527951373976424514588431 5291927060964636771882647)
            ·
              refine ⟨7937890591446955157823971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5291927060964636771882647 7937890591446955157823971)
              ·
                refine ⟨11906835887170432736735957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7937890591446955157823971 11906835887170432736735957)
                ·
                  refine ⟨279066466105557017267249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11906835887170432736735957 279066466105557017267249)
                  ·
                    rfl

theorem cell22_2445660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_2445660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445660 prefixEnd_2445660 := by exact prefixLift 2445660
  have htrace : WordTrace (prefixWord ++ tailWord_2445660) baseStart_2445660 baseEnd_2445660 := by
    simpa [prefixWord, tailWord_2445660, baseEnd_2445660] using wordTrace_append hprefix tailTrace_2445660
  have hstable : (prefixWord ++ tailWord_2445660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445660).length < 2 ^ (prefixWord ++ tailWord_2445660).sum := by decide
  have hdescent : baseEnd_2445660 < baseStart_2445660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445698 : List Nat := [3, 4, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2445698 : Nat := 118140960795 + 2445698 * 2 ^ 59
def prefixEnd_2445698 : Nat := 4983230072969 + 3 ^ 40 * 2445698 * 2
def baseEnd_2445698 : Nat := 837212406493251619351631

theorem tailTrace_2445698 : CollatzResearch.WordTrace tailWord_2445698 prefixEnd_2445698 837212406493251619351631 := by
  unfold tailWord_2445698
  simp only [CollatzResearch.WordTrace]
  refine ⟨22300483573415328202338437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59467956195774208539569165 22300483573415328202338437)
  ·
    refine ⟨4181340670015374037938457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22300483573415328202338437 4181340670015374037938457)
    ·
      refine ⟨3136005502511530528453843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4181340670015374037938457 3136005502511530528453843)
      ·
        refine ⟨4704008253767295792680765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3136005502511530528453843 4704008253767295792680765)
        ·
          refine ⟨1764003095162735922255287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4704008253767295792680765 1764003095162735922255287)
          ·
            refine ⟨2646004642744103883382931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764003095162735922255287 2646004642744103883382931)
            ·
              refine ⟨3969006964116155825074397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646004642744103883382931 3969006964116155825074397)
              ·
                refine ⟨1488377611543558434402899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3969006964116155825074397 1488377611543558434402899)
                ·
                  refine ⟨2232566417315337651604349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488377611543558434402899 2232566417315337651604349)
                  ·
                    refine ⟨837212406493251619351631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2232566417315337651604349 837212406493251619351631)
                    ·
                      rfl

theorem cell22_2445698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2445698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445698 prefixEnd_2445698 := by exact prefixLift 2445698
  have htrace : WordTrace (prefixWord ++ tailWord_2445698) baseStart_2445698 baseEnd_2445698 := by
    simpa [prefixWord, tailWord_2445698, baseEnd_2445698] using wordTrace_append hprefix tailTrace_2445698
  have hstable : (prefixWord ++ tailWord_2445698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445698).length < 2 ^ (prefixWord ++ tailWord_2445698).sum := by decide
  have hdescent : baseEnd_2445698 < baseStart_2445698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445703 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 6, 3]
def baseStart_2445703 : Nat := 118140960795 + 2445703 * 2 ^ 59
def prefixEnd_2445703 : Nat := 4983230072969 + 3 ^ 40 * 2445703 * 2
def baseEnd_2445703 : Nat := 837214118095433272976615

theorem tailTrace_2445703 : CollatzResearch.WordTrace tailWord_2445703 prefixEnd_2445703 837214118095433272976615 := by
  unfold tailWord_2445703
  simp only [CollatzResearch.WordTrace]
  refine ⟨89202116658643198663285763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59468077772428799108857175 89202116658643198663285763)
  ·
    refine ⟨133803174987964797994928645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89202116658643198663285763 133803174987964797994928645)
    ·
      refine ⟨25088095310243399624049121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133803174987964797994928645 25088095310243399624049121)
      ·
        refine ⟨18816071482682549718036841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25088095310243399624049121 18816071482682549718036841)
        ·
          refine ⟨14112053612011912288527631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18816071482682549718036841 14112053612011912288527631)
          ·
            refine ⟨21168080418017868432791447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14112053612011912288527631 21168080418017868432791447)
            ·
              refine ⟨31752120627026802649187171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21168080418017868432791447 31752120627026802649187171)
              ·
                refine ⟨47628180940540203973780757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31752120627026802649187171 47628180940540203973780757)
                ·
                  refine ⟨2232570981587822061270973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47628180940540203973780757 2232570981587822061270973)
                  ·
                    refine ⟨837214118095433272976615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2232570981587822061270973 837214118095433272976615)
                    ·
                      rfl

theorem cell22_2445703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_2445703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445703 prefixEnd_2445703 := by exact prefixLift 2445703
  have htrace : WordTrace (prefixWord ++ tailWord_2445703) baseStart_2445703 baseEnd_2445703 := by
    simpa [prefixWord, tailWord_2445703, baseEnd_2445703] using wordTrace_append hprefix tailTrace_2445703
  have hstable : (prefixWord ++ tailWord_2445703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445703).length < 2 ^ (prefixWord ++ tailWord_2445703).sum := by decide
  have hdescent : baseEnd_2445703 < baseStart_2445703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445705 : List Nat := [1, 2, 1, 1, 6, 1, 3, 3, 4]
def baseStart_2445705 : Nat := 118140960795 + 2445705 * 2 ^ 59
def prefixEnd_2445705 : Nat := 4983230072969 + 3 ^ 40 * 2445705 * 2
def baseEnd_2445705 : Nat := 279071600912101978142203

theorem tailTrace_2445705 : CollatzResearch.WordTrace tailWord_2445705 prefixEnd_2445705 279071600912101978142203 := by
  unfold tailWord_2445705
  simp only [CollatzResearch.WordTrace]
  refine ⟨89202189604635953004858569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59468126403090635336572379 89202189604635953004858569)
  ·
    refine ⟨66901642203476964753643927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89202189604635953004858569 66901642203476964753643927)
    ·
      refine ⟨100352463305215447130465891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66901642203476964753643927 100352463305215447130465891)
      ·
        refine ⟨150528694957823170695698837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100352463305215447130465891 150528694957823170695698837)
        ·
          refine ⟨7056032576147961126360883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 150528694957823170695698837 7056032576147961126360883)
          ·
            refine ⟨10584048864221941689541325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7056032576147961126360883 10584048864221941689541325)
            ·
              refine ⟨3969018324083228133577997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10584048864221941689541325 3969018324083228133577997)
              ·
                refine ⟨1488381871531210550091749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3969018324083228133577997 1488381871531210550091749)
                ·
                  refine ⟨279071600912101978142203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1488381871531210550091749 279071600912101978142203)
                  ·
                    rfl

theorem cell22_2445705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 4].length) (baseStart_2445705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445705 prefixEnd_2445705 := by exact prefixLift 2445705
  have htrace : WordTrace (prefixWord ++ tailWord_2445705) baseStart_2445705 baseEnd_2445705 := by
    simpa [prefixWord, tailWord_2445705, baseEnd_2445705] using wordTrace_append hprefix tailTrace_2445705
  have hstable : (prefixWord ++ tailWord_2445705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445705).length < 2 ^ (prefixWord ++ tailWord_2445705).sum := by decide
  have hdescent : baseEnd_2445705 < baseStart_2445705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445720 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 4, 3]
def baseStart_2445720 : Nat := 118140960795 + 2445720 * 2 ^ 59
def prefixEnd_2445720 : Nat := 4983230072969 + 3 ^ 40 * 2445720 * 2
def baseEnd_2445720 : Nat := 837219937542850895301563

theorem tailTrace_2445720 : CollatzResearch.WordTrace tailWord_2445720 prefixEnd_2445720 837219937542850895301563 := by
  unfold tailWord_2445720
  simp only [CollatzResearch.WordTrace]
  refine ⟨44601368349790805283327307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59468491133054407044436409 44601368349790805283327307)
  ·
    refine ⟨66902052524686207924990961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44601368349790805283327307 66902052524686207924990961)
    ·
      refine ⟨50176539393514655943743221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66902052524686207924990961 50176539393514655943743221)
      ·
        refine ⟨4704050568141998994725927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50176539393514655943743221 4704050568141998994725927)
        ·
          refine ⟨7056075852212998492088891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704050568141998994725927 7056075852212998492088891)
          ·
            refine ⟨10584113778319497738133337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7056075852212998492088891 10584113778319497738133337)
            ·
              refine ⟨7938085333739623303600003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10584113778319497738133337 7938085333739623303600003)
              ·
                refine ⟨11907128000609434955400005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7938085333739623303600003 11907128000609434955400005)
                ·
                  refine ⟨2232586500114269054137501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11907128000609434955400005 2232586500114269054137501)
                  ·
                    refine ⟨837219937542850895301563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2232586500114269054137501 837219937542850895301563)
                    ·
                      rfl

theorem cell22_2445720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_2445720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445720 prefixEnd_2445720 := by exact prefixLift 2445720
  have htrace : WordTrace (prefixWord ++ tailWord_2445720) baseStart_2445720 baseEnd_2445720 := by
    simpa [prefixWord, tailWord_2445720, baseEnd_2445720] using wordTrace_append hprefix tailTrace_2445720
  have hstable : (prefixWord ++ tailWord_2445720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445720).length < 2 ^ (prefixWord ++ tailWord_2445720).sum := by decide
  have hdescent : baseEnd_2445720 < baseStart_2445720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445722 : List Nat := [3, 1, 1, 4, 1, 3, 3, 2, 4]
def baseStart_2445722 : Nat := 118140960795 + 2445722 * 2 ^ 59
def prefixEnd_2445722 : Nat := 4983230072969 + 3 ^ 40 * 2445722 * 2
def baseEnd_2445722 : Nat := 279073540727907852250519

theorem tailTrace_2445722 : CollatzResearch.WordTrace tailWord_2445722 prefixEnd_2445722 279073540727907852250519 := by
  unfold tailWord_2445722
  simp only [CollatzResearch.WordTrace]
  refine ⟨22300702411393591227056855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59468539763716243272151613 22300702411393591227056855)
  ·
    refine ⟨33451053617090386840585283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22300702411393591227056855 33451053617090386840585283)
    ·
      refine ⟨50176580425635580260877925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33451053617090386840585283 50176580425635580260877925)
      ·
        refine ⟨9408108829806671298914611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50176580425635580260877925 9408108829806671298914611)
        ·
          refine ⟨14112163244710006948371917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9408108829806671298914611 14112163244710006948371917)
          ·
            refine ⟨5292061216766252605639469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14112163244710006948371917 5292061216766252605639469)
            ·
              refine ⟨1984522956287344727114801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5292061216766252605639469 1984522956287344727114801)
              ·
                refine ⟨1488392217215508545336101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984522956287344727114801 1488392217215508545336101)
                ·
                  refine ⟨279073540727907852250519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1488392217215508545336101 279073540727907852250519)
                  ·
                    rfl

theorem cell22_2445722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_2445722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445722 prefixEnd_2445722 := by exact prefixLift 2445722
  have htrace : WordTrace (prefixWord ++ tailWord_2445722) baseStart_2445722 baseEnd_2445722 := by
    simpa [prefixWord, tailWord_2445722, baseEnd_2445722] using wordTrace_append hprefix tailTrace_2445722
  have hstable : (prefixWord ++ tailWord_2445722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445722).length < 2 ^ (prefixWord ++ tailWord_2445722).sum := by decide
  have hdescent : baseEnd_2445722 < baseStart_2445722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445782 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_2445782 : Nat := 118140960795 + 2445782 * 2 ^ 59
def prefixEnd_2445782 : Nat := 4983230072969 + 3 ^ 40 * 2445782 * 2
def baseEnd_2445782 : Nat := 837241161409903400251373

theorem tailTrace_2445782 : CollatzResearch.WordTrace tailWord_2445782 prefixEnd_2445782 837241161409903400251373 := by
  unfold tailWord_2445782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5575312376584812197213225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59469998683571330103607733 5575312376584812197213225)
  ·
    refine ⟨4181484282438609147909919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5575312376584812197213225 4181484282438609147909919)
    ·
      refine ⟨6272226423657913721864879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4181484282438609147909919 6272226423657913721864879)
      ·
        refine ⟨9408339635486870582797319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6272226423657913721864879 9408339635486870582797319)
        ·
          refine ⟨14112509453230305874195979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9408339635486870582797319 14112509453230305874195979)
          ·
            refine ⟨21168764179845458811293969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14112509453230305874195979 21168764179845458811293969)
            ·
              refine ⟨15876573134884094108470477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21168764179845458811293969 15876573134884094108470477)
              ·
                refine ⟨5953714925581535290676429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15876573134884094108470477 5953714925581535290676429)
                ·
                  refine ⟨2232643097093075734003661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5953714925581535290676429 2232643097093075734003661)
                  ·
                    refine ⟨837241161409903400251373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2232643097093075734003661 837241161409903400251373)
                    ·
                      rfl

theorem cell22_2445782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_2445782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445782 prefixEnd_2445782 := by exact prefixLift 2445782
  have htrace : WordTrace (prefixWord ++ tailWord_2445782) baseStart_2445782 baseEnd_2445782 := by
    simpa [prefixWord, tailWord_2445782, baseEnd_2445782] using wordTrace_append hprefix tailTrace_2445782
  have hstable : (prefixWord ++ tailWord_2445782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445782).length < 2 ^ (prefixWord ++ tailWord_2445782).sum := by decide
  have hdescent : baseEnd_2445782 < baseStart_2445782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445793 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 2, 5]
def baseStart_2445793 : Nat := 118140960795 + 2445793 * 2 ^ 59
def prefixEnd_2445793 : Nat := 4983230072969 + 3 ^ 40 * 2445793 * 2
def baseEnd_2445793 : Nat := 837244926934703038226339

theorem tailTrace_2445793 : CollatzResearch.WordTrace tailWord_2445793 prefixEnd_2445793 837244926934703038226339 := by
  unfold tailWord_2445793
  simp only [CollatzResearch.WordTrace]
  refine ⟨89205399228317144034062033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59470266152211429356041355 89205399228317144034062033)
  ·
    refine ⟨66904049421237858025546525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89205399228317144034062033 66904049421237858025546525)
    ·
      refine ⟨25089018532964196759579947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66904049421237858025546525 25089018532964196759579947)
      ·
        refine ⟨37633527799446295139369921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25089018532964196759579947 37633527799446295139369921)
        ·
          refine ⟨28225145849584721354527441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37633527799446295139369921 28225145849584721354527441)
          ·
            refine ⟨21168859387188541015895581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28225145849584721354527441 21168859387188541015895581)
            ·
              refine ⟨7938322270195702880960843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21168859387188541015895581 7938322270195702880960843)
              ·
                refine ⟨11907483405293554321441265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7938322270195702880960843 11907483405293554321441265)
                ·
                  refine ⟨8930612553970165741080949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11907483405293554321441265 8930612553970165741080949)
                  ·
                    refine ⟨837244926934703038226339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8930612553970165741080949 837244926934703038226339)
                    ·
                      rfl

theorem cell22_2445793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_2445793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445793 prefixEnd_2445793 := by exact prefixLift 2445793
  have htrace : WordTrace (prefixWord ++ tailWord_2445793) baseStart_2445793 baseEnd_2445793 := by
    simpa [prefixWord, tailWord_2445793, baseEnd_2445793] using wordTrace_append hprefix tailTrace_2445793
  have hstable : (prefixWord ++ tailWord_2445793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445793).length < 2 ^ (prefixWord ++ tailWord_2445793).sum := by decide
  have hdescent : baseEnd_2445793 < baseStart_2445793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445808 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 3, 4]
def baseStart_2445808 : Nat := 118140960795 + 2445808 * 2 ^ 59
def prefixEnd_2445808 : Nat := 4983230072969 + 3 ^ 40 * 2445808 * 2
def baseEnd_2445808 : Nat := 837250061741247999101293

theorem tailTrace_2445808 : CollatzResearch.WordTrace tailWord_2445808 prefixEnd_2445808 837250061741247999101293 := by
  unfold tailWord_2445808
  simp only [CollatzResearch.WordTrace]
  refine ⟨44602973161631400797929039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59470630882175201063905385 44602973161631400797929039)
  ·
    refine ⟨66904459742447101196893559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44602973161631400797929039 66904459742447101196893559)
    ·
      refine ⟨100356689613670651795340339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66904459742447101196893559 100356689613670651795340339)
      ·
        refine ⟨150535034420505977693010509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100356689613670651795340339 150535034420505977693010509)
        ·
          refine ⟨56450637907689741634878941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150535034420505977693010509 56450637907689741634878941)
          ·
            refine ⟨21168989215383653113079603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56450637907689741634878941 21168989215383653113079603)
            ·
              refine ⟨31753483823075479669619405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21168989215383653113079603 31753483823075479669619405)
              ·
                refine ⟨11907556433653304876107277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31753483823075479669619405 11907556433653304876107277)
                ·
                  refine ⟨4465333662619989328540229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11907556433653304876107277 4465333662619989328540229)
                  ·
                    refine ⟨837250061741247999101293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4465333662619989328540229 837250061741247999101293)
                    ·
                      rfl

theorem cell22_2445808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_2445808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445808 prefixEnd_2445808 := by exact prefixLift 2445808
  have htrace : WordTrace (prefixWord ++ tailWord_2445808) baseStart_2445808 baseEnd_2445808 := by
    simpa [prefixWord, tailWord_2445808, baseEnd_2445808] using wordTrace_append hprefix tailTrace_2445808
  have hstable : (prefixWord ++ tailWord_2445808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445808).length < 2 ^ (prefixWord ++ tailWord_2445808).sum := by decide
  have hdescent : baseEnd_2445808 < baseStart_2445808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445885 : List Nat := [1, 4, 1, 3, 2, 3, 8]
def baseStart_2445885 : Nat := 118140960795 + 2445885 * 2 ^ 59
def prefixEnd_2445885 : Nat := 4983230072969 + 3 ^ 40 * 2445885 * 2
def baseEnd_2445885 : Nat := 31010237793142424626891

theorem tailTrace_2445885 : CollatzResearch.WordTrace tailWord_2445885 prefixEnd_2445885 31010237793142424626891 := by
  unfold tailWord_2445885
  simp only [CollatzResearch.WordTrace]
  refine ⟨89208754743983843746411109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59472503162655895830940739 89208754743983843746411109)
  ·
    refine ⟨16726641514496970702452083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89208754743983843746411109 16726641514496970702452083)
    ·
      refine ⟨25089962271745456053678125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16726641514496970702452083 25089962271745456053678125)
      ·
        refine ⟨9408735851904546020129297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25089962271745456053678125 9408735851904546020129297)
        ·
          refine ⟨7056551888928409515096973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9408735851904546020129297 7056551888928409515096973)
          ·
            refine ⟨2646206958348153568161365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7056551888928409515096973 2646206958348153568161365)
            ·
              refine ⟨31010237793142424626891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2646206958348153568161365 31010237793142424626891)
              ·
                rfl

theorem cell22_2445885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 8].length) (baseStart_2445885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445885 prefixEnd_2445885 := by exact prefixLift 2445885
  have htrace : WordTrace (prefixWord ++ tailWord_2445885) baseStart_2445885 baseEnd_2445885 := by
    simpa [prefixWord, tailWord_2445885, baseEnd_2445885] using wordTrace_append hprefix tailTrace_2445885
  have hstable : (prefixWord ++ tailWord_2445885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445885).length < 2 ^ (prefixWord ++ tailWord_2445885).sum := by decide
  have hdescent : baseEnd_2445885 < baseStart_2445885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445962 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_2445962 : Nat := 118140960795 + 2445962 * 2 ^ 59
def prefixEnd_2445962 : Nat := 4983230072969 + 3 ^ 40 * 2445962 * 2
def baseEnd_2445962 : Nat := 837302779088442930750821

theorem tailTrace_2445962 : CollatzResearch.WordTrace tailWord_2445962 prefixEnd_2445962 837302779088442930750821 := by
  unfold tailWord_2445962
  simp only [CollatzResearch.WordTrace]
  refine ⟨22302890791176221474241035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59474375443136590597976093 22302890791176221474241035)
  ·
    refine ⟨33454336186764332211361553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22302890791176221474241035 33454336186764332211361553)
    ·
      refine ⟨25090752140073249158521165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33454336186764332211361553 25090752140073249158521165)
      ·
        refine ⟨9409032052527468434445437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25090752140073249158521165 9409032052527468434445437)
        ·
          refine ⟨3528387019697800662917039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9409032052527468434445437 3528387019697800662917039)
          ·
            refine ⟨5292580529546700994375559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528387019697800662917039 5292580529546700994375559)
            ·
              refine ⟨7938870794320051491563339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5292580529546700994375559 7938870794320051491563339)
              ·
                refine ⟨11908306191480077237345009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7938870794320051491563339 11908306191480077237345009)
                ·
                  refine ⟨8931229643610057928008757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11908306191480077237345009 8931229643610057928008757)
                  ·
                    refine ⟨837302779088442930750821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8931229643610057928008757 837302779088442930750821)
                    ·
                      rfl

theorem cell22_2445962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_2445962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445962 prefixEnd_2445962 := by exact prefixLift 2445962
  have htrace : WordTrace (prefixWord ++ tailWord_2445962) baseStart_2445962 baseEnd_2445962 := by
    simpa [prefixWord, tailWord_2445962, baseEnd_2445962] using wordTrace_append hprefix tailTrace_2445962
  have hstable : (prefixWord ++ tailWord_2445962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445962).length < 2 ^ (prefixWord ++ tailWord_2445962).sum := by decide
  have hdescent : baseEnd_2445962 < baseStart_2445962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445975 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 6]
def baseStart_2445975 : Nat := 118140960795 + 2445975 * 2 ^ 59
def prefixEnd_2445975 : Nat := 4983230072969 + 3 ^ 40 * 2445975 * 2
def baseEnd_2445975 : Nat := 279102409751371743391927

theorem tailTrace_2445975 : CollatzResearch.WordTrace tailWord_2445975 prefixEnd_2445975 279102409751371743391927 := by
  unfold tailWord_2445975
  simp only [CollatzResearch.WordTrace]
  refine ⟨89212037313657789117187379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59474691542438526078124919 89212037313657789117187379)
  ·
    refine ⟨133818055970486683675781069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89212037313657789117187379 133818055970486683675781069)
    ·
      refine ⟨50181770988932506378417901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133818055970486683675781069 50181770988932506378417901)
      ·
        refine ⟨18818164120849689891906713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50181770988932506378417901 18818164120849689891906713)
        ·
          refine ⟨14113623090637267418930035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18818164120849689891906713 14113623090637267418930035)
          ·
            refine ⟨21170434635955901128395053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14113623090637267418930035 21170434635955901128395053)
            ·
              refine ⟨7938912988483462923148145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21170434635955901128395053 7938912988483462923148145)
              ·
                refine ⟨5954184741362597192361109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7938912988483462923148145 5954184741362597192361109)
                ·
                  refine ⟨279102409751371743391927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5954184741362597192361109 279102409751371743391927)
                  ·
                    rfl

theorem cell22_2445975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 6].length) (baseStart_2445975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2445975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2445975 prefixEnd_2445975 := by exact prefixLift 2445975
  have htrace : WordTrace (prefixWord ++ tailWord_2445975) baseStart_2445975 baseEnd_2445975 := by
    simpa [prefixWord, tailWord_2445975, baseEnd_2445975] using wordTrace_append hprefix tailTrace_2445975
  have hstable : (prefixWord ++ tailWord_2445975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445975).length < 2 ^ (prefixWord ++ tailWord_2445975).sum := by decide
  have hdescent : baseEnd_2445975 < baseStart_2445975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446065 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 7]
def baseStart_2446065 : Nat := 118140960795 + 2446065 * 2 ^ 59
def prefixEnd_2446065 : Nat := 4983230072969 + 3 ^ 40 * 2446065 * 2
def baseEnd_2446065 : Nat := 279112679364461665141835

theorem tailTrace_2446065 : CollatzResearch.WordTrace tailWord_2446065 prefixEnd_2446065 279112679364461665141835 := by
  unfold tailWord_2446065
  simp only [CollatzResearch.WordTrace]
  refine ⟨89215319883331734487963649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59476879922221156325309099 89215319883331734487963649)
  ·
    refine ⟨66911489912498800865972737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89215319883331734487963649 66911489912498800865972737)
    ·
      refine ⟨50183617434374100649479553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66911489912498800865972737 50183617434374100649479553)
      ·
        refine ⟨37637713075780575487109665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50183617434374100649479553 37637713075780575487109665)
        ·
          refine ⟨28228284806835431615332249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37637713075780575487109665 28228284806835431615332249)
          ·
            refine ⟨21171213605126573711499187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28228284806835431615332249 21171213605126573711499187)
            ·
              refine ⟨31756820407689860567248781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21171213605126573711499187 31756820407689860567248781)
              ·
                refine ⟨11908807652883697712718293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31756820407689860567248781 11908807652883697712718293)
                ·
                  refine ⟨279112679364461665141835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11908807652883697712718293 279112679364461665141835)
                  ·
                    rfl

theorem cell22_2446065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_2446065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446065 prefixEnd_2446065 := by exact prefixLift 2446065
  have htrace : WordTrace (prefixWord ++ tailWord_2446065) baseStart_2446065 baseEnd_2446065 := by
    simpa [prefixWord, tailWord_2446065, baseEnd_2446065] using wordTrace_append hprefix tailTrace_2446065
  have hstable : (prefixWord ++ tailWord_2446065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446065).length < 2 ^ (prefixWord ++ tailWord_2446065).sum := by decide
  have hdescent : baseEnd_2446065 < baseStart_2446065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446161 : List Nat := [1, 2, 2, 1, 6, 1, 2, 3, 4]
def baseStart_2446161 : Nat := 118140960795 + 2446161 * 2 ^ 59
def prefixEnd_2446161 : Nat := 4983230072969 + 3 ^ 40 * 2446161 * 2
def baseEnd_2446161 : Nat := 279123633618424248341737

theorem tailTrace_2446161 : CollatzResearch.WordTrace tailWord_2446161 prefixEnd_2446161 279123633618424248341737 := by
  unfold tailWord_2446161
  simp only [CollatzResearch.WordTrace]
  refine ⟨89218821290983942883458337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59479214193989295255638891 89218821290983942883458337)
  ·
    refine ⟨66914115968237957162593753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89218821290983942883458337 66914115968237957162593753)
    ·
      refine ⟨50185586976178467871945315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66914115968237957162593753 50185586976178467871945315)
      ·
        refine ⟨75278380464267701807917973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50185586976178467871945315 75278380464267701807917973)
        ·
          refine ⟨3528674084262548522246155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75278380464267701807917973 3528674084262548522246155)
          ·
            refine ⟨5293011126393822783369233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528674084262548522246155 5293011126393822783369233)
            ·
              refine ⟨3969758344795367087526925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5293011126393822783369233 3969758344795367087526925)
              ·
                refine ⟨1488659379298262657822597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3969758344795367087526925 1488659379298262657822597)
                ·
                  refine ⟨279123633618424248341737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1488659379298262657822597 279123633618424248341737)
                  ·
                    rfl

theorem cell22_2446161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 4].length) (baseStart_2446161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446161 prefixEnd_2446161 := by exact prefixLift 2446161
  have htrace : WordTrace (prefixWord ++ tailWord_2446161) baseStart_2446161 baseEnd_2446161 := by
    simpa [prefixWord, tailWord_2446161, baseEnd_2446161] using wordTrace_append hprefix tailTrace_2446161
  have hstable : (prefixWord ++ tailWord_2446161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446161).length < 2 ^ (prefixWord ++ tailWord_2446161).sum := by decide
  have hdescent : baseEnd_2446161 < baseStart_2446161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446206 : List Nat := [4, 2, 3, 1, 2, 1, 1, 8]
def baseStart_2446206 : Nat := 118140960795 + 2446206 * 2 ^ 59
def prefixEnd_2446206 : Nat := 4983230072969 + 3 ^ 40 * 2446206 * 2
def baseEnd_2446206 : Nat := 93042922808323069738897

theorem tailTrace_2446206 : CollatzResearch.WordTrace tailWord_2446206 prefixEnd_2446206 93042922808323069738897 := by
  unfold tailWord_2446206
  simp only [CollatzResearch.WordTrace]
  refine ⟨11152557821977614446105809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59480308383880610379230981 11152557821977614446105809)
  ·
    refine ⟨8364418366483210834579357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11152557821977614446105809 8364418366483210834579357)
    ·
      refine ⟨3136656887431204062967259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8364418366483210834579357 3136656887431204062967259)
      ·
        refine ⟨4704985331146806094450889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3136656887431204062967259 4704985331146806094450889)
        ·
          refine ⟨3528738998360104570838167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4704985331146806094450889 3528738998360104570838167)
          ·
            refine ⟨5293108497540156856257251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528738998360104570838167 5293108497540156856257251)
            ·
              refine ⟨7939662746310235284385877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5293108497540156856257251 7939662746310235284385877)
              ·
                refine ⟨93042922808323069738897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7939662746310235284385877 93042922808323069738897)
                ·
                  rfl

theorem cell22_2446206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_2446206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446206 prefixEnd_2446206 := by exact prefixLift 2446206
  have htrace : WordTrace (prefixWord ++ tailWord_2446206) baseStart_2446206 baseEnd_2446206 := by
    simpa [prefixWord, tailWord_2446206, baseEnd_2446206] using wordTrace_append hprefix tailTrace_2446206
  have hstable : (prefixWord ++ tailWord_2446206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446206).length < 2 ^ (prefixWord ++ tailWord_2446206).sum := by decide
  have hdescent : baseEnd_2446206 < baseStart_2446206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446217 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 7]
def baseStart_2446217 : Nat := 118140960795 + 2446217 * 2 ^ 59
def prefixEnd_2446217 : Nat := 4983230072969 + 3 ^ 40 * 2446217 * 2
def baseEnd_2446217 : Nat := 279130023599902421875013

theorem tailTrace_2446217 : CollatzResearch.WordTrace tailWord_2446217 prefixEnd_2446217 279130023599902421875013 := by
  unfold tailWord_2446217
  simp only [CollatzResearch.WordTrace]
  refine ⟨89220863778781064447496905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59480575852520709631664603 89220863778781064447496905)
  ·
    refine ⟨66915647834085798335622679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89220863778781064447496905 66915647834085798335622679)
    ·
      refine ⟨100373471751128697503434019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66915647834085798335622679 100373471751128697503434019)
      ·
        refine ⟨150560207626693046255151029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100373471751128697503434019 150560207626693046255151029)
        ·
          refine ⟨14115019465002473086420409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150560207626693046255151029 14115019465002473086420409)
          ·
            refine ⟨10586264598751854814815307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14115019465002473086420409 10586264598751854814815307)
            ·
              refine ⟨15879396898127782222222961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10586264598751854814815307 15879396898127782222222961)
              ·
                refine ⟨11909547673595836666667221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15879396898127782222222961 11909547673595836666667221)
                ·
                  refine ⟨279130023599902421875013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11909547673595836666667221 279130023599902421875013)
                  ·
                    rfl

theorem cell22_2446217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_2446217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446217 prefixEnd_2446217 := by exact prefixLift 2446217
  have htrace : WordTrace (prefixWord ++ tailWord_2446217) baseStart_2446217 baseEnd_2446217 := by
    simpa [prefixWord, tailWord_2446217, baseEnd_2446217] using wordTrace_append hprefix tailTrace_2446217
  have hstable : (prefixWord ++ tailWord_2446217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446217).length < 2 ^ (prefixWord ++ tailWord_2446217).sum := by decide
  have hdescent : baseEnd_2446217 < baseStart_2446217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446264 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 3, 4]
def baseStart_2446264 : Nat := 118140960795 + 2446264 * 2 ^ 59
def prefixEnd_2446264 : Nat := 4983230072969 + 3 ^ 40 * 2446264 * 2
def baseEnd_2446264 : Nat := 837406159860214809699895

theorem tailTrace_2446264 : CollatzResearch.WordTrace tailWord_2446264 prefixEnd_2446264 837406159860214809699895 := by
  unfold tailWord_2446264
  simp only [CollatzResearch.WordTrace]
  refine ⟨44611289004805395737228923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59481718673073860982971897 44611289004805395737228923)
  ·
    refine ⟨66916933507208093605843385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44611289004805395737228923 66916933507208093605843385)
    ·
      refine ⟨50187700130406070204382539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66916933507208093605843385 50187700130406070204382539)
      ·
        refine ⟨75281550195609105306573809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50187700130406070204382539 75281550195609105306573809)
        ·
          refine ⟨56461162646706828979930357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75281550195609105306573809 56461162646706828979930357)
          ·
            refine ⟨5293233998128765216868471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56461162646706828979930357 5293233998128765216868471)
            ·
              refine ⟨7939850997193147825302707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5293233998128765216868471 7939850997193147825302707)
              ·
                refine ⟨11909776495789721737954061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7939850997193147825302707 11909776495789721737954061)
                ·
                  refine ⟨4466166185921145651732773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11909776495789721737954061 4466166185921145651732773)
                  ·
                    refine ⟨837406159860214809699895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4466166185921145651732773 837406159860214809699895)
                    ·
                      rfl

theorem cell22_2446264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_2446264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446264 prefixEnd_2446264 := by exact prefixLift 2446264
  have htrace : WordTrace (prefixWord ++ tailWord_2446264) baseStart_2446264 baseEnd_2446264 := by
    simpa [prefixWord, tailWord_2446264, baseEnd_2446264] using wordTrace_append hprefix tailTrace_2446264
  have hstable : (prefixWord ++ tailWord_2446264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446264).length < 2 ^ (prefixWord ++ tailWord_2446264).sum := by decide
  have hdescent : baseEnd_2446264 < baseStart_2446264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446296 : List Nat := [2, 1, 2, 2, 2, 4, 1, 4, 4]
def baseStart_2446296 : Nat := 118140960795 + 2446296 * 2 ^ 59
def prefixEnd_2446296 : Nat := 4983230072969 + 3 ^ 40 * 2446296 * 2
def baseEnd_2446296 : Nat := 279139038038059130966599

theorem tailTrace_2446296 : CollatzResearch.WordTrace tailWord_2446296 prefixEnd_2446296 279139038038059130966599 := by
  unfold tailWord_2446296
  simp only [CollatzResearch.WordTrace]
  refine ⟨44611872572747430469811371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59482496763663240626415161 44611872572747430469811371)
  ·
    refine ⟨66917808859121145704717057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44611872572747430469811371 66917808859121145704717057)
    ·
      refine ⟨50188356644340859278537793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66917808859121145704717057 50188356644340859278537793)
      ·
        refine ⟨37641267483255644458903345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50188356644340859278537793 37641267483255644458903345)
        ·
          refine ⟨28230950612441733344177509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37641267483255644458903345 28230950612441733344177509)
          ·
            refine ⟨5293303239832825002033283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28230950612441733344177509 5293303239832825002033283)
            ·
              refine ⟨7939954859749237503049925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5293303239832825002033283 7939954859749237503049925)
              ·
                refine ⟨1488741536202982031821861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7939954859749237503049925 1488741536202982031821861)
                ·
                  refine ⟨279139038038059130966599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1488741536202982031821861 279139038038059130966599)
                  ·
                    rfl

theorem cell22_2446296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 4].length) (baseStart_2446296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446296 prefixEnd_2446296 := by exact prefixLift 2446296
  have htrace : WordTrace (prefixWord ++ tailWord_2446296) baseStart_2446296 baseEnd_2446296 := by
    simpa [prefixWord, tailWord_2446296, baseEnd_2446296] using wordTrace_append hprefix tailTrace_2446296
  have hstable : (prefixWord ++ tailWord_2446296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446296).length < 2 ^ (prefixWord ++ tailWord_2446296).sum := by decide
  have hdescent : baseEnd_2446296 < baseStart_2446296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446311 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2446311 : Nat := 118140960795 + 2446311 * 2 ^ 59
def prefixEnd_2446311 : Nat := 4983230072969 + 3 ^ 40 * 2446311 * 2
def baseEnd_2446311 : Nat := 837422248920722353774751

theorem tailTrace_2446311 : CollatzResearch.WordTrace tailWord_2446311 prefixEnd_2446311 837422248920722353774751 := by
  unfold tailWord_2446311
  simp only [CollatzResearch.WordTrace]
  refine ⟨89224292240440518501418787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59482861493627012334279191 89224292240440518501418787)
  ·
    refine ⟨133836438360660777752128181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89224292240440518501418787 133836438360660777752128181)
    ·
      refine ⟨12547166096311947914262017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133836438360660777752128181 12547166096311947914262017)
      ·
        refine ⟨9410374572233960935696513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12547166096311947914262017 9410374572233960935696513)
        ·
          refine ⟨7057780929175470701772385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9410374572233960935696513 7057780929175470701772385)
          ·
            refine ⟨5293335696881603026329289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7057780929175470701772385 5293335696881603026329289)
            ·
              refine ⟨3970001772661202269746967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5293335696881603026329289 3970001772661202269746967)
              ·
                refine ⟨5955002658991803404620451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3970001772661202269746967 5955002658991803404620451)
                ·
                  refine ⟨8932503988487705106930677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5955002658991803404620451 8932503988487705106930677)
                  ·
                    refine ⟨837422248920722353774751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8932503988487705106930677 837422248920722353774751)
                    ·
                      rfl

theorem cell22_2446311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2446311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446311 prefixEnd_2446311 := by exact prefixLift 2446311
  have htrace : WordTrace (prefixWord ++ tailWord_2446311) baseStart_2446311 baseEnd_2446311 := by
    simpa [prefixWord, tailWord_2446311, baseEnd_2446311] using wordTrace_append hprefix tailTrace_2446311
  have hstable : (prefixWord ++ tailWord_2446311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446311).length < 2 ^ (prefixWord ++ tailWord_2446311).sum := by decide
  have hdescent : baseEnd_2446311 < baseStart_2446311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446326 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_2446326 : Nat := 118140960795 + 2446326 * 2 ^ 59
def prefixEnd_2446326 : Nat := 4983230072969 + 3 ^ 40 * 2446326 * 2
def baseEnd_2446326 : Nat := 837427383727267314649705

theorem tailTrace_2446326 : CollatzResearch.WordTrace tailWord_2446326 prefixEnd_2446326 837427383727267314649705 := by
  unfold tailWord_2446326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5576552458461636003950927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59483226223590784042143221 5576552458461636003950927)
  ·
    refine ⟨8364828687692454005926391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5576552458461636003950927 8364828687692454005926391)
    ·
      refine ⟨12547243031538681008889587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8364828687692454005926391 12547243031538681008889587)
      ·
        refine ⟨18820864547308021513334381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12547243031538681008889587 18820864547308021513334381)
        ·
          refine ⟨7057824205240508067500393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18820864547308021513334381 7057824205240508067500393)
          ·
            refine ⟨5293368153930381050625295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7057824205240508067500393 5293368153930381050625295)
            ·
              refine ⟨7940052230895571575937943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5293368153930381050625295 7940052230895571575937943)
              ·
                refine ⟨11910078346343357363906915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7940052230895571575937943 11910078346343357363906915)
                ·
                  refine ⟨17865117519515036045860373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11910078346343357363906915 17865117519515036045860373)
                  ·
                    refine ⟨837427383727267314649705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17865117519515036045860373 837427383727267314649705)
                    ·
                      rfl

theorem cell22_2446326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_2446326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446326 prefixEnd_2446326 := by exact prefixLift 2446326
  have htrace : WordTrace (prefixWord ++ tailWord_2446326) baseStart_2446326 baseEnd_2446326 := by
    simpa [prefixWord, tailWord_2446326, baseEnd_2446326] using wordTrace_append hprefix tailTrace_2446326
  have hstable : (prefixWord ++ tailWord_2446326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446326).length < 2 ^ (prefixWord ++ tailWord_2446326).sum := by decide
  have hdescent : baseEnd_2446326 < baseStart_2446326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446399 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 5, 4]
def baseStart_2446399 : Nat := 118140960795 + 2446399 * 2 ^ 59
def prefixEnd_2446399 : Nat := 4983230072969 + 3 ^ 40 * 2446399 * 2
def baseEnd_2446399 : Nat := 837452373119119457574481

theorem tailTrace_2446399 : CollatzResearch.WordTrace tailWord_2446399 prefixEnd_2446399 837452373119119457574481 := by
  unfold tailWord_2446399
  simp only [CollatzResearch.WordTrace]
  refine ⟨89227501864121709530622251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59485001242747806353748167 89227501864121709530622251)
  ·
    refine ⟨133841252796182564295933377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89227501864121709530622251 133841252796182564295933377)
    ·
      refine ⟨100380939597136923221950033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133841252796182564295933377 100380939597136923221950033)
      ·
        refine ⟨75285704697852692416462525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100380939597136923221950033 75285704697852692416462525)
        ·
          refine ⟨28232139261694759656173447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75285704697852692416462525 28232139261694759656173447)
          ·
            refine ⟨42348208892542139484260171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28232139261694759656173447 42348208892542139484260171)
            ·
              refine ⟨63522313338813209226390257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42348208892542139484260171 63522313338813209226390257)
              ·
                refine ⟨47641735004109906919792693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63522313338813209226390257 47641735004109906919792693)
                ·
                  refine ⟨4466412656635303773730565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47641735004109906919792693 4466412656635303773730565)
                  ·
                    refine ⟨837452373119119457574481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4466412656635303773730565 837452373119119457574481)
                    ·
                      rfl

theorem cell22_2446399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_2446399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446399 prefixEnd_2446399 := by exact prefixLift 2446399
  have htrace : WordTrace (prefixWord ++ tailWord_2446399) baseStart_2446399 baseEnd_2446399 := by
    simpa [prefixWord, tailWord_2446399, baseEnd_2446399] using wordTrace_append hprefix tailTrace_2446399
  have hstable : (prefixWord ++ tailWord_2446399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446399).length < 2 ^ (prefixWord ++ tailWord_2446399).sum := by decide
  have hdescent : baseEnd_2446399 < baseStart_2446399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446446 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2446446 : Nat := 118140960795 + 2446446 * 2 ^ 59
def prefixEnd_2446446 : Nat := 4983230072969 + 3 ^ 40 * 2446446 * 2
def baseEnd_2446446 : Nat := 837468462179627001649337

theorem tailTrace_2446446 : CollatzResearch.WordTrace tailWord_2446446 prefixEnd_2446446 837468462179627001649337 := by
  unfold tailWord_2446446
  simp only [CollatzResearch.WordTrace]
  refine ⟨11153652011868929569697899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59486144063300957705055461 11153652011868929569697899)
  ·
    refine ⟨16730478017803394354546849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11153652011868929569697899 16730478017803394354546849)
    ·
      refine ⟨12547858513352545765910137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16730478017803394354546849 12547858513352545765910137)
      ·
        refine ⟨9410893885014409324432603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12547858513352545765910137 9410893885014409324432603)
        ·
          refine ⟨14116340827521613986648905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9410893885014409324432603 14116340827521613986648905)
          ·
            refine ⟨10587255620641210489986679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14116340827521613986648905 10587255620641210489986679)
            ·
              refine ⟨15880883430961815734980019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10587255620641210489986679 15880883430961815734980019)
              ·
                refine ⟨23821325146442723602470029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15880883430961815734980019 23821325146442723602470029)
                ·
                  refine ⟨8932996929916021350926261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23821325146442723602470029 8932996929916021350926261)
                  ·
                    refine ⟨837468462179627001649337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8932996929916021350926261 837468462179627001649337)
                    ·
                      rfl

theorem cell22_2446446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2446446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446446 prefixEnd_2446446 := by exact prefixLift 2446446
  have htrace : WordTrace (prefixWord ++ tailWord_2446446) baseStart_2446446 baseEnd_2446446 := by
    simpa [prefixWord, tailWord_2446446, baseEnd_2446446] using wordTrace_append hprefix tailTrace_2446446
  have hstable : (prefixWord ++ tailWord_2446446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446446).length < 2 ^ (prefixWord ++ tailWord_2446446).sum := by decide
  have hdescent : baseEnd_2446446 < baseStart_2446446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446461 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_2446461 : Nat := 118140960795 + 2446461 * 2 ^ 59
def prefixEnd_2446461 : Nat := 4983230072969 + 3 ^ 40 * 2446461 * 2
def baseEnd_2446461 : Nat := 837473596986171962524291

theorem tailTrace_2446461 : CollatzResearch.WordTrace tailWord_2446461 prefixEnd_2446461 837473596986171962524291 := by
  unfold tailWord_2446461
  simp only [CollatzResearch.WordTrace]
  refine ⟨89229763189897094119379237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59486508793264729412919491 89229763189897094119379237)
  ·
    refine ⟨16730580598105705147383607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89229763189897094119379237 16730580598105705147383607)
    ·
      refine ⟨25095870897158557721075411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16730580598105705147383607 25095870897158557721075411)
      ·
        refine ⟨37643806345737836581613117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25095870897158557721075411 37643806345737836581613117)
        ·
          refine ⟨14116427379651688718104919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37643806345737836581613117 14116427379651688718104919)
          ·
            refine ⟨21174641069477533077157379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14116427379651688718104919 21174641069477533077157379)
            ·
              refine ⟨31761961604216299615736069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21174641069477533077157379 31761961604216299615736069)
              ·
                refine ⟨5955367800790556177950513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31761961604216299615736069 5955367800790556177950513)
                ·
                  refine ⟨4466525850592917133462885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5955367800790556177950513 4466525850592917133462885)
                  ·
                    refine ⟨837473596986171962524291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4466525850592917133462885 837473596986171962524291)
                    ·
                      rfl

theorem cell22_2446461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_2446461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446461 prefixEnd_2446461 := by exact prefixLift 2446461
  have htrace : WordTrace (prefixWord ++ tailWord_2446461) baseStart_2446461 baseEnd_2446461 := by
    simpa [prefixWord, tailWord_2446461, baseEnd_2446461] using wordTrace_append hprefix tailTrace_2446461
  have hstable : (prefixWord ++ tailWord_2446461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446461).length < 2 ^ (prefixWord ++ tailWord_2446461).sum := by decide
  have hdescent : baseEnd_2446461 < baseStart_2446461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446465 : List Nat := [1, 2, 4, 2, 2, 1, 4, 2, 4]
def baseStart_2446465 : Nat := 118140960795 + 2446465 * 2 ^ 59
def prefixEnd_2446465 : Nat := 4983230072969 + 3 ^ 40 * 2446465 * 2
def baseEnd_2446465 : Nat := 279158322089305761808093

theorem tailTrace_2446465 : CollatzResearch.WordTrace tailWord_2446465 prefixEnd_2446465 279158322089305761808093 := by
  unfold tailWord_2446465
  simp only [CollatzResearch.WordTrace]
  refine ⟨89229909081882602802524849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59486606054588401868349899 89229909081882602802524849)
  ·
    refine ⟨66922431811411952101893637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89229909081882602802524849 66922431811411952101893637)
    ·
      refine ⟨12547955964639741019105057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66922431811411952101893637 12547955964639741019105057)
      ·
        refine ⟨9410966973479805764328793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12547955964639741019105057 9410966973479805764328793)
        ·
          refine ⟨7058225230109854323246595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9410966973479805764328793 7058225230109854323246595)
          ·
            refine ⟨10587337845164781484869893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058225230109854323246595 10587337845164781484869893)
            ·
              refine ⟨1985125845968396528413105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10587337845164781484869893 1985125845968396528413105)
              ·
                refine ⟨1488844384476297396309829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1985125845968396528413105 1488844384476297396309829)
                ·
                  refine ⟨279158322089305761808093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1488844384476297396309829 279158322089305761808093)
                  ·
                    rfl

theorem cell22_2446465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 4].length) (baseStart_2446465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446465 prefixEnd_2446465 := by exact prefixLift 2446465
  have htrace : WordTrace (prefixWord ++ tailWord_2446465) baseStart_2446465 baseEnd_2446465 := by
    simpa [prefixWord, tailWord_2446465, baseEnd_2446465] using wordTrace_append hprefix tailTrace_2446465
  have hstable : (prefixWord ++ tailWord_2446465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446465).length < 2 ^ (prefixWord ++ tailWord_2446465).sum := by decide
  have hdescent : baseEnd_2446465 < baseStart_2446465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446495 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 2, 4]
def baseStart_2446495 : Nat := 118140960795 + 2446495 * 2 ^ 59
def prefixEnd_2446495 : Nat := 4983230072969 + 3 ^ 40 * 2446495 * 2
def baseEnd_2446495 : Nat := 837485235881007207174187

theorem tailTrace_2446495 : CollatzResearch.WordTrace tailWord_2446495 prefixEnd_2446495 837485235881007207174187 := by
  unfold tailWord_2446495
  simp only [CollatzResearch.WordTrace]
  refine ⟨89231003271773917926116939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59487335514515945284077959 89231003271773917926116939)
  ·
    refine ⟨133846504907660876889175409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89231003271773917926116939 133846504907660876889175409)
    ·
      refine ⟨100384878680745657666881557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133846504907660876889175409 100384878680745657666881557)
      ·
        refine ⟨4705541188159952703135073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100384878680745657666881557 4705541188159952703135073)
        ·
          refine ⟨3529155891119964527351305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4705541188159952703135073 3529155891119964527351305)
          ·
            refine ⟨2646866918339973395513479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3529155891119964527351305 2646866918339973395513479)
            ·
              refine ⟨3970300377509960093270219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646866918339973395513479 3970300377509960093270219)
              ·
                refine ⟨5955450566264940139905329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3970300377509960093270219 5955450566264940139905329)
                ·
                  refine ⟨4466587924698705104928997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5955450566264940139905329 4466587924698705104928997)
                  ·
                    refine ⟨837485235881007207174187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4466587924698705104928997 837485235881007207174187)
                    ·
                      rfl

theorem cell22_2446495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 4].length) (baseStart_2446495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446495 prefixEnd_2446495 := by exact prefixLift 2446495
  have htrace : WordTrace (prefixWord ++ tailWord_2446495) baseStart_2446495 baseEnd_2446495 := by
    simpa [prefixWord, tailWord_2446495, baseEnd_2446495] using wordTrace_append hprefix tailTrace_2446495
  have hstable : (prefixWord ++ tailWord_2446495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446495).length < 2 ^ (prefixWord ++ tailWord_2446495).sum := by decide
  have hdescent : baseEnd_2446495 < baseStart_2446495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446521 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 7]
def baseStart_2446521 : Nat := 118140960795 + 2446521 * 2 ^ 59
def prefixEnd_2446521 : Nat := 4983230072969 + 3 ^ 40 * 2446521 * 2
def baseEnd_2446521 : Nat := 279164712070783935341369

theorem tailTrace_2446521 : CollatzResearch.WordTrace tailWord_2446521 prefixEnd_2446521 279164712070783935341369 := by
  unfold tailWord_2446521
  simp only [CollatzResearch.WordTrace]
  refine ⟨89231951569679724366563417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59487967713119816244375611 89231951569679724366563417)
  ·
    refine ⟨66923963677259793274922563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89231951569679724366563417 66923963677259793274922563)
    ·
      refine ⟨100385945515889689912383845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66923963677259793274922563 100385945515889689912383845)
      ·
        refine ⟨18822364784229316858571971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100385945515889689912383845 18822364784229316858571971)
        ·
          refine ⟨28233547176343975287857957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18822364784229316858571971 28233547176343975287857957)
          ·
            refine ⟨5293790095564495366473367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28233547176343975287857957 5293790095564495366473367)
            ·
              refine ⟨7940685143346743049710051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5293790095564495366473367 7940685143346743049710051)
              ·
                refine ⟨11911027715020114574565077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7940685143346743049710051 11911027715020114574565077)
                ·
                  refine ⟨279164712070783935341369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11911027715020114574565077 279164712070783935341369)
                  ·
                    rfl

theorem cell22_2446521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_2446521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446521 prefixEnd_2446521 := by exact prefixLift 2446521
  have htrace : WordTrace (prefixWord ++ tailWord_2446521) baseStart_2446521 baseEnd_2446521 := by
    simpa [prefixWord, tailWord_2446521, baseEnd_2446521] using wordTrace_append hprefix tailTrace_2446521
  have hstable : (prefixWord ++ tailWord_2446521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446521).length < 2 ^ (prefixWord ++ tailWord_2446521).sum := by decide
  have hdescent : baseEnd_2446521 < baseStart_2446521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446525 : List Nat := [1, 4, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_2446525 : Nat := 118140960795 + 2446525 * 2 ^ 59
def prefixEnd_2446525 : Nat := 4983230072969 + 3 ^ 40 * 2446525 * 2
def baseEnd_2446525 : Nat := 837495505494097128924095

theorem tailTrace_2446525 : CollatzResearch.WordTrace tailWord_2446525 prefixEnd_2446525 837495505494097128924095 := by
  unfold tailWord_2446525
  simp only [CollatzResearch.WordTrace]
  refine ⟨89232097461665233049709029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59488064974443488699806019 89232097461665233049709029)
  ·
    refine ⟨16731018274062231196820443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89232097461665233049709029 16731018274062231196820443)
    ·
      refine ⟨25096527411093346795230665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16731018274062231196820443 25096527411093346795230665)
      ·
        refine ⟨18822395558320010096422999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25096527411093346795230665 18822395558320010096422999)
        ·
          refine ⟨28233593337480015144634499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18822395558320010096422999 28233593337480015144634499)
          ·
            refine ⟨42350390006220022716951749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28233593337480015144634499 42350390006220022716951749)
            ·
              refine ⟨7940698126166254259428453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42350390006220022716951749 7940698126166254259428453)
              ·
                refine ⟨1488880898656172673642835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7940698126166254259428453 1488880898656172673642835)
                ·
                  refine ⟨2233321347984259010464253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488880898656172673642835 2233321347984259010464253)
                  ·
                    refine ⟨837495505494097128924095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2233321347984259010464253 837495505494097128924095)
                    ·
                      rfl

theorem cell22_2446525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_2446525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446525 prefixEnd_2446525 := by exact prefixLift 2446525
  have htrace : WordTrace (prefixWord ++ tailWord_2446525) baseStart_2446525 baseEnd_2446525 := by
    simpa [prefixWord, tailWord_2446525, baseEnd_2446525] using wordTrace_append hprefix tailTrace_2446525
  have hstable : (prefixWord ++ tailWord_2446525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446525).length < 2 ^ (prefixWord ++ tailWord_2446525).sum := by decide
  have hdescent : baseEnd_2446525 < baseStart_2446525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446536 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 2, 5]
def baseStart_2446536 : Nat := 118140960795 + 2446536 * 2 ^ 59
def prefixEnd_2446536 : Nat := 4983230072969 + 3 ^ 40 * 2446536 * 2
def baseEnd_2446536 : Nat := 837499271018896766899061

theorem tailTrace_2446536 : CollatzResearch.WordTrace tailWord_2446536 prefixEnd_2446536 837499271018896766899061 := by
  unfold tailWord_2446536
  simp only [CollatzResearch.WordTrace]
  refine ⟨44616249332312690964179731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59488332443083587952239641 44616249332312690964179731)
  ·
    refine ⟨66924373998469036446269597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44616249332312690964179731 66924373998469036446269597)
    ·
      refine ⟨25096640249425888667351099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66924373998469036446269597 25096640249425888667351099)
      ·
        refine ⟨37644960374138833001026649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25096640249425888667351099 37644960374138833001026649)
        ·
          refine ⟨28233720280604124750769987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37644960374138833001026649 28233720280604124750769987)
          ·
            refine ⟨42350580420906187126154981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28233720280604124750769987 42350580420906187126154981)
            ·
              refine ⟨7940733828919910086154059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42350580420906187126154981 7940733828919910086154059)
              ·
                refine ⟨11911100743379865129231089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7940733828919910086154059 11911100743379865129231089)
                ·
                  refine ⟨8933325557534898846923317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11911100743379865129231089 8933325557534898846923317)
                  ·
                    refine ⟨837499271018896766899061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8933325557534898846923317 837499271018896766899061)
                    ·
                      rfl

theorem cell22_2446536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_2446536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446536 prefixEnd_2446536 := by exact prefixLift 2446536
  have htrace : WordTrace (prefixWord ++ tailWord_2446536) baseStart_2446536 baseEnd_2446536 := by
    simpa [prefixWord, tailWord_2446536, baseEnd_2446536] using wordTrace_append hprefix tailTrace_2446536
  have hstable : (prefixWord ++ tailWord_2446536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446536).length < 2 ^ (prefixWord ++ tailWord_2446536).sum := by decide
  have hdescent : baseEnd_2446536 < baseStart_2446536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446551 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 3, 4]
def baseStart_2446551 : Nat := 118140960795 + 2446551 * 2 ^ 59
def prefixEnd_2446551 : Nat := 4983230072969 + 3 ^ 40 * 2446551 * 2
def baseEnd_2446551 : Nat := 837504405825441727774015

theorem tailTrace_2446551 : CollatzResearch.WordTrace tailWord_2446551 prefixEnd_2446551 837504405825441727774015 := by
  unfold tailWord_2446551
  simp only [CollatzResearch.WordTrace]
  refine ⟨89233045759571039490155507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59488697173047359660103671 89233045759571039490155507)
  ·
    refine ⟨133849568639356559235233261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89233045759571039490155507 133849568639356559235233261)
    ·
      refine ⟨50193588239758709713212473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133849568639356559235233261 50193588239758709713212473)
      ·
        refine ⟨37645191179819032284909355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50193588239758709713212473 37645191179819032284909355)
        ·
          refine ⟨56467786769728548427364033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37645191179819032284909355 56467786769728548427364033)
          ·
            refine ⟨42350840077296411320523025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56467786769728548427364033 42350840077296411320523025)
            ·
              refine ⟨31763130057972308490392269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42350840077296411320523025 31763130057972308490392269)
              ·
                refine ⟨11911173771739615683897101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31763130057972308490392269 11911173771739615683897101)
                ·
                  refine ⟨4466690164402355881461413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11911173771739615683897101 4466690164402355881461413)
                  ·
                    refine ⟨837504405825441727774015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4466690164402355881461413 837504405825441727774015)
                    ·
                      rfl

theorem cell22_2446551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_2446551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446551 prefixEnd_2446551 := by exact prefixLift 2446551
  have htrace : WordTrace (prefixWord ++ tailWord_2446551) baseStart_2446551 baseEnd_2446551 := by
    simpa [prefixWord, tailWord_2446551, baseEnd_2446551] using wordTrace_append hprefix tailTrace_2446551
  have hstable : (prefixWord ++ tailWord_2446551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446551).length < 2 ^ (prefixWord ++ tailWord_2446551).sum := by decide
  have hdescent : baseEnd_2446551 < baseStart_2446551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446568 : List Nat := [2, 1, 4, 1, 2, 1, 1, 5, 1, 4]
def baseStart_2446568 : Nat := 118140960795 + 2446568 * 2 ^ 59
def prefixEnd_2446568 : Nat := 4983230072969 + 3 ^ 40 * 2446568 * 2
def baseEnd_2446568 : Nat := 837510225272859350098963

theorem tailTrace_2446568 : CollatzResearch.WordTrace tailWord_2446568 prefixEnd_2446568 837510225272859350098963 := by
  unfold tailWord_2446568
  simp only [CollatzResearch.WordTrace]
  refine ⟨44616832900254725696762179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59489110533672967595682905 44616832900254725696762179)
  ·
    refine ⟨66925249350382088545143269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44616832900254725696762179 66925249350382088545143269)
    ·
      refine ⟨12548484253196641602214363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66925249350382088545143269 12548484253196641602214363)
      ·
        refine ⟨18822726379794962403321545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12548484253196641602214363 18822726379794962403321545)
        ·
          refine ⟨14117044784846221802491159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18822726379794962403321545 14117044784846221802491159)
          ·
            refine ⟨21175567177269332703736739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14117044784846221802491159 21175567177269332703736739)
            ·
              refine ⟨31763350765903999055605109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21175567177269332703736739 31763350765903999055605109)
              ·
                refine ⟨2977814134303499911462979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31763350765903999055605109 2977814134303499911462979)
                ·
                  refine ⟨4466721201455249867194469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977814134303499911462979 4466721201455249867194469)
                  ·
                    refine ⟨837510225272859350098963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4466721201455249867194469 837510225272859350098963)
                    ·
                      rfl

theorem cell22_2446568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_2446568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446568 prefixEnd_2446568 := by exact prefixLift 2446568
  have htrace : WordTrace (prefixWord ++ tailWord_2446568) baseStart_2446568 baseEnd_2446568 := by
    simpa [prefixWord, tailWord_2446568, baseEnd_2446568] using wordTrace_append hprefix tailTrace_2446568
  have hstable : (prefixWord ++ tailWord_2446568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446568).length < 2 ^ (prefixWord ++ tailWord_2446568).sum := by decide
  have hdescent : baseEnd_2446568 < baseStart_2446568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446632 : List Nat := [2, 1, 5, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2446632 : Nat := 118140960795 + 2446632 * 2 ^ 59
def prefixEnd_2446632 : Nat := 4983230072969 + 3 ^ 40 * 2446632 * 2
def baseEnd_2446632 : Nat := 837532133780784516498767

theorem tailTrace_2446632 : CollatzResearch.WordTrace tailWord_2446632 prefixEnd_2446632 837532133780784516498767 := by
  unfold tailWord_2446632
  simp only [CollatzResearch.WordTrace]
  refine ⟨44618000036138795161927075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59490666714851726882569433 44618000036138795161927075)
  ·
    refine ⟨66927000054208192742890613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44618000036138795161927075 66927000054208192742890613)
    ·
      refine ⟨6274406255082018069645995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66927000054208192742890613 6274406255082018069645995)
      ·
        refine ⟨9411609382623027104468993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6274406255082018069645995 9411609382623027104468993)
        ·
          refine ⟨7058707036967270328351745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9411609382623027104468993 7058707036967270328351745)
          ·
            refine ⟨5294030277725452746263809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7058707036967270328351745 5294030277725452746263809)
            ·
              refine ⟨3970522708294089559697857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5294030277725452746263809 3970522708294089559697857)
              ·
                refine ⟨2977892031220567169773393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3970522708294089559697857 2977892031220567169773393)
                ·
                  refine ⟨2233419023415425377330045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2977892031220567169773393 2233419023415425377330045)
                  ·
                    refine ⟨837532133780784516498767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2233419023415425377330045 837532133780784516498767)
                    ·
                      rfl

theorem cell22_2446632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2446632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446632 prefixEnd_2446632 := by exact prefixLift 2446632
  have htrace : WordTrace (prefixWord ++ tailWord_2446632) baseStart_2446632 baseEnd_2446632 := by
    simpa [prefixWord, tailWord_2446632, baseEnd_2446632] using wordTrace_append hprefix tailTrace_2446632
  have hstable : (prefixWord ++ tailWord_2446632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446632).length < 2 ^ (prefixWord ++ tailWord_2446632).sum := by decide
  have hdescent : baseEnd_2446632 < baseStart_2446632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446634 : List Nat := [3, 1, 4, 2, 1, 3, 2, 2, 4]
def baseStart_2446634 : Nat := 118140960795 + 2446634 * 2 ^ 59
def prefixEnd_2446634 : Nat := 4983230072969 + 3 ^ 40 * 2446634 * 2
def baseEnd_2446634 : Nat := 279177606140552392649587

theorem tailTrace_2446634 : CollatzResearch.WordTrace tailWord_2446634 prefixEnd_2446634 279177606140552392649587 := by
  unfold tailWord_2446634
  simp only [CollatzResearch.WordTrace]
  refine ⟨22309018254567586166356739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59490715345513563110284637 22309018254567586166356739)
  ·
    refine ⟨33463527381851379249535109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22309018254567586166356739 33463527381851379249535109)
    ·
      refine ⟨6274411384097133609287833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33463527381851379249535109 6274411384097133609287833)
      ·
        refine ⟨4705808538072850206965875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6274411384097133609287833 4705808538072850206965875)
        ·
          refine ⟨7058712807109275310448813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4705808538072850206965875 7058712807109275310448813)
          ·
            refine ⟨2647017302665978241418305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7058712807109275310448813 2647017302665978241418305)
            ·
              refine ⟨1985262976999483681063729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2647017302665978241418305 1985262976999483681063729)
              ·
                refine ⟨1488947232749612760797797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1985262976999483681063729 1488947232749612760797797)
                ·
                  refine ⟨279177606140552392649587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1488947232749612760797797 279177606140552392649587)
                  ·
                    rfl

theorem cell22_2446634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_2446634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446634 prefixEnd_2446634 := by exact prefixLift 2446634
  have htrace : WordTrace (prefixWord ++ tailWord_2446634) baseStart_2446634 baseEnd_2446634 := by
    simpa [prefixWord, tailWord_2446634, baseEnd_2446634] using wordTrace_append hprefix tailTrace_2446634
  have hstable : (prefixWord ++ tailWord_2446634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446634).length < 2 ^ (prefixWord ++ tailWord_2446634).sum := by decide
  have hdescent : baseEnd_2446634 < baseStart_2446634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446677 : List Nat := [1, 3, 2, 2, 3, 1, 1, 5, 1, 3]
def baseStart_2446677 : Nat := 118140960795 + 2446677 * 2 ^ 59
def prefixEnd_2446677 : Nat := 4983230072969 + 3 ^ 40 * 2446677 * 2
def baseEnd_2446677 : Nat := 837547538200419399123629

theorem tailTrace_2446677 : CollatzResearch.WordTrace tailWord_2446677 prefixEnd_2446677 837547538200419399123629 := by
  unfold tailWord_2446677
  simp only [CollatzResearch.WordTrace]
  refine ⟨89237641357114563009242285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59491760904743042006161523 89237641357114563009242285)
  ·
    refine ⟨33464115508917961128465857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89237641357114563009242285 33464115508917961128465857)
    ·
      refine ⟨25098086631688470846349393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33464115508917961128465857 25098086631688470846349393)
      ·
        refine ⟨18823564973766353134762045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25098086631688470846349393 18823564973766353134762045)
        ·
          refine ⟨7058836865162382425535767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18823564973766353134762045 7058836865162382425535767)
          ·
            refine ⟨10588255297743573638303651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058836865162382425535767 10588255297743573638303651)
            ·
              refine ⟨15882382946615360457455477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10588255297743573638303651 15882382946615360457455477)
              ·
                refine ⟨1488973401245190042886451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15882382946615360457455477 1488973401245190042886451)
                ·
                  refine ⟨2233460101867785064329677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488973401245190042886451 2233460101867785064329677)
                  ·
                    refine ⟨837547538200419399123629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2233460101867785064329677 837547538200419399123629)
                    ·
                      rfl

theorem cell22_2446677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_2446677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446677 prefixEnd_2446677 := by exact prefixLift 2446677
  have htrace : WordTrace (prefixWord ++ tailWord_2446677) baseStart_2446677 baseEnd_2446677 := by
    simpa [prefixWord, tailWord_2446677, baseEnd_2446677] using wordTrace_append hprefix tailTrace_2446677
  have hstable : (prefixWord ++ tailWord_2446677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446677).length < 2 ^ (prefixWord ++ tailWord_2446677).sum := by decide
  have hdescent : baseEnd_2446677 < baseStart_2446677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446688 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 2, 5]
def baseStart_2446688 : Nat := 118140960795 + 2446688 * 2 ^ 59
def prefixEnd_2446688 : Nat := 4983230072969 + 3 ^ 40 * 2446688 * 2
def baseEnd_2446688 : Nat := 837551303725219037098595

theorem tailTrace_2446688 : CollatzResearch.WordTrace tailWord_2446688 prefixEnd_2446688 837551303725219037098595 := by
  unfold tailWord_2446688
  simp only [CollatzResearch.WordTrace]
  refine ⟨44619021280037355943946359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59492028373383141258595145 44619021280037355943946359)
  ·
    refine ⟨66928531920056033915919539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44619021280037355943946359 66928531920056033915919539)
    ·
      refine ⟨100392797880084050873879309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66928531920056033915919539 100392797880084050873879309)
      ·
        refine ⟨37647299205031519077704741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100392797880084050873879309 37647299205031519077704741)
        ·
          refine ⟨7058868600943409827069639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37647299205031519077704741 7058868600943409827069639)
          ·
            refine ⟨10588302901415114740604459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058868600943409827069639 10588302901415114740604459)
            ·
              refine ⟨15882454352122672110906689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10588302901415114740604459 15882454352122672110906689)
              ·
                refine ⟨11911840764092004083180017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15882454352122672110906689 11911840764092004083180017)
                ·
                  refine ⟨8933880573069003062385013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11911840764092004083180017 8933880573069003062385013)
                  ·
                    refine ⟨837551303725219037098595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8933880573069003062385013 837551303725219037098595)
                    ·
                      rfl

theorem cell22_2446688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_2446688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446688 prefixEnd_2446688 := by exact prefixLift 2446688
  have htrace : WordTrace (prefixWord ++ tailWord_2446688) baseStart_2446688 baseEnd_2446688 := by
    simpa [prefixWord, tailWord_2446688, baseEnd_2446688] using wordTrace_append hprefix tailTrace_2446688
  have hstable : (prefixWord ++ tailWord_2446688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446688).length < 2 ^ (prefixWord ++ tailWord_2446688).sum := by decide
  have hdescent : baseEnd_2446688 < baseStart_2446688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446752 : List Nat := [2, 1, 1, 4, 1, 2, 5, 2, 4]
def baseStart_2446752 : Nat := 118140960795 + 2446752 * 2 ^ 59
def prefixEnd_2446752 : Nat := 4983230072969 + 3 ^ 40 * 2446752 * 2
def baseEnd_2446752 : Nat := 279191070744381401166133

theorem tailTrace_2446752 : CollatzResearch.WordTrace tailWord_2446752 prefixEnd_2446752 279191070744381401166133 := by
  unfold tailWord_2446752
  simp only [CollatzResearch.WordTrace]
  refine ⟨44620188415921425409111255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59493584554561900545481673 44620188415921425409111255)
  ·
    refine ⟨66930282623882138113666883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44620188415921425409111255 66930282623882138113666883)
    ·
      refine ⟨100395423935823207170500325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66930282623882138113666883 100395423935823207170500325)
      ·
        refine ⟨18824141987966851344468811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100395423935823207170500325 18824141987966851344468811)
        ·
          refine ⟨28236212981950277016703217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18824141987966851344468811 28236212981950277016703217)
          ·
            refine ⟨21177159736462707762527413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28236212981950277016703217 21177159736462707762527413)
            ·
              refine ⟨1985358725293378852736945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21177159736462707762527413 1985358725293378852736945)
              ·
                refine ⟨1489019043970034139552709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1985358725293378852736945 1489019043970034139552709)
                ·
                  refine ⟨279191070744381401166133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1489019043970034139552709 279191070744381401166133)
                  ·
                    rfl

theorem cell22_2446752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 4].length) (baseStart_2446752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446752 prefixEnd_2446752 := by exact prefixLift 2446752
  have htrace : WordTrace (prefixWord ++ tailWord_2446752) baseStart_2446752 baseEnd_2446752 := by
    simpa [prefixWord, tailWord_2446752, baseEnd_2446752] using wordTrace_append hprefix tailTrace_2446752
  have hstable : (prefixWord ++ tailWord_2446752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446752).length < 2 ^ (prefixWord ++ tailWord_2446752).sum := by decide
  have hdescent : baseEnd_2446752 < baseStart_2446752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446808 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 7]
def baseStart_2446808 : Nat := 118140960795 + 2446808 * 2 ^ 59
def prefixEnd_2446808 : Nat := 4983230072969 + 3 ^ 40 * 2446808 * 2
def baseEnd_2446808 : Nat := 279197460725859574699409

theorem tailTrace_2446808 : CollatzResearch.WordTrace tailWord_2446808 prefixEnd_2446808 279197460725859574699409 := by
  unfold tailWord_2446808
  simp only [CollatzResearch.WordTrace]
  refine ⟨44621209659819986191130539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59494946213093314921507385 44621209659819986191130539)
  ·
    refine ⟨66931814489729979286695809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44621209659819986191130539 66931814489729979286695809)
    ·
      refine ⟨50198860867297484465021857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66931814489729979286695809 50198860867297484465021857)
      ·
        refine ⟨37649145650473113348766393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50198860867297484465021857 37649145650473113348766393)
        ·
          refine ⟨28236859237854835011574795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37649145650473113348766393 28236859237854835011574795)
          ·
            refine ⟨42355288856782252517362193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28236859237854835011574795 42355288856782252517362193)
            ·
              refine ⟨31766466642586689388021645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42355288856782252517362193 31766466642586689388021645)
              ·
                refine ⟨11912424990970008520508117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31766466642586689388021645 11912424990970008520508117)
                ·
                  refine ⟨279197460725859574699409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11912424990970008520508117 279197460725859574699409)
                  ·
                    rfl

theorem cell22_2446808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_2446808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446808 prefixEnd_2446808 := by exact prefixLift 2446808
  have htrace : WordTrace (prefixWord ++ tailWord_2446808) baseStart_2446808 baseEnd_2446808 := by
    simpa [prefixWord, tailWord_2446808, baseEnd_2446808] using wordTrace_append hprefix tailTrace_2446808
  have hstable : (prefixWord ++ tailWord_2446808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446808).length < 2 ^ (prefixWord ++ tailWord_2446808).sum := by decide
  have hdescent : baseEnd_2446808 < baseStart_2446808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446829 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_2446829 : Nat := 118140960795 + 2446829 * 2 ^ 59
def prefixEnd_2446829 : Nat := 4983230072969 + 3 ^ 40 * 2446829 * 2
def baseEnd_2446829 : Nat := 837599570906741669323163

theorem tailTrace_2446829 : CollatzResearch.WordTrace tailWord_2446829 prefixEnd_2446829 837599570906741669323163 := by
  unfold tailWord_2446829
  simp only [CollatzResearch.WordTrace]
  refine ⟨89243185252563892968775541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59495456835042595312517027 89243185252563892968775541)
  ·
    refine ⟨8366548617427864965822707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89243185252563892968775541 8366548617427864965822707)
    ·
      refine ⟨12549822926141797448734061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8366548617427864965822707 12549822926141797448734061)
      ·
        refine ⟨4706183597303174043275273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12549822926141797448734061 4706183597303174043275273)
        ·
          refine ⟨3529637697977380532456455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4706183597303174043275273 3529637697977380532456455)
          ·
            refine ⟨5294456546966070798684683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3529637697977380532456455 5294456546966070798684683)
            ·
              refine ⟨7941684820449106198027025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5294456546966070798684683 7941684820449106198027025)
              ·
                refine ⟨5956263615336829648520269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7941684820449106198027025 5956263615336829648520269)
                ·
                  refine ⟨2233598855751311118195101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5956263615336829648520269 2233598855751311118195101)
                  ·
                    refine ⟨837599570906741669323163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2233598855751311118195101 837599570906741669323163)
                    ·
                      rfl

theorem cell22_2446829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_2446829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446829 prefixEnd_2446829 := by exact prefixLift 2446829
  have htrace : WordTrace (prefixWord ++ tailWord_2446829) baseStart_2446829 baseEnd_2446829 := by
    simpa [prefixWord, tailWord_2446829, baseEnd_2446829] using wordTrace_append hprefix tailTrace_2446829
  have hstable : (prefixWord ++ tailWord_2446829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446829).length < 2 ^ (prefixWord ++ tailWord_2446829).sum := by decide
  have hdescent : baseEnd_2446829 < baseStart_2446829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446853 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 10]
def baseStart_2446853 : Nat := 118140960795 + 2446853 * 2 ^ 59
def prefixEnd_2446853 : Nat := 4983230072969 + 3 ^ 40 * 2446853 * 2
def baseEnd_2446853 : Nat := 279202595532404535574363

theorem tailTrace_2446853 : CollatzResearch.WordTrace tailWord_2446853 prefixEnd_2446853 279202595532404535574363 := by
  unfold tailWord_2446853
  simp only [CollatzResearch.WordTrace]
  refine ⟨89244060604476945067649213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59496040402984630045099475 89244060604476945067649213)
  ·
    refine ⟨33466522726678854400368455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89244060604476945067649213 33466522726678854400368455)
    ·
      refine ⟨50199784090018281600552683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33466522726678854400368455 50199784090018281600552683)
      ·
        refine ⟨75299676135027422400829025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50199784090018281600552683 75299676135027422400829025)
        ·
          refine ⟨56474757101270566800621769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75299676135027422400829025 56474757101270566800621769)
          ·
            refine ⟨42356067825952925100466327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56474757101270566800621769 42356067825952925100466327)
            ·
              refine ⟨63534101738929387650699491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42356067825952925100466327 63534101738929387650699491)
              ·
                refine ⟨95301152608394081476049237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63534101738929387650699491 95301152608394081476049237)
                ·
                  refine ⟨279202595532404535574363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 95301152608394081476049237 279202595532404535574363)
                  ·
                    rfl

theorem cell22_2446853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_2446853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446853 prefixEnd_2446853 := by exact prefixLift 2446853
  have htrace : WordTrace (prefixWord ++ tailWord_2446853) baseStart_2446853 baseEnd_2446853 := by
    simpa [prefixWord, tailWord_2446853, baseEnd_2446853] using wordTrace_append hprefix tailTrace_2446853
  have hstable : (prefixWord ++ tailWord_2446853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446853).length < 2 ^ (prefixWord ++ tailWord_2446853).sum := by decide
  have hdescent : baseEnd_2446853 < baseStart_2446853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446859 : List Nat := [1, 1, 1, 1, 9, 1, 1, 2, 5]
def baseStart_2446859 : Nat := 118140960795 + 2446859 * 2 ^ 59
def prefixEnd_2446859 : Nat := 4983230072969 + 3 ^ 40 * 2446859 * 2
def baseEnd_2446859 : Nat := 279203280173277197024357

theorem tailTrace_2446859 : CollatzResearch.WordTrace tailWord_2446859 prefixEnd_2446859 279203280173277197024357 := by
  unfold tailWord_2446859
  simp only [CollatzResearch.WordTrace]
  refine ⟨89244279442455208092367631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59496186294970138728245087 89244279442455208092367631)
  ·
    refine ⟨133866419163682812138551447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89244279442455208092367631 133866419163682812138551447)
    ·
      refine ⟨200799628745524218207827171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133866419163682812138551447 200799628745524218207827171)
      ·
        refine ⟨301199443118286327311740757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200799628745524218207827171 301199443118286327311740757)
        ·
          refine ⟨1764840487021208949092231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 301199443118286327311740757 1764840487021208949092231)
          ·
            refine ⟨2647260730531813423638347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764840487021208949092231 2647260730531813423638347)
            ·
              refine ⟨3970891095797720135457521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647260730531813423638347 3970891095797720135457521)
              ·
                refine ⟨2978168321848290101593141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3970891095797720135457521 2978168321848290101593141)
                ·
                  refine ⟨279203280173277197024357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2978168321848290101593141 279203280173277197024357)
                  ·
                    rfl

theorem cell22_2446859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 5].length) (baseStart_2446859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446859 prefixEnd_2446859 := by exact prefixLift 2446859
  have htrace : WordTrace (prefixWord ++ tailWord_2446859) baseStart_2446859 baseEnd_2446859 := by
    simpa [prefixWord, tailWord_2446859, baseEnd_2446859] using wordTrace_append hprefix tailTrace_2446859
  have hstable : (prefixWord ++ tailWord_2446859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446859).length < 2 ^ (prefixWord ++ tailWord_2446859).sum := by decide
  have hdescent : baseEnd_2446859 < baseStart_2446859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446904 : List Nat := [2, 1, 2, 1, 4, 4, 1, 3, 4]
def baseStart_2446904 : Nat := 118140960795 + 2446904 * 2 ^ 59
def prefixEnd_2446904 : Nat := 4983230072969 + 3 ^ 40 * 2446904 * 2
def baseEnd_2446904 : Nat := 279208414979822157899311

theorem tailTrace_2446904 : CollatzResearch.WordTrace tailWord_2446904 prefixEnd_2446904 279208414979822157899311 := by
  unfold tailWord_2446904
  simp only [CollatzResearch.WordTrace]
  refine ⟨44622960363646090388877883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59497280484861453851837177 44622960363646090388877883)
  ·
    refine ⟨66934440545469135583316825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44622960363646090388877883 66934440545469135583316825)
    ·
      refine ⟨50200830409101851687487619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66934440545469135583316825 50200830409101851687487619)
      ·
        refine ⟨75301245613652777531231429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50200830409101851687487619 75301245613652777531231429)
        ·
          refine ⟨14118983552559895787105893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75301245613652777531231429 14118983552559895787105893)
          ·
            refine ⟨2647309416104980460082355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14118983552559895787105893 2647309416104980460082355)
            ·
              refine ⟨3970964124157470690123533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647309416104980460082355 3970964124157470690123533)
              ·
                refine ⟨1489111546559051508796325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3970964124157470690123533 1489111546559051508796325)
                ·
                  refine ⟨279208414979822157899311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1489111546559051508796325 279208414979822157899311)
                  ·
                    rfl

theorem cell22_2446904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 4].length) (baseStart_2446904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446904 prefixEnd_2446904 := by exact prefixLift 2446904
  have htrace : WordTrace (prefixWord ++ tailWord_2446904) baseStart_2446904 baseEnd_2446904 := by
    simpa [prefixWord, tailWord_2446904, baseEnd_2446904] using wordTrace_append hprefix tailTrace_2446904
  have hstable : (prefixWord ++ tailWord_2446904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446904).length < 2 ^ (prefixWord ++ tailWord_2446904).sum := by decide
  have hdescent : baseEnd_2446904 < baseStart_2446904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446977 : List Nat := [1, 2, 4, 2, 1, 2, 1, 4, 5]
def baseStart_2446977 : Nat := 118140960795 + 2446977 * 2 ^ 59
def prefixEnd_2446977 : Nat := 4983230072969 + 3 ^ 40 * 2446977 * 2
def baseEnd_2446977 : Nat := 279216744777106205540903

theorem tailTrace_2446977 : CollatzResearch.WordTrace tailWord_2446977 prefixEnd_2446977 279216744777106205540903 := by
  unfold tailWord_2446977
  simp only [CollatzResearch.WordTrace]
  refine ⟨89248583256027714245163185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59499055504018476163442123 89248583256027714245163185)
  ·
    refine ⟨66936437442020785683872389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89248583256027714245163185 66936437442020785683872389)
    ·
      refine ⟨12550582020378897315726073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66936437442020785683872389 12550582020378897315726073)
      ·
        refine ⟨9412936515284172986794555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12550582020378897315726073 9412936515284172986794555)
        ·
          refine ⟨14119404772926259480191833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9412936515284172986794555 14119404772926259480191833)
          ·
            refine ⟨10589553579694694610143875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14119404772926259480191833 10589553579694694610143875)
            ·
              refine ⟨15884330369542041915215813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10589553579694694610143875 15884330369542041915215813)
              ·
                refine ⟨2978311944289132859102965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15884330369542041915215813 2978311944289132859102965)
                ·
                  refine ⟨279216744777106205540903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2978311944289132859102965 279216744777106205540903)
                  ·
                    rfl

theorem cell22_2446977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_2446977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2446977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2446977 prefixEnd_2446977 := by exact prefixLift 2446977
  have htrace : WordTrace (prefixWord ++ tailWord_2446977) baseStart_2446977 baseEnd_2446977 := by
    simpa [prefixWord, tailWord_2446977, baseEnd_2446977] using wordTrace_append hprefix tailTrace_2446977
  have hstable : (prefixWord ++ tailWord_2446977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446977).length < 2 ^ (prefixWord ++ tailWord_2446977).sum := by decide
  have hdescent : baseEnd_2446977 < baseStart_2446977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447024 : List Nat := [2, 1, 1, 1, 2, 1, 8, 1, 1, 4]
def baseStart_2447024 : Nat := 118140960795 + 2447024 * 2 ^ 59
def prefixEnd_2447024 : Nat := 4983230072969 + 3 ^ 40 * 2447024 * 2
def baseEnd_2447024 : Nat := 837666323391826160697565

theorem tailTrace_2447024 : CollatzResearch.WordTrace tailWord_2447024 prefixEnd_2447024 837666323391826160697565 := by
  unfold tailWord_2447024
  simp only [CollatzResearch.WordTrace]
  refine ⟨44625148743428720636062063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59500198324571627514749417 44625148743428720636062063)
  ·
    refine ⟨66937723115143080954093095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44625148743428720636062063 66937723115143080954093095)
    ·
      refine ⟨100406584672714621431139643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66937723115143080954093095 100406584672714621431139643)
      ·
        refine ⟨150609877009071932146709465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100406584672714621431139643 150609877009071932146709465)
        ·
          refine ⟨112957407756803949110032099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150609877009071932146709465 112957407756803949110032099)
          ·
            refine ⟨169436111635205923665048149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112957407756803949110032099 169436111635205923665048149)
            ·
              refine ⟨1985579433225069417949783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 169436111635205923665048149 1985579433225069417949783)
              ·
                refine ⟨2978369149837604126924675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985579433225069417949783 2978369149837604126924675)
                ·
                  refine ⟨4467553724756406190387013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978369149837604126924675 4467553724756406190387013)
                  ·
                    refine ⟨837666323391826160697565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4467553724756406190387013 837666323391826160697565)
                    ·
                      rfl

theorem cell22_2447024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 1, 4].length) (baseStart_2447024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447024 prefixEnd_2447024 := by exact prefixLift 2447024
  have htrace : WordTrace (prefixWord ++ tailWord_2447024) baseStart_2447024 baseEnd_2447024 := by
    simpa [prefixWord, tailWord_2447024, baseEnd_2447024] using wordTrace_append hprefix tailTrace_2447024
  have hstable : (prefixWord ++ tailWord_2447024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447024).length < 2 ^ (prefixWord ++ tailWord_2447024).sum := by decide
  have hdescent : baseEnd_2447024 < baseStart_2447024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447073 : List Nat := [1, 2, 3, 1, 6, 1, 1, 3, 4]
def baseStart_2447073 : Nat := 118140960795 + 2447073 * 2 ^ 59
def prefixEnd_2447073 : Nat := 4983230072969 + 3 ^ 40 * 2447073 * 2
def baseEnd_2447073 : Nat := 279227699031068788740805

theorem tailTrace_2447073 : CollatzResearch.WordTrace tailWord_2447073 prefixEnd_2447073 279227699031068788740805 := by
  unfold tailWord_2447073
  simp only [CollatzResearch.WordTrace]
  refine ⟨89252084663679922640657873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59501389775786615093771915 89252084663679922640657873)
  ·
    refine ⟨66939063497759941980493405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89252084663679922640657873 66939063497759941980493405)
    ·
      refine ⟨25102148811659978242685027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66939063497759941980493405 25102148811659978242685027)
      ·
        refine ⟨37653223217489967364027541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25102148811659978242685027 37653223217489967364027541)
        ·
          refine ⟨1764994838319842220188791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37653223217489967364027541 1764994838319842220188791)
          ·
            refine ⟨2647492257479763330283187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764994838319842220188791 2647492257479763330283187)
            ·
              refine ⟨3971238386219644995424781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647492257479763330283187 3971238386219644995424781)
              ·
                refine ⟨1489214394832366873284293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3971238386219644995424781 1489214394832366873284293)
                ·
                  refine ⟨279227699031068788740805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1489214394832366873284293 279227699031068788740805)
                  ·
                    rfl

theorem cell22_2447073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 4].length) (baseStart_2447073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447073 prefixEnd_2447073 := by exact prefixLift 2447073
  have htrace : WordTrace (prefixWord ++ tailWord_2447073) baseStart_2447073 baseEnd_2447073 := by
    simpa [prefixWord, tailWord_2447073, baseEnd_2447073] using wordTrace_append hprefix tailTrace_2447073
  have hstable : (prefixWord ++ tailWord_2447073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447073).length < 2 ^ (prefixWord ++ tailWord_2447073).sum := by decide
  have hdescent : baseEnd_2447073 < baseStart_2447073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447150 : List Nat := [4, 1, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2447150 : Nat := 118140960795 + 2447150 * 2 ^ 59
def prefixEnd_2447150 : Nat := 4983230072969 + 3 ^ 40 * 2447150 * 2
def baseEnd_2447150 : Nat := 837709455766803832047179

theorem tailTrace_2447150 : CollatzResearch.WordTrace tailWord_2447150 prefixEnd_2447150 837709455766803832047179 := by
  unfold tailWord_2447150
  simp only [CollatzResearch.WordTrace]
  refine ⟨11156861635550120598901363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59503262056267309860807269 11156861635550120598901363)
  ·
    refine ⟨16735292453325180898352045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11156861635550120598901363 16735292453325180898352045)
    ·
      refine ⟨6275734669996942836882017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16735292453325180898352045 6275734669996942836882017)
      ·
        refine ⟨4706801002497707127661513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6275734669996942836882017 4706801002497707127661513)
        ·
          refine ⟨3530100751873280345746135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4706801002497707127661513 3530100751873280345746135)
          ·
            refine ⟨5295151127809920518619203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3530100751873280345746135 5295151127809920518619203)
            ·
              refine ⟨7942726691714880777928805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5295151127809920518619203 7942726691714880777928805)
              ·
                refine ⟨1489261254696540145861651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7942726691714880777928805 1489261254696540145861651)
                ·
                  refine ⟨2233891882044810218792477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489261254696540145861651 2233891882044810218792477)
                  ·
                    refine ⟨837709455766803832047179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2233891882044810218792477 837709455766803832047179)
                    ·
                      rfl

theorem cell22_2447150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2447150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447150 prefixEnd_2447150 := by exact prefixLift 2447150
  have htrace : WordTrace (prefixWord ++ tailWord_2447150) baseStart_2447150 baseEnd_2447150 := by
    simpa [prefixWord, tailWord_2447150, baseEnd_2447150] using wordTrace_append hprefix tailTrace_2447150
  have hstable : (prefixWord ++ tailWord_2447150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447150).length < 2 ^ (prefixWord ++ tailWord_2447150).sum := by decide
  have hdescent : baseEnd_2447150 < baseStart_2447150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447161 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 2, 5]
def baseStart_2447161 : Nat := 118140960795 + 2447161 * 2 ^ 59
def prefixEnd_2447161 : Nat := 4983230072969 + 3 ^ 40 * 2447161 * 2
def baseEnd_2447161 : Nat := 837713221291603470022145

theorem tailTrace_2447161 : CollatzResearch.WordTrace tailWord_2447161 prefixEnd_2447161 837713221291603470022145 := by
  unfold tailWord_2447161
  simp only [CollatzResearch.WordTrace]
  refine ⟨89255294287361113669861337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59503529524907409113240891 89255294287361113669861337)
  ·
    refine ⟨66941470715520835252396003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89255294287361113669861337 66941470715520835252396003)
    ·
      refine ⟨100412206073281252878594005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66941470715520835252396003 100412206073281252878594005)
      ·
        refine ⟨2353411079842529364342047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 100412206073281252878594005 2353411079842529364342047)
        ·
          refine ⟨3530116619763794046513071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353411079842529364342047 3530116619763794046513071)
          ·
            refine ⟨5295174929645691069769607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3530116619763794046513071 5295174929645691069769607)
            ·
              refine ⟨7942762394468536604654411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5295174929645691069769607 7942762394468536604654411)
              ·
                refine ⟨11914143591702804906981617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7942762394468536604654411 11914143591702804906981617)
                ·
                  refine ⟨8935607693777103680236213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11914143591702804906981617 8935607693777103680236213)
                  ·
                    refine ⟨837713221291603470022145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8935607693777103680236213 837713221291603470022145)
                    ·
                      rfl

theorem cell22_2447161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 5].length) (baseStart_2447161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447161 prefixEnd_2447161 := by exact prefixLift 2447161
  have htrace : WordTrace (prefixWord ++ tailWord_2447161) baseStart_2447161 baseEnd_2447161 := by
    simpa [prefixWord, tailWord_2447161, baseEnd_2447161] using wordTrace_append hprefix tailTrace_2447161
  have hstable : (prefixWord ++ tailWord_2447161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447161).length < 2 ^ (prefixWord ++ tailWord_2447161).sum := by decide
  have hdescent : baseEnd_2447161 < baseStart_2447161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447189 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_2447189 : Nat := 118140960795 + 2447189 * 2 ^ 59
def prefixEnd_2447189 : Nat := 4983230072969 + 3 ^ 40 * 2447189 * 2
def baseEnd_2447189 : Nat := 837722806263820730322059

theorem tailTrace_2447189 : CollatzResearch.WordTrace tailWord_2447189 prefixEnd_2447189 837722806263820730322059 := by
  unfold tailWord_2447189
  simp only [CollatzResearch.WordTrace]
  refine ⟨89256315531259674451880621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59504210354173116301253747 89256315531259674451880621)
  ·
    refine ⟨33471118324222377919455233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89256315531259674451880621 33471118324222377919455233)
    ·
      refine ⟨25103338743166783439591425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33471118324222377919455233 25103338743166783439591425)
      ·
        refine ⟨18827504057375087579693569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25103338743166783439591425 18827504057375087579693569)
        ·
          refine ⟨14120628043031315684770177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18827504057375087579693569 14120628043031315684770177)
          ·
            refine ⟨10590471032273486763577633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14120628043031315684770177 10590471032273486763577633)
            ·
              refine ⟨7942853274205115072683225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10590471032273486763577633 7942853274205115072683225)
              ·
                refine ⟨5957139955653836304512419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7942853274205115072683225 5957139955653836304512419)
                ·
                  refine ⟨8935709933480754456768629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5957139955653836304512419 8935709933480754456768629)
                  ·
                    refine ⟨837722806263820730322059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8935709933480754456768629 837722806263820730322059)
                    ·
                      rfl

theorem cell22_2447189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_2447189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447189 prefixEnd_2447189 := by exact prefixLift 2447189
  have htrace : WordTrace (prefixWord ++ tailWord_2447189) baseStart_2447189 baseEnd_2447189 := by
    simpa [prefixWord, tailWord_2447189, baseEnd_2447189] using wordTrace_append hprefix tailTrace_2447189
  have hstable : (prefixWord ++ tailWord_2447189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447189).length < 2 ^ (prefixWord ++ tailWord_2447189).sum := by decide
  have hdescent : baseEnd_2447189 < baseStart_2447189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447264 : List Nat := [2, 1, 1, 4, 1, 1, 1, 6, 5]
def baseStart_2447264 : Nat := 118140960795 + 2447264 * 2 ^ 59
def prefixEnd_2447264 : Nat := 4983230072969 + 3 ^ 40 * 2447264 * 2
def baseEnd_2447264 : Nat := 279249493432181844898943

theorem tailTrace_2447264 : CollatzResearch.WordTrace tailWord_2447264 prefixEnd_2447264 279249493432181844898943 := by
  unfold tailWord_2447264
  simp only [CollatzResearch.WordTrace]
  refine ⟨44629525502993981130430423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59506034003991974840573897 44629525502993981130430423)
  ·
    refine ⟨66944288254490971695645635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44629525502993981130430423 66944288254490971695645635)
    ·
      refine ⟨100416432381736457543468453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66944288254490971695645635 100416432381736457543468453)
      ·
        refine ⟨18828081071575585789400335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100416432381736457543468453 18828081071575585789400335)
        ·
          refine ⟨28242121607363378684100503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18828081071575585789400335 28242121607363378684100503)
          ·
            refine ⟨42363182411045068026150755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28242121607363378684100503 42363182411045068026150755)
            ·
              refine ⟨63544773616567602039226133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42363182411045068026150755 63544773616567602039226133)
              ·
                refine ⟨2978661263276606345588725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63544773616567602039226133 2978661263276606345588725)
                ·
                  refine ⟨279249493432181844898943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2978661263276606345588725 279249493432181844898943)
                  ·
                    rfl

theorem cell22_2447264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_2447264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447264 prefixEnd_2447264 := by exact prefixLift 2447264
  have htrace : WordTrace (prefixWord ++ tailWord_2447264) baseStart_2447264 baseEnd_2447264 := by
    simpa [prefixWord, tailWord_2447264, baseEnd_2447264] using wordTrace_append hprefix tailTrace_2447264
  have hstable : (prefixWord ++ tailWord_2447264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447264).length < 2 ^ (prefixWord ++ tailWord_2447264).sum := by decide
  have hdescent : baseEnd_2447264 < baseStart_2447264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447268 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_2447268 : Nat := 118140960795 + 2447268 * 2 ^ 59
def prefixEnd_2447268 : Nat := 4983230072969 + 3 ^ 40 * 2447268 * 2
def baseEnd_2447268 : Nat := 837749849578290857596817

theorem tailTrace_2447268 : CollatzResearch.WordTrace tailWord_2447268 prefixEnd_2447268 837749849578290857596817 := by
  unfold tailWord_2447268
  simp only [CollatzResearch.WordTrace]
  refine ⟨44629598448986735472003229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59506131265315647296004305 44629598448986735472003229)
  ·
    refine ⟨16736099418370025802001211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44629598448986735472003229 16736099418370025802001211)
    ·
      refine ⟨25104149127555038703001817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16736099418370025802001211 25104149127555038703001817)
      ·
        refine ⟨18828111845666279027251363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25104149127555038703001817 18828111845666279027251363)
        ·
          refine ⟨28242167768499418540877045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18828111845666279027251363 28242167768499418540877045)
          ·
            refine ⟨2647703228296820488207223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28242167768499418540877045 2647703228296820488207223)
            ·
              refine ⟨3971554842445230732310835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647703228296820488207223 3971554842445230732310835)
              ·
                refine ⟨5957332263667846098466253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971554842445230732310835 5957332263667846098466253)
                ·
                  refine ⟨2233999598875442286924845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5957332263667846098466253 2233999598875442286924845)
                  ·
                    refine ⟨837749849578290857596817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2233999598875442286924845 837749849578290857596817)
                    ·
                      rfl

theorem cell22_2447268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_2447268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447268 prefixEnd_2447268 := by exact prefixLift 2447268
  have htrace : WordTrace (prefixWord ++ tailWord_2447268) baseStart_2447268 baseEnd_2447268 := by
    simpa [prefixWord, tailWord_2447268, baseEnd_2447268] using wordTrace_append hprefix tailTrace_2447268
  have hstable : (prefixWord ++ tailWord_2447268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447268).length < 2 ^ (prefixWord ++ tailWord_2447268).sum := by decide
  have hdescent : baseEnd_2447268 < baseStart_2447268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447281 : List Nat := [1, 2, 2, 4, 2, 2, 1, 3, 5]
def baseStart_2447281 : Nat := 118140960795 + 2447281 * 2 ^ 59
def prefixEnd_2447281 : Nat := 4983230072969 + 3 ^ 40 * 2447281 * 2
def baseEnd_2447281 : Nat := 279251433247987719007259

theorem tailTrace_2447281 : CollatzResearch.WordTrace tailWord_2447281 prefixEnd_2447281 279251433247987719007259 := by
  unfold tailWord_2447281
  simp only [CollatzResearch.WordTrace]
  refine ⟨89259671046926374164229697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59506447364617582776153131 89259671046926374164229697)
  ·
    refine ⟨66944753285194780623172273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89259671046926374164229697 66944753285194780623172273)
    ·
      refine ⟨50208564963896085467379205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66944753285194780623172273 50208564963896085467379205)
      ·
        refine ⟨9414105930730516025133601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50208564963896085467379205 9414105930730516025133601)
        ·
          refine ⟨7060579448047887018850201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9414105930730516025133601 7060579448047887018850201)
          ·
            refine ⟨5295434586035915264137651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7060579448047887018850201 5295434586035915264137651)
            ·
              refine ⟨7943151879053872896206477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5295434586035915264137651 7943151879053872896206477)
              ·
                refine ⟨2978681954645202336077429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7943151879053872896206477 2978681954645202336077429)
                ·
                  refine ⟨279251433247987719007259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2978681954645202336077429 279251433247987719007259)
                  ·
                    rfl

theorem cell22_2447281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_2447281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447281 prefixEnd_2447281 := by exact prefixLift 2447281
  have htrace : WordTrace (prefixWord ++ tailWord_2447281) baseStart_2447281 baseEnd_2447281 := by
    simpa [prefixWord, tailWord_2447281, baseEnd_2447281] using wordTrace_append hprefix tailTrace_2447281
  have hstable : (prefixWord ++ tailWord_2447281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447281).length < 2 ^ (prefixWord ++ tailWord_2447281).sum := by decide
  have hdescent : baseEnd_2447281 < baseStart_2447281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447339 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 4, 4]
def baseStart_2447339 : Nat := 118140960795 + 2447339 * 2 ^ 59
def prefixEnd_2447339 : Nat := 4983230072969 + 3 ^ 40 * 2447339 * 2
def baseEnd_2447339 : Nat := 837774154329270339071599

theorem tailTrace_2447339 : CollatzResearch.WordTrace tailWord_2447339 prefixEnd_2447339 837774154329270339071599 := by
  unfold tailWord_2447339
  simp only [CollatzResearch.WordTrace]
  refine ⟨89261786480716250069841071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59507857653810833379894047 89261786480716250069841071)
  ·
    refine ⟨133892679721074375104761607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89261786480716250069841071 133892679721074375104761607)
    ·
      refine ⟨200839019581611562657142411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133892679721074375104761607 200839019581611562657142411)
      ·
        refine ⟨301258529372417343985713617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200839019581611562657142411 301258529372417343985713617)
        ·
          refine ⟨225943897029313007989285213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301258529372417343985713617 225943897029313007989285213)
          ·
            refine ⟨84728961385992377995981955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225943897029313007989285213 84728961385992377995981955)
            ·
              refine ⟨127093442078988566993972933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84728961385992377995981955 127093442078988566993972933)
              ·
                refine ⟨23830020389810356311369925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127093442078988566993972933 23830020389810356311369925)
                ·
                  refine ⟨4468128823089441808381861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23830020389810356311369925 4468128823089441808381861)
                  ·
                    refine ⟨837774154329270339071599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4468128823089441808381861 837774154329270339071599)
                    ·
                      rfl

theorem cell22_2447339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 4].length) (baseStart_2447339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447339 prefixEnd_2447339 := by exact prefixLift 2447339
  have htrace : WordTrace (prefixWord ++ tailWord_2447339) baseStart_2447339 baseEnd_2447339 := by
    simpa [prefixWord, tailWord_2447339, baseEnd_2447339] using wordTrace_append hprefix tailTrace_2447339
  have hstable : (prefixWord ++ tailWord_2447339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447339).length < 2 ^ (prefixWord ++ tailWord_2447339).sum := by decide
  have hdescent : baseEnd_2447339 < baseStart_2447339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447358 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2447358 : Nat := 118140960795 + 2447358 * 2 ^ 59
def prefixEnd_2447358 : Nat := 4983230072969 + 3 ^ 40 * 2447358 * 2
def baseEnd_2447358 : Nat := 837780658417560622846541

theorem tailTrace_2447358 : CollatzResearch.WordTrace tailWord_2447358 prefixEnd_2447358 837780658417560622846541 := by
  unfold tailWord_2447358
  simp only [CollatzResearch.WordTrace]
  refine ⟨11157809933455927039347841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59508319645098277543188485 11157809933455927039347841)
  ·
    refine ⟨8368357450091945279510881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11157809933455927039347841 8368357450091945279510881)
    ·
      refine ⟨6276268087568958959633161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8368357450091945279510881 6276268087568958959633161)
      ·
        refine ⟨4707201065676719219724871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6276268087568958959633161 4707201065676719219724871)
        ·
          refine ⟨7060801598515078829587307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4707201065676719219724871 7060801598515078829587307)
          ·
            refine ⟨10591202397772618244380961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7060801598515078829587307 10591202397772618244380961)
            ·
              refine ⟨7943401798329463683285721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10591202397772618244380961 7943401798329463683285721)
              ·
                refine ⟨5957551348747097762464291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7943401798329463683285721 5957551348747097762464291)
                ·
                  refine ⟨8936327023120646643696437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5957551348747097762464291 8936327023120646643696437)
                  ·
                    refine ⟨837780658417560622846541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8936327023120646643696437 837780658417560622846541)
                    ·
                      rfl

theorem cell22_2447358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2447358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447358 prefixEnd_2447358 := by exact prefixLift 2447358
  have htrace : WordTrace (prefixWord ++ tailWord_2447358) baseStart_2447358 baseEnd_2447358 := by
    simpa [prefixWord, tailWord_2447358, baseEnd_2447358] using wordTrace_append hprefix tailTrace_2447358
  have hstable : (prefixWord ++ tailWord_2447358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447358).length < 2 ^ (prefixWord ++ tailWord_2447358).sum := by decide
  have hdescent : baseEnd_2447358 < baseStart_2447358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447366 : List Nat := [6, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2447366 : Nat := 118140960795 + 2447366 * 2 ^ 59
def prefixEnd_2447366 : Nat := 4983230072969 + 3 ^ 40 * 2447366 * 2
def baseEnd_2447366 : Nat := 279261132327017089548839

theorem tailTrace_2447366 : CollatzResearch.WordTrace tailWord_2447366 prefixEnd_2447366 279261132327017089548839 := by
  unfold tailWord_2447366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2789461601613076052533561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59508514167745622454049301 2789461601613076052533561)
  ·
    refine ⟨2092096201209807039400171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2789461601613076052533561 2092096201209807039400171)
    ·
      refine ⟨3138144301814710559100257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2092096201209807039400171 3138144301814710559100257)
      ·
        refine ⟨2353608226361032919325193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3138144301814710559100257 2353608226361032919325193)
        ·
          refine ⟨1765206169770774689493895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2353608226361032919325193 1765206169770774689493895)
          ·
            refine ⟨2647809254656162034240843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765206169770774689493895 2647809254656162034240843)
            ·
              refine ⟨3971713881984243051361265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647809254656162034240843 3971713881984243051361265)
              ·
                refine ⟨2978785411488182288520949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3971713881984243051361265 2978785411488182288520949)
                ·
                  refine ⟨279261132327017089548839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2978785411488182288520949 279261132327017089548839)
                  ·
                    rfl

theorem cell22_2447366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2447366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447366 prefixEnd_2447366 := by exact prefixLift 2447366
  have htrace : WordTrace (prefixWord ++ tailWord_2447366) baseStart_2447366 baseEnd_2447366 := by
    simpa [prefixWord, tailWord_2447366, baseEnd_2447366] using wordTrace_append hprefix tailTrace_2447366
  have hstable : (prefixWord ++ tailWord_2447366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447366).length < 2 ^ (prefixWord ++ tailWord_2447366).sum := by decide
  have hdescent : baseEnd_2447366 < baseStart_2447366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447495 : List Nat := [1, 1, 4, 2, 1, 1, 6, 2, 4]
def baseStart_2447495 : Nat := 118140960795 + 2447495 * 2 ^ 59
def prefixEnd_2447495 : Nat := 4983230072969 + 3 ^ 40 * 2447495 * 2
def baseEnd_2447495 : Nat := 279275852105779310723707

theorem tailTrace_2447495 : CollatzResearch.WordTrace tailWord_2447495 prefixEnd_2447495 279275852105779310723707 := by
  unfold tailWord_2447495
  simp only [CollatzResearch.WordTrace]
  refine ⟨89267476268151088712519939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59511650845434059141679959 89267476268151088712519939)
  ·
    refine ⟨133901214402226633068779909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89267476268151088712519939 133901214402226633068779909)
    ·
      refine ⟨25106477700417493700396233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133901214402226633068779909 25106477700417493700396233)
      ·
        refine ⟨18829858275313120275297175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25106477700417493700396233 18829858275313120275297175)
        ·
          refine ⟨28244787412969680412945763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18829858275313120275297175 28244787412969680412945763)
          ·
            refine ⟨42367181119454520619418645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28244787412969680412945763 42367181119454520619418645)
            ·
              refine ⟨1985961614974430654035249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42367181119454520619418645 1985961614974430654035249)
              ·
                refine ⟨1489471211230822990526437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1985961614974430654035249 1489471211230822990526437)
                ·
                  refine ⟨279275852105779310723707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1489471211230822990526437 279275852105779310723707)
                  ·
                    rfl

theorem cell22_2447495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 4].length) (baseStart_2447495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447495 prefixEnd_2447495 := by exact prefixLift 2447495
  have htrace : WordTrace (prefixWord ++ tailWord_2447495) baseStart_2447495 baseEnd_2447495 := by
    simpa [prefixWord, tailWord_2447495, baseEnd_2447495] using wordTrace_append hprefix tailTrace_2447495
  have hstable : (prefixWord ++ tailWord_2447495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447495).length < 2 ^ (prefixWord ++ tailWord_2447495).sum := by decide
  have hdescent : baseEnd_2447495 < baseStart_2447495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447538 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_2447538 : Nat := 118140960795 + 2447538 * 2 ^ 59
def prefixEnd_2447538 : Nat := 4983230072969 + 3 ^ 40 * 2447538 * 2
def baseEnd_2447538 : Nat := 837842276096100153345989

theorem tailTrace_2447538 : CollatzResearch.WordTrace tailWord_2447538 prefixEnd_2447538 837842276096100153345989 := by
  unfold tailWord_2447538
  simp only [CollatzResearch.WordTrace]
  refine ⟨22317261151748826764083817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59512696404663538037556845 22317261151748826764083817)
  ·
    refine ⟨16737945863811620073062863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22317261151748826764083817 16737945863811620073062863)
    ·
      refine ⟨25106918795717430109594295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16737945863811620073062863 25106918795717430109594295)
      ·
        refine ⟨37660378193576145164391443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25106918795717430109594295 37660378193576145164391443)
        ·
          refine ⟨56490567290364217746587165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37660378193576145164391443 56490567290364217746587165)
          ·
            refine ⟨21183962733886581654970187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56490567290364217746587165 21183962733886581654970187)
            ·
              refine ⟨31775944100829872482455281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21183962733886581654970187 31775944100829872482455281)
              ·
                refine ⟨23831958075622404361841461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31775944100829872482455281 23831958075622404361841461)
                ·
                  refine ⟨2234246069589600408922637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23831958075622404361841461 2234246069589600408922637)
                  ·
                    refine ⟨837842276096100153345989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2234246069589600408922637 837842276096100153345989)
                    ·
                      rfl

theorem cell22_2447538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_2447538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447538 prefixEnd_2447538 := by exact prefixLift 2447538
  have htrace : WordTrace (prefixWord ++ tailWord_2447538) baseStart_2447538 baseEnd_2447538 := by
    simpa [prefixWord, tailWord_2447538, baseEnd_2447538] using wordTrace_append hprefix tailTrace_2447538
  have hstable : (prefixWord ++ tailWord_2447538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447538).length < 2 ^ (prefixWord ++ tailWord_2447538).sum := by decide
  have hdescent : baseEnd_2447538 < baseStart_2447538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447589 : List Nat := [1, 3, 1, 4, 2, 3, 1, 3, 1, 3]
def baseStart_2447589 : Nat := 118140960795 + 2447589 * 2 ^ 59
def prefixEnd_2447589 : Nat := 4983230072969 + 3 ^ 40 * 2447589 * 2
def baseEnd_2447589 : Nat := 837859734438353020320833

theorem tailTrace_2447589 : CollatzResearch.WordTrace tailWord_2447589 prefixEnd_2447589 837859734438353020320833 := by
  unfold tailWord_2447589
  simp only [CollatzResearch.WordTrace]
  refine ⟨89270904729810542766441821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59513936486540361844294547 89270904729810542766441821)
  ·
    refine ⟨33476589273678953537415683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89270904729810542766441821 33476589273678953537415683)
    ·
      refine ⟨50214883910518430306123525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33476589273678953537415683 50214883910518430306123525)
      ·
        refine ⟨9415290733222205682398161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50214883910518430306123525 9415290733222205682398161)
        ·
          refine ⟨7061468049916654261798621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9415290733222205682398161 7061468049916654261798621)
          ·
            refine ⟨2648050518718745348174483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7061468049916654261798621 2648050518718745348174483)
            ·
              refine ⟨3972075778078118022261725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2648050518718745348174483 3972075778078118022261725)
              ·
                refine ⟨1489528416779294258348147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3972075778078118022261725 1489528416779294258348147)
                ·
                  refine ⟨2234292625168941387522221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489528416779294258348147 2234292625168941387522221)
                  ·
                    refine ⟨837859734438353020320833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2234292625168941387522221 837859734438353020320833)
                    ·
                      rfl

theorem cell22_2447589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_2447589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447589 prefixEnd_2447589 := by exact prefixLift 2447589
  have htrace : WordTrace (prefixWord ++ tailWord_2447589) baseStart_2447589 baseEnd_2447589 := by
    simpa [prefixWord, tailWord_2447589, baseEnd_2447589] using wordTrace_append hprefix tailTrace_2447589
  have hstable : (prefixWord ++ tailWord_2447589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447589).length < 2 ^ (prefixWord ++ tailWord_2447589).sum := by decide
  have hdescent : baseEnd_2447589 < baseStart_2447589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447598 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2447598 : Nat := 118140960795 + 2447598 * 2 ^ 59
def prefixEnd_2447598 : Nat := 4983230072969 + 3 ^ 40 * 2447598 * 2
def baseEnd_2447598 : Nat := 837862815322279996845805

theorem tailTrace_2447598 : CollatzResearch.WordTrace tailWord_2447598 prefixEnd_2447598 837862815322279996845805 := by
  unfold tailWord_2447598
  simp only [CollatzResearch.WordTrace]
  refine ⟨11158904123347242162939931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59514155324518624869012965 11158904123347242162939931)
  ·
    refine ⟨16738356185020863244409897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11158904123347242162939931 16738356185020863244409897)
    ·
      refine ⟨12553767138765647433307423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16738356185020863244409897 12553767138765647433307423)
      ·
        refine ⟨18830650708148471149961135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12553767138765647433307423 18830650708148471149961135)
        ·
          refine ⟨28245976062222706724941703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18830650708148471149961135 28245976062222706724941703)
          ·
            refine ⟨42368964093334060087412555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28245976062222706724941703 42368964093334060087412555)
            ·
              refine ⟨63553446140001090131118833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42368964093334060087412555 63553446140001090131118833)
              ·
                refine ⟨47665084605000817598339125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63553446140001090131118833 47665084605000817598339125)
                ·
                  refine ⟨4468601681718826649844293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47665084605000817598339125 4468601681718826649844293)
                  ·
                    refine ⟨837862815322279996845805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4468601681718826649844293 837862815322279996845805)
                    ·
                      rfl

theorem cell22_2447598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2447598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447598 prefixEnd_2447598 := by exact prefixLift 2447598
  have htrace : WordTrace (prefixWord ++ tailWord_2447598) baseStart_2447598 baseEnd_2447598 := by
    simpa [prefixWord, tailWord_2447598, baseEnd_2447598] using wordTrace_append hprefix tailTrace_2447598
  have hstable : (prefixWord ++ tailWord_2447598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447598).length < 2 ^ (prefixWord ++ tailWord_2447598).sum := by decide
  have hdescent : baseEnd_2447598 < baseStart_2447598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447628 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_2447628 : Nat := 118140960795 + 2447628 * 2 ^ 59
def prefixEnd_2447628 : Nat := 4983230072969 + 3 ^ 40 * 2447628 * 2
def baseEnd_2447628 : Nat := 837873084935369918595713

theorem tailTrace_2447628 : CollatzResearch.WordTrace tailWord_2447628 prefixEnd_2447628 837873084935369918595713 := by
  unfold tailWord_2447628
  simp only [CollatzResearch.WordTrace]
  refine ⟨44636163588334626213555769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59514884784446168284741025 44636163588334626213555769)
  ·
    refine ⟨33477122691250969660166827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44636163588334626213555769 33477122691250969660166827)
    ·
      refine ⟨50215684036876454490250241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33477122691250969660166827 50215684036876454490250241)
      ·
        refine ⟨37661763027657340867687681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50215684036876454490250241 37661763027657340867687681)
        ·
          refine ⟨28246322270743005650765761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37661763027657340867687681 28246322270743005650765761)
          ·
            refine ⟨21184741703057254238074321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28246322270743005650765761 21184741703057254238074321)
            ·
              refine ⟨15888556277292940678555741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21184741703057254238074321 15888556277292940678555741)
              ·
                refine ⟨5958208603984852754458403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15888556277292940678555741 5958208603984852754458403)
                ·
                  refine ⟨8937312905977279131687605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5958208603984852754458403 8937312905977279131687605)
                  ·
                    refine ⟨837873084935369918595713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8937312905977279131687605 837873084935369918595713)
                    ·
                      rfl

theorem cell22_2447628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_2447628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447628 prefixEnd_2447628 := by exact prefixLift 2447628
  have htrace : WordTrace (prefixWord ++ tailWord_2447628) baseStart_2447628 baseEnd_2447628 := by
    simpa [prefixWord, tailWord_2447628, baseEnd_2447628] using wordTrace_append hprefix tailTrace_2447628
  have hstable : (prefixWord ++ tailWord_2447628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447628).length < 2 ^ (prefixWord ++ tailWord_2447628).sum := by decide
  have hdescent : baseEnd_2447628 < baseStart_2447628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447643 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 2, 4]
def baseStart_2447643 : Nat := 118140960795 + 2447643 * 2 ^ 59
def prefixEnd_2447643 : Nat := 4983230072969 + 3 ^ 40 * 2447643 * 2
def baseEnd_2447643 : Nat := 837878219741914879470667

theorem tailTrace_2447643 : CollatzResearch.WordTrace tailWord_2447643 prefixEnd_2447643 837878219741914879470667 := by
  unfold tailWord_2447643
  simp only [CollatzResearch.WordTrace]
  refine ⟨89272874271614909988907583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59515249514409939992605055 89272874271614909988907583)
  ·
    refine ⟨133909311407422364983361375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89272874271614909988907583 133909311407422364983361375)
    ·
      refine ⟨200863967111133547475042063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133909311407422364983361375 200863967111133547475042063)
      ·
        refine ⟨301295950666700321212563095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200863967111133547475042063 301295950666700321212563095)
        ·
          refine ⟨451943926000050481818844643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301295950666700321212563095 451943926000050481818844643)
          ·
            refine ⟨677915889000075722728266965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451943926000050481818844643 677915889000075722728266965)
            ·
              refine ⟨15888653648439274751443757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 677915889000075722728266965 15888653648439274751443757)
              ·
                refine ⟨5958245118164728031791409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15888653648439274751443757 5958245118164728031791409)
                ·
                  refine ⟨4468683838623546023843557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5958245118164728031791409 4468683838623546023843557)
                  ·
                    refine ⟨837878219741914879470667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4468683838623546023843557 837878219741914879470667)
                    ·
                      rfl

theorem cell22_2447643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 4].length) (baseStart_2447643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447643 prefixEnd_2447643 := by exact prefixLift 2447643
  have htrace : WordTrace (prefixWord ++ tailWord_2447643) baseStart_2447643 baseEnd_2447643 := by
    simpa [prefixWord, tailWord_2447643, baseEnd_2447643] using wordTrace_append hprefix tailTrace_2447643
  have hstable : (prefixWord ++ tailWord_2447643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447643).length < 2 ^ (prefixWord ++ tailWord_2447643).sum := by decide
  have hdescent : baseEnd_2447643 < baseStart_2447643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447658 : List Nat := [3, 1, 4, 2, 12]
def baseStart_2447658 : Nat := 118140960795 + 2447658 * 2 ^ 59
def prefixEnd_2447658 : Nat := 4983230072969 + 3 ^ 40 * 2447658 * 2
def baseEnd_2447658 : Nat := 3448079648347571359447

theorem tailTrace_2447658 : CollatzResearch.WordTrace tailWord_2447658 prefixEnd_2447658 3448079648347571359447 := by
  unfold tailWord_2447658
  simp only [CollatzResearch.WordTrace]
  refine ⟨22318355341640141887675907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59515614244373711700469085 22318355341640141887675907)
  ·
    refine ⟨33477533012460212831513861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22318355341640141887675907 33477533012460212831513861)
    ·
      refine ⟨6277037439836289905908849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33477533012460212831513861 6277037439836289905908849)
      ·
        refine ⟨4707778079877217429431637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6277037439836289905908849 4707778079877217429431637)
        ·
          refine ⟨3448079648347571359447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4707778079877217429431637 3448079648347571359447)
          ·
            rfl

theorem cell22_2447658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 12].length) (baseStart_2447658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447658 prefixEnd_2447658 := by exact prefixLift 2447658
  have htrace : WordTrace (prefixWord ++ tailWord_2447658) baseStart_2447658 baseEnd_2447658 := by
    simpa [prefixWord, tailWord_2447658, baseEnd_2447658] using wordTrace_append hprefix tailTrace_2447658
  have hstable : (prefixWord ++ tailWord_2447658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447658).length < 2 ^ (prefixWord ++ tailWord_2447658).sum := by decide
  have hdescent : baseEnd_2447658 < baseStart_2447658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447703 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 7]
def baseStart_2447703 : Nat := 118140960795 + 2447703 * 2 ^ 59
def prefixEnd_2447703 : Nat := 4983230072969 + 3 ^ 40 * 2447703 * 2
def baseEnd_2447703 : Nat := 279299586322698240990161

theorem tailTrace_2447703 : CollatzResearch.WordTrace tailWord_2447703 prefixEnd_2447703 279299586322698240990161 := by
  unfold tailWord_2447703
  simp only [CollatzResearch.WordTrace]
  refine ⟨89275062651397540236091763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59516708434265026824061175 89275062651397540236091763)
  ·
    refine ⟨133912593977096310354137645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89275062651397540236091763 133912593977096310354137645)
    ·
      refine ⟨50217222741411116382801617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133912593977096310354137645 50217222741411116382801617)
      ·
        refine ⟨37662917056058337287101213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50217222741411116382801617 37662917056058337287101213)
        ·
          refine ⟨14123593896021876482662955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37662917056058337287101213 14123593896021876482662955)
          ·
            refine ⟨21185390844032814723994433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14123593896021876482662955 21185390844032814723994433)
            ·
              refine ⟨15889043133024611042995825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21185390844032814723994433 15889043133024611042995825)
              ·
                refine ⟨11916782349768458282246869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15889043133024611042995825 11916782349768458282246869)
                ·
                  refine ⟨279299586322698240990161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11916782349768458282246869 279299586322698240990161)
                  ·
                    rfl

theorem cell22_2447703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 7].length) (baseStart_2447703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447703 prefixEnd_2447703 := by exact prefixLift 2447703
  have htrace : WordTrace (prefixWord ++ tailWord_2447703) baseStart_2447703 baseEnd_2447703 := by
    simpa [prefixWord, tailWord_2447703, baseEnd_2447703] using wordTrace_append hprefix tailTrace_2447703
  have hstable : (prefixWord ++ tailWord_2447703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447703).length < 2 ^ (prefixWord ++ tailWord_2447703).sum := by decide
  have hdescent : baseEnd_2447703 < baseStart_2447703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447720 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 7]
def baseStart_2447720 : Nat := 118140960795 + 2447720 * 2 ^ 59
def prefixEnd_2447720 : Nat := 4983230072969 + 3 ^ 40 * 2447720 * 2
def baseEnd_2447720 : Nat := 279301526138504115098477

theorem tailTrace_2447720 : CollatzResearch.WordTrace tailWord_2447720 prefixEnd_2447720 279301526138504115098477 := by
  unfold tailWord_2447720
  simp only [CollatzResearch.WordTrace]
  refine ⟨44637841346167976069730307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59517121794890634759640409 44637841346167976069730307)
  ·
    refine ⟨66956762019251964104595461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44637841346167976069730307 66956762019251964104595461)
    ·
      refine ⟨12554392878609743269611649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66956762019251964104595461 12554392878609743269611649)
      ·
        refine ⟨9415794658957307452208737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12554392878609743269611649 9415794658957307452208737)
        ·
          refine ⟨7061845994217980589156553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9415794658957307452208737 7061845994217980589156553)
          ·
            refine ⟨5296384495663485441867415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7061845994217980589156553 5296384495663485441867415)
            ·
              refine ⟨7944576743495228162801123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5296384495663485441867415 7944576743495228162801123)
              ·
                refine ⟨11916865115242842244201685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7944576743495228162801123 11916865115242842244201685)
                ·
                  refine ⟨279301526138504115098477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11916865115242842244201685 279301526138504115098477)
                  ·
                    rfl

theorem cell22_2447720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_2447720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447720 prefixEnd_2447720 := by exact prefixLift 2447720
  have htrace : WordTrace (prefixWord ++ tailWord_2447720) baseStart_2447720 baseEnd_2447720 := by
    simpa [prefixWord, tailWord_2447720, baseEnd_2447720] using wordTrace_append hprefix tailTrace_2447720
  have hstable : (prefixWord ++ tailWord_2447720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447720).length < 2 ^ (prefixWord ++ tailWord_2447720).sum := by decide
  have hdescent : baseEnd_2447720 < baseStart_2447720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447876 : List Nat := [2, 3, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_2447876 : Nat := 118140960795 + 2447876 * 2 ^ 59
def prefixEnd_2447876 : Nat := 4983230072969 + 3 ^ 40 * 2447876 * 2
def baseEnd_2447876 : Nat := 837957980403579938394953

theorem tailTrace_2447876 : CollatzResearch.WordTrace tailWord_2447876 prefixEnd_2447876 837957980403579938394953 := by
  unfold tailWord_2447876
  simp only [CollatzResearch.WordTrace]
  refine ⟨44640686239885395391069741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59520914986513860521426321 44640686239885395391069741)
  ·
    refine ⟨16740257339957023271651153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44640686239885395391069741 16740257339957023271651153)
    ·
      refine ⟨12555193004967767453738365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16740257339957023271651153 12555193004967767453738365)
      ·
        refine ⟨4708197376862912795151887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12555193004967767453738365 4708197376862912795151887)
        ·
          refine ⟨7062296065294369192727831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4708197376862912795151887 7062296065294369192727831)
          ·
            refine ⟨10593444097941553789091747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7062296065294369192727831 10593444097941553789091747)
            ·
              refine ⟨15890166146912330683637621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10593444097941553789091747 15890166146912330683637621)
              ·
                refine ⟨1489703076273031001591027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15890166146912330683637621 1489703076273031001591027)
                ·
                  refine ⟨2234554614409546502386541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489703076273031001591027 2234554614409546502386541)
                  ·
                    refine ⟨837957980403579938394953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2234554614409546502386541 837957980403579938394953)
                    ·
                      rfl

theorem cell22_2447876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_2447876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447876 prefixEnd_2447876 := by exact prefixLift 2447876
  have htrace : WordTrace (prefixWord ++ tailWord_2447876) baseStart_2447876 baseEnd_2447876 := by
    simpa [prefixWord, tailWord_2447876, baseEnd_2447876] using wordTrace_append hprefix tailTrace_2447876
  have hstable : (prefixWord ++ tailWord_2447876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447876).length < 2 ^ (prefixWord ++ tailWord_2447876).sum := by decide
  have hdescent : baseEnd_2447876 < baseStart_2447876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447970 : List Nat := [3, 3, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2447970 : Nat := 118140960795 + 2447970 * 2 ^ 59
def prefixEnd_2447970 : Nat := 4983230072969 + 3 ^ 40 * 2447970 * 2
def baseEnd_2447970 : Nat := 837990158524595026544665

theorem tailTrace_2447970 : CollatzResearch.WordTrace tailWord_2447970 prefixEnd_2447970 837990158524595026544665 := by
  unfold tailWord_2447970
  simp only [CollatzResearch.WordTrace]
  refine ⟨22321200235357561209015341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59523200627620163224040909 22321200235357561209015341)
  ·
    refine ⟨8370450088259085453380753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22321200235357561209015341 8370450088259085453380753)
    ·
      refine ⟨6277837566194314090035565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8370450088259085453380753 6277837566194314090035565)
      ·
        refine ⟨2354189087322867783763337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6277837566194314090035565 2354189087322867783763337)
        ·
          refine ⟨1765641815492150837822503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2354189087322867783763337 1765641815492150837822503)
          ·
            refine ⟨2648462723238226256733755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765641815492150837822503 2648462723238226256733755)
            ·
              refine ⟨3972694084857339385100633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2648462723238226256733755 3972694084857339385100633)
              ·
                refine ⟨2979520563643004538825475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3972694084857339385100633 2979520563643004538825475)
                ·
                  refine ⟨4469280845464506808238213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2979520563643004538825475 4469280845464506808238213)
                  ·
                    refine ⟨837990158524595026544665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4469280845464506808238213 837990158524595026544665)
                    ·
                      rfl

theorem cell22_2447970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2447970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447970 prefixEnd_2447970 := by exact prefixLift 2447970
  have htrace : WordTrace (prefixWord ++ tailWord_2447970) baseStart_2447970 baseEnd_2447970 := by
    simpa [prefixWord, tailWord_2447970, baseEnd_2447970] using wordTrace_append hprefix tailTrace_2447970
  have hstable : (prefixWord ++ tailWord_2447970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447970).length < 2 ^ (prefixWord ++ tailWord_2447970).sum := by decide
  have hdescent : baseEnd_2447970 < baseStart_2447970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447977 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 5, 3]
def baseStart_2447977 : Nat := 118140960795 + 2447977 * 2 ^ 59
def prefixEnd_2447977 : Nat := 4983230072969 + 3 ^ 40 * 2447977 * 2
def baseEnd_2447977 : Nat := 837992554767649341619643

theorem tailTrace_2447977 : CollatzResearch.WordTrace tailWord_2447977 prefixEnd_2447977 837992554767649341619643 := by
  unfold tailWord_2447977
  simp only [CollatzResearch.WordTrace]
  refine ⟨89285056252404885031566185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59523370834936590021044123 89285056252404885031566185)
  ·
    refine ⟨66963792189303663773674639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89285056252404885031566185 66963792189303663773674639)
    ·
      refine ⟨100445688283955495660511959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66963792189303663773674639 100445688283955495660511959)
      ·
        refine ⟨150668532425933243490767939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100445688283955495660511959 150668532425933243490767939)
        ·
          refine ⟨226002798638899865236151909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150668532425933243490767939 226002798638899865236151909)
          ·
            refine ⟨42375524744793724731778483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226002798638899865236151909 42375524744793724731778483)
            ·
              refine ⟨63563287117190587097667725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42375524744793724731778483 63563287117190587097667725)
              ·
                refine ⟨23836232668946470161625397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63563287117190587097667725 23836232668946470161625397)
                ·
                  refine ⟨2234646812713731577652381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23836232668946470161625397 2234646812713731577652381)
                  ·
                    refine ⟨837992554767649341619643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2234646812713731577652381 837992554767649341619643)
                    ·
                      rfl

theorem cell22_2447977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 3].length) (baseStart_2447977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2447977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2447977 prefixEnd_2447977 := by exact prefixLift 2447977
  have htrace : WordTrace (prefixWord ++ tailWord_2447977) baseStart_2447977 baseEnd_2447977 := by
    simpa [prefixWord, tailWord_2447977, baseEnd_2447977] using wordTrace_append hprefix tailTrace_2447977
  have hstable : (prefixWord ++ tailWord_2447977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447977).length < 2 ^ (prefixWord ++ tailWord_2447977).sum := by decide
  have hdescent : baseEnd_2447977 < baseStart_2447977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448099 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 1, 6]
def baseStart_2448099 : Nat := 118140960795 + 2448099 * 2 ^ 59
def prefixEnd_2448099 : Nat := 4983230072969 + 3 ^ 40 * 2448099 * 2
def baseEnd_2448099 : Nat := 838034317860881690069269

theorem tailTrace_2448099 : CollatzResearch.WordTrace tailWord_2448099 prefixEnd_2448099 838034317860881690069269 := by
  unfold tailWord_2448099
  simp only [CollatzResearch.WordTrace]
  refine ⟨89289505957962899867507351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59526337305308599911671567 89289505957962899867507351)
  ·
    refine ⟨133934258936944349801261027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89289505957962899867507351 133934258936944349801261027)
    ·
      refine ⟨200901388405416524701891541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133934258936944349801261027 200901388405416524701891541)
      ·
        refine ⟨4708626290751949797700583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 200901388405416524701891541 4708626290751949797700583)
        ·
          refine ⟨7062939436127924696550875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4708626290751949797700583 7062939436127924696550875)
          ·
            refine ⟨10594409154191887044826313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7062939436127924696550875 10594409154191887044826313)
            ·
              refine ⟨7945806865643915283619735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10594409154191887044826313 7945806865643915283619735)
              ·
                refine ⟨11918710298465872925429603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7945806865643915283619735 11918710298465872925429603)
                ·
                  refine ⟨17878065447698809388144405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11918710298465872925429603 17878065447698809388144405)
                  ·
                    refine ⟨838034317860881690069269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17878065447698809388144405 838034317860881690069269)
                    ·
                      rfl

theorem cell22_2448099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 6].length) (baseStart_2448099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448099 prefixEnd_2448099 := by exact prefixLift 2448099
  have htrace : WordTrace (prefixWord ++ tailWord_2448099) baseStart_2448099 baseEnd_2448099 := by
    simpa [prefixWord, tailWord_2448099, baseEnd_2448099] using wordTrace_append hprefix tailTrace_2448099
  have hstable : (prefixWord ++ tailWord_2448099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448099).length < 2 ^ (prefixWord ++ tailWord_2448099).sum := by decide
  have hdescent : baseEnd_2448099 < baseStart_2448099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448114 : List Nat := [3, 2, 1, 3, 1, 4, 8]
def baseStart_2448114 : Nat := 118140960795 + 2448114 * 2 ^ 59
def prefixEnd_2448114 : Nat := 4983230072969 + 3 ^ 40 * 2448114 * 2
def baseEnd_2448114 : Nat := 31038498246941727812749

theorem tailTrace_2448114 : CollatzResearch.WordTrace tailWord_2448114 prefixEnd_2448114 31038498246941727812749 := by
  unfold tailWord_2448114
  simp only [CollatzResearch.WordTrace]
  refine ⟨22322513263227139357325849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59526702035272371619535597 22322513263227139357325849)
  ·
    refine ⟨16741884947420354517994387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22322513263227139357325849 16741884947420354517994387)
    ·
      refine ⟨25112827421130531776991581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16741884947420354517994387 25112827421130531776991581)
      ·
        refine ⟨9417310282923949416371843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25112827421130531776991581 9417310282923949416371843)
        ·
          refine ⟨14125965424385924124557765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9417310282923949416371843 14125965424385924124557765)
          ·
            refine ⟨2648618517072360773354581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14125965424385924124557765 2648618517072360773354581)
            ·
              refine ⟨31038498246941727812749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2648618517072360773354581 31038498246941727812749)
              ·
                rfl

theorem cell22_2448114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 8].length) (baseStart_2448114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448114 prefixEnd_2448114 := by exact prefixLift 2448114
  have htrace : WordTrace (prefixWord ++ tailWord_2448114) baseStart_2448114 baseEnd_2448114 := by
    simpa [prefixWord, tailWord_2448114, baseEnd_2448114] using wordTrace_append hprefix tailTrace_2448114
  have hstable : (prefixWord ++ tailWord_2448114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448114).length < 2 ^ (prefixWord ++ tailWord_2448114).sum := by decide
  have hdescent : baseEnd_2448114 < baseStart_2448114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448127 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 2, 6]
def baseStart_2448127 : Nat := 118140960795 + 2448127 * 2 ^ 59
def prefixEnd_2448127 : Nat := 4983230072969 + 3 ^ 40 * 2448127 * 2
def baseEnd_2448127 : Nat := 838043902833098950369183

theorem tailTrace_2448127 : CollatzResearch.WordTrace tailWord_2448127 prefixEnd_2448127 838043902833098950369183 := by
  unfold tailWord_2448127
  simp only [CollatzResearch.WordTrace]
  refine ⟨89290527201861460649526635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59527018134574307099684423 89290527201861460649526635)
  ·
    refine ⟨133935790802792190974289953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89290527201861460649526635 133935790802792190974289953)
    ·
      refine ⟨100451843102094143230717465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133935790802792190974289953 100451843102094143230717465)
      ·
        refine ⟨75338882326570607423038099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100451843102094143230717465 75338882326570607423038099)
        ·
          refine ⟨113008323489855911134557149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75338882326570607423038099 113008323489855911134557149)
          ·
            refine ⟨42378121308695966675458931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113008323489855911134557149 42378121308695966675458931)
            ·
              refine ⟨63567181963043950013188397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42378121308695966675458931 63567181963043950013188397)
              ·
                refine ⟨23837693236141481254945649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63567181963043950013188397 23837693236141481254945649)
                ·
                  refine ⟨17878269927106110941209237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23837693236141481254945649 17878269927106110941209237)
                  ·
                    refine ⟨838043902833098950369183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17878269927106110941209237 838043902833098950369183)
                    ·
                      rfl

theorem cell22_2448127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_2448127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448127 prefixEnd_2448127 := by exact prefixLift 2448127
  have htrace : WordTrace (prefixWord ++ tailWord_2448127) baseStart_2448127 baseEnd_2448127 := by
    simpa [prefixWord, tailWord_2448127, baseEnd_2448127] using wordTrace_append hprefix tailTrace_2448127
  have hstable : (prefixWord ++ tailWord_2448127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448127).length < 2 ^ (prefixWord ++ tailWord_2448127).sum := by decide
  have hdescent : baseEnd_2448127 < baseStart_2448127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448135 : List Nat := [1, 1, 4, 4, 1, 3, 2, 1, 2, 3]
def baseStart_2448135 : Nat := 118140960795 + 2448135 * 2 ^ 59
def prefixEnd_2448135 : Nat := 4983230072969 + 3 ^ 40 * 2448135 * 2
def baseEnd_2448135 : Nat := 838046641396589596169159

theorem tailTrace_2448135 : CollatzResearch.WordTrace tailWord_2448135 prefixEnd_2448135 838046641396589596169159 := by
  unfold tailWord_2448135
  simp only [CollatzResearch.WordTrace]
  refine ⟨89290818985832478015817859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59527212657221652010545239 89290818985832478015817859)
  ·
    refine ⟨133936228478748717023726789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89290818985832478015817859 133936228478748717023726789)
    ·
      refine ⟨25113042839765384441948773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133936228478748717023726789 25113042839765384441948773)
      ·
        refine ⟨4708695532456009582865395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25113042839765384441948773 4708695532456009582865395)
        ·
          refine ⟨7063043298684014374298093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4708695532456009582865395 7063043298684014374298093)
          ·
            refine ⟨2648641237006505390361785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7063043298684014374298093 2648641237006505390361785)
            ·
              refine ⟨1986480927754879042771339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2648641237006505390361785 1986480927754879042771339)
              ·
                refine ⟨2979721391632318564157009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1986480927754879042771339 2979721391632318564157009)
                ·
                  refine ⟨2234791043724238923117757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2979721391632318564157009 2234791043724238923117757)
                  ·
                    refine ⟨838046641396589596169159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2234791043724238923117757 838046641396589596169159)
                    ·
                      rfl

theorem cell22_2448135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_2448135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448135 prefixEnd_2448135 := by exact prefixLift 2448135
  have htrace : WordTrace (prefixWord ++ tailWord_2448135) baseStart_2448135 baseEnd_2448135 := by
    simpa [prefixWord, tailWord_2448135, baseEnd_2448135] using wordTrace_append hprefix tailTrace_2448135
  have hstable : (prefixWord ++ tailWord_2448135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448135).length < 2 ^ (prefixWord ++ tailWord_2448135).sum := by decide
  have hdescent : baseEnd_2448135 < baseStart_2448135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448204 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 8]
def baseStart_2448204 : Nat := 118140960795 + 2448204 * 2 ^ 59
def prefixEnd_2448204 : Nat := 4983230072969 + 3 ^ 40 * 2448204 * 2
def baseEnd_2448204 : Nat := 279356753835565472064649

theorem tailTrace_2448204 : CollatzResearch.WordTrace tailWord_2448204 prefixEnd_2448204 279356753835565472064649 := by
  unfold tailWord_2448204
  simp only [CollatzResearch.WordTrace]
  refine ⟨44646667811291251400039833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59528890415055001866719777 44646667811291251400039833)
  ·
    refine ⟨33485000858468438550029875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44646667811291251400039833 33485000858468438550029875)
    ·
      refine ⟨50227501287702657825044813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33485000858468438550029875 50227501287702657825044813)
      ·
        refine ⟨18835312982888496684391805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50227501287702657825044813 18835312982888496684391805)
        ·
          refine ⟨7063242368583186256646927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18835312982888496684391805 7063242368583186256646927)
          ·
            refine ⟨10594863552874779384970391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063242368583186256646927 10594863552874779384970391)
            ·
              refine ⟨15892295329312169077455587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10594863552874779384970391 15892295329312169077455587)
              ·
                refine ⟨23838442993968253616183381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15892295329312169077455587 23838442993968253616183381)
                ·
                  refine ⟨279356753835565472064649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23838442993968253616183381 279356753835565472064649)
                  ·
                    rfl

theorem cell22_2448204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_2448204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448204 prefixEnd_2448204 := by exact prefixLift 2448204
  have htrace : WordTrace (prefixWord ++ tailWord_2448204) baseStart_2448204 baseEnd_2448204 := by
    simpa [prefixWord, tailWord_2448204, baseEnd_2448204] using wordTrace_append hprefix tailTrace_2448204
  have hstable : (prefixWord ++ tailWord_2448204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448204).length < 2 ^ (prefixWord ++ tailWord_2448204).sum := by decide
  have hdescent : baseEnd_2448204 < baseStart_2448204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448236 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 4, 3]
def baseStart_2448236 : Nat := 118140960795 + 2448236 * 2 ^ 59
def prefixEnd_2448236 : Nat := 4983230072969 + 3 ^ 40 * 2448236 * 2
def baseEnd_2448236 : Nat := 838081215760658999393849

theorem tailTrace_2448236 : CollatzResearch.WordTrace tailWord_2448236 prefixEnd_2448236 838081215760658999393849 := by
  unfold tailWord_2448236
  simp only [CollatzResearch.WordTrace]
  refine ⟨44647251379233286132622281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59529668505644381510163041 44647251379233286132622281)
  ·
    refine ⟨33485438534424964599466711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44647251379233286132622281 33485438534424964599466711)
    ·
      refine ⟨50228157801637446899200067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33485438534424964599466711 50228157801637446899200067)
      ·
        refine ⟨75342236702456170348800101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50228157801637446899200067 75342236702456170348800101)
        ·
          refine ⟨14126669381710531940400019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75342236702456170348800101 14126669381710531940400019)
          ·
            refine ⟨21190004072565797910600029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14126669381710531940400019 21190004072565797910600029)
            ·
              refine ⟨7946251527212174216475011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21190004072565797910600029 7946251527212174216475011)
              ·
                refine ⟨11919377290818261324712517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7946251527212174216475011 11919377290818261324712517)
                ·
                  refine ⟨2234883242028423998383597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11919377290818261324712517 2234883242028423998383597)
                  ·
                    refine ⟨838081215760658999393849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2234883242028423998383597 838081215760658999393849)
                    ·
                      rfl

theorem cell22_2448236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_2448236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448236 prefixEnd_2448236 := by exact prefixLift 2448236
  have htrace : WordTrace (prefixWord ++ tailWord_2448236) baseStart_2448236 baseEnd_2448236 := by
    simpa [prefixWord, tailWord_2448236, baseEnd_2448236] using wordTrace_append hprefix tailTrace_2448236
  have hstable : (prefixWord ++ tailWord_2448236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448236).length < 2 ^ (prefixWord ++ tailWord_2448236).sum := by decide
  have hdescent : baseEnd_2448236 < baseStart_2448236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448238 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_2448238 : Nat := 118140960795 + 2448238 * 2 ^ 59
def prefixEnd_2448238 : Nat := 4983230072969 + 3 ^ 40 * 2448238 * 2
def baseEnd_2448238 : Nat := 279360633467177220281281

theorem tailTrace_2448238 : CollatzResearch.WordTrace tailWord_2448238 prefixEnd_2448238 279360633467177220281281 := by
  unfold tailWord_2448238
  simp only [CollatzResearch.WordTrace]
  refine ⟨11161821963057415825852171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59529717136306217737878245 11161821963057415825852171)
  ·
    refine ⟨16742732944586123738778257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11161821963057415825852171 16742732944586123738778257)
    ·
      refine ⟨12557049708439592804083693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16742732944586123738778257 12557049708439592804083693)
      ·
        refine ⟨4708893640664847301531385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12557049708439592804083693 4708893640664847301531385)
        ·
          refine ⟨3531670230498635476148539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4708893640664847301531385 3531670230498635476148539)
          ·
            refine ⟨5297505345747953214222809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3531670230498635476148539 5297505345747953214222809)
            ·
              refine ⟨3973129009310964910667107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5297505345747953214222809 3973129009310964910667107)
              ·
                refine ⟨5959693513966447366000661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3973129009310964910667107 5959693513966447366000661)
                ·
                  refine ⟨279360633467177220281281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5959693513966447366000661 279360633467177220281281)
                  ·
                    rfl

theorem cell22_2448238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_2448238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448238 prefixEnd_2448238 := by exact prefixLift 2448238
  have htrace : WordTrace (prefixWord ++ tailWord_2448238) baseStart_2448238 baseEnd_2448238 := by
    simpa [prefixWord, tailWord_2448238, baseEnd_2448238] using wordTrace_append hprefix tailTrace_2448238
  have hstable : (prefixWord ++ tailWord_2448238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448238).length < 2 ^ (prefixWord ++ tailWord_2448238).sum := by decide
  have hdescent : baseEnd_2448238 < baseStart_2448238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448266 : List Nat := [3, 1, 2, 4, 1, 2, 1, 8]
def baseStart_2448266 : Nat := 118140960795 + 2448266 * 2 ^ 59
def prefixEnd_2448266 : Nat := 4983230072969 + 3 ^ 40 * 2448266 * 2
def baseEnd_2448266 : Nat := 93121276152638769015973

theorem tailTrace_2448266 : CollatzResearch.WordTrace tailWord_2448266 prefixEnd_2448266 93121276152638769015973 := by
  unfold tailWord_2448266
  simp only [CollatzResearch.WordTrace]
  refine ⟨22323899237089471847209163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59530397965571924925891101 22323899237089471847209163)
  ·
    refine ⟨33485848855634207770813745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22323899237089471847209163 33485848855634207770813745)
    ·
      refine ⟨25114386641725655828110309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33485848855634207770813745 25114386641725655828110309)
      ·
        refine ⟨4708947495323560467770683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25114386641725655828110309 4708947495323560467770683)
        ·
          refine ⟨7063421242985340701656025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4708947495323560467770683 7063421242985340701656025)
          ·
            refine ⟨5297565932239005526242019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7063421242985340701656025 5297565932239005526242019)
            ·
              refine ⟨7946348898358508289363029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5297565932239005526242019 7946348898358508289363029)
              ·
                refine ⟨93121276152638769015973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7946348898358508289363029 93121276152638769015973)
                ·
                  rfl

theorem cell22_2448266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_2448266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448266 prefixEnd_2448266 := by exact prefixLift 2448266
  have htrace : WordTrace (prefixWord ++ tailWord_2448266) baseStart_2448266 baseEnd_2448266 := by
    simpa [prefixWord, tailWord_2448266, baseEnd_2448266] using wordTrace_append hprefix tailTrace_2448266
  have hstable : (prefixWord ++ tailWord_2448266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448266).length < 2 ^ (prefixWord ++ tailWord_2448266).sum := by decide
  have hdescent : baseEnd_2448266 < baseStart_2448266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448349 : List Nat := [1, 4, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_2448349 : Nat := 118140960795 + 2448349 * 2 ^ 59
def prefixEnd_2448349 : Nat := 4983230072969 + 3 ^ 40 * 2448349 * 2
def baseEnd_2448349 : Nat := 838119897969964371318503

theorem tailTrace_2448349 : CollatzResearch.WordTrace tailWord_2448349 prefixEnd_2448349 838119897969964371318503 := by
  unfold tailWord_2448349
  simp only [CollatzResearch.WordTrace]
  refine ⟨89298624207057192564108101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59532416138038128376072067 89298624207057192564108101)
  ·
    refine ⟨16743492038823223605770269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89298624207057192564108101 16743492038823223605770269)
    ·
      refine ⟨6278809514558708852163851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16743492038823223605770269 6278809514558708852163851)
      ·
        refine ⟨9418214271838063278245777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6278809514558708852163851 9418214271838063278245777)
        ·
          refine ⟨7063660703878547458684333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9418214271838063278245777 7063660703878547458684333)
          ·
            refine ⟨2648872763954455297006625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7063660703878547458684333 2648872763954455297006625)
            ·
              refine ⟨1986654572965841472754969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2648872763954455297006625 1986654572965841472754969)
              ·
                refine ⟨1489990929724381104566227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1986654572965841472754969 1489990929724381104566227)
                ·
                  refine ⟨2234986394586571656849341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489990929724381104566227 2234986394586571656849341)
                  ·
                    refine ⟨838119897969964371318503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2234986394586571656849341 838119897969964371318503)
                    ·
                      rfl

theorem cell22_2448349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_2448349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448349 prefixEnd_2448349 := by exact prefixLift 2448349
  have htrace : WordTrace (prefixWord ++ tailWord_2448349) baseStart_2448349 baseEnd_2448349 := by
    simpa [prefixWord, tailWord_2448349, baseEnd_2448349] using wordTrace_append hprefix tailTrace_2448349
  have hstable : (prefixWord ++ tailWord_2448349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448349).length < 2 ^ (prefixWord ++ tailWord_2448349).sum := by decide
  have hdescent : baseEnd_2448349 < baseStart_2448349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448371 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 8, 3]
def baseStart_2448371 : Nat := 118140960795 + 2448371 * 2 ^ 59
def prefixEnd_2448371 : Nat := 4983230072969 + 3 ^ 40 * 2448371 * 2
def baseEnd_2448371 : Nat := 838127429019563647268435

theorem tailTrace_2448371 : CollatzResearch.WordTrace tailWord_2448371 prefixEnd_2448371 838127429019563647268435 := by
  unfold tailWord_2448371
  simp only [CollatzResearch.WordTrace]
  refine ⟨89299426612977490321408967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59532951075318326880939311 89299426612977490321408967)
  ·
    refine ⟨133949139919466235482113451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89299426612977490321408967 133949139919466235482113451)
    ·
      refine ⟨200923709879199353223170177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133949139919466235482113451 200923709879199353223170177)
      ·
        refine ⟨150692782409399514917377633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200923709879199353223170177 150692782409399514917377633)
        ·
          refine ⟨113019586807049636188033225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150692782409399514917377633 113019586807049636188033225)
          ·
            refine ⟨84764690105287227141024919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113019586807049636188033225 84764690105287227141024919)
            ·
              refine ⟨127147035157930840711537379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84764690105287227141024919 127147035157930840711537379)
              ·
                refine ⟨190720552736896261067306069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127147035157930840711537379 190720552736896261067306069)
                ·
                  refine ⟨2235006477385503059382493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 190720552736896261067306069 2235006477385503059382493)
                  ·
                    refine ⟨838127429019563647268435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235006477385503059382493 838127429019563647268435)
                    ·
                      rfl

theorem cell22_2448371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 3].length) (baseStart_2448371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448371 prefixEnd_2448371 := by exact prefixLift 2448371
  have htrace : WordTrace (prefixWord ++ tailWord_2448371) baseStart_2448371 baseEnd_2448371 := by
    simpa [prefixWord, tailWord_2448371, baseEnd_2448371] using wordTrace_append hprefix tailTrace_2448371
  have hstable : (prefixWord ++ tailWord_2448371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448371).length < 2 ^ (prefixWord ++ tailWord_2448371).sum := by decide
  have hdescent : baseEnd_2448371 < baseStart_2448371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448405 : List Nat := [1, 3, 2, 1, 4, 1, 3, 2, 2, 3]
def baseStart_2448405 : Nat := 118140960795 + 2448405 * 2 ^ 59
def prefixEnd_2448405 : Nat := 4983230072969 + 3 ^ 40 * 2448405 * 2
def baseEnd_2448405 : Nat := 838139067914398891918331

theorem tailTrace_2448405 : CollatzResearch.WordTrace tailWord_2448405 prefixEnd_2448405 838139067914398891918331 := by
  unfold tailWord_2448405
  simp only [CollatzResearch.WordTrace]
  refine ⟨89300666694854314128146669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59533777796569542752097779 89300666694854314128146669)
  ·
    refine ⟨33487750010570367798055001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89300666694854314128146669 33487750010570367798055001)
    ·
      refine ⟨25115812507927775848541251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33487750010570367798055001 25115812507927775848541251)
      ·
        refine ⟨37673718761891663772811877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25115812507927775848541251 37673718761891663772811877)
        ·
          refine ⟨7063822267854686957402227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37673718761891663772811877 7063822267854686957402227)
          ·
            refine ⟨10595733401782030436103341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063822267854686957402227 10595733401782030436103341)
            ·
              refine ⟨3973400025668261413538753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10595733401782030436103341 3973400025668261413538753)
              ·
                refine ⟨2980050019251196060154065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3973400025668261413538753 2980050019251196060154065)
                ·
                  refine ⟨2235037514438397045115549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2980050019251196060154065 2235037514438397045115549)
                  ·
                    refine ⟨838139067914398891918331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235037514438397045115549 838139067914398891918331)
                    ·
                      rfl

theorem cell22_2448405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_2448405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448405 prefixEnd_2448405 := by exact prefixLift 2448405
  have htrace : WordTrace (prefixWord ++ tailWord_2448405) baseStart_2448405 baseEnd_2448405 := by
    simpa [prefixWord, tailWord_2448405, baseEnd_2448405] using wordTrace_append hprefix tailTrace_2448405
  have hstable : (prefixWord ++ tailWord_2448405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448405).length < 2 ^ (prefixWord ++ tailWord_2448405).sum := by decide
  have hdescent : baseEnd_2448405 < baseStart_2448405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448433 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 3, 3]
def baseStart_2448433 : Nat := 118140960795 + 2448433 * 2 ^ 59
def prefixEnd_2448433 : Nat := 4983230072969 + 3 ^ 40 * 2448433 * 2
def baseEnd_2448433 : Nat := 838148652886616152218245

theorem tailTrace_2448433 : CollatzResearch.WordTrace tailWord_2448433 prefixEnd_2448433 838148652886616152218245 := by
  unfold tailWord_2448433
  simp only [CollatzResearch.WordTrace]
  refine ⟨89301687938752874910165953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59534458625835249940110635 89301687938752874910165953)
  ·
    refine ⟨66976265954064656182624465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89301687938752874910165953 66976265954064656182624465)
    ·
      refine ⟨50232199465548492136968349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66976265954064656182624465 50232199465548492136968349)
      ·
        refine ⟨18837074799580684551363131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50232199465548492136968349 18837074799580684551363131)
        ·
          refine ⟨28255612199371026827044697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18837074799580684551363131 28255612199371026827044697)
          ·
            refine ⟨21191709149528270120283523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28255612199371026827044697 21191709149528270120283523)
            ·
              refine ⟨31787563724292405180425285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21191709149528270120283523 31787563724292405180425285)
              ·
                refine ⟨5960168198304825971329741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31787563724292405180425285 5960168198304825971329741)
                ·
                  refine ⟨2235063074364309739248653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5960168198304825971329741 2235063074364309739248653)
                  ·
                    refine ⟨838148652886616152218245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235063074364309739248653 838148652886616152218245)
                    ·
                      rfl

theorem cell22_2448433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_2448433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448433 prefixEnd_2448433 := by exact prefixLift 2448433
  have htrace : WordTrace (prefixWord ++ tailWord_2448433) baseStart_2448433 baseEnd_2448433 := by
    simpa [prefixWord, tailWord_2448433, baseEnd_2448433] using wordTrace_append hprefix tailTrace_2448433
  have hstable : (prefixWord ++ tailWord_2448433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448433).length < 2 ^ (prefixWord ++ tailWord_2448433).sum := by decide
  have hdescent : baseEnd_2448433 < baseStart_2448433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448523 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 4, 3]
def baseStart_2448523 : Nat := 118140960795 + 2448523 * 2 ^ 59
def prefixEnd_2448523 : Nat := 4983230072969 + 3 ^ 40 * 2448523 * 2
def baseEnd_2448523 : Nat := 838179461725885917467969

theorem tailTrace_2448523 : CollatzResearch.WordTrace tailWord_2448523 prefixEnd_2448523 838179461725885917467969 := by
  unfold tailWord_2448523
  simp only [CollatzResearch.WordTrace]
  refine ⟨89304970508426820280942223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59536647005617880187294815 89304970508426820280942223)
  ·
    refine ⟨133957455762640230421413335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89304970508426820280942223 133957455762640230421413335)
    ·
      refine ⟨200936183643960345632120003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133957455762640230421413335 200936183643960345632120003)
      ·
        refine ⟨301404275465940518448180005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200936183643960345632120003 301404275465940518448180005)
        ·
          refine ⟨56513301649863847209033751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 301404275465940518448180005 56513301649863847209033751)
          ·
            refine ⟨84769952474795770813550627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56513301649863847209033751 84769952474795770813550627)
            ·
              refine ⟨127154928712193656220325941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84769952474795770813550627 127154928712193656220325941)
              ·
                refine ⟨11920774566768155270655557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127154928712193656220325941 11920774566768155270655557)
                ·
                  refine ⟨2235145231269029113247917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11920774566768155270655557 2235145231269029113247917)
                  ·
                    refine ⟨838179461725885917467969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235145231269029113247917 838179461725885917467969)
                    ·
                      rfl

theorem cell22_2448523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 3].length) (baseStart_2448523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448523 prefixEnd_2448523 := by exact prefixLift 2448523
  have htrace : WordTrace (prefixWord ++ tailWord_2448523) baseStart_2448523 baseEnd_2448523 := by
    simpa [prefixWord, tailWord_2448523, baseEnd_2448523] using wordTrace_append hprefix tailTrace_2448523
  have hstable : (prefixWord ++ tailWord_2448523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448523).length < 2 ^ (prefixWord ++ tailWord_2448523).sum := by decide
  have hdescent : baseEnd_2448523 < baseStart_2448523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448540 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_2448540 : Nat := 118140960795 + 2448540 * 2 ^ 59
def prefixEnd_2448540 : Nat := 4983230072969 + 3 ^ 40 * 2448540 * 2
def baseEnd_2448540 : Nat := 838185281173303539792917

theorem tailTrace_2448540 : CollatzResearch.WordTrace tailWord_2448540 prefixEnd_2448540 838185281173303539792917 := by
  unfold tailWord_2448540
  simp only [CollatzResearch.WordTrace]
  refine ⟨44652795274682616092155537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59537060366243488122874049 44652795274682616092155537)
  ·
    refine ⟨33489596456011962069116653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44652795274682616092155537 33489596456011962069116653)
    ·
      refine ⟨12558598671004485775918745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33489596456011962069116653 12558598671004485775918745)
      ·
        refine ⟨9418949003253364331939059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12558598671004485775918745 9418949003253364331939059)
        ·
          refine ⟨14128423504880046497908589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9418949003253364331939059 14128423504880046497908589)
          ·
            refine ⟨5298158814330017436715721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14128423504880046497908589 5298158814330017436715721)
            ·
              refine ⟨3973619110747513077536791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5298158814330017436715721 3973619110747513077536791)
              ·
                refine ⟨5960428666121269616305187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3973619110747513077536791 5960428666121269616305187)
                ·
                  refine ⟨8940642999181904424457781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5960428666121269616305187 8940642999181904424457781)
                  ·
                    refine ⟨838185281173303539792917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8940642999181904424457781 838185281173303539792917)
                    ·
                      rfl

theorem cell22_2448540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_2448540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448540 prefixEnd_2448540 := by exact prefixLift 2448540
  have htrace : WordTrace (prefixWord ++ tailWord_2448540) baseStart_2448540 baseEnd_2448540 := by
    simpa [prefixWord, tailWord_2448540, baseEnd_2448540] using wordTrace_append hprefix tailTrace_2448540
  have hstable : (prefixWord ++ tailWord_2448540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448540).length < 2 ^ (prefixWord ++ tailWord_2448540).sum := by decide
  have hdescent : baseEnd_2448540 < baseStart_2448540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448574 : List Nat := [4, 2, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_2448574 : Nat := 118140960795 + 2448574 * 2 ^ 59
def prefixEnd_2448574 : Nat := 4983230072969 + 3 ^ 40 * 2448574 * 2
def baseEnd_2448574 : Nat := 838196920068138784442813

theorem tailTrace_2448574 : CollatzResearch.WordTrace tailWord_2448574 prefixEnd_2448574 838196920068138784442813 := by
  unfold tailWord_2448574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11163353828905256998881097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59537887087494703994032517 11163353828905256998881097)
  ·
    refine ⟨8372515371678942749160823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11163353828905256998881097 8372515371678942749160823)
    ·
      refine ⟨12558773057518414123741235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8372515371678942749160823 12558773057518414123741235)
      ·
        refine ⟨18838159586277621185611853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12558773057518414123741235 18838159586277621185611853)
        ·
          refine ⟨7064309844854107944604445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18838159586277621185611853 7064309844854107944604445)
          ·
            refine ⟨2649116191820290479226667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7064309844854107944604445 2649116191820290479226667)
            ·
              refine ⟨3973674287730435718840001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649116191820290479226667 3973674287730435718840001)
              ·
                refine ⟨2980255715797826789130001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3973674287730435718840001 2980255715797826789130001)
                ·
                  refine ⟨2235191786848370091847501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2980255715797826789130001 2235191786848370091847501)
                  ·
                    refine ⟨838196920068138784442813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235191786848370091847501 838196920068138784442813)
                    ·
                      rfl

theorem cell22_2448574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_2448574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448574 prefixEnd_2448574 := by exact prefixLift 2448574
  have htrace : WordTrace (prefixWord ++ tailWord_2448574) baseStart_2448574 baseEnd_2448574 := by
    simpa [prefixWord, tailWord_2448574, baseEnd_2448574] using wordTrace_append hprefix tailTrace_2448574
  have hstable : (prefixWord ++ tailWord_2448574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448574).length < 2 ^ (prefixWord ++ tailWord_2448574).sum := by decide
  have hdescent : baseEnd_2448574 < baseStart_2448574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448619 : List Nat := [1, 1, 1, 1, 2, 8, 1, 3, 1, 3]
def baseStart_2448619 : Nat := 118140960795 + 2448619 * 2 ^ 59
def prefixEnd_2448619 : Nat := 4983230072969 + 3 ^ 40 * 2448619 * 2
def baseEnd_2448619 : Nat := 838212324487773667067675

theorem tailTrace_2448619 : CollatzResearch.WordTrace tailWord_2448619 prefixEnd_2448619 838212324487773667067675 := by
  unfold tailWord_2448619
  simp only [CollatzResearch.WordTrace]
  refine ⟨89308471916079028676436911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59538981277386019117624607 89308471916079028676436911)
  ·
    refine ⟨133962707874118543014655367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89308471916079028676436911 133962707874118543014655367)
    ·
      refine ⟨200944061811177814521983051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133962707874118543014655367 200944061811177814521983051)
      ·
        refine ⟨301416092716766721782974577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200944061811177814521983051 301416092716766721782974577)
        ·
          refine ⟨226062069537575041337230933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301416092716766721782974577 226062069537575041337230933)
          ·
            refine ⟨2649164877393457515670675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 226062069537575041337230933 2649164877393457515670675)
            ·
              refine ⟨3973747316090186273506013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649164877393457515670675 3973747316090186273506013)
              ·
                refine ⟨1490155243533819852564755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3973747316090186273506013 1490155243533819852564755)
                ·
                  refine ⟨2235232865300729778847133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490155243533819852564755 2235232865300729778847133)
                  ·
                    refine ⟨838212324487773667067675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235232865300729778847133 838212324487773667067675)
                    ·
                      rfl

theorem cell22_2448619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 1, 3].length) (baseStart_2448619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448619 prefixEnd_2448619 := by exact prefixLift 2448619
  have htrace : WordTrace (prefixWord ++ tailWord_2448619) baseStart_2448619 baseEnd_2448619 := by
    simpa [prefixWord, tailWord_2448619, baseEnd_2448619] using wordTrace_append hprefix tailTrace_2448619
  have hstable : (prefixWord ++ tailWord_2448619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448619).length < 2 ^ (prefixWord ++ tailWord_2448619).sum := by decide
  have hdescent : baseEnd_2448619 < baseStart_2448619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448636 : List Nat := [2, 2, 2, 1, 5, 1, 3, 2, 1, 3]
def baseStart_2448636 : Nat := 118140960795 + 2448636 * 2 ^ 59
def prefixEnd_2448636 : Nat := 4983230072969 + 3 ^ 40 * 2448636 * 2
def baseEnd_2448636 : Nat := 838218143935191289392623

theorem tailTrace_2448636 : CollatzResearch.WordTrace tailWord_2448636 prefixEnd_2448636 838218143935191289392623 := by
  unfold tailWord_2448636
  simp only [CollatzResearch.WordTrace]
  refine ⟨44654545978508720289902881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59539394638011627053203841 44654545978508720289902881)
  ·
    refine ⟨33490909483881540217427161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44654545978508720289902881 33490909483881540217427161)
    ·
      refine ⟨25118182112911155163070371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33490909483881540217427161 25118182112911155163070371)
      ·
        refine ⟨37677273169366732744605557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25118182112911155163070371 37677273169366732744605557)
        ·
          refine ⟨3532244359628131194806771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37677273169366732744605557 3532244359628131194806771)
          ·
            refine ⟨5298366539442196792210157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3532244359628131194806771 5298366539442196792210157)
            ·
              refine ⟨1986887452290823797078809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5298366539442196792210157 1986887452290823797078809)
              ·
                refine ⟨1490165589218117847809107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1986887452290823797078809 1490165589218117847809107)
                ·
                  refine ⟨2235248383827176771713661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490165589218117847809107 2235248383827176771713661)
                  ·
                    refine ⟨838218143935191289392623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235248383827176771713661 838218143935191289392623)
                    ·
                      rfl

theorem cell22_2448636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_2448636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448636 prefixEnd_2448636 := by exact prefixLift 2448636
  have htrace : WordTrace (prefixWord ++ tailWord_2448636) baseStart_2448636 baseEnd_2448636 := by
    simpa [prefixWord, tailWord_2448636, baseEnd_2448636] using wordTrace_append hprefix tailTrace_2448636
  have hstable : (prefixWord ++ tailWord_2448636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448636).length < 2 ^ (prefixWord ++ tailWord_2448636).sum := by decide
  have hdescent : baseEnd_2448636 < baseStart_2448636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448675 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 1, 5]
def baseStart_2448675 : Nat := 118140960795 + 2448675 * 2 ^ 59
def prefixEnd_2448675 : Nat := 4983230072969 + 3 ^ 40 * 2448675 * 2
def baseEnd_2448675 : Nat := 838231494432208187667503

theorem tailTrace_2448675 : CollatzResearch.WordTrace tailWord_2448675 prefixEnd_2448675 838231494432208187667503 := by
  unfold tailWord_2448675
  simp only [CollatzResearch.WordTrace]
  refine ⟨89310514403876150240475479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59540342935917433493650319 89310514403876150240475479)
  ·
    refine ⟨133965771605814225360713219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89310514403876150240475479 133965771605814225360713219)
    ·
      refine ⟨200948657408721338041069829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133965771605814225360713219 200948657408721338041069829)
      ·
        refine ⟨37677873264135250882700593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200948657408721338041069829 37677873264135250882700593)
        ·
          refine ⟨28258404948101438162025445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37677873264135250882700593 28258404948101438162025445)
          ·
            refine ⟨5298450927769019655379771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28258404948101438162025445 5298450927769019655379771)
            ·
              refine ⟨7947676391653529483069657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5298450927769019655379771 7947676391653529483069657)
              ·
                refine ⟨5960757293740147112302243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7947676391653529483069657 5960757293740147112302243)
                ·
                  refine ⟨8941135940610220668453365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5960757293740147112302243 8941135940610220668453365)
                  ·
                    refine ⟨838231494432208187667503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8941135940610220668453365 838231494432208187667503)
                    ·
                      rfl

theorem cell22_2448675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 5].length) (baseStart_2448675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448675 prefixEnd_2448675 := by exact prefixLift 2448675
  have htrace : WordTrace (prefixWord ++ tailWord_2448675) baseStart_2448675 baseEnd_2448675 := by
    simpa [prefixWord, tailWord_2448675, baseEnd_2448675] using wordTrace_append hprefix tailTrace_2448675
  have hstable : (prefixWord ++ tailWord_2448675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448675).length < 2 ^ (prefixWord ++ tailWord_2448675).sum := by decide
  have hdescent : baseEnd_2448675 < baseStart_2448675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448754 : List Nat := [3, 2, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_2448754 : Nat := 118140960795 + 2448754 * 2 ^ 59
def prefixEnd_2448754 : Nat := 4983230072969 + 3 ^ 40 * 2448754 * 2
def baseEnd_2448754 : Nat := 838258537746678314942261

theorem tailTrace_2448754 : CollatzResearch.WordTrace tailWord_2448754 prefixEnd_2448754 838258537746678314942261 := by
  unfold tailWord_2448754
  simp only [CollatzResearch.WordTrace]
  refine ⟨22328348942647486683150329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59542263847059964488400877 22328348942647486683150329)
  ·
    refine ⟨16746261706985615012362747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22328348942647486683150329 16746261706985615012362747)
    ·
      refine ⟨25119392560478422518544121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16746261706985615012362747 25119392560478422518544121)
      ·
        refine ⟨18839544420358816888908091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25119392560478422518544121 18839544420358816888908091)
        ·
          refine ⟨28259316630538225333362137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18839544420358816888908091 28259316630538225333362137)
          ·
            refine ⟨21194487472903669000021603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28259316630538225333362137 21194487472903669000021603)
            ·
              refine ⟨31791731209355503500032405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21194487472903669000021603 31791731209355503500032405)
              ·
                refine ⟨1490237400438539226564019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31791731209355503500032405 1490237400438539226564019)
                ·
                  refine ⟨2235356100657808839846029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490237400438539226564019 2235356100657808839846029)
                  ·
                    refine ⟨838258537746678314942261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235356100657808839846029 838258537746678314942261)
                    ·
                      rfl

theorem cell22_2448754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_2448754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448754 prefixEnd_2448754 := by exact prefixLift 2448754
  have htrace : WordTrace (prefixWord ++ tailWord_2448754) baseStart_2448754 baseEnd_2448754 := by
    simpa [prefixWord, tailWord_2448754, baseEnd_2448754] using wordTrace_append hprefix tailTrace_2448754
  have hstable : (prefixWord ++ tailWord_2448754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448754).length < 2 ^ (prefixWord ++ tailWord_2448754).sum := by decide
  have hdescent : baseEnd_2448754 < baseStart_2448754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448765 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_2448765 : Nat := 118140960795 + 2448765 * 2 ^ 59
def prefixEnd_2448765 : Nat := 4983230072969 + 3 ^ 40 * 2448765 * 2
def baseEnd_2448765 : Nat := 838262303271477952917227

theorem tailTrace_2448765 : CollatzResearch.WordTrace tailWord_2448765 prefixEnd_2448765 838262303271477952917227 := by
  unfold tailWord_2448765
  simp only [CollatzResearch.WordTrace]
  refine ⟨89313796973550095611251749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59542531315700063740834499 89313796973550095611251749)
  ·
    refine ⟨16746336932540642927109703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89313796973550095611251749 16746336932540642927109703)
    ·
      refine ⟨25119505398810964390664555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16746336932540642927109703 25119505398810964390664555)
      ·
        refine ⟨37679258098216446585996833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25119505398810964390664555 37679258098216446585996833)
        ·
          refine ⟨28259443573662334939497625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37679258098216446585996833 28259443573662334939497625)
          ·
            refine ⟨21194582680246751204623219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28259443573662334939497625 21194582680246751204623219)
            ·
              refine ⟨31791874020370126806934829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21194582680246751204623219 31791874020370126806934829)
              ·
                refine ⟨11921952757638797552600561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31791874020370126806934829 11921952757638797552600561)
                ·
                  refine ⟨8941464568229098164450421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11921952757638797552600561 8941464568229098164450421)
                  ·
                    refine ⟨838262303271477952917227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8941464568229098164450421 838262303271477952917227)
                    ·
                      rfl

theorem cell22_2448765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_2448765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448765 prefixEnd_2448765 := by exact prefixLift 2448765
  have htrace : WordTrace (prefixWord ++ tailWord_2448765) baseStart_2448765 baseEnd_2448765 := by
    simpa [prefixWord, tailWord_2448765, baseEnd_2448765] using wordTrace_append hprefix tailTrace_2448765
  have hstable : (prefixWord ++ tailWord_2448765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448765).length < 2 ^ (prefixWord ++ tailWord_2448765).sum := by decide
  have hdescent : baseEnd_2448765 < baseStart_2448765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448788 : List Nat := [2, 4, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_2448788 : Nat := 118140960795 + 2448788 * 2 ^ 59
def prefixEnd_2448788 : Nat := 4983230072969 + 3 ^ 40 * 2448788 * 2
def baseEnd_2448788 : Nat := 838270176641513559592157

theorem tailTrace_2448788 : CollatzResearch.WordTrace tailWord_2448788 prefixEnd_2448788 838270176641513559592157 := by
  unfold tailWord_2448788
  simp only [CollatzResearch.WordTrace]
  refine ⟨44657317926233385269669509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59543090568311180359559345 44657317926233385269669509)
  ·
    refine ⟨8373247111168759738063033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44657317926233385269669509 8373247111168759738063033)
    ·
      refine ⟨6279935333376569803547275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8373247111168759738063033 6279935333376569803547275)
      ·
        refine ⟨9419903000064854705320913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6279935333376569803547275 9419903000064854705320913)
        ·
          refine ⟨7064927250048641028990685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9419903000064854705320913 7064927250048641028990685)
          ·
            refine ⟨2649347718768240385871507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7064927250048641028990685 2649347718768240385871507)
            ·
              refine ⟨3974021578152360578807261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649347718768240385871507 3974021578152360578807261)
              ·
                refine ⟨1490258091807135217052723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3974021578152360578807261 1490258091807135217052723)
                ·
                  refine ⟨2235387137710702825579085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490258091807135217052723 2235387137710702825579085)
                  ·
                    refine ⟨838270176641513559592157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235387137710702825579085 838270176641513559592157)
                    ·
                      rfl

theorem cell22_2448788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_2448788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448788 prefixEnd_2448788 := by exact prefixLift 2448788
  have htrace : WordTrace (prefixWord ++ tailWord_2448788) baseStart_2448788 baseEnd_2448788 := by
    simpa [prefixWord, tailWord_2448788, baseEnd_2448788] using wordTrace_append hprefix tailTrace_2448788
  have hstable : (prefixWord ++ tailWord_2448788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448788).length < 2 ^ (prefixWord ++ tailWord_2448788).sum := by decide
  have hdescent : baseEnd_2448788 < baseStart_2448788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448812 : List Nat := [2, 2, 1, 1, 1, 1, 4, 6, 4]
def baseStart_2448812 : Nat := 118140960795 + 2448812 * 2 ^ 59
def prefixEnd_2448812 : Nat := 4983230072969 + 3 ^ 40 * 2448812 * 2
def baseEnd_2448812 : Nat := 279426130777328498997361

theorem tailTrace_2448812 : CollatzResearch.WordTrace tailWord_2448812 prefixEnd_2448812 279426130777328498997361 := by
  unfold tailWord_2448812
  simp only [CollatzResearch.WordTrace]
  refine ⟨44657755602189911319106345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59543674136253215092141793 44657755602189911319106345)
  ·
    refine ⟨33493316701642433489329759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44657755602189911319106345 33493316701642433489329759)
    ·
      refine ⟨50239975052463650233994639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33493316701642433489329759 50239975052463650233994639)
      ·
        refine ⟨75359962578695475350991959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50239975052463650233994639 75359962578695475350991959)
        ·
          refine ⟨113039943868043213026487939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75359962578695475350991959 113039943868043213026487939)
          ·
            refine ⟨169559915802064819539731909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113039943868043213026487939 169559915802064819539731909)
            ·
              refine ⟨31792484212887153663699733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169559915802064819539731909 31792484212887153663699733)
              ·
                refine ⟨1490272697479085327985925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31792484212887153663699733 1490272697479085327985925)
                ·
                  refine ⟨279426130777328498997361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1490272697479085327985925 279426130777328498997361)
                  ·
                    rfl

theorem cell22_2448812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_2448812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448812 prefixEnd_2448812 := by exact prefixLift 2448812
  have htrace : WordTrace (prefixWord ++ tailWord_2448812) baseStart_2448812 baseEnd_2448812 := by
    simpa [prefixWord, tailWord_2448812, baseEnd_2448812] using wordTrace_append hprefix tailTrace_2448812
  have hstable : (prefixWord ++ tailWord_2448812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448812).length < 2 ^ (prefixWord ++ tailWord_2448812).sum := by decide
  have hdescent : baseEnd_2448812 < baseStart_2448812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448840 : List Nat := [2, 1, 3, 1, 3, 1, 1, 10]
def baseStart_2448840 : Nat := 118140960795 + 2448840 * 2 ^ 59
def prefixEnd_2448840 : Nat := 4983230072969 + 3 ^ 40 * 2448840 * 2
def baseEnd_2448840 : Nat := 93143108589355861921333

theorem tailTrace_2448840 : CollatzResearch.WordTrace tailWord_2448840 prefixEnd_2448840 93143108589355861921333 := by
  unfold tailWord_2448840
  simp only [CollatzResearch.WordTrace]
  refine ⟨44658266224139191710115987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59544354965518922280154649 44658266224139191710115987)
  ·
    refine ⟨66987399336208787565173981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44658266224139191710115987 66987399336208787565173981)
    ·
      refine ⟨25120274751078295336940243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66987399336208787565173981 25120274751078295336940243)
      ·
        refine ⟨37680412126617443005410365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25120274751078295336940243 37680412126617443005410365)
        ·
          refine ⟨14130154547481541127028887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37680412126617443005410365 14130154547481541127028887)
          ·
            refine ⟨21195231821222311690543331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14130154547481541127028887 21195231821222311690543331)
            ·
              refine ⟨31792847731833467535814997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21195231821222311690543331 31792847731833467535814997)
              ·
                refine ⟨93143108589355861921333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31792847731833467535814997 93143108589355861921333)
                ·
                  rfl

theorem cell22_2448840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 10].length) (baseStart_2448840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448840 prefixEnd_2448840 := by exact prefixLift 2448840
  have htrace : WordTrace (prefixWord ++ tailWord_2448840) baseStart_2448840 baseEnd_2448840 := by
    simpa [prefixWord, tailWord_2448840, baseEnd_2448840] using wordTrace_append hprefix tailTrace_2448840
  have hstable : (prefixWord ++ tailWord_2448840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448840).length < 2 ^ (prefixWord ++ tailWord_2448840).sum := by decide
  have hdescent : baseEnd_2448840 < baseStart_2448840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448842 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_2448842 : Nat := 118140960795 + 2448842 * 2 ^ 59
def prefixEnd_2448842 : Nat := 4983230072969 + 3 ^ 40 * 2448842 * 2
def baseEnd_2448842 : Nat := 838288661945075418741991

theorem tailTrace_2448842 : CollatzResearch.WordTrace tailWord_2448842 prefixEnd_2448842 838288661945075418741991 := by
  unfold tailWord_2448842
  simp only [CollatzResearch.WordTrace]
  refine ⟨22329151348567784440451195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59544403596180758507869853 22329151348567784440451195)
  ·
    refine ⟨33493727022851676660676793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22329151348567784440451195 33493727022851676660676793)
    ·
      refine ⟨25120295267138757495507595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33493727022851676660676793 25120295267138757495507595)
      ·
        refine ⟨37680442900708136243261393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25120295267138757495507595 37680442900708136243261393)
        ·
          refine ⟨28260332175531102182446045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37680442900708136243261393 28260332175531102182446045)
          ·
            refine ⟨10597624565824163318417267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28260332175531102182446045 10597624565824163318417267)
            ·
              refine ⟨15896436848736244977625901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10597624565824163318417267 15896436848736244977625901)
              ·
                refine ⟨5961163818276091866609713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15896436848736244977625901 5961163818276091866609713)
                ·
                  refine ⟨4470872863707068899957285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5961163818276091866609713 4470872863707068899957285)
                  ·
                    refine ⟨838288661945075418741991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4470872863707068899957285 838288661945075418741991)
                    ·
                      rfl

theorem cell22_2448842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_2448842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448842 prefixEnd_2448842 := by exact prefixLift 2448842
  have htrace : WordTrace (prefixWord ++ tailWord_2448842) baseStart_2448842 baseEnd_2448842 := by
    simpa [prefixWord, tailWord_2448842, baseEnd_2448842] using wordTrace_append hprefix tailTrace_2448842
  have hstable : (prefixWord ++ tailWord_2448842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448842).length < 2 ^ (prefixWord ++ tailWord_2448842).sum := by decide
  have hdescent : baseEnd_2448842 < baseStart_2448842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448861 : List Nat := [1, 4, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_2448861 : Nat := 118140960795 + 2448861 * 2 ^ 59
def prefixEnd_2448861 : Nat := 4983230072969 + 3 ^ 40 * 2448861 * 2
def baseEnd_2448861 : Nat := 838295166033365702516933

theorem tailTrace_2448861 : CollatzResearch.WordTrace tailWord_2448861 prefixEnd_2448861 838295166033365702516933 := by
  unfold tailWord_2448861
  simp only [CollatzResearch.WordTrace]
  refine ⟨89317298381202304006746437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59544865587468202671164291 89317298381202304006746437)
  ·
    refine ⟨16746993446475432001264957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89317298381202304006746437 16746993446475432001264957)
    ·
      refine ⟨6280122542428287000474359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16746993446475432001264957 6280122542428287000474359)
      ·
        refine ⟨9420183813642430500711539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6280122542428287000474359 9420183813642430500711539)
        ·
          refine ⟨14130275720463645751067309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9420183813642430500711539 14130275720463645751067309)
          ·
            refine ⟨5298853395173867156650241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14130275720463645751067309 5298853395173867156650241)
            ·
              refine ⟨3974140046380400367487681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5298853395173867156650241 3974140046380400367487681)
              ·
                refine ⟨2980605034785300275615761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3974140046380400367487681 2980605034785300275615761)
                ·
                  refine ⟨2235453776088975206711821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2980605034785300275615761 2235453776088975206711821)
                  ·
                    refine ⟨838295166033365702516933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235453776088975206711821 838295166033365702516933)
                    ·
                      rfl

theorem cell22_2448861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_2448861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448861 prefixEnd_2448861 := by exact prefixLift 2448861
  have htrace : WordTrace (prefixWord ++ tailWord_2448861) baseStart_2448861 baseEnd_2448861 := by
    simpa [prefixWord, tailWord_2448861, baseEnd_2448861] using wordTrace_append hprefix tailTrace_2448861
  have hstable : (prefixWord ++ tailWord_2448861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448861).length < 2 ^ (prefixWord ++ tailWord_2448861).sum := by decide
  have hdescent : baseEnd_2448861 < baseStart_2448861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448874 : List Nat := [3, 1, 3, 1, 4, 2, 1, 7]
def baseStart_2448874 : Nat := 118140960795 + 2448874 * 2 ^ 59
def prefixEnd_2448874 : Nat := 4983230072969 + 3 ^ 40 * 2448874 * 2
def baseEnd_2448874 : Nat := 93144401799893111326877

theorem tailTrace_2448874 : CollatzResearch.WordTrace tailWord_2448874 prefixEnd_2448874 93144401799893111326877 := by
  unfold tailWord_2448874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22329443132538801806742419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59545181686770138151313117 22329443132538801806742419)
  ·
    refine ⟨33494164698808202710113629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22329443132538801806742419 33494164698808202710113629)
    ·
      refine ⟨12560311762053076016292611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33494164698808202710113629 12560311762053076016292611)
      ·
        refine ⟨18840467643079614024438917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12560311762053076016292611 18840467643079614024438917)
        ·
          refine ⟨3532587683077427629582297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18840467643079614024438917 3532587683077427629582297)
          ·
            refine ⟨2649440762308070722186723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3532587683077427629582297 2649440762308070722186723)
            ·
              refine ⟨3974161143462106083280085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649440762308070722186723 3974161143462106083280085)
              ·
                refine ⟨93144401799893111326877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3974161143462106083280085 93144401799893111326877)
                ·
                  rfl

theorem cell22_2448874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_2448874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448874 prefixEnd_2448874 := by exact prefixLift 2448874
  have htrace : WordTrace (prefixWord ++ tailWord_2448874) baseStart_2448874 baseEnd_2448874 := by
    simpa [prefixWord, tailWord_2448874, baseEnd_2448874] using wordTrace_append hprefix tailTrace_2448874
  have hstable : (prefixWord ++ tailWord_2448874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448874).length < 2 ^ (prefixWord ++ tailWord_2448874).sum := by decide
  have hdescent : baseEnd_2448874 < baseStart_2448874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448906 : List Nat := [3, 1, 2, 2, 2, 2, 1, 5, 1, 3]
def baseStart_2448906 : Nat := 118140960795 + 2448906 * 2 ^ 59
def prefixEnd_2448906 : Nat := 4983230072969 + 3 ^ 40 * 2448906 * 2
def baseEnd_2448906 : Nat := 838310570453000585141795

theorem tailTrace_2448906 : CollatzResearch.WordTrace tailWord_2448906 prefixEnd_2448906 838310570453000585141795 := by
  unfold tailWord_2448906
  simp only [CollatzResearch.WordTrace]
  refine ⟨22329734916509819173033643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59545959777359517794756381 22329734916509819173033643)
  ·
    refine ⟨33494602374764728759550465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22329734916509819173033643 33494602374764728759550465)
    ·
      refine ⟨25120951781073546569662849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33494602374764728759550465 25120951781073546569662849)
      ·
        refine ⟨18840713835805159927247137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25120951781073546569662849 18840713835805159927247137)
        ·
          refine ⟨14130535376853869945435353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18840713835805159927247137 14130535376853869945435353)
          ·
            refine ⟨10597901532640402459076515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14130535376853869945435353 10597901532640402459076515)
            ·
              refine ⟨15896852298960603688614773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10597901532640402459076515 15896852298960603688614773)
              ·
                refine ⟨1490329903027556595807635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15896852298960603688614773 1490329903027556595807635)
                ·
                  refine ⟨2235494854541334893711453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490329903027556595807635 2235494854541334893711453)
                  ·
                    refine ⟨838310570453000585141795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235494854541334893711453 838310570453000585141795)
                    ·
                      rfl

theorem cell22_2448906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_2448906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448906 prefixEnd_2448906 := by exact prefixLift 2448906
  have htrace : WordTrace (prefixWord ++ tailWord_2448906) baseStart_2448906 baseEnd_2448906 := by
    simpa [prefixWord, tailWord_2448906, baseEnd_2448906] using wordTrace_append hprefix tailTrace_2448906
  have hstable : (prefixWord ++ tailWord_2448906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448906).length < 2 ^ (prefixWord ++ tailWord_2448906).sum := by decide
  have hdescent : baseEnd_2448906 < baseStart_2448906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448917 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_2448917 : Nat := 118140960795 + 2448917 * 2 ^ 59
def prefixEnd_2448917 : Nat := 4983230072969 + 3 ^ 40 * 2448917 * 2
def baseEnd_2448917 : Nat := 838314335977800223116761

theorem tailTrace_2448917 : CollatzResearch.WordTrace tailWord_2448917 prefixEnd_2448917 838314335977800223116761 := by
  unfold tailWord_2448917
  simp only [CollatzResearch.WordTrace]
  refine ⟨89319340868999425570785005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59546227245999617047190003 89319340868999425570785005)
  ·
    refine ⟨33494752825874784589044377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89319340868999425570785005 33494752825874784589044377)
    ·
      refine ⟨25121064619406088441783283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33494752825874784589044377 25121064619406088441783283)
      ·
        refine ⟨37681596929109132662674925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25121064619406088441783283 37681596929109132662674925)
        ·
          refine ⟨14130598848415924748503097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37681596929109132662674925 14130598848415924748503097)
          ·
            refine ⟨10597949136311943561377323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14130598848415924748503097 10597949136311943561377323)
            ·
              refine ⟨15896923704467915342065985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10597949136311943561377323 15896923704467915342065985)
              ·
                refine ⟨11922692778350936506549489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15896923704467915342065985 11922692778350936506549489)
                ·
                  refine ⟨8942019583763202379912117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11922692778350936506549489 8942019583763202379912117)
                  ·
                    refine ⟨838314335977800223116761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8942019583763202379912117 838314335977800223116761)
                    ·
                      rfl

theorem cell22_2448917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_2448917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448917 prefixEnd_2448917 := by exact prefixLift 2448917
  have htrace : WordTrace (prefixWord ++ tailWord_2448917) baseStart_2448917 baseEnd_2448917 := by
    simpa [prefixWord, tailWord_2448917, baseEnd_2448917] using wordTrace_append hprefix tailTrace_2448917
  have hstable : (prefixWord ++ tailWord_2448917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448917).length < 2 ^ (prefixWord ++ tailWord_2448917).sum := by decide
  have hdescent : baseEnd_2448917 < baseStart_2448917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448947 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 6]
def baseStart_2448947 : Nat := 118140960795 + 2448947 * 2 ^ 59
def prefixEnd_2448947 : Nat := 4983230072969 + 3 ^ 40 * 2448947 * 2
def baseEnd_2448947 : Nat := 279441535196963381622223

theorem tailTrace_2448947 : CollatzResearch.WordTrace tailWord_2448947 prefixEnd_2448947 279441535196963381622223 := by
  unfold tailWord_2448947
  simp only [CollatzResearch.WordTrace]
  refine ⟨89320435058890740694377095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59546956705927160462918063 89320435058890740694377095)
  ·
    refine ⟨133980652588336111041565643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89320435058890740694377095 133980652588336111041565643)
    ·
      refine ⟨200970978882504166562348465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133980652588336111041565643 200970978882504166562348465)
      ·
        refine ⟨150728234161878124921761349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200970978882504166562348465 150728234161878124921761349)
        ·
          refine ⟨28261543905352148422830253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150728234161878124921761349 28261543905352148422830253)
          ·
            refine ⟨10598078964507055658561345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28261543905352148422830253 10598078964507055658561345)
            ·
              refine ⟨7948559223380291743921009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10598078964507055658561345 7948559223380291743921009)
              ·
                refine ⟨5961419417535218807940757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7948559223380291743921009 5961419417535218807940757)
                ·
                  refine ⟨279441535196963381622223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5961419417535218807940757 279441535196963381622223)
                  ·
                    rfl

theorem cell22_2448947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 6].length) (baseStart_2448947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448947 prefixEnd_2448947 := by exact prefixLift 2448947
  have htrace : WordTrace (prefixWord ++ tailWord_2448947) baseStart_2448947 baseEnd_2448947 := by
    simpa [prefixWord, tailWord_2448947, baseEnd_2448947] using wordTrace_append hprefix tailTrace_2448947
  have hstable : (prefixWord ++ tailWord_2448947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448947).length < 2 ^ (prefixWord ++ tailWord_2448947).sum := by decide
  have hdescent : baseEnd_2448947 < baseStart_2448947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448949 : List Nat := [1, 3, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2448949 : Nat := 118140960795 + 2448949 * 2 ^ 59
def prefixEnd_2448949 : Nat := 4983230072969 + 3 ^ 40 * 2448949 * 2
def baseEnd_2448949 : Nat := 838325290231762806316663

theorem tailTrace_2448949 : CollatzResearch.WordTrace tailWord_2448949 prefixEnd_2448949 838325290231762806316663 := by
  unfold tailWord_2448949
  simp only [CollatzResearch.WordTrace]
  refine ⟨89320508004883495035949901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59547005336588996690633267 89320508004883495035949901)
  ·
    refine ⟨33495190501831310638481213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89320508004883495035949901 33495190501831310638481213)
    ·
      refine ⟨12560696438186741489430455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33495190501831310638481213 12560696438186741489430455)
      ·
        refine ⟨18841044657280112234145683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12560696438186741489430455 18841044657280112234145683)
        ·
          refine ⟨28261566985920168351218525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18841044657280112234145683 28261566985920168351218525)
          ·
            refine ⟨10598087619720063131706947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28261566985920168351218525 10598087619720063131706947)
            ·
              refine ⟨15897131429580094697560421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10598087619720063131706947 15897131429580094697560421)
              ·
                refine ⟨2980712143046267755792579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15897131429580094697560421 2980712143046267755792579)
                ·
                  refine ⟨4471068214569401633688869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2980712143046267755792579 4471068214569401633688869)
                  ·
                    refine ⟨838325290231762806316663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4471068214569401633688869 838325290231762806316663)
                    ·
                      rfl

theorem cell22_2448949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2448949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448949 prefixEnd_2448949 := by exact prefixLift 2448949
  have htrace : WordTrace (prefixWord ++ tailWord_2448949) baseStart_2448949 baseEnd_2448949 := by
    simpa [prefixWord, tailWord_2448949, baseEnd_2448949] using wordTrace_append hprefix tailTrace_2448949
  have hstable : (prefixWord ++ tailWord_2448949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448949).length < 2 ^ (prefixWord ++ tailWord_2448949).sum := by decide
  have hdescent : baseEnd_2448949 < baseStart_2448949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448996 : List Nat := [2, 3, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_2448996 : Nat := 118140960795 + 2448996 * 2 ^ 59
def prefixEnd_2448996 : Nat := 4983230072969 + 3 ^ 40 * 2448996 * 2
def baseEnd_2448996 : Nat := 838341379292270350391519

theorem tailTrace_2448996 : CollatzResearch.WordTrace tailWord_2448996 prefixEnd_2448996 838341379292270350391519 := by
  unfold tailWord_2448996
  simp only [CollatzResearch.WordTrace]
  refine ⟨44661111117856611031455421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59548148157142148041940561 44661111117856611031455421)
  ·
    refine ⟨16747916669196229136795783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44661111117856611031455421 16747916669196229136795783)
    ·
      refine ⟨25121875003794343705193675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16747916669196229136795783 25121875003794343705193675)
      ·
        refine ⟨37682812505691515557790513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25121875003794343705193675 37682812505691515557790513)
        ·
          refine ⟨28262109379268636668342885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37682812505691515557790513 28262109379268636668342885)
          ·
            refine ⟨5299145508612869375314291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28262109379268636668342885 5299145508612869375314291)
            ·
              refine ⟨7948718262919304062971437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5299145508612869375314291 7948718262919304062971437)
              ·
                refine ⟨2980769348594739023614289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7948718262919304062971437 2980769348594739023614289)
                ·
                  refine ⟨2235577011446054267710717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2980769348594739023614289 2235577011446054267710717)
                  ·
                    refine ⟨838341379292270350391519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235577011446054267710717 838341379292270350391519)
                    ·
                      rfl

theorem cell22_2448996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_2448996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2448996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2448996 prefixEnd_2448996 := by exact prefixLift 2448996
  have htrace : WordTrace (prefixWord ++ tailWord_2448996) baseStart_2448996 baseEnd_2448996 := by
    simpa [prefixWord, tailWord_2448996, baseEnd_2448996] using wordTrace_append hprefix tailTrace_2448996
  have hstable : (prefixWord ++ tailWord_2448996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448996).length < 2 ^ (prefixWord ++ tailWord_2448996).sum := by decide
  have hdescent : baseEnd_2448996 < baseStart_2448996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449032 : List Nat := [2, 1, 3, 5, 2, 1, 2, 2, 4]
def baseStart_2449032 : Nat := 118140960795 + 2449032 * 2 ^ 59
def prefixEnd_2449032 : Nat := 4983230072969 + 3 ^ 40 * 2449032 * 2
def baseEnd_2449032 : Nat := 279451234275992752163803

theorem tailTrace_2449032 : CollatzResearch.WordTrace tailWord_2449032 prefixEnd_2449032 279451234275992752163803 := by
  unfold tailWord_2449032
  simp only [CollatzResearch.WordTrace]
  refine ⟨44661767631791400105610675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59549023509055200140814233 44661767631791400105610675)
  ·
    refine ⟨66992651447687100158416013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44661767631791400105610675 66992651447687100158416013)
    ·
      refine ⟨25122244292882662559406005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66992651447687100158416013 25122244292882662559406005)
      ·
        refine ⟨2355210402457749614944313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25122244292882662559406005 2355210402457749614944313)
        ·
          refine ⟨1766407801843312211208235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2355210402457749614944313 1766407801843312211208235)
          ·
            refine ⟨2649611702764968316812353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766407801843312211208235 2649611702764968316812353)
            ·
              refine ⟨1987208777073726237609265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2649611702764968316812353 1987208777073726237609265)
              ·
                refine ⟨1490406582805294678206949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1987208777073726237609265 1490406582805294678206949)
                ·
                  refine ⟨279451234275992752163803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1490406582805294678206949 279451234275992752163803)
                  ·
                    rfl

theorem cell22_2449032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 4].length) (baseStart_2449032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449032 prefixEnd_2449032 := by exact prefixLift 2449032
  have htrace : WordTrace (prefixWord ++ tailWord_2449032) baseStart_2449032 baseEnd_2449032 := by
    simpa [prefixWord, tailWord_2449032, baseEnd_2449032] using wordTrace_append hprefix tailTrace_2449032
  have hstable : (prefixWord ++ tailWord_2449032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449032).length < 2 ^ (prefixWord ++ tailWord_2449032).sum := by decide
  have hdescent : baseEnd_2449032 < baseStart_2449032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449069 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2449069 : Nat := 118140960795 + 2449069 * 2 ^ 59
def prefixEnd_2449069 : Nat := 4983230072969 + 3 ^ 40 * 2449069 * 2
def baseEnd_2449069 : Nat := 838366368684122493316295

theorem tailTrace_2449069 : CollatzResearch.WordTrace tailWord_2449069 prefixEnd_2449069 838366368684122493316295 := by
  unfold tailWord_2449069
  simp only [CollatzResearch.WordTrace]
  refine ⟨89324884764448755530318261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59549923176299170353545507 89324884764448755530318261)
  ·
    refine ⟨8374207946667070830967337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89324884764448755530318261 8374207946667070830967337)
    ·
      refine ⟨6280655960000303123225503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8374207946667070830967337 6280655960000303123225503)
      ·
        refine ⟨9420983940000454684838255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6280655960000303123225503 9420983940000454684838255)
        ·
          refine ⟨14131475910000682027257383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9420983940000454684838255 14131475910000682027257383)
          ·
            refine ⟨21197213865001023040886075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14131475910000682027257383 21197213865001023040886075)
            ·
              refine ⟨31795820797501534561329113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21197213865001023040886075 31795820797501534561329113)
              ·
                refine ⟨23846865598126150920996835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31795820797501534561329113 23846865598126150920996835)
                ·
                  refine ⟨35770298397189226381495253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23846865598126150920996835 35770298397189226381495253)
                  ·
                    refine ⟨838366368684122493316295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35770298397189226381495253 838366368684122493316295)
                    ·
                      rfl

theorem cell22_2449069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2449069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449069 prefixEnd_2449069 := by exact prefixLift 2449069
  have htrace : WordTrace (prefixWord ++ tailWord_2449069) baseStart_2449069 baseEnd_2449069 := by
    simpa [prefixWord, tailWord_2449069, baseEnd_2449069] using wordTrace_append hprefix tailTrace_2449069
  have hstable : (prefixWord ++ tailWord_2449069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449069).length < 2 ^ (prefixWord ++ tailWord_2449069).sum := by decide
  have hdescent : baseEnd_2449069 < baseStart_2449069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449097 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 1, 11]
def baseStart_2449097 : Nat := 118140960795 + 2449097 * 2 ^ 59
def prefixEnd_2449097 : Nat := 4983230072969 + 3 ^ 40 * 2449097 * 2
def baseEnd_2449097 : Nat := 838375953656339753616209

theorem tailTrace_2449097 : CollatzResearch.WordTrace tailWord_2449097 prefixEnd_2449097 838375953656339753616209 := by
  unfold tailWord_2449097
  simp only [CollatzResearch.WordTrace]
  refine ⟨89325906008347316312337545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59550604005564877541558363 89325906008347316312337545)
  ·
    refine ⟨66994429506260487234253159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89325906008347316312337545 66994429506260487234253159)
    ·
      refine ⟨100491644259390730851379739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66994429506260487234253159 100491644259390730851379739)
      ·
        refine ⟨150737466389086096277069609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100491644259390730851379739 150737466389086096277069609)
        ·
          refine ⟨113053099791814572207802207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150737466389086096277069609 113053099791814572207802207)
          ·
            refine ⟨169579649687721858311703311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113053099791814572207802207 169579649687721858311703311)
            ·
              refine ⟨254369474531582787467554967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169579649687721858311703311 254369474531582787467554967)
              ·
                refine ⟨381554211797374181201332451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254369474531582787467554967 381554211797374181201332451)
                ·
                  refine ⟨572331317696061271801998677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381554211797374181201332451 572331317696061271801998677)
                  ·
                    refine ⟨838375953656339753616209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 572331317696061271801998677 838375953656339753616209)
                    ·
                      rfl

theorem cell22_2449097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_2449097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449097 prefixEnd_2449097 := by exact prefixLift 2449097
  have htrace : WordTrace (prefixWord ++ tailWord_2449097) baseStart_2449097 baseEnd_2449097 := by
    simpa [prefixWord, tailWord_2449097, baseEnd_2449097] using wordTrace_append hprefix tailTrace_2449097
  have hstable : (prefixWord ++ tailWord_2449097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449097).length < 2 ^ (prefixWord ++ tailWord_2449097).sum := by decide
  have hdescent : baseEnd_2449097 < baseStart_2449097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449129 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 2, 4]
def baseStart_2449129 : Nat := 118140960795 + 2449129 * 2 ^ 59
def prefixEnd_2449129 : Nat := 4983230072969 + 3 ^ 40 * 2449129 * 2
def baseEnd_2449129 : Nat := 838386907910302336816111

theorem tailTrace_2449129 : CollatzResearch.WordTrace tailWord_2449129 prefixEnd_2449129 838386907910302336816111 := by
  unfold tailWord_2449129
  simp only [CollatzResearch.WordTrace]
  refine ⟨89327073144231385777502441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59551382096154257185001627 89327073144231385777502441)
  ·
    refine ⟨66995304858173539333126831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89327073144231385777502441 66995304858173539333126831)
    ·
      refine ⟨100492957287260308999690247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66995304858173539333126831 100492957287260308999690247)
      ·
        refine ⟨150739435930890463499535371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100492957287260308999690247 150739435930890463499535371)
        ·
          refine ⟨226109153896335695249303057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150739435930890463499535371 226109153896335695249303057)
          ·
            refine ⟨169581865422251771436977293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226109153896335695249303057 169581865422251771436977293)
            ·
              refine ⟨63593199533344414288866485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169581865422251771436977293 63593199533344414288866485)
              ·
                refine ⟨5961862456251038839581233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63593199533344414288866485 5961862456251038839581233)
                ·
                  refine ⟨4471396842188279129685925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5961862456251038839581233 4471396842188279129685925)
                  ·
                    refine ⟨838386907910302336816111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4471396842188279129685925 838386907910302336816111)
                    ·
                      rfl

theorem cell22_2449129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_2449129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449129 prefixEnd_2449129 := by exact prefixLift 2449129
  have htrace : WordTrace (prefixWord ++ tailWord_2449129) baseStart_2449129 baseEnd_2449129 := by
    simpa [prefixWord, tailWord_2449129, baseEnd_2449129] using wordTrace_append hprefix tailTrace_2449129
  have hstable : (prefixWord ++ tailWord_2449129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449129).length < 2 ^ (prefixWord ++ tailWord_2449129).sum := by decide
  have hdescent : baseEnd_2449129 < baseStart_2449129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449133 : List Nat := [1, 5, 1, 2, 1, 2, 3, 3, 4]
def baseStart_2449133 : Nat := 118140960795 + 2449133 * 2 ^ 59
def prefixEnd_2449133 : Nat := 4983230072969 + 3 ^ 40 * 2449133 * 2
def baseEnd_2449133 : Nat := 279462759064015886572033

theorem tailTrace_2449133 : CollatzResearch.WordTrace tailWord_2449133 prefixEnd_2449133 279462759064015886572033 := by
  unfold tailWord_2449133
  simp only [CollatzResearch.WordTrace]
  refine ⟨89327219036216894460648053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59551479357477929640432035 89327219036216894460648053)
  ·
    refine ⟨8374426784645333855685755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89327219036216894460648053 8374426784645333855685755)
    ·
      refine ⟨12561640176968000783528633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8374426784645333855685755 12561640176968000783528633)
      ·
        refine ⟨9421230132726000587646475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12561640176968000783528633 9421230132726000587646475)
        ·
          refine ⟨14131845199089000881469713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9421230132726000587646475 14131845199089000881469713)
          ·
            refine ⟨10598883899316750661102285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14131845199089000881469713 10598883899316750661102285)
            ·
              refine ⟨3974581462243781497913357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10598883899316750661102285 3974581462243781497913357)
              ·
                refine ⟨1490468048341418061717509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3974581462243781497913357 1490468048341418061717509)
                ·
                  refine ⟨279462759064015886572033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1490468048341418061717509 279462759064015886572033)
                  ·
                    rfl

theorem cell22_2449133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_2449133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449133 prefixEnd_2449133 := by exact prefixLift 2449133
  have htrace : WordTrace (prefixWord ++ tailWord_2449133) baseStart_2449133 baseEnd_2449133 := by
    simpa [prefixWord, tailWord_2449133, baseEnd_2449133] using wordTrace_append hprefix tailTrace_2449133
  have hstable : (prefixWord ++ tailWord_2449133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449133).length < 2 ^ (prefixWord ++ tailWord_2449133).sum := by decide
  have hdescent : baseEnd_2449133 < baseStart_2449133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449150 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_2449150 : Nat := 118140960795 + 2449150 * 2 ^ 59
def prefixEnd_2449150 : Nat := 4983230072969 + 3 ^ 40 * 2449150 * 2
def baseEnd_2449150 : Nat := 279464698879821760680349

theorem tailTrace_2449150 : CollatzResearch.WordTrace tailWord_2449150 prefixEnd_2449150 279464698879821760680349 := by
  unfold tailWord_2449150
  simp only [CollatzResearch.WordTrace]
  refine ⟨11165979884644413295502113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59551892718103537576011269 11165979884644413295502113)
  ·
    refine ⟨8374484913483309971626585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11165979884644413295502113 8374484913483309971626585)
    ·
      refine ⟨6280863685112482478719939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8374484913483309971626585 6280863685112482478719939)
      ·
        refine ⟨9421295527668723718079909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6280863685112482478719939 9421295527668723718079909)
        ·
          refine ⟨1766492911437885697139983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9421295527668723718079909 1766492911437885697139983)
          ·
            refine ⟨2649739367156828545709975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766492911437885697139983 2649739367156828545709975)
            ·
              refine ⟨3974609050735242818564963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649739367156828545709975 3974609050735242818564963)
              ·
                refine ⟨5961913576102864227847445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974609050735242818564963 5961913576102864227847445)
                ·
                  refine ⟨279464698879821760680349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5961913576102864227847445 279464698879821760680349)
                  ·
                    rfl

theorem cell22_2449150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_2449150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449150 prefixEnd_2449150 := by exact prefixLift 2449150
  have htrace : WordTrace (prefixWord ++ tailWord_2449150) baseStart_2449150 baseEnd_2449150 := by
    simpa [prefixWord, tailWord_2449150, baseEnd_2449150] using wordTrace_append hprefix tailTrace_2449150
  have hstable : (prefixWord ++ tailWord_2449150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449150).length < 2 ^ (prefixWord ++ tailWord_2449150).sum := by decide
  have hdescent : baseEnd_2449150 < baseStart_2449150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449176 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 3, 3]
def baseStart_2449176 : Nat := 118140960795 + 2449176 * 2 ^ 59
def prefixEnd_2449176 : Nat := 4983230072969 + 3 ^ 40 * 2449176 * 2
def baseEnd_2449176 : Nat := 838402996970809880890967

theorem tailTrace_2449176 : CollatzResearch.WordTrace tailWord_2449176 prefixEnd_2449176 838402996970809880890967 := by
  unfold tailWord_2449176
  simp only [CollatzResearch.WordTrace]
  refine ⟨44664393687530556402231691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59552524916707408536308921 44664393687530556402231691)
  ·
    refine ⟨66996590531295834603347537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44664393687530556402231691 66996590531295834603347537)
    ·
      refine ⟨50247442898471875952510653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66996590531295834603347537 50247442898471875952510653)
      ·
        refine ⟨18842791086926953482191495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50247442898471875952510653 18842791086926953482191495)
        ·
          refine ⟨28264186630390430223287243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18842791086926953482191495 28264186630390430223287243)
          ·
            refine ⟨42396279945585645334930865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28264186630390430223287243 42396279945585645334930865)
            ·
              refine ⟨31797209959189234001198149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42396279945585645334930865 31797209959189234001198149)
              ·
                refine ⟨5961976867347981375224653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31797209959189234001198149 5961976867347981375224653)
                ·
                  refine ⟨2235741325255493015709245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5961976867347981375224653 2235741325255493015709245)
                  ·
                    refine ⟨838402996970809880890967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235741325255493015709245 838402996970809880890967)
                    ·
                      rfl

theorem cell22_2449176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_2449176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449176 prefixEnd_2449176 := by exact prefixLift 2449176
  have htrace : WordTrace (prefixWord ++ tailWord_2449176) baseStart_2449176 baseEnd_2449176 := by
    simpa [prefixWord, tailWord_2449176, baseEnd_2449176] using wordTrace_append hprefix tailTrace_2449176
  have hstable : (prefixWord ++ tailWord_2449176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449176).length < 2 ^ (prefixWord ++ tailWord_2449176).sum := by decide
  have hdescent : baseEnd_2449176 < baseStart_2449176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449210 : List Nat := [3, 1, 1, 1, 5, 2, 1, 4, 1, 3]
def baseStart_2449210 : Nat := 118140960795 + 2449210 * 2 ^ 59
def prefixEnd_2449210 : Nat := 4983230072969 + 3 ^ 40 * 2449210 * 2
def baseEnd_2449210 : Nat := 838414635865645125540863

theorem tailTrace_2449210 : CollatzResearch.WordTrace tailWord_2449210 prefixEnd_2449210 838414635865645125540863 := by
  unfold tailWord_2449210
  simp only [CollatzResearch.WordTrace]
  refine ⟨22332506864234484152800271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59553351637958624407467389 22332506864234484152800271)
  ·
    refine ⟨33498760296351726229200407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22332506864234484152800271 33498760296351726229200407)
    ·
      refine ⟨50248140444527589343800611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33498760296351726229200407 50248140444527589343800611)
      ·
        refine ⟨75372210666791384015700917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50248140444527589343800611 75372210666791384015700917)
        ·
          refine ⟨7066144750011692251471961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75372210666791384015700917 7066144750011692251471961)
          ·
            refine ⟨5299608562508769188603971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7066144750011692251471961 5299608562508769188603971)
            ·
              refine ⟨7949412843763153782905957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5299608562508769188603971 7949412843763153782905957)
              ·
                refine ⟨1490514908205591334294867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7949412843763153782905957 1490514908205591334294867)
                ·
                  refine ⟨2235772362308387001442301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490514908205591334294867 2235772362308387001442301)
                  ·
                    refine ⟨838414635865645125540863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235772362308387001442301 838414635865645125540863)
                    ·
                      rfl

theorem cell22_2449210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_2449210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449210 prefixEnd_2449210 := by exact prefixLift 2449210
  have htrace : WordTrace (prefixWord ++ tailWord_2449210) baseStart_2449210 baseEnd_2449210 := by
    simpa [prefixWord, tailWord_2449210, baseEnd_2449210] using wordTrace_append hprefix tailTrace_2449210
  have hstable : (prefixWord ++ tailWord_2449210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449210).length < 2 ^ (prefixWord ++ tailWord_2449210).sum := by decide
  have hdescent : baseEnd_2449210 < baseStart_2449210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449279 : List Nat := [1, 1, 2, 2, 1, 1, 3, 11]
def baseStart_2449279 : Nat := 118140960795 + 2449279 * 2 ^ 59
def prefixEnd_2449279 : Nat := 4983230072969 + 3 ^ 40 * 2449279 * 2
def baseEnd_2449279 : Nat := 93159806219527993951739

theorem tailTrace_2449279 : CollatzResearch.WordTrace tailWord_2449279 prefixEnd_2449279 93159806219527993951739 := by
  unfold tailWord_2449279
  simp only [CollatzResearch.WordTrace]
  refine ⟨89332544093687961395462891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59555029395791974263641927 89332544093687961395462891)
  ·
    refine ⟨133998816140531942093194337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89332544093687961395462891 133998816140531942093194337)
    ·
      refine ⟨100499112105398956569895753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133998816140531942093194337 100499112105398956569895753)
      ·
        refine ⟨75374334079049217427421815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100499112105398956569895753 75374334079049217427421815)
        ·
          refine ⟨113061501118573826141132723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75374334079049217427421815 113061501118573826141132723)
          ·
            refine ⟨169592251677860739211699085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113061501118573826141132723 169592251677860739211699085)
            ·
              refine ⟨63597094379197777204387157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169592251677860739211699085 63597094379197777204387157)
              ·
                refine ⟨93159806219527993951739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 63597094379197777204387157 93159806219527993951739)
                ·
                  rfl

theorem cell22_2449279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 11].length) (baseStart_2449279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449279 prefixEnd_2449279 := by exact prefixLift 2449279
  have htrace : WordTrace (prefixWord ++ tailWord_2449279) baseStart_2449279 baseEnd_2449279 := by
    simpa [prefixWord, tailWord_2449279, baseEnd_2449279] using wordTrace_append hprefix tailTrace_2449279
  have hstable : (prefixWord ++ tailWord_2449279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449279).length < 2 ^ (prefixWord ++ tailWord_2449279).sum := by decide
  have hdescent : baseEnd_2449279 < baseStart_2449279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449283 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 1, 5]
def baseStart_2449283 : Nat := 118140960795 + 2449283 * 2 ^ 59
def prefixEnd_2449283 : Nat := 4983230072969 + 3 ^ 40 * 2449283 * 2
def baseEnd_2449283 : Nat := 838439625257497268465639

theorem tailTrace_2449283 : CollatzResearch.WordTrace tailWord_2449283 prefixEnd_2449283 838439625257497268465639 := by
  unfold tailWord_2449283
  simp only [CollatzResearch.WordTrace]
  refine ⟨89332689985673470078608503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59555126657115646719072335 89332689985673470078608503)
  ·
    refine ⟨133999034978510205117912755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89332689985673470078608503 133999034978510205117912755)
    ·
      refine ⟨200998552467765307676869133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133999034978510205117912755 200998552467765307676869133)
      ·
        refine ⟨75374457175411990378825925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200998552467765307676869133 75374457175411990378825925)
        ·
          refine ⟨14132710720389748196029861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75374457175411990378825925 14132710720389748196029861)
          ·
            refine ⟨2649883260073077786755599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14132710720389748196029861 2649883260073077786755599)
            ·
              refine ⟨3974824890109616680133399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649883260073077786755599 3974824890109616680133399)
              ·
                refine ⟨5962237335164425020200099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974824890109616680133399 5962237335164425020200099)
                ·
                  refine ⟨8943356002746637530300149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5962237335164425020200099 8943356002746637530300149)
                  ·
                    refine ⟨838439625257497268465639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8943356002746637530300149 838439625257497268465639)
                    ·
                      rfl

theorem cell22_2449283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 5].length) (baseStart_2449283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449283 prefixEnd_2449283 := by exact prefixLift 2449283
  have htrace : WordTrace (prefixWord ++ tailWord_2449283) baseStart_2449283 baseEnd_2449283 := by
    simpa [prefixWord, tailWord_2449283, baseEnd_2449283] using wordTrace_append hprefix tailTrace_2449283
  have hstable : (prefixWord ++ tailWord_2449283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449283).length < 2 ^ (prefixWord ++ tailWord_2449283).sum := by decide
  have hdescent : baseEnd_2449283 < baseStart_2449283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449298 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2449298 : Nat := 118140960795 + 2449298 * 2 ^ 59
def prefixEnd_2449298 : Nat := 4983230072969 + 3 ^ 40 * 2449298 * 2
def baseEnd_2449298 : Nat := 838444760064042229340593

theorem tailTrace_2449298 : CollatzResearch.WordTrace tailWord_2449298 prefixEnd_2449298 838444760064042229340593 := by
  unfold tailWord_2449298
  simp only [CollatzResearch.WordTrace]
  refine ⟨22333309270154781910101137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59555491387079418426936365 22333309270154781910101137)
  ·
    refine ⟨16749981952616086432575853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22333309270154781910101137 16749981952616086432575853)
    ·
      refine ⟨6281243232231032412215945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16749981952616086432575853 6281243232231032412215945)
      ·
        refine ⟨4710932424173274309161959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6281243232231032412215945 4710932424173274309161959)
        ·
          refine ⟨7066398636259911463742939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4710932424173274309161959 7066398636259911463742939)
          ·
            refine ⟨10599597954389867195614409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7066398636259911463742939 10599597954389867195614409)
            ·
              refine ⟨7949698465792400396710807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10599597954389867195614409 7949698465792400396710807)
              ·
                refine ⟨11924547698688600595066211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7949698465792400396710807 11924547698688600595066211)
                ·
                  refine ⟨17886821548032900892599317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11924547698688600595066211 17886821548032900892599317)
                  ·
                    refine ⟨838444760064042229340593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17886821548032900892599317 838444760064042229340593)
                    ·
                      rfl

theorem cell22_2449298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2449298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449298 prefixEnd_2449298 := by exact prefixLift 2449298
  have htrace : WordTrace (prefixWord ++ tailWord_2449298) baseStart_2449298 baseEnd_2449298 := by
    simpa [prefixWord, tailWord_2449298, baseEnd_2449298] using wordTrace_append hprefix tailTrace_2449298
  have hstable : (prefixWord ++ tailWord_2449298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449298).length < 2 ^ (prefixWord ++ tailWord_2449298).sum := by decide
  have hdescent : baseEnd_2449298 < baseStart_2449298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449313 : List Nat := [1, 2, 3, 4, 2, 2, 8]
def baseStart_2449313 : Nat := 118140960795 + 2449313 * 2 ^ 59
def prefixEnd_2449313 : Nat := 4983230072969 + 3 ^ 40 * 2449313 * 2
def baseEnd_2449313 : Nat := 31053699810021747785761

theorem tailTrace_2449313 : CollatzResearch.WordTrace tailWord_2449313 prefixEnd_2449313 31053699810021747785761 := by
  unfold tailWord_2449313
  simp only [CollatzResearch.WordTrace]
  refine ⟨89333784175564785202200593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59555856117043190134800395 89333784175564785202200593)
  ·
    refine ⟨67000338131673588901650445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89333784175564785202200593 67000338131673588901650445)
    ·
      refine ⟨25125126799377595838118917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67000338131673588901650445 25125126799377595838118917)
      ·
        refine ⟨4710961274883299219647297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25125126799377595838118917 4710961274883299219647297)
        ·
          refine ⟨3533220956162474414735473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4710961274883299219647297 3533220956162474414735473)
          ·
            refine ⟨2649915717121855811051605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3533220956162474414735473 2649915717121855811051605)
            ·
              refine ⟨31053699810021747785761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2649915717121855811051605 31053699810021747785761)
              ·
                rfl

theorem cell22_2449313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 8].length) (baseStart_2449313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449313 prefixEnd_2449313 := by exact prefixLift 2449313
  have htrace : WordTrace (prefixWord ++ tailWord_2449313) baseStart_2449313 baseEnd_2449313 := by
    simpa [prefixWord, tailWord_2449313, baseEnd_2449313] using wordTrace_append hprefix tailTrace_2449313
  have hstable : (prefixWord ++ tailWord_2449313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449313).length < 2 ^ (prefixWord ++ tailWord_2449313).sum := by decide
  have hdescent : baseEnd_2449313 < baseStart_2449313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449379 : List Nat := [1, 1, 1, 6, 1, 4, 2, 2, 1, 3]
def baseStart_2449379 : Nat := 118140960795 + 2449379 * 2 ^ 59
def prefixEnd_2449379 : Nat := 4983230072969 + 3 ^ 40 * 2449379 * 2
def baseEnd_2449379 : Nat := 838472488019385018065345

theorem tailTrace_2449379 : CollatzResearch.WordTrace tailWord_2449379 prefixEnd_2449379 838472488019385018065345 := by
  unfold tailWord_2449379
  simp only [CollatzResearch.WordTrace]
  refine ⟨89336191393325678474103191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59557460928883785649402127 89336191393325678474103191)
  ·
    refine ⟨134004287089988517711154787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89336191393325678474103191 134004287089988517711154787)
    ·
      refine ⟨201006430634982776566732181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134004287089988517711154787 201006430634982776566732181)
      ·
        refine ⟨9422176436014817651565571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 201006430634982776566732181 9422176436014817651565571)
        ·
          refine ⟨14133264654022226477348357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9422176436014817651565571 14133264654022226477348357)
          ·
            refine ⟨2649987122629167464502817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14133264654022226477348357 2649987122629167464502817)
            ·
              refine ⟨1987490341971875598377113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2649987122629167464502817 1987490341971875598377113)
              ·
                refine ⟨1490617756478906698782835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1987490341971875598377113 1490617756478906698782835)
                ·
                  refine ⟨2235926634718360048174253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490617756478906698782835 2235926634718360048174253)
                  ·
                    refine ⟨838472488019385018065345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2235926634718360048174253 838472488019385018065345)
                    ·
                      rfl

theorem cell22_2449379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 1, 3].length) (baseStart_2449379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449379 prefixEnd_2449379 := by exact prefixLift 2449379
  have htrace : WordTrace (prefixWord ++ tailWord_2449379) baseStart_2449379 baseEnd_2449379 := by
    simpa [prefixWord, tailWord_2449379, baseEnd_2449379] using wordTrace_append hprefix tailTrace_2449379
  have hstable : (prefixWord ++ tailWord_2449379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449379).length < 2 ^ (prefixWord ++ tailWord_2449379).sum := by decide
  have hdescent : baseEnd_2449379 < baseStart_2449379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449420 : List Nat := [2, 2, 1, 2, 3, 1, 4, 3, 4]
def baseStart_2449420 : Nat := 118140960795 + 2449420 * 2 ^ 59
def prefixEnd_2449420 : Nat := 4983230072969 + 3 ^ 40 * 2449420 * 2
def baseEnd_2449420 : Nat := 279495507719091525930073

theorem tailTrace_2449420 : CollatzResearch.WordTrace tailWord_2449420 prefixEnd_2449420 279495507719091525930073 := by
  unfold tailWord_2449420
  simp only [CollatzResearch.WordTrace]
  refine ⟨44668843393088571238172857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59558457857451428317563809 44668843393088571238172857)
  ·
    refine ⟨33501632544816428428629643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44668843393088571238172857 33501632544816428428629643)
    ·
      refine ⟨50252448817224642642944465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33501632544816428428629643 50252448817224642642944465)
      ·
        refine ⟨37689336612918481982208349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50252448817224642642944465 37689336612918481982208349)
        ·
          refine ⟨14133501229844430743328131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37689336612918481982208349 14133501229844430743328131)
          ·
            refine ⟨21200251844766646114992197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14133501229844430743328131 21200251844766646114992197)
            ·
              refine ⟨3975047220893746146561037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21200251844766646114992197 3975047220893746146561037)
              ·
                refine ⟨1490642707835154804960389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3975047220893746146561037 1490642707835154804960389)
                ·
                  refine ⟨279495507719091525930073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1490642707835154804960389 279495507719091525930073)
                  ·
                    rfl

theorem cell22_2449420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_2449420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449420 prefixEnd_2449420 := by exact prefixLift 2449420
  have htrace : WordTrace (prefixWord ++ tailWord_2449420) baseStart_2449420 baseEnd_2449420 := by
    simpa [prefixWord, tailWord_2449420, baseEnd_2449420] using wordTrace_append hprefix tailTrace_2449420
  have hstable : (prefixWord ++ tailWord_2449420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449420).length < 2 ^ (prefixWord ++ tailWord_2449420).sum := by decide
  have hdescent : baseEnd_2449420 < baseStart_2449420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449493 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 7]
def baseStart_2449493 : Nat := 118140960795 + 2449493 * 2 ^ 59
def prefixEnd_2449493 : Nat := 4983230072969 + 3 ^ 40 * 2449493 * 2
def baseEnd_2449493 : Nat := 279503837516375573571665

theorem tailTrace_2449493 : CollatzResearch.WordTrace tailWord_2449493 prefixEnd_2449493 279503837516375573571665 := by
  unfold tailWord_2449493
  simp only [CollatzResearch.WordTrace]
  refine ⟨89340349314912675943753133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59560232876608450629168755 89340349314912675943753133)
  ·
    refine ⟨33502630993092253478907425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89340349314912675943753133 33502630993092253478907425)
    ·
      refine ⟨25126973244819190109180569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33502630993092253478907425 25126973244819190109180569)
      ·
        refine ⟨18845229933614392581885427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25126973244819190109180569 18845229933614392581885427)
        ·
          refine ⟨28267844900421588872828141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18845229933614392581885427 28267844900421588872828141)
          ·
            refine ⟨10600441837658095827310553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28267844900421588872828141 10600441837658095827310553)
            ·
              refine ⟨7950331378243571870482915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10600441837658095827310553 7950331378243571870482915)
              ·
                refine ⟨11925497067365357805724373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7950331378243571870482915 11925497067365357805724373)
                ·
                  refine ⟨279503837516375573571665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11925497067365357805724373 279503837516375573571665)
                  ·
                    rfl

theorem cell22_2449493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_2449493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449493 prefixEnd_2449493 := by exact prefixLift 2449493
  have htrace : WordTrace (prefixWord ++ tailWord_2449493) baseStart_2449493 baseEnd_2449493 := by
    simpa [prefixWord, tailWord_2449493, baseEnd_2449493] using wordTrace_append hprefix tailTrace_2449493
  have hstable : (prefixWord ++ tailWord_2449493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449493).length < 2 ^ (prefixWord ++ tailWord_2449493).sum := by decide
  have hdescent : baseEnd_2449493 < baseStart_2449493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449508 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_2449508 : Nat := 118140960795 + 2449508 * 2 ^ 59
def prefixEnd_2449508 : Nat := 4983230072969 + 3 ^ 40 * 2449508 * 2
def baseEnd_2449508 : Nat := 838516647355671681589949

theorem tailTrace_2449508 : CollatzResearch.WordTrace tailWord_2449508 prefixEnd_2449508 838516647355671681589949 := by
  unfold tailWord_2449508
  simp only [CollatzResearch.WordTrace]
  refine ⟨44670448204929166752774589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59560597606572222337032785 44670448204929166752774589)
  ·
    refine ⟨16751418076848437532290471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44670448204929166752774589 16751418076848437532290471)
    ·
      refine ⟨25127127115272656298435707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16751418076848437532290471 25127127115272656298435707)
      ·
        refine ⟨37690690672908984447653561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25127127115272656298435707 37690690672908984447653561)
        ·
          refine ⟨28268018004681738335740171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37690690672908984447653561 28268018004681738335740171)
          ·
            refine ⟨42402027007022607503610257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28268018004681738335740171 42402027007022607503610257)
            ·
              refine ⟨31801520255266955627707693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42402027007022607503610257 31801520255266955627707693)
              ·
                refine ⟨11925570095725108360390385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31801520255266955627707693 11925570095725108360390385)
                ·
                  refine ⟨8944177571793831270292789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11925570095725108360390385 8944177571793831270292789)
                  ·
                    refine ⟨838516647355671681589949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8944177571793831270292789 838516647355671681589949)
                    ·
                      rfl

theorem cell22_2449508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_2449508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449508 prefixEnd_2449508 := by exact prefixLift 2449508
  have htrace : WordTrace (prefixWord ++ tailWord_2449508) baseStart_2449508 baseEnd_2449508 := by
    simpa [prefixWord, tailWord_2449508, baseEnd_2449508] using wordTrace_append hprefix tailTrace_2449508
  have hstable : (prefixWord ++ tailWord_2449508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449508).length < 2 ^ (prefixWord ++ tailWord_2449508).sum := by decide
  have hdescent : baseEnd_2449508 < baseStart_2449508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449604 : List Nat := [2, 3, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_2449604 : Nat := 118140960795 + 2449604 * 2 ^ 59
def prefixEnd_2449604 : Nat := 4983230072969 + 3 ^ 40 * 2449604 * 2
def baseEnd_2449604 : Nat := 838549510117559431189655

theorem tailTrace_2449604 : CollatzResearch.WordTrace tailWord_2449604 prefixEnd_2449604 838549510117559431189655 := by
  unfold tailWord_2449604
  simp only [CollatzResearch.WordTrace]
  refine ⟨44672198908755270950521933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59562931878340361267362577 44672198908755270950521933)
  ·
    refine ⟨16752074590783226606445725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44672198908755270950521933 16752074590783226606445725)
    ·
      refine ⟨6282027971543709977417147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16752074590783226606445725 6282027971543709977417147)
      ·
        refine ⟨9423041957315564966125721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6282027971543709977417147 9423041957315564966125721)
        ·
          refine ⟨7067281467986673724594291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9423041957315564966125721 7067281467986673724594291)
          ·
            refine ⟨10600922201980010586891437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7067281467986673724594291 10600922201980010586891437)
            ·
              refine ⟨3975345825742503970084289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10600922201980010586891437 3975345825742503970084289)
              ·
                refine ⟨2981509369306877977563217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3975345825742503970084289 2981509369306877977563217)
                ·
                  refine ⟨2236132026980158483172413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2981509369306877977563217 2236132026980158483172413)
                  ·
                    refine ⟨838549510117559431189655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2236132026980158483172413 838549510117559431189655)
                    ·
                      rfl

theorem cell22_2449604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_2449604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449604 prefixEnd_2449604 := by exact prefixLift 2449604
  have htrace : WordTrace (prefixWord ++ tailWord_2449604) baseStart_2449604 baseEnd_2449604 := by
    simpa [prefixWord, tailWord_2449604, baseEnd_2449604] using wordTrace_append hprefix tailTrace_2449604
  have hstable : (prefixWord ++ tailWord_2449604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449604).length < 2 ^ (prefixWord ++ tailWord_2449604).sum := by decide
  have hdescent : baseEnd_2449604 < baseStart_2449604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449621 : List Nat := [1, 3, 2, 4, 2, 1, 3, 1, 2, 3]
def baseStart_2449621 : Nat := 118140960795 + 2449621 * 2 ^ 59
def prefixEnd_2449621 : Nat := 4983230072969 + 3 ^ 40 * 2449621 * 2
def baseEnd_2449621 : Nat := 838555329564977053514603

theorem tailTrace_2449621 : CollatzResearch.WordTrace tailWord_2449621 prefixEnd_2449621 838555329564977053514603 := by
  unfold tailWord_2449621
  simp only [CollatzResearch.WordTrace]
  refine ⟨89345017858448953804412717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59563345238965969202941811 89345017858448953804412717)
  ·
    refine ⟨33504381696918357676654769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89345017858448953804412717 33504381696918357676654769)
    ·
      refine ⟨25128286272688768257491077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33504381696918357676654769 25128286272688768257491077)
      ·
        refine ⟨4711553676129144048279577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25128286272688768257491077 4711553676129144048279577)
        ·
          refine ⟨3533665257096858036209683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4711553676129144048279577 3533665257096858036209683)
          ·
            refine ⟨5300497885645287054314525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3533665257096858036209683 5300497885645287054314525)
            ·
              refine ⟨1987686707116982645367947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5300497885645287054314525 1987686707116982645367947)
              ·
                refine ⟨2981530060675473968051921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987686707116982645367947 2981530060675473968051921)
                ·
                  refine ⟨2236147545506605476038941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2981530060675473968051921 2236147545506605476038941)
                  ·
                    refine ⟨838555329564977053514603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2236147545506605476038941 838555329564977053514603)
                    ·
                      rfl

theorem cell22_2449621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_2449621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449621 prefixEnd_2449621 := by exact prefixLift 2449621
  have htrace : WordTrace (prefixWord ++ tailWord_2449621) baseStart_2449621 baseEnd_2449621 := by
    simpa [prefixWord, tailWord_2449621, baseEnd_2449621] using wordTrace_append hprefix tailTrace_2449621
  have hstable : (prefixWord ++ tailWord_2449621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449621).length < 2 ^ (prefixWord ++ tailWord_2449621).sum := by decide
  have hdescent : baseEnd_2449621 < baseStart_2449621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449649 : List Nat := [1, 2, 2, 2, 2, 1, 5, 3, 1, 3]
def baseStart_2449649 : Nat := 118140960795 + 2449649 * 2 ^ 59
def prefixEnd_2449649 : Nat := 4983230072969 + 3 ^ 40 * 2449649 * 2
def baseEnd_2449649 : Nat := 838564914537194313814517

theorem tailTrace_2449649 : CollatzResearch.WordTrace tailWord_2449649 prefixEnd_2449649 838564914537194313814517 := by
  unfold tailWord_2449649
  simp only [CollatzResearch.WordTrace]
  refine ⟨89346039102347514586432001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59564026068231676390954667 89346039102347514586432001)
  ·
    refine ⟨67009529326760635939824001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89346039102347514586432001 67009529326760635939824001)
    ·
      refine ⟨50257146995070476954868001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67009529326760635939824001 50257146995070476954868001)
      ·
        refine ⟨37692860246302857716151001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50257146995070476954868001 37692860246302857716151001)
        ·
          refine ⟨28269645184727143287113251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37692860246302857716151001 28269645184727143287113251)
          ·
            refine ⟨42404467777090714930669877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28269645184727143287113251 42404467777090714930669877)
            ·
              refine ⟨3975418854102254524750301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42404467777090714930669877 3975418854102254524750301)
              ·
                refine ⟨1490782070288345446781363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3975418854102254524750301 1490782070288345446781363)
                ·
                  refine ⟨2236173105432518170172045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490782070288345446781363 2236173105432518170172045)
                  ·
                    refine ⟨838564914537194313814517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2236173105432518170172045 838564914537194313814517)
                    ·
                      rfl

theorem cell22_2449649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_2449649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449649 prefixEnd_2449649 := by exact prefixLift 2449649
  have htrace : WordTrace (prefixWord ++ tailWord_2449649) baseStart_2449649 baseEnd_2449649 := by
    simpa [prefixWord, tailWord_2449649, baseEnd_2449649] using wordTrace_append hprefix tailTrace_2449649
  have hstable : (prefixWord ++ tailWord_2449649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449649).length < 2 ^ (prefixWord ++ tailWord_2449649).sum := by decide
  have hdescent : baseEnd_2449649 < baseStart_2449649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449662 : List Nat := [4, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_2449662 : Nat := 118140960795 + 2449662 * 2 ^ 59
def prefixEnd_2449662 : Nat := 4983230072969 + 3 ^ 40 * 2449662 * 2
def baseEnd_2449662 : Nat := 279523121567622204413159

theorem tailTrace_2449662 : CollatzResearch.WordTrace tailWord_2449662 prefixEnd_2449662 279523121567622204413159 := by
  unfold tailWord_2449662
  simp only [CollatzResearch.WordTrace]
  refine ⟨11168314156412552225831905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59564342167533611871103493 11168314156412552225831905)
  ·
    refine ⟨8376235617309414169373929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11168314156412552225831905 8376235617309414169373929)
    ·
      refine ⟨6282176712982060627030447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8376235617309414169373929 6282176712982060627030447)
      ·
        refine ⟨9423265069473090940545671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6282176712982060627030447 9423265069473090940545671)
        ·
          refine ⟨14134897604209636410818507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9423265069473090940545671 14134897604209636410818507)
          ·
            refine ⟨21202346406314454616227761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14134897604209636410818507 21202346406314454616227761)
            ·
              refine ⟨15901759804735840962170821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21202346406314454616227761 15901759804735840962170821)
              ·
                refine ⟨2981579963387970180407029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15901759804735840962170821 2981579963387970180407029)
                ·
                  refine ⟨279523121567622204413159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2981579963387970180407029 279523121567622204413159)
                  ·
                    rfl

theorem cell22_2449662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_2449662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449662 prefixEnd_2449662 := by exact prefixLift 2449662
  have htrace : WordTrace (prefixWord ++ tailWord_2449662) baseStart_2449662 baseEnd_2449662 := by
    simpa [prefixWord, tailWord_2449662, baseEnd_2449662] using wordTrace_append hprefix tailTrace_2449662
  have hstable : (prefixWord ++ tailWord_2449662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449662).length < 2 ^ (prefixWord ++ tailWord_2449662).sum := by decide
  have hdescent : baseEnd_2449662 < baseStart_2449662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449666 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2449666 : Nat := 118140960795 + 2449666 * 2 ^ 59
def prefixEnd_2449666 : Nat := 4983230072969 + 3 ^ 40 * 2449666 * 2
def baseEnd_2449666 : Nat := 838570733984611936139465

theorem tailTrace_2449666 : CollatzResearch.WordTrace tailWord_2449666 prefixEnd_2449666 838570733984611936139465 := by
  unfold tailWord_2449666
  simp only [CollatzResearch.WordTrace]
  refine ⟨22336664785821481622450213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59564439428857284326533901 22336664785821481622450213)
  ·
    refine ⟨4188124647341527804209415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22336664785821481622450213 4188124647341527804209415)
    ·
      refine ⟨6282186971012291706314123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4188124647341527804209415 6282186971012291706314123)
      ·
        refine ⟨9423280456518437559471185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6282186971012291706314123 9423280456518437559471185)
        ·
          refine ⟨7067460342388828169603389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9423280456518437559471185 7067460342388828169603389)
          ·
            refine ⟨2650297628395810563601271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7067460342388828169603389 2650297628395810563601271)
            ·
              refine ⟨3975446442593715845401907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2650297628395810563601271 3975446442593715845401907)
              ·
                refine ⟨5963169663890573768102861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3975446442593715845401907 5963169663890573768102861)
                ·
                  refine ⟨2236188623958965163038573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5963169663890573768102861 2236188623958965163038573)
                  ·
                    refine ⟨838570733984611936139465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2236188623958965163038573 838570733984611936139465)
                    ·
                      rfl

theorem cell22_2449666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2449666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449666 prefixEnd_2449666 := by exact prefixLift 2449666
  have htrace : WordTrace (prefixWord ++ tailWord_2449666) baseStart_2449666 baseEnd_2449666 := by
    simpa [prefixWord, tailWord_2449666, baseEnd_2449666] using wordTrace_append hprefix tailTrace_2449666
  have hstable : (prefixWord ++ tailWord_2449666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449666).length < 2 ^ (prefixWord ++ tailWord_2449666).sum := by decide
  have hdescent : baseEnd_2449666 < baseStart_2449666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449675 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 3, 4]
def baseStart_2449675 : Nat := 118140960795 + 2449675 * 2 ^ 59
def prefixEnd_2449675 : Nat := 4983230072969 + 3 ^ 40 * 2449675 * 2
def baseEnd_2449675 : Nat := 838573814868538912664437

theorem tailTrace_2449675 : CollatzResearch.WordTrace tailWord_2449675 prefixEnd_2449675 838573814868538912664437 := by
  unfold tailWord_2449675
  simp only [CollatzResearch.WordTrace]
  refine ⟨89346987400253321026878479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59564658266835547351252319 89346987400253321026878479)
  ·
    refine ⟨134020481100379981540317719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89346987400253321026878479 134020481100379981540317719)
    ·
      refine ⟨201030721650569972310476579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134020481100379981540317719 201030721650569972310476579)
      ·
        refine ⟨301546082475854958465714869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201030721650569972310476579 301546082475854958465714869)
        ·
          refine ⟨28269945232111402356160769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 301546082475854958465714869 28269945232111402356160769)
          ·
            refine ⟨21202458924083551767120577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28269945232111402356160769 21202458924083551767120577)
            ·
              refine ⟨15901844193062663825340433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21202458924083551767120577 15901844193062663825340433)
              ·
                refine ⟨11926383144796997869005325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15901844193062663825340433 11926383144796997869005325)
                ·
                  refine ⟨4472393679298874200876997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11926383144796997869005325 4472393679298874200876997)
                  ·
                    refine ⟨838573814868538912664437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4472393679298874200876997 838573814868538912664437)
                    ·
                      rfl

theorem cell22_2449675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 4].length) (baseStart_2449675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449675 prefixEnd_2449675 := by exact prefixLift 2449675
  have htrace : WordTrace (prefixWord ++ tailWord_2449675) baseStart_2449675 baseEnd_2449675 := by
    simpa [prefixWord, tailWord_2449675, baseEnd_2449675] using wordTrace_append hprefix tailTrace_2449675
  have hstable : (prefixWord ++ tailWord_2449675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449675).length < 2 ^ (prefixWord ++ tailWord_2449675).sum := by decide
  have hdescent : baseEnd_2449675 < baseStart_2449675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449818 : List Nat := [3, 1, 1, 4, 1, 4, 1, 3, 1, 3]
def baseStart_2449818 : Nat := 118140960795 + 2449818 * 2 ^ 59
def prefixEnd_2449818 : Nat := 4983230072969 + 3 ^ 40 * 2449818 * 2
def baseEnd_2449818 : Nat := 838622766690934206338999

theorem tailTrace_2449818 : CollatzResearch.WordTrace tailWord_2449818 prefixEnd_2449818 838622766690934206338999 := by
  unfold tailWord_2449818
  simp only [CollatzResearch.WordTrace]
  refine ⟨22338050759683814112333527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59568135359156837632889405 22338050759683814112333527)
  ·
    refine ⟨33507076139525721168500291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22338050759683814112333527 33507076139525721168500291)
    ·
      refine ⟨50260614209288581752750437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33507076139525721168500291 50260614209288581752750437)
      ·
        refine ⟨9423865164241609078640707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50260614209288581752750437 9423865164241609078640707)
        ·
          refine ⟨14135797746362413617961061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9423865164241609078640707 14135797746362413617961061)
          ·
            refine ⟨2650462077442952553367699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14135797746362413617961061 2650462077442952553367699)
            ·
              refine ⟨3975693116164428830051549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2650462077442952553367699 3975693116164428830051549)
              ·
                refine ⟨1490884918561660811269331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3975693116164428830051549 1490884918561660811269331)
                ·
                  refine ⟨2236327377842491216903997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490884918561660811269331 2236327377842491216903997)
                  ·
                    refine ⟨838622766690934206338999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2236327377842491216903997 838622766690934206338999)
                    ·
                      rfl

theorem cell22_2449818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_2449818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449818 prefixEnd_2449818 := by exact prefixLift 2449818
  have htrace : WordTrace (prefixWord ++ tailWord_2449818) baseStart_2449818 baseEnd_2449818 := by
    simpa [prefixWord, tailWord_2449818, baseEnd_2449818] using wordTrace_append hprefix tailTrace_2449818
  have hstable : (prefixWord ++ tailWord_2449818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449818).length < 2 ^ (prefixWord ++ tailWord_2449818).sum := by decide
  have hdescent : baseEnd_2449818 < baseStart_2449818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449878 : List Nat := [5, 2, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_2449878 : Nat := 118140960795 + 2449878 * 2 ^ 59
def prefixEnd_2449878 : Nat := 4983230072969 + 3 ^ 40 * 2449878 * 2
def baseEnd_2449878 : Nat := 838643305917114049838815

theorem tailTrace_2449878 : CollatzResearch.WordTrace tailWord_2449878 prefixEnd_2449878 838643305917114049838815 := by
  unfold tailWord_2449878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5584649463657367918532393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59569594279011924464345525 5584649463657367918532393)
  ·
    refine ⟨4188487097743025938899295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5584649463657367918532393 4188487097743025938899295)
    ·
      refine ⟨6282730646614538908348943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4188487097743025938899295 6282730646614538908348943)
      ·
        refine ⟨9424095969921808362523415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6282730646614538908348943 9424095969921808362523415)
        ·
          refine ⟨14136143954882712543785123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9424095969921808362523415 14136143954882712543785123)
          ·
            refine ⟨21204215932324068815677685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14136143954882712543785123 21204215932324068815677685)
            ·
              refine ⟨1987895243655381451469783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21204215932324068815677685 1987895243655381451469783)
              ·
                refine ⟨2981842865483072177204675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987895243655381451469783 2981842865483072177204675)
                ·
                  refine ⟨4472764298224608265807013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2981842865483072177204675 4472764298224608265807013)
                  ·
                    refine ⟨838643305917114049838815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4472764298224608265807013 838643305917114049838815)
                    ·
                      rfl

theorem cell22_2449878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_2449878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449878 prefixEnd_2449878 := by exact prefixLift 2449878
  have htrace : WordTrace (prefixWord ++ tailWord_2449878) baseStart_2449878 baseEnd_2449878 := by
    simpa [prefixWord, tailWord_2449878, baseEnd_2449878] using wordTrace_append hprefix tailTrace_2449878
  have hstable : (prefixWord ++ tailWord_2449878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449878).length < 2 ^ (prefixWord ++ tailWord_2449878).sum := by decide
  have hdescent : baseEnd_2449878 < baseStart_2449878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449917 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_2449917 : Nat := 118140960795 + 2449917 * 2 ^ 59
def prefixEnd_2449917 : Nat := 4983230072969 + 3 ^ 40 * 2449917 * 2
def baseEnd_2449917 : Nat := 838656656414130948113695

theorem tailTrace_2449917 : CollatzResearch.WordTrace tailWord_2449917 prefixEnd_2449917 838656656414130948113695 := by
  unfold tailWord_2449917
  simp only [CollatzResearch.WordTrace]
  refine ⟨89355813865376596357188005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59570542576917730904792003 89355813865376596357188005)
  ·
    refine ⟨16754215099758111816972751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89355813865376596357188005 16754215099758111816972751)
    ·
      refine ⟨25131322649637167725459127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16754215099758111816972751 25131322649637167725459127)
      ·
        refine ⟨37696983974455751588188691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25131322649637167725459127 37696983974455751588188691)
        ·
          refine ⟨56545475961683627382283037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37696983974455751588188691 56545475961683627382283037)
          ·
            refine ⟨21204553485631360268356139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56545475961683627382283037 21204553485631360268356139)
            ·
              refine ⟨31806830228447040402534209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21204553485631360268356139 31806830228447040402534209)
              ·
                refine ⟨23855122671335280301900657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31806830228447040402534209 23855122671335280301900657)
                ·
                  refine ⟨17891342003501460226425493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23855122671335280301900657 17891342003501460226425493)
                  ·
                    refine ⟨838656656414130948113695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17891342003501460226425493 838656656414130948113695)
                    ·
                      rfl

theorem cell22_2449917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_2449917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449917 prefixEnd_2449917 := by exact prefixLift 2449917
  have htrace : WordTrace (prefixWord ++ tailWord_2449917) baseStart_2449917 baseEnd_2449917 := by
    simpa [prefixWord, tailWord_2449917, baseEnd_2449917] using wordTrace_append hprefix tailTrace_2449917
  have hstable : (prefixWord ++ tailWord_2449917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449917).length < 2 ^ (prefixWord ++ tailWord_2449917).sum := by decide
  have hdescent : baseEnd_2449917 < baseStart_2449917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449919 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 3, 3]
def baseStart_2449919 : Nat := 118140960795 + 2449919 * 2 ^ 59
def prefixEnd_2449919 : Nat := 4983230072969 + 3 ^ 40 * 2449919 * 2
def baseEnd_2449919 : Nat := 838657341055003609563689

theorem tailTrace_2449919 : CollatzResearch.WordTrace tailWord_2449919 prefixEnd_2449919 838657341055003609563689 := by
  unfold tailWord_2449919
  simp only [CollatzResearch.WordTrace]
  refine ⟨89355886811369350698760811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59570591207579567132507207 89355886811369350698760811)
  ·
    refine ⟨134033830217054026048141217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89355886811369350698760811 134033830217054026048141217)
    ·
      refine ⟨100525372662790519536105913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134033830217054026048141217 100525372662790519536105913)
      ·
        refine ⟨75394029497092889652079435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100525372662790519536105913 75394029497092889652079435)
        ·
          refine ⟨113091044245639334478119153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75394029497092889652079435 113091044245639334478119153)
          ·
            refine ⟨84818283184229500858589365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113091044245639334478119153 84818283184229500858589365)
            ·
              refine ⟨7951714048521515705492753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84818283184229500858589365 7951714048521515705492753)
              ·
                refine ⟨5963785536391136779119565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7951714048521515705492753 5963785536391136779119565)
                ·
                  refine ⟨2236419576146676292169837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5963785536391136779119565 2236419576146676292169837)
                  ·
                    refine ⟨838657341055003609563689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2236419576146676292169837 838657341055003609563689)
                    ·
                      rfl

theorem cell22_2449919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 3].length) (baseStart_2449919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449919 prefixEnd_2449919 := by exact prefixLift 2449919
  have htrace : WordTrace (prefixWord ++ tailWord_2449919) baseStart_2449919 baseEnd_2449919 := by
    simpa [prefixWord, tailWord_2449919, baseEnd_2449919] using wordTrace_append hprefix tailTrace_2449919
  have hstable : (prefixWord ++ tailWord_2449919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449919).length < 2 ^ (prefixWord ++ tailWord_2449919).sum := by decide
  have hdescent : baseEnd_2449919 < baseStart_2449919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449949 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 7]
def baseStart_2449949 : Nat := 118140960795 + 2449949 * 2 ^ 59
def prefixEnd_2449949 : Nat := 4983230072969 + 3 ^ 40 * 2449949 * 2
def baseEnd_2449949 : Nat := 279555870222697843771199

theorem tailTrace_2449949 : CollatzResearch.WordTrace tailWord_2449949 prefixEnd_2449949 279555870222697843771199 := by
  unfold tailWord_2449949
  simp only [CollatzResearch.WordTrace]
  refine ⟨89356981001260665822352901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59571320667507110548235267 89356981001260665822352901)
  ·
    refine ⟨16754433937736374841691169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89356981001260665822352901 16754433937736374841691169)
    ·
      refine ⟨12565825453302281131268377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16754433937736374841691169 12565825453302281131268377)
      ·
        refine ⟨9424369089976710848451283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12565825453302281131268377 9424369089976710848451283)
        ·
          refine ⟨14136553634965066272676925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9424369089976710848451283 14136553634965066272676925)
          ·
            refine ⟨5301207613111899852253847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14136553634965066272676925 5301207613111899852253847)
            ·
              refine ⟨7951811419667849778380771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5301207613111899852253847 7951811419667849778380771)
              ·
                refine ⟨11927717129501774667571157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7951811419667849778380771 11927717129501774667571157)
                ·
                  refine ⟨279555870222697843771199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11927717129501774667571157 279555870222697843771199)
                  ·
                    rfl

theorem cell22_2449949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_2449949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2449949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2449949 prefixEnd_2449949 := by exact prefixLift 2449949
  have htrace : WordTrace (prefixWord ++ tailWord_2449949) baseStart_2449949 baseEnd_2449949 := by
    simpa [prefixWord, tailWord_2449949, baseEnd_2449949] using wordTrace_append hprefix tailTrace_2449949
  have hstable : (prefixWord ++ tailWord_2449949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449949).length < 2 ^ (prefixWord ++ tailWord_2449949).sum := by decide
  have hdescent : baseEnd_2449949 < baseStart_2449949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450041 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 2, 4]
def baseStart_2450041 : Nat := 118140960795 + 2450041 * 2 ^ 59
def prefixEnd_2450041 : Nat := 4983230072969 + 3 ^ 40 * 2450041 * 2
def baseEnd_2450041 : Nat := 838699104148235958013315

theorem tailTrace_2450041 : CollatzResearch.WordTrace tailWord_2450041 prefixEnd_2450041 838699104148235958013315 := by
  unfold tailWord_2450041
  simp only [CollatzResearch.WordTrace]
  refine ⟨89360336516927365534701977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59573557677951577023134651 89360336516927365534701977)
  ·
    refine ⟨67020252387695524151026483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89360336516927365534701977 67020252387695524151026483)
    ·
      refine ⟨100530378581543286226539725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67020252387695524151026483 100530378581543286226539725)
      ·
        refine ⟨37698891968078732334952397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100530378581543286226539725 37698891968078732334952397)
        ·
          refine ⟨14137084488029524625607149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37698891968078732334952397 14137084488029524625607149)
          ·
            refine ⟨5301406683011071734602681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14137084488029524625607149 5301406683011071734602681)
            ·
              refine ⟨3976055012258303800952011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5301406683011071734602681 3976055012258303800952011)
              ·
                refine ⟨5964082518387455701428017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3976055012258303800952011 5964082518387455701428017)
                ·
                  refine ⟨4473061888790591776071013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5964082518387455701428017 4473061888790591776071013)
                  ·
                    refine ⟨838699104148235958013315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4473061888790591776071013 838699104148235958013315)
                    ·
                      rfl

theorem cell22_2450041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_2450041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450041 prefixEnd_2450041 := by exact prefixLift 2450041
  have htrace : WordTrace (prefixWord ++ tailWord_2450041) baseStart_2450041 baseEnd_2450041 := by
    simpa [prefixWord, tailWord_2450041, baseEnd_2450041] using wordTrace_append hprefix tailTrace_2450041
  have hstable : (prefixWord ++ tailWord_2450041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450041).length < 2 ^ (prefixWord ++ tailWord_2450041).sum := by decide
  have hdescent : baseEnd_2450041 < baseStart_2450041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450071 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 3, 3]
def baseStart_2450071 : Nat := 118140960795 + 2450071 * 2 ^ 59
def prefixEnd_2450071 : Nat := 4983230072969 + 3 ^ 40 * 2450071 * 2
def baseEnd_2450071 : Nat := 838709373761325879763223

theorem tailTrace_2450071 : CollatzResearch.WordTrace tailWord_2450071 prefixEnd_2450071 838709373761325879763223 := by
  unfold tailWord_2450071
  simp only [CollatzResearch.WordTrace]
  refine ⟨89361430706818680658294067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59574287137879120438862711 89361430706818680658294067)
  ·
    refine ⟨134042146060228020987441101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89361430706818680658294067 134042146060228020987441101)
    ·
      refine ⟨50265804772585507870290413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134042146060228020987441101 50265804772585507870290413)
      ·
        refine ⟨18849676789719565451358905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50265804772585507870290413 18849676789719565451358905)
        ·
          refine ⟨14137257592289674088519179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18849676789719565451358905 14137257592289674088519179)
          ·
            refine ⟨21205886388434511132778769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14137257592289674088519179 21205886388434511132778769)
            ·
              refine ⟨15904414791325883349584077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21205886388434511132778769 15904414791325883349584077)
              ·
                refine ⟨5964155546747206256094029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15904414791325883349584077 5964155546747206256094029)
                ·
                  refine ⟨2236558330030202346035261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5964155546747206256094029 2236558330030202346035261)
                  ·
                    refine ⟨838709373761325879763223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2236558330030202346035261 838709373761325879763223)
                    ·
                      rfl

theorem cell22_2450071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_2450071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450071 prefixEnd_2450071 := by exact prefixLift 2450071
  have htrace : WordTrace (prefixWord ++ tailWord_2450071) baseStart_2450071 baseEnd_2450071 := by
    simpa [prefixWord, tailWord_2450071, baseEnd_2450071] using wordTrace_append hprefix tailTrace_2450071
  have hstable : (prefixWord ++ tailWord_2450071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450071).length < 2 ^ (prefixWord ++ tailWord_2450071).sum := by decide
  have hdescent : baseEnd_2450071 < baseStart_2450071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450090 : List Nat := [3, 1, 5, 2, 1, 1, 3, 6]
def baseStart_2450090 : Nat := 118140960795 + 2450090 * 2 ^ 59
def prefixEnd_2450090 : Nat := 4983230072969 + 3 ^ 40 * 2450090 * 2
def baseEnd_2450090 : Nat := 93190653094401795948685

theorem tailTrace_2450090 : CollatzResearch.WordTrace tailWord_2450090 prefixEnd_2450090 93190653094401795948685 := by
  unfold tailWord_2450090
  simp only [CollatzResearch.WordTrace]
  refine ⟨22340530923437461725808931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59574749129166564602157149 22340530923437461725808931)
  ·
    refine ⟨33510796385156192588713397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22340530923437461725808931 33510796385156192588713397)
    ·
      refine ⟨3141637161108393055191881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33510796385156192588713397 3141637161108393055191881)
      ·
        refine ⟨2356227870831294791393911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3141637161108393055191881 2356227870831294791393911)
        ·
          refine ⟨3534341806246942187090867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356227870831294791393911 3534341806246942187090867)
          ·
            refine ⟨5301512709370413280636301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534341806246942187090867 5301512709370413280636301)
            ·
              refine ⟨1988067266013904980238613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5301512709370413280636301 1988067266013904980238613)
              ·
                refine ⟨93190653094401795948685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1988067266013904980238613 93190653094401795948685)
                ·
                  rfl

theorem cell22_2450090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_2450090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450090 prefixEnd_2450090 := by exact prefixLift 2450090
  have htrace : WordTrace (prefixWord ++ tailWord_2450090) baseStart_2450090 baseEnd_2450090 := by
    simpa [prefixWord, tailWord_2450090, baseEnd_2450090] using wordTrace_append hprefix tailTrace_2450090
  have hstable : (prefixWord ++ tailWord_2450090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450090).length < 2 ^ (prefixWord ++ tailWord_2450090).sum := by decide
  have hdescent : baseEnd_2450090 < baseStart_2450090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450116 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2450116 : Nat := 118140960795 + 2450116 * 2 ^ 59
def prefixEnd_2450116 : Nat := 4983230072969 + 3 ^ 40 * 2450116 * 2
def baseEnd_2450116 : Nat := 838724778180960762388085

theorem tailTrace_2450116 : CollatzResearch.WordTrace tailWord_2450116 prefixEnd_2450116 838724778180960762388085 := by
  unfold tailWord_2450116
  simp only [CollatzResearch.WordTrace]
  refine ⟨44681535995827826671841101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59575381327770435562454801 44681535995827826671841101)
  ·
    refine ⟨16755575998435435001940413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44681535995827826671841101 16755575998435435001940413)
    ·
      refine ⟨6283340999413288125727655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16755575998435435001940413 6283340999413288125727655)
      ·
        refine ⟨9425011499119932188591483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6283340999413288125727655 9425011499119932188591483)
        ·
          refine ⟨14137517248679898282887225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9425011499119932188591483 14137517248679898282887225)
          ·
            refine ⟨10603137936509923712165419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14137517248679898282887225 10603137936509923712165419)
            ·
              refine ⟨15904706904764885568248129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10603137936509923712165419 15904706904764885568248129)
              ·
                refine ⟨11928530178573664176186097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15904706904764885568248129 11928530178573664176186097)
                ·
                  refine ⟨8946397633930248132139573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11928530178573664176186097 8946397633930248132139573)
                  ·
                    refine ⟨838724778180960762388085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8946397633930248132139573 838724778180960762388085)
                    ·
                      rfl

theorem cell22_2450116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2450116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450116 prefixEnd_2450116 := by exact prefixLift 2450116
  have htrace : WordTrace (prefixWord ++ tailWord_2450116) baseStart_2450116 baseEnd_2450116 := by
    simpa [prefixWord, tailWord_2450116, baseEnd_2450116] using wordTrace_append hprefix tailTrace_2450116
  have hstable : (prefixWord ++ tailWord_2450116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450116).length < 2 ^ (prefixWord ++ tailWord_2450116).sum := by decide
  have hdescent : baseEnd_2450116 < baseStart_2450116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450148 : List Nat := [2, 3, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_2450148 : Nat := 118140960795 + 2450148 * 2 ^ 59
def prefixEnd_2450148 : Nat := 4983230072969 + 3 ^ 40 * 2450148 * 2
def baseEnd_2450148 : Nat := 838735732434923345587987

theorem tailTrace_2450148 : CollatzResearch.WordTrace tailWord_2450148 prefixEnd_2450148 838735732434923345587987 := by
  unfold tailWord_2450148
  simp only [CollatzResearch.WordTrace]
  refine ⟨44682119563769861404423549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59576159418359815205898065 44682119563769861404423549)
  ·
    refine ⟨16755794836413698026658831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44682119563769861404423549 16755794836413698026658831)
    ·
      refine ⟨25133692254620547039988247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16755794836413698026658831 25133692254620547039988247)
      ·
        refine ⟨37700538381930820559982371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25133692254620547039988247 37700538381930820559982371)
        ·
          refine ⟨56550807572896230839973557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37700538381930820559982371 56550807572896230839973557)
          ·
            refine ⟨5301638209959021641247521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56550807572896230839973557 5301638209959021641247521)
            ·
              refine ⟨3976228657469266230935641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5301638209959021641247521 3976228657469266230935641)
              ·
                refine ⟨2982171493101949673201731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3976228657469266230935641 2982171493101949673201731)
                ·
                  refine ⟨4473257239652924509802597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2982171493101949673201731 4473257239652924509802597)
                  ·
                    refine ⟨838735732434923345587987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4473257239652924509802597 838735732434923345587987)
                    ·
                      rfl

theorem cell22_2450148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_2450148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450148 prefixEnd_2450148 := by exact prefixLift 2450148
  have htrace : WordTrace (prefixWord ++ tailWord_2450148) baseStart_2450148 baseEnd_2450148 := by
    simpa [prefixWord, tailWord_2450148, baseEnd_2450148] using wordTrace_append hprefix tailTrace_2450148
  have hstable : (prefixWord ++ tailWord_2450148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450148).length < 2 ^ (prefixWord ++ tailWord_2450148).sum := by decide
  have hdescent : baseEnd_2450148 < baseStart_2450148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450161 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 6, 3]
def baseStart_2450161 : Nat := 118140960795 + 2450161 * 2 ^ 59
def prefixEnd_2450161 : Nat := 4983230072969 + 3 ^ 40 * 2450161 * 2
def baseEnd_2450161 : Nat := 838740182600595645012947

theorem tailTrace_2450161 : CollatzResearch.WordTrace tailWord_2450161 prefixEnd_2450161 838740182600595645012947 := by
  unfold tailWord_2450161
  simp only [CollatzResearch.WordTrace]
  refine ⟨89364713276492626029070337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59576475517661750686046891 89364713276492626029070337)
  ·
    refine ⟨67023534957369469521802753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89364713276492626029070337 67023534957369469521802753)
    ·
      refine ⟨50267651218027102141352065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67023534957369469521802753 50267651218027102141352065)
      ·
        refine ⟨37700738413520326606014049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50267651218027102141352065 37700738413520326606014049)
        ·
          refine ⟨28275553810140244954510537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37700738413520326606014049 28275553810140244954510537)
          ·
            refine ⟨21206665357605183715882903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28275553810140244954510537 21206665357605183715882903)
            ·
              refine ⟨31809998036407775573824355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21206665357605183715882903 31809998036407775573824355)
              ·
                refine ⟨47714997054611663360736533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31809998036407775573824355 47714997054611663360736533)
                ·
                  refine ⟨2236640486934921720034525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47714997054611663360736533 2236640486934921720034525)
                  ·
                    refine ⟨838740182600595645012947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2236640486934921720034525 838740182600595645012947)
                    ·
                      rfl

theorem cell22_2450161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_2450161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450161 prefixEnd_2450161 := by exact prefixLift 2450161
  have htrace : WordTrace (prefixWord ++ tailWord_2450161) baseStart_2450161 baseEnd_2450161 := by
    simpa [prefixWord, tailWord_2450161, baseEnd_2450161] using wordTrace_append hprefix tailTrace_2450161
  have hstable : (prefixWord ++ tailWord_2450161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450161).length < 2 ^ (prefixWord ++ tailWord_2450161).sum := by decide
  have hdescent : baseEnd_2450161 < baseStart_2450161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450180 : List Nat := [2, 3, 2, 2, 1, 1, 5, 2, 4]
def baseStart_2450180 : Nat := 118140960795 + 2450180 * 2 ^ 59
def prefixEnd_2450180 : Nat := 4983230072969 + 3 ^ 40 * 2450180 * 2
def baseEnd_2450180 : Nat := 279582228896295309595963

theorem tailTrace_2450180 : CollatzResearch.WordTrace tailWord_2450180 prefixEnd_2450180 279582228896295309595963 := by
  unfold tailWord_2450180
  simp only [CollatzResearch.WordTrace]
  refine ⟨44682703131711896137005997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59576937508949194849341329 44682703131711896137005997)
  ·
    refine ⟨16756013674391961051377249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44682703131711896137005997 16756013674391961051377249)
    ·
      refine ⟨12567010255793970788532937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16756013674391961051377249 12567010255793970788532937)
      ·
        refine ⟨9425257691845478091399703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12567010255793970788532937 9425257691845478091399703)
        ·
          refine ⟨14137886537768217137099555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9425257691845478091399703 14137886537768217137099555)
          ·
            refine ⟨21206829806652325705649333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14137886537768217137099555 21206829806652325705649333)
            ·
              refine ⟨1988140294373655534904625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21206829806652325705649333 1988140294373655534904625)
              ·
                refine ⟨1491105220780241651178469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1988140294373655534904625 1491105220780241651178469)
                ·
                  refine ⟨279582228896295309595963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1491105220780241651178469 279582228896295309595963)
                  ·
                    rfl

theorem cell22_2450180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_2450180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450180 prefixEnd_2450180 := by exact prefixLift 2450180
  have htrace : WordTrace (prefixWord ++ tailWord_2450180) baseStart_2450180 baseEnd_2450180 := by
    simpa [prefixWord, tailWord_2450180, baseEnd_2450180] using wordTrace_append hprefix tailTrace_2450180
  have hstable : (prefixWord ++ tailWord_2450180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450180).length < 2 ^ (prefixWord ++ tailWord_2450180).sum := by decide
  have hdescent : baseEnd_2450180 < baseStart_2450180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450274 : List Nat := [3, 3, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2450274 : Nat := 118140960795 + 2450274 * 2 ^ 59
def prefixEnd_2450274 : Nat := 4983230072969 + 3 ^ 40 * 2450274 * 2
def baseEnd_2450274 : Nat := 838778864809901016937601

theorem tailTrace_2450274 : CollatzResearch.WordTrace tailWord_2450274 prefixEnd_2450274 838778864809901016937601 := by
  unfold tailWord_2450274
  simp only [CollatzResearch.WordTrace]
  refine ⟨22342208681270811581983469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59579223150055497551955917 22342208681270811581983469)
  ·
    refine ⟨8378328255476554343243801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22342208681270811581983469 8378328255476554343243801)
    ·
      refine ⟨6283746191607415757432851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8378328255476554343243801 6283746191607415757432851)
      ·
        refine ⟨9425619287411123636149277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6283746191607415757432851 9425619287411123636149277)
        ·
          refine ⟨3534607232779171363555979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9425619287411123636149277 3534607232779171363555979)
          ·
            refine ⟨5301910849168757045333969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534607232779171363555979 5301910849168757045333969)
            ·
              refine ⟨3976433136876567784000477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5301910849168757045333969 3976433136876567784000477)
              ·
                refine ⟨1491162426328712919000179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3976433136876567784000477 1491162426328712919000179)
                ·
                  refine ⟨2236743639493069378500269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1491162426328712919000179 2236743639493069378500269)
                  ·
                    refine ⟨838778864809901016937601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2236743639493069378500269 838778864809901016937601)
                    ·
                      rfl

theorem cell22_2450274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2450274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450274 prefixEnd_2450274 := by exact prefixLift 2450274
  have htrace : WordTrace (prefixWord ++ tailWord_2450274) baseStart_2450274 baseEnd_2450274 := by
    simpa [prefixWord, tailWord_2450274, baseEnd_2450274] using wordTrace_append hprefix tailTrace_2450274
  have hstable : (prefixWord ++ tailWord_2450274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450274).length < 2 ^ (prefixWord ++ tailWord_2450274).sum := by decide
  have hdescent : baseEnd_2450274 < baseStart_2450274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450313 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 1, 5]
def baseStart_2450313 : Nat := 118140960795 + 2450313 * 2 ^ 59
def prefixEnd_2450313 : Nat := 4983230072969 + 3 ^ 40 * 2450313 * 2
def baseEnd_2450313 : Nat := 838792215306917915212481

theorem tailTrace_2450313 : CollatzResearch.WordTrace tailWord_2450313 prefixEnd_2450313 838792215306917915212481 := by
  unfold tailWord_2450313
  simp only [CollatzResearch.WordTrace]
  refine ⟨89370257171941955988603593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59580171447961303992402395 89370257171941955988603593)
  ·
    refine ⟨67027692878956466991452695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89370257171941955988603593 67027692878956466991452695)
    ·
      refine ⟨100541539318434700487179043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67027692878956466991452695 100541539318434700487179043)
      ·
        refine ⟨150812308977652050730768565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100541539318434700487179043 150812308977652050730768565)
        ·
          refine ⟨14138653966654879756009553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150812308977652050730768565 14138653966654879756009553)
          ·
            refine ⟨10603990474991159817007165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14138653966654879756009553 10603990474991159817007165)
            ·
              refine ⟨3976496428121684931377687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10603990474991159817007165 3976496428121684931377687)
              ·
                refine ⟨5964744642182527397066531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3976496428121684931377687 5964744642182527397066531)
                ·
                  refine ⟨8947116963273791095599797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5964744642182527397066531 8947116963273791095599797)
                  ·
                    refine ⟨838792215306917915212481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8947116963273791095599797 838792215306917915212481)
                    ·
                      rfl

theorem cell22_2450313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_2450313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450313 prefixEnd_2450313 := by exact prefixLift 2450313
  have htrace : WordTrace (prefixWord ++ tailWord_2450313) baseStart_2450313 baseEnd_2450313 := by
    simpa [prefixWord, tailWord_2450313, baseEnd_2450313] using wordTrace_append hprefix tailTrace_2450313
  have hstable : (prefixWord ++ tailWord_2450313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450313).length < 2 ^ (prefixWord ++ tailWord_2450313).sum := by decide
  have hdescent : baseEnd_2450313 < baseStart_2450313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450349 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2450349 : Nat := 118140960795 + 2450349 * 2 ^ 59
def prefixEnd_2450349 : Nat := 4983230072969 + 3 ^ 40 * 2450349 * 2
def baseEnd_2450349 : Nat := 279601512947541940437457

theorem tailTrace_2450349 : CollatzResearch.WordTrace tailWord_2450349 prefixEnd_2450349 279601512947541940437457 := by
  unfold tailWord_2450349
  simp only [CollatzResearch.WordTrace]
  refine ⟨89371570199811534136914101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59581046799874356091276067 89371570199811534136914101)
  ·
    refine ⟨8378584706232331325335697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89371570199811534136914101 8378584706232331325335697)
    ·
      refine ⟨6283938529674248494001773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8378584706232331325335697 6283938529674248494001773)
      ·
        refine ⟨2356476948627843185250665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6283938529674248494001773 2356476948627843185250665)
        ·
          refine ⟨1767357711470882388937999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2356476948627843185250665 1767357711470882388937999)
          ·
            refine ⟨2651036567206323583406999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767357711470882388937999 2651036567206323583406999)
            ·
              refine ⟨3976554850809485375110499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2651036567206323583406999 3976554850809485375110499)
              ·
                refine ⟨5964832276214228062665749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3976554850809485375110499 5964832276214228062665749)
                ·
                  refine ⟨279601512947541940437457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5964832276214228062665749 279601512947541940437457)
                  ·
                    rfl

theorem cell22_2450349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2450349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450349 prefixEnd_2450349 := by exact prefixLift 2450349
  have htrace : WordTrace (prefixWord ++ tailWord_2450349) baseStart_2450349 baseEnd_2450349 := by
    simpa [prefixWord, tailWord_2450349, baseEnd_2450349] using wordTrace_append hprefix tailTrace_2450349
  have hstable : (prefixWord ++ tailWord_2450349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450349).length < 2 ^ (prefixWord ++ tailWord_2450349).sum := by decide
  have hdescent : baseEnd_2450349 < baseStart_2450349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450403 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 2, 5]
def baseStart_2450403 : Nat := 118140960795 + 2450403 * 2 ^ 59
def prefixEnd_2450403 : Nat := 4983230072969 + 3 ^ 40 * 2450403 * 2
def baseEnd_2450403 : Nat := 838823024146187680462205

theorem tailTrace_2450403 : CollatzResearch.WordTrace tailWord_2450403 prefixEnd_2450403 838823024146187680462205 := by
  unfold tailWord_2450403
  simp only [CollatzResearch.WordTrace]
  refine ⟨89373539741615901359379863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59582359827743934239586575 89373539741615901359379863)
  ·
    refine ⟨134060309612423852039069795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89373539741615901359379863 134060309612423852039069795)
    ·
      refine ⟨201090464418635778058604693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134060309612423852039069795 201090464418635778058604693)
      ·
        refine ⟨9426115519623552096497095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 201090464418635778058604693 9426115519623552096497095)
        ·
          refine ⟨14139173279435328144745643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9426115519623552096497095 14139173279435328144745643)
          ·
            refine ⟨21208759919152992217118465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14139173279435328144745643 21208759919152992217118465)
            ·
              refine ⟨15906569939364744162838849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21208759919152992217118465 15906569939364744162838849)
              ·
                refine ⟨11929927454523558122129137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15906569939364744162838849 11929927454523558122129137)
                ·
                  refine ⟨8947445590892668591596853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11929927454523558122129137 8947445590892668591596853)
                  ·
                    refine ⟨838823024146187680462205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8947445590892668591596853 838823024146187680462205)
                    ·
                      rfl

theorem cell22_2450403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_2450403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450403 prefixEnd_2450403 := by exact prefixLift 2450403
  have htrace : WordTrace (prefixWord ++ tailWord_2450403) baseStart_2450403 baseEnd_2450403 := by
    simpa [prefixWord, tailWord_2450403, baseEnd_2450403] using wordTrace_append hprefix tailTrace_2450403
  have hstable : (prefixWord ++ tailWord_2450403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450403).length < 2 ^ (prefixWord ++ tailWord_2450403).sum := by decide
  have hdescent : baseEnd_2450403 < baseStart_2450403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450433 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 8]
def baseStart_2450433 : Nat := 118140960795 + 2450433 * 2 ^ 59
def prefixEnd_2450433 : Nat := 4983230072969 + 3 ^ 40 * 2450433 * 2
def baseEnd_2450433 : Nat := 279611097919759200737371

theorem tailTrace_2450433 : CollatzResearch.WordTrace tailWord_2450433 prefixEnd_2450433 279611097919759200737371 := by
  unfold tailWord_2450433
  simp only [CollatzResearch.WordTrace]
  refine ⟨89374633931507216482971953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59583089287671477655314635 89374633931507216482971953)
  ·
    refine ⟨67030975448630412362228965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89374633931507216482971953 67030975448630412362228965)
    ·
      refine ⟨12568307896618202317917931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67030975448630412362228965 12568307896618202317917931)
      ·
        refine ⟨18852461844927303476876897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12568307896618202317917931 18852461844927303476876897)
        ·
          refine ⟨14139346383695477607657673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18852461844927303476876897 14139346383695477607657673)
          ·
            refine ⟨10604509787771608205743255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14139346383695477607657673 10604509787771608205743255)
            ·
              refine ⟨15906764681657412308614883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10604509787771608205743255 15906764681657412308614883)
              ·
                refine ⟨23860147022486118462922325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15906764681657412308614883 23860147022486118462922325)
                ·
                  refine ⟨279611097919759200737371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23860147022486118462922325 279611097919759200737371)
                  ·
                    rfl

theorem cell22_2450433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_2450433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450433 prefixEnd_2450433 := by exact prefixLift 2450433
  have htrace : WordTrace (prefixWord ++ tailWord_2450433) baseStart_2450433 baseEnd_2450433 := by
    simpa [prefixWord, tailWord_2450433, baseEnd_2450433] using wordTrace_append hprefix tailTrace_2450433
  have hstable : (prefixWord ++ tailWord_2450433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450433).length < 2 ^ (prefixWord ++ tailWord_2450433).sum := by decide
  have hdescent : baseEnd_2450433 < baseStart_2450433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450508 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_2450508 : Nat := 118140960795 + 2450508 * 2 ^ 59
def prefixEnd_2450508 : Nat := 4983230072969 + 3 ^ 40 * 2450508 * 2
def baseEnd_2450508 : Nat := 838858967792002406586883

theorem tailTrace_2450508 : CollatzResearch.WordTrace tailWord_2450508 prefixEnd_2450508 838858967792002406586883 := by
  unfold tailWord_2450508
  simp only [CollatzResearch.WordTrace]
  refine ⟨44688684703117752145976089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59584912937490336194634785 44688684703117752145976089)
  ·
    refine ⟨33516513527338314109482067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44688684703117752145976089 33516513527338314109482067)
    ·
      refine ⟨50274770291007471164223101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33516513527338314109482067 50274770291007471164223101)
      ·
        refine ⟨18853038859127801686583663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50274770291007471164223101 18853038859127801686583663)
        ·
          refine ⟨28279558288691702529875495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18853038859127801686583663 28279558288691702529875495)
          ·
            refine ⟨42419337433037553794813243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28279558288691702529875495 42419337433037553794813243)
            ·
              refine ⟨63629006149556330692219865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42419337433037553794813243 63629006149556330692219865)
              ·
                refine ⟨47721754612167248019164899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63629006149556330692219865 47721754612167248019164899)
                ·
                  refine ⟨71582631918250872028747349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47721754612167248019164899 71582631918250872028747349)
                  ·
                    refine ⟨838858967792002406586883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71582631918250872028747349 838858967792002406586883)
                    ·
                      rfl

theorem cell22_2450508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_2450508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450508 prefixEnd_2450508 := by exact prefixLift 2450508
  have htrace : WordTrace (prefixWord ++ tailWord_2450508) baseStart_2450508 baseEnd_2450508 := by
    simpa [prefixWord, tailWord_2450508, baseEnd_2450508] using wordTrace_append hprefix tailTrace_2450508
  have hstable : (prefixWord ++ tailWord_2450508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450508).length < 2 ^ (prefixWord ++ tailWord_2450508).sum := by decide
  have hdescent : baseEnd_2450508 < baseStart_2450508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450518 : List Nat := [5, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2450518 : Nat := 118140960795 + 2450518 * 2 ^ 59
def prefixEnd_2450518 : Nat := 4983230072969 + 3 ^ 40 * 2450518 * 2
def baseEnd_2450518 : Nat := 279620796998788571278951

theorem tailTrace_2450518 : CollatzResearch.WordTrace tailWord_2450518 prefixEnd_2450518 279620796998788571278951 := by
  unfold tailWord_2450518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5586108383512454749988513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59585156090799517333210805 5586108383512454749988513)
  ·
    refine ⟨4189581287634341062491385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5586108383512454749988513 4189581287634341062491385)
    ·
      refine ⟨3142185965725755796868539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4189581287634341062491385 3142185965725755796868539)
      ·
        refine ⟨4713278948588633695302809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3142185965725755796868539 4713278948588633695302809)
        ·
          refine ⟨3534959211441475271477107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4713278948588633695302809 3534959211441475271477107)
          ·
            refine ⟨5302438817162212907215661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534959211441475271477107 5302438817162212907215661)
            ·
              refine ⟨1988414556435829840205873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5302438817162212907215661 1988414556435829840205873)
              ·
                refine ⟨1491310917326872380154405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1988414556435829840205873 1491310917326872380154405)
                ·
                  refine ⟨279620796998788571278951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1491310917326872380154405 279620796998788571278951)
                  ·
                    rfl

theorem cell22_2450518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2450518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450518 prefixEnd_2450518 := by exact prefixLift 2450518
  have htrace : WordTrace (prefixWord ++ tailWord_2450518) baseStart_2450518 baseEnd_2450518 := by
    simpa [prefixWord, tailWord_2450518, baseEnd_2450518] using wordTrace_append hprefix tailTrace_2450518
  have hstable : (prefixWord ++ tailWord_2450518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450518).length < 2 ^ (prefixWord ++ tailWord_2450518).sum := by decide
  have hdescent : baseEnd_2450518 < baseStart_2450518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450540 : List Nat := [2, 2, 1, 1, 3, 2, 3, 3, 5]
def baseStart_2450540 : Nat := 118140960795 + 2450540 * 2 ^ 59
def prefixEnd_2450540 : Nat := 4983230072969 + 3 ^ 40 * 2450540 * 2
def baseEnd_2450540 : Nat := 279623307348654996595595

theorem tailTrace_2450540 : CollatzResearch.WordTrace tailWord_2450540 prefixEnd_2450540 279623307348654996595595 := by
  unfold tailWord_2450540
  simp only [CollatzResearch.WordTrace]
  refine ⟨44689268271059786878558537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59585691028079715838078049 44689268271059786878558537)
  ·
    refine ⟨33516951203294840158918903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44689268271059786878558537 33516951203294840158918903)
    ·
      refine ⟨50275426804942260238378355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33516951203294840158918903 50275426804942260238378355)
      ·
        refine ⟨75413140207413390357567533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50275426804942260238378355 75413140207413390357567533)
        ·
          refine ⟨28279927577780021384087825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75413140207413390357567533 28279927577780021384087825)
          ·
            refine ⟨21209945683335016038065869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28279927577780021384087825 21209945683335016038065869)
            ·
              refine ⟨7953729631250631014274701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21209945683335016038065869 7953729631250631014274701)
              ·
                refine ⟨2982648611718986630353013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7953729631250631014274701 2982648611718986630353013)
                ·
                  refine ⟨279623307348654996595595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2982648611718986630353013 279623307348654996595595)
                  ·
                    rfl

theorem cell22_2450540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_2450540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450540 prefixEnd_2450540 := by exact prefixLift 2450540
  have htrace : WordTrace (prefixWord ++ tailWord_2450540) baseStart_2450540 baseEnd_2450540 := by
    simpa [prefixWord, tailWord_2450540, baseEnd_2450540] using wordTrace_append hprefix tailTrace_2450540
  have hstable : (prefixWord ++ tailWord_2450540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450540).length < 2 ^ (prefixWord ++ tailWord_2450540).sum := by decide
  have hdescent : baseEnd_2450540 < baseStart_2450540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450578 : List Nat := [3, 2, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_2450578 : Nat := 118140960795 + 2450578 * 2 ^ 59
def prefixEnd_2450578 : Nat := 4983230072969 + 3 ^ 40 * 2450578 * 2
def baseEnd_2450578 : Nat := 838882930222545557336669

theorem tailTrace_2450578 : CollatzResearch.WordTrace tailWord_2450578 prefixEnd_2450578 838882930222545557336669 := by
  unfold tailWord_2450578
  simp only [CollatzResearch.WordTrace]
  refine ⟨22344980628995476561750097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59586615010654604164666925 22344980628995476561750097)
  ·
    refine ⟨16758735471746607421312573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22344980628995476561750097 16758735471746607421312573)
    ·
      refine ⟨6284525801904977782992215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16758735471746607421312573 6284525801904977782992215)
      ·
        refine ⟨9426788702857466674488323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6284525801904977782992215 9426788702857466674488323)
        ·
          refine ⟨14140183054286200011732485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9426788702857466674488323 14140183054286200011732485)
          ·
            refine ⟨2651284322678662502199841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14140183054286200011732485 2651284322678662502199841)
            ·
              refine ⟨1988463242008996876649881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2651284322678662502199841 1988463242008996876649881)
              ·
                refine ⟨1491347431506747657487411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1988463242008996876649881 1491347431506747657487411)
                ·
                  refine ⟨2237021147260121486231117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1491347431506747657487411 2237021147260121486231117)
                  ·
                    refine ⟨838882930222545557336669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2237021147260121486231117 838882930222545557336669)
                    ·
                      rfl

theorem cell22_2450578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_2450578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450578 prefixEnd_2450578 := by exact prefixLift 2450578
  have htrace : WordTrace (prefixWord ++ tailWord_2450578) baseStart_2450578 baseEnd_2450578 := by
    simpa [prefixWord, tailWord_2450578, baseEnd_2450578] using wordTrace_append hprefix tailTrace_2450578
  have hstable : (prefixWord ++ tailWord_2450578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450578).length < 2 ^ (prefixWord ++ tailWord_2450578).sum := by decide
  have hdescent : baseEnd_2450578 < baseStart_2450578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450602 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 8]
def baseStart_2450602 : Nat := 118140960795 + 2450602 * 2 ^ 59
def prefixEnd_2450602 : Nat := 4983230072969 + 3 ^ 40 * 2450602 * 2
def baseEnd_2450602 : Nat := 279630381971005831578865

theorem tailTrace_2450602 : CollatzResearch.WordTrace tailWord_2450602 prefixEnd_2450602 279630381971005831578865 := by
  unfold tailWord_2450602
  simp only [CollatzResearch.WordTrace]
  refine ⟨22345199466973739586468515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59587198578596638897249373 22345199466973739586468515)
  ·
    refine ⟨33517799200460609379702773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22345199466973739586468515 33517799200460609379702773)
    ·
      refine ⟨3142293675043182129347135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33517799200460609379702773 3142293675043182129347135)
      ·
        refine ⟨4713440512564773194020703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3142293675043182129347135 4713440512564773194020703)
        ·
          refine ⟨7070160768847159791031055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4713440512564773194020703 7070160768847159791031055)
          ·
            refine ⟨10605241153270739686546583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7070160768847159791031055 10605241153270739686546583)
            ·
              refine ⟨15907861729906109529819875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10605241153270739686546583 15907861729906109529819875)
              ·
                refine ⟨23861792594859164294729813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15907861729906109529819875 23861792594859164294729813)
                ·
                  refine ⟨279630381971005831578865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23861792594859164294729813 279630381971005831578865)
                  ·
                    rfl

theorem cell22_2450602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_2450602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450602 prefixEnd_2450602 := by exact prefixLift 2450602
  have htrace : WordTrace (prefixWord ++ tailWord_2450602) baseStart_2450602 baseEnd_2450602 := by
    simpa [prefixWord, tailWord_2450602, baseEnd_2450602] using wordTrace_append hprefix tailTrace_2450602
  have hstable : (prefixWord ++ tailWord_2450602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450602).length < 2 ^ (prefixWord ++ tailWord_2450602).sum := by decide
  have hdescent : baseEnd_2450602 < baseStart_2450602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450615 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 1, 6]
def baseStart_2450615 : Nat := 118140960795 + 2450615 * 2 ^ 59
def prefixEnd_2450615 : Nat := 4983230072969 + 3 ^ 40 * 2450615 * 2
def baseEnd_2450615 : Nat := 838895596078689794161555

theorem tailTrace_2450615 : CollatzResearch.WordTrace tailWord_2450615 prefixEnd_2450615 838895596078689794161555 := by
  unfold tailWord_2450615
  simp only [CollatzResearch.WordTrace]
  refine ⟨89381272016847861566097299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59587514677898574377398199 89381272016847861566097299)
  ·
    refine ⟨134071908025271792349145949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89381272016847861566097299 134071908025271792349145949)
    ·
      refine ⟨50276965509476922130929731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134071908025271792349145949 50276965509476922130929731)
      ·
        refine ⟨75415448264215383196394597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50276965509476922130929731 75415448264215383196394597)
        ·
          refine ⟨14140396549540384349323987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75415448264215383196394597 14140396549540384349323987)
          ·
            refine ⟨21210594824310576523985981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14140396549540384349323987 21210594824310576523985981)
            ·
              refine ⟨7953973059116466196494743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21210594824310576523985981 7953973059116466196494743)
              ·
                refine ⟨11930959588674699294742115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7953973059116466196494743 11930959588674699294742115)
                ·
                  refine ⟨17896439383012048942113173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11930959588674699294742115 17896439383012048942113173)
                  ·
                    refine ⟨838895596078689794161555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17896439383012048942113173 838895596078689794161555)
                    ·
                      rfl

theorem cell22_2450615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_2450615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450615 prefixEnd_2450615 := by exact prefixLift 2450615
  have htrace : WordTrace (prefixWord ++ tailWord_2450615) baseStart_2450615 baseEnd_2450615 := by
    simpa [prefixWord, tailWord_2450615, baseEnd_2450615] using wordTrace_append hprefix tailTrace_2450615
  have hstable : (prefixWord ++ tailWord_2450615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450615).length < 2 ^ (prefixWord ++ tailWord_2450615).sum := by decide
  have hdescent : baseEnd_2450615 < baseStart_2450615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450634 : List Nat := [3, 1, 2, 1, 3, 2, 3, 2, 2, 3]
def baseStart_2450634 : Nat := 118140960795 + 2450634 * 2 ^ 59
def prefixEnd_2450634 : Nat := 4983230072969 + 3 ^ 40 * 2450634 * 2
def baseEnd_2450634 : Nat := 838902100166980077936497

theorem tailTrace_2450634 : CollatzResearch.WordTrace tailWord_2450634 prefixEnd_2450634 838902100166980077936497 := by
  unfold tailWord_2450634
  simp only [CollatzResearch.WordTrace]
  refine ⟨22345491250944756952759739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59587976669186018540692637 22345491250944756952759739)
  ·
    refine ⟨33518236876417135429139609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22345491250944756952759739 33518236876417135429139609)
    ·
      refine ⟨25138677657312851571854707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33518236876417135429139609 25138677657312851571854707)
      ·
        refine ⟨37708016485969277357782061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25138677657312851571854707 37708016485969277357782061)
        ·
          refine ⟨14140506182238479009168273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37708016485969277357782061 14140506182238479009168273)
          ·
            refine ⟨10605379636678859256876205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14140506182238479009168273 10605379636678859256876205)
            ·
              refine ⟨3977017363754572221328577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10605379636678859256876205 3977017363754572221328577)
              ·
                refine ⟨2982763022815929165996433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3977017363754572221328577 2982763022815929165996433)
                ·
                  refine ⟨2237072267111946874497325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2982763022815929165996433 2237072267111946874497325)
                  ·
                    refine ⟨838902100166980077936497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2237072267111946874497325 838902100166980077936497)
                    ·
                      rfl

theorem cell22_2450634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_2450634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450634 prefixEnd_2450634 := by exact prefixLift 2450634
  have htrace : WordTrace (prefixWord ++ tailWord_2450634) baseStart_2450634 baseEnd_2450634 := by
    simpa [prefixWord, tailWord_2450634, baseEnd_2450634] using wordTrace_append hprefix tailTrace_2450634
  have hstable : (prefixWord ++ tailWord_2450634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450634).length < 2 ^ (prefixWord ++ tailWord_2450634).sum := by decide
  have hdescent : baseEnd_2450634 < baseStart_2450634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450660 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_2450660 : Nat := 118140960795 + 2450660 * 2 ^ 59
def prefixEnd_2450660 : Nat := 4983230072969 + 3 ^ 40 * 2450660 * 2
def baseEnd_2450660 : Nat := 838911000498324676786417

theorem tailTrace_2450660 : CollatzResearch.WordTrace tailWord_2450660 prefixEnd_2450660 838911000498324676786417 := by
  unfold tailWord_2450660
  simp only [CollatzResearch.WordTrace]
  refine ⟨44691456650842417125742717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59588608867789889500990289 44691456650842417125742717)
  ·
    refine ⟨16759296244065906422153519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44691456650842417125742717 16759296244065906422153519)
    ·
      refine ⟨25138944366098859633230279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16759296244065906422153519 25138944366098859633230279)
      ·
        refine ⟨37708416549148289449845419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25138944366098859633230279 37708416549148289449845419)
        ·
          refine ⟨56562624823722434174768129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37708416549148289449845419 56562624823722434174768129)
          ·
            refine ⟨42421968617791825631076097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56562624823722434174768129 42421968617791825631076097)
            ·
              refine ⟨31816476463343869223307073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42421968617791825631076097 31816476463343869223307073)
              ·
                refine ⟨23862357347507901917480305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31816476463343869223307073 23862357347507901917480305)
                ·
                  refine ⟨17896768010630926438110229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23862357347507901917480305 17896768010630926438110229)
                  ·
                    refine ⟨838911000498324676786417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17896768010630926438110229 838911000498324676786417)
                    ·
                      rfl

theorem cell22_2450660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_2450660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450660 prefixEnd_2450660 := by exact prefixLift 2450660
  have htrace : WordTrace (prefixWord ++ tailWord_2450660) baseStart_2450660 baseEnd_2450660 := by
    simpa [prefixWord, tailWord_2450660, baseEnd_2450660] using wordTrace_append hprefix tailTrace_2450660
  have hstable : (prefixWord ++ tailWord_2450660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450660).length < 2 ^ (prefixWord ++ tailWord_2450660).sum := by decide
  have hdescent : baseEnd_2450660 < baseStart_2450660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450675 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 7]
def baseStart_2450675 : Nat := 118140960795 + 2450675 * 2 ^ 59
def prefixEnd_2450675 : Nat := 4983230072969 + 3 ^ 40 * 2450675 * 2
def baseEnd_2450675 : Nat := 279638711768289879220457

theorem tailTrace_2450675 : CollatzResearch.WordTrace tailWord_2450675 prefixEnd_2450675 279638711768289879220457 := by
  unfold tailWord_2450675
  simp only [CollatzResearch.WordTrace]
  refine ⟨89383460396630491813281479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59588973597753661208854319 89383460396630491813281479)
  ·
    refine ⟨134075190594945737719922219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89383460396630491813281479 134075190594945737719922219)
    ·
      refine ⟨201112785892418606579883329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134075190594945737719922219 201112785892418606579883329)
      ·
        refine ⟨150834589419313954934912497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201112785892418606579883329 150834589419313954934912497)
        ·
          refine ⟨113125942064485466201184373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150834589419313954934912497 113125942064485466201184373)
          ·
            refine ⟨10605557068545512456361035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113125942064485466201184373 10605557068545512456361035)
            ·
              refine ⟨15908335602818268684541553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10605557068545512456361035 15908335602818268684541553)
              ·
                refine ⟨11931251702113701513406165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15908335602818268684541553 11931251702113701513406165)
                ·
                  refine ⟨279638711768289879220457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11931251702113701513406165 279638711768289879220457)
                  ·
                    rfl

theorem cell22_2450675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 7].length) (baseStart_2450675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450675 prefixEnd_2450675 := by exact prefixLift 2450675
  have htrace : WordTrace (prefixWord ++ tailWord_2450675) baseStart_2450675 baseEnd_2450675 := by
    simpa [prefixWord, tailWord_2450675, baseEnd_2450675] using wordTrace_append hprefix tailTrace_2450675
  have hstable : (prefixWord ++ tailWord_2450675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450675).length < 2 ^ (prefixWord ++ tailWord_2450675).sum := by decide
  have hdescent : baseEnd_2450675 < baseStart_2450675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450692 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 7]
def baseStart_2450692 : Nat := 118140960795 + 2450692 * 2 ^ 59
def prefixEnd_2450692 : Nat := 4983230072969 + 3 ^ 40 * 2450692 * 2
def baseEnd_2450692 : Nat := 279640651584095753328773

theorem tailTrace_2450692 : CollatzResearch.WordTrace tailWord_2450692 prefixEnd_2450692 279640651584095753328773 := by
  unfold tailWord_2450692
  simp only [CollatzResearch.WordTrace]
  refine ⟨44692040218784451858325165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59589386958379269144433553 44692040218784451858325165)
  ·
    refine ⟨16759515082044169446871937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44692040218784451858325165 16759515082044169446871937)
    ·
      refine ⟨12569636311533127085153953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16759515082044169446871937 12569636311533127085153953)
      ·
        refine ⟨9427227233649845313865465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12569636311533127085153953 9427227233649845313865465)
        ·
          refine ⟨7070420425237383985399099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9427227233649845313865465 7070420425237383985399099)
          ·
            refine ⟨10605630637856075978098649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7070420425237383985399099 10605630637856075978098649)
            ·
              refine ⟨7954222978392056983573987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10605630637856075978098649 7954222978392056983573987)
              ·
                refine ⟨11931334467588085475360981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7954222978392056983573987 11931334467588085475360981)
                ·
                  refine ⟨279640651584095753328773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11931334467588085475360981 279640651584095753328773)
                  ·
                    rfl

theorem cell22_2450692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_2450692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450692 prefixEnd_2450692 := by exact prefixLift 2450692
  have htrace : WordTrace (prefixWord ++ tailWord_2450692) baseStart_2450692 baseEnd_2450692 := by
    simpa [prefixWord, tailWord_2450692, baseEnd_2450692] using wordTrace_append hprefix tailTrace_2450692
  have hstable : (prefixWord ++ tailWord_2450692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450692).length < 2 ^ (prefixWord ++ tailWord_2450692).sum := by decide
  have hdescent : baseEnd_2450692 < baseStart_2450692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450696 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 3, 3]
def baseStart_2450696 : Nat := 118140960795 + 2450696 * 2 ^ 59
def prefixEnd_2450696 : Nat := 4983230072969 + 3 ^ 40 * 2450696 * 2
def baseEnd_2450696 : Nat := 838923324034032582886307

theorem tailTrace_2450696 : CollatzResearch.WordTrace tailWord_2450696 prefixEnd_2450696 838923324034032582886307 := by
  unfold tailWord_2450696
  simp only [CollatzResearch.WordTrace]
  refine ⟨44692113164777206199897971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59589484219702941599863961 44692113164777206199897971)
  ·
    refine ⟨67038169747165809299846957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44692113164777206199897971 67038169747165809299846957)
    ·
      refine ⟨25139313655187178487442609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67038169747165809299846957 25139313655187178487442609)
      ·
        refine ⟨18854485241390383865581957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25139313655187178487442609 18854485241390383865581957)
        ·
          refine ⟨3535215982760696974796617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18854485241390383865581957 3535215982760696974796617)
          ·
            refine ⟨2651411987070522731097463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3535215982760696974796617 2651411987070522731097463)
            ·
              refine ⟨3977117980605784096646195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2651411987070522731097463 3977117980605784096646195)
              ·
                refine ⟨5965676970908676144969293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3977117980605784096646195 5965676970908676144969293)
                ·
                  refine ⟨2237128864090753554363485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5965676970908676144969293 2237128864090753554363485)
                  ·
                    refine ⟨838923324034032582886307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2237128864090753554363485 838923324034032582886307)
                    ·
                      rfl

theorem cell22_2450696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_2450696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450696 prefixEnd_2450696 := by exact prefixLift 2450696
  have htrace : WordTrace (prefixWord ++ tailWord_2450696) baseStart_2450696 baseEnd_2450696 := by
    simpa [prefixWord, tailWord_2450696, baseEnd_2450696] using wordTrace_append hprefix tailTrace_2450696
  have hstable : (prefixWord ++ tailWord_2450696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450696).length < 2 ^ (prefixWord ++ tailWord_2450696).sum := by decide
  have hdescent : baseEnd_2450696 < baseStart_2450696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450758 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_2450758 : Nat := 118140960795 + 2450758 * 2 ^ 59
def prefixEnd_2450758 : Nat := 4983230072969 + 3 ^ 40 * 2450758 * 2
def baseEnd_2450758 : Nat := 838944547901085087836117

theorem tailTrace_2450758 : CollatzResearch.WordTrace tailWord_2450758 prefixEnd_2450758 838944547901085087836117 := by
  unfold tailWord_2450758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2793327739229056155892279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59590991770219864659035285 2793327739229056155892279)
  ·
    refine ⟨4189991608843584233838419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2793327739229056155892279 4189991608843584233838419)
    ·
      refine ⟨6284987413265376350757629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4189991608843584233838419 6284987413265376350757629)
      ·
        refine ⟨2356870279974516131534111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6284987413265376350757629 2356870279974516131534111)
        ·
          refine ⟨3535305419961774197301167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356870279974516131534111 3535305419961774197301167)
          ·
            refine ⟨5302958129942661295951751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535305419961774197301167 5302958129942661295951751)
            ·
              refine ⟨7954437194913991943927627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5302958129942661295951751 7954437194913991943927627)
              ·
                refine ⟨11931655792370987915891441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7954437194913991943927627 11931655792370987915891441)
                ·
                  refine ⟨8948741844278240936918581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11931655792370987915891441 8948741844278240936918581)
                  ·
                    refine ⟨838944547901085087836117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8948741844278240936918581 838944547901085087836117)
                    ·
                      rfl

theorem cell22_2450758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_2450758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450758 prefixEnd_2450758 := by exact prefixLift 2450758
  have htrace : WordTrace (prefixWord ++ tailWord_2450758) baseStart_2450758 baseEnd_2450758 := by
    simpa [prefixWord, tailWord_2450758, baseEnd_2450758] using wordTrace_append hprefix tailTrace_2450758
  have hstable : (prefixWord ++ tailWord_2450758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450758).length < 2 ^ (prefixWord ++ tailWord_2450758).sum := by decide
  have hdescent : baseEnd_2450758 < baseStart_2450758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450769 : List Nat := [1, 2, 2, 1, 4, 1, 1, 5, 2, 3]
def baseStart_2450769 : Nat := 118140960795 + 2450769 * 2 ^ 59
def prefixEnd_2450769 : Nat := 4983230072969 + 3 ^ 40 * 2450769 * 2
def baseEnd_2450769 : Nat := 838948313425884725811083

theorem tailTrace_2450769 : CollatzResearch.WordTrace tailWord_2450769 prefixEnd_2450769 838948313425884725811083 := by
  unfold tailWord_2450769
  simp only [CollatzResearch.WordTrace]
  refine ⟨89386888858289945867203361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59591259238859963911468907 89386888858289945867203361)
  ·
    refine ⟨67040166643717459400402521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89386888858289945867203361 67040166643717459400402521)
    ·
      refine ⟨50280124982788094550301891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67040166643717459400402521 50280124982788094550301891)
      ·
        refine ⟨75420187474182141825452837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50280124982788094550301891 75420187474182141825452837)
        ·
          refine ⟨14141285151409151592272407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75420187474182141825452837 14141285151409151592272407)
          ·
            refine ⟨21211927727113727388408611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14141285151409151592272407 21211927727113727388408611)
            ·
              refine ⟨31817891590670591082612917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21211927727113727388408611 31817891590670591082612917)
              ·
                refine ⟨2982927336625367913994961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31817891590670591082612917 2982927336625367913994961)
                ·
                  refine ⟨2237195502469025935496221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2982927336625367913994961 2237195502469025935496221)
                  ·
                    refine ⟨838948313425884725811083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2237195502469025935496221 838948313425884725811083)
                    ·
                      rfl

theorem cell22_2450769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_2450769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450769 prefixEnd_2450769 := by exact prefixLift 2450769
  have htrace : WordTrace (prefixWord ++ tailWord_2450769) baseStart_2450769 baseEnd_2450769 := by
    simpa [prefixWord, tailWord_2450769, baseEnd_2450769] using wordTrace_append hprefix tailTrace_2450769
  have hstable : (prefixWord ++ tailWord_2450769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450769).length < 2 ^ (prefixWord ++ tailWord_2450769).sum := by decide
  have hdescent : baseEnd_2450769 < baseStart_2450769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450784 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 2, 4]
def baseStart_2450784 : Nat := 118140960795 + 2450784 * 2 ^ 59
def prefixEnd_2450784 : Nat := 4983230072969 + 3 ^ 40 * 2450784 * 2
def baseEnd_2450784 : Nat := 838953448232429686686037

theorem tailTrace_2450784 : CollatzResearch.WordTrace tailWord_2450784 prefixEnd_2450784 838953448232429686686037 := by
  unfold tailWord_2450784
  simp only [CollatzResearch.WordTrace]
  refine ⟨44693717976617801714499703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59591623968823735619332937 44693717976617801714499703)
  ·
    refine ⟨67040576964926702571749555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44693717976617801714499703 67040576964926702571749555)
    ·
      refine ⟨100560865447390053857624333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67040576964926702571749555 100560865447390053857624333)
      ·
        refine ⟨37710324542771270196609125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100560865447390053857624333 37710324542771270196609125)
        ·
          refine ⟨7070685851769613161864211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37710324542771270196609125 7070685851769613161864211)
          ·
            refine ⟨10606028777654419742796317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7070685851769613161864211 10606028777654419742796317)
            ·
              refine ⟨3977260791620407403548619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10606028777654419742796317 3977260791620407403548619)
              ·
                refine ⟨5965891187430611105322929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3977260791620407403548619 5965891187430611105322929)
                ·
                  refine ⟨4474418390572958328992197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5965891187430611105322929 4474418390572958328992197)
                  ·
                    refine ⟨838953448232429686686037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4474418390572958328992197 838953448232429686686037)
                    ·
                      rfl

theorem cell22_2450784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_2450784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450784 prefixEnd_2450784 := by exact prefixLift 2450784
  have htrace : WordTrace (prefixWord ++ tailWord_2450784) baseStart_2450784 baseEnd_2450784 := by
    simpa [prefixWord, tailWord_2450784, baseEnd_2450784] using wordTrace_append hprefix tailTrace_2450784
  have hstable : (prefixWord ++ tailWord_2450784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450784).length < 2 ^ (prefixWord ++ tailWord_2450784).sum := by decide
  have hdescent : baseEnd_2450784 < baseStart_2450784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450857 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 7, 4]
def baseStart_2450857 : Nat := 118140960795 + 2450857 * 2 ^ 59
def prefixEnd_2450857 : Nat := 4983230072969 + 3 ^ 40 * 2450857 * 2
def baseEnd_2450857 : Nat := 838978437624281829610813

theorem tailTrace_2450857 : CollatzResearch.WordTrace tailWord_2450857 prefixEnd_2450857 838978437624281829610813 := by
  unfold tailWord_2450857
  simp only [CollatzResearch.WordTrace]
  refine ⟨89390098481971136896406825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59593398987980757930937883 89390098481971136896406825)
  ·
    refine ⟨67042573861478352672305119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89390098481971136896406825 67042573861478352672305119)
    ·
      refine ⟨100563860792217529008457679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67042573861478352672305119 100563860792217529008457679)
      ·
        refine ⟨150845791188326293512686519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100563860792217529008457679 150845791188326293512686519)
        ·
          refine ⟨226268686782489440269029779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150845791188326293512686519 226268686782489440269029779)
          ·
            refine ⟨339403030173734160403544669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226268686782489440269029779 339403030173734160403544669)
            ·
              refine ⟨127276136315150310151329251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 339403030173734160403544669 127276136315150310151329251)
              ·
                refine ⟨190914204472725465226993877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127276136315150310151329251 190914204472725465226993877)
                ·
                  refine ⟨4474551667329503091257669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 190914204472725465226993877 4474551667329503091257669)
                  ·
                    refine ⟨838978437624281829610813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4474551667329503091257669 838978437624281829610813)
                    ·
                      rfl

theorem cell22_2450857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_2450857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450857 prefixEnd_2450857 := by exact prefixLift 2450857
  have htrace : WordTrace (prefixWord ++ tailWord_2450857) baseStart_2450857 baseEnd_2450857 := by
    simpa [prefixWord, tailWord_2450857, baseEnd_2450857] using wordTrace_append hprefix tailTrace_2450857
  have hstable : (prefixWord ++ tailWord_2450857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450857).length < 2 ^ (prefixWord ++ tailWord_2450857).sum := by decide
  have hdescent : baseEnd_2450857 < baseStart_2450857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450904 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 6, 3]
def baseStart_2450904 : Nat := 118140960795 + 2450904 * 2 ^ 59
def prefixEnd_2450904 : Nat := 4983230072969 + 3 ^ 40 * 2450904 * 2
def baseEnd_2450904 : Nat := 838994526684789373685669

theorem tailTrace_2450904 : CollatzResearch.WordTrace tailWord_2450904 prefixEnd_2450904 838994526684789373685669 := by
  unfold tailWord_2450904
  simp only [CollatzResearch.WordTrace]
  refine ⟨44695906356400431961683883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59594541808533909282245177 44695906356400431961683883)
  ·
    refine ⟨67043859534600647942525825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44695906356400431961683883 67043859534600647942525825)
    ·
      refine ⟨50282894650950485956894369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67043859534600647942525825 50282894650950485956894369)
      ·
        refine ⟨37712170988212864467670777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50282894650950485956894369 37712170988212864467670777)
        ·
          refine ⟨28284128241159648350753083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37712170988212864467670777 28284128241159648350753083)
          ·
            refine ⟨42426192361739472526129625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28284128241159648350753083 42426192361739472526129625)
            ·
              refine ⟨31819644271304604394597219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42426192361739472526129625 31819644271304604394597219)
              ·
                refine ⟨47729466406956906591895829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31819644271304604394597219 47729466406956906591895829)
                ·
                  refine ⟨2237318737826104996495117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47729466406956906591895829 2237318737826104996495117)
                  ·
                    refine ⟨838994526684789373685669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2237318737826104996495117 838994526684789373685669)
                    ·
                      rfl

theorem cell22_2450904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_2450904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450904 prefixEnd_2450904 := by exact prefixLift 2450904
  have htrace : WordTrace (prefixWord ++ tailWord_2450904) baseStart_2450904 baseEnd_2450904 := by
    simpa [prefixWord, tailWord_2450904, baseEnd_2450904] using wordTrace_append hprefix tailTrace_2450904
  have hstable : (prefixWord ++ tailWord_2450904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450904).length < 2 ^ (prefixWord ++ tailWord_2450904).sum := by decide
  have hdescent : baseEnd_2450904 < baseStart_2450904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450951 : List Nat := [1, 1, 4, 3, 2, 2, 3, 6]
def baseStart_2450951 : Nat := 118140960795 + 2450951 * 2 ^ 59
def prefixEnd_2450951 : Nat := 4983230072969 + 3 ^ 40 * 2450951 * 2
def baseEnd_2450951 : Nat := 93223401749477435306725

theorem tailTrace_2450951 : CollatzResearch.WordTrace tailWord_2450951 prefixEnd_2450951 93223401749477435306725 := by
  unfold tailWord_2450951
  simp only [CollatzResearch.WordTrace]
  refine ⟨89393526943630590950328707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59595684629087060633552471 89393526943630590950328707)
  ·
    refine ⟨134090290415445886425493061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89393526943630590950328707 134090290415445886425493061)
    ·
      refine ⟨25141929452896103704779949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134090290415445886425493061 25141929452896103704779949)
      ·
        refine ⟨9428223544836038889292481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25141929452896103704779949 9428223544836038889292481)
        ·
          refine ⟨7071167658627029166969361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9428223544836038889292481 7071167658627029166969361)
          ·
            refine ⟨5303375743970271875227021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7071167658627029166969361 5303375743970271875227021)
            ·
              refine ⟨1988765903988851953210133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5303375743970271875227021 1988765903988851953210133)
              ·
                refine ⟨93223401749477435306725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1988765903988851953210133 93223401749477435306725)
                ·
                  rfl

theorem cell22_2450951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 6].length) (baseStart_2450951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450951 prefixEnd_2450951 := by exact prefixLift 2450951
  have htrace : WordTrace (prefixWord ++ tailWord_2450951) baseStart_2450951 baseEnd_2450951 := by
    simpa [prefixWord, tailWord_2450951, baseEnd_2450951] using wordTrace_append hprefix tailTrace_2450951
  have hstable : (prefixWord ++ tailWord_2450951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450951).length < 2 ^ (prefixWord ++ tailWord_2450951).sum := by decide
  have hdescent : baseEnd_2450951 < baseStart_2450951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450957 : List Nat := [1, 7, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2450957 : Nat := 118140960795 + 2450957 * 2 ^ 59
def prefixEnd_2450957 : Nat := 4983230072969 + 3 ^ 40 * 2450957 * 2
def baseEnd_2450957 : Nat := 279670889889304967370169

theorem tailTrace_2450957 : CollatzResearch.WordTrace tailWord_2450957 prefixEnd_2450957 279670889889304967370169 := by
  unfold tailWord_2450957
  simp only [CollatzResearch.WordTrace]
  refine ⟨89393745781608853975047125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59595830521072569316698083 89393745781608853975047125)
  ·
    refine ⟨2095165916756457515040167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 89393745781608853975047125 2095165916756457515040167)
    ·
      refine ⟨3142748875134686272560251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2095165916756457515040167 3142748875134686272560251)
      ·
        refine ⟨4714123312702029408840377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3142748875134686272560251 4714123312702029408840377)
        ·
          refine ⟨3535592484526522056630283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4714123312702029408840377 3535592484526522056630283)
          ·
            refine ⟨5303388726789783084945425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535592484526522056630283 5303388726789783084945425)
            ·
              refine ⟨3977541545092337313709069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5303388726789783084945425 3977541545092337313709069)
              ·
                refine ⟨1491578079409626492640901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3977541545092337313709069 1491578079409626492640901)
                ·
                  refine ⟨279670889889304967370169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1491578079409626492640901 279670889889304967370169)
                  ·
                    rfl

theorem cell22_2450957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2450957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2450957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2450957 prefixEnd_2450957 := by exact prefixLift 2450957
  have htrace : WordTrace (prefixWord ++ tailWord_2450957) baseStart_2450957 baseEnd_2450957 := by
    simpa [prefixWord, tailWord_2450957, baseEnd_2450957] using wordTrace_append hprefix tailTrace_2450957
  have hstable : (prefixWord ++ tailWord_2450957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450957).length < 2 ^ (prefixWord ++ tailWord_2450957).sum := by decide
  have hdescent : baseEnd_2450957 < baseStart_2450957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451135 : List Nat := [1, 1, 2, 2, 2, 3, 4, 3, 1, 3]
def baseStart_2451135 : Nat := 118140960795 + 2451135 * 2 ^ 59
def prefixEnd_2451135 : Nat := 4983230072969 + 3 ^ 40 * 2451135 * 2
def baseEnd_2451135 : Nat := 839073602705581771159961

theorem tailTrace_2451135 : CollatzResearch.WordTrace tailWord_2451135 prefixEnd_2451135 839073602705581771159961 := by
  unfold tailWord_2451135
  simp only [CollatzResearch.WordTrace]
  refine ⟨89400237974963990375026859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59600158649975993583351239 89400237974963990375026859)
  ·
    refine ⟨134100356962445985562540289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89400237974963990375026859 134100356962445985562540289)
    ·
      refine ⟨100575267721834489171905217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134100356962445985562540289 100575267721834489171905217)
      ·
        refine ⟨75431450791375866878928913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100575267721834489171905217 75431450791375866878928913)
        ·
          refine ⟨56573588093531900159196685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75431450791375866878928913 56573588093531900159196685)
          ·
            refine ⟨21215095535074462559698757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56573588093531900159196685 21215095535074462559698757)
            ·
              refine ⟨3977830412826461729943517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21215095535074462559698757 3977830412826461729943517)
              ·
                refine ⟨1491686404809923148728819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3977830412826461729943517 1491686404809923148728819)
                ·
                  refine ⟨2237529607214884723093229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1491686404809923148728819 2237529607214884723093229)
                  ·
                    refine ⟨839073602705581771159961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2237529607214884723093229 839073602705581771159961)
                    ·
                      rfl

theorem cell22_2451135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 1, 3].length) (baseStart_2451135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451135 prefixEnd_2451135 := by exact prefixLift 2451135
  have htrace : WordTrace (prefixWord ++ tailWord_2451135) baseStart_2451135 baseEnd_2451135 := by
    simpa [prefixWord, tailWord_2451135, baseEnd_2451135] using wordTrace_append hprefix tailTrace_2451135
  have hstable : (prefixWord ++ tailWord_2451135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451135).length < 2 ^ (prefixWord ++ tailWord_2451135).sum := by decide
  have hdescent : baseEnd_2451135 < baseStart_2451135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451148 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 7]
def baseStart_2451148 : Nat := 118140960795 + 2451148 * 2 ^ 59
def prefixEnd_2451148 : Nat := 4983230072969 + 3 ^ 40 * 2451148 * 2
def baseEnd_2451148 : Nat := 279692684290418023528307

theorem tailTrace_2451148 : CollatzResearch.WordTrace tailWord_2451148 prefixEnd_2451148 279692684290418023528307 := by
  unfold tailWord_2451148
  simp only [CollatzResearch.WordTrace]
  refine ⟨44700356061958446797625049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59600474749277929063500065 44700356061958446797625049)
  ·
    refine ⟨33525267046468835098218787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44700356061958446797625049 33525267046468835098218787)
    ·
      refine ⟨50287900569703252647328181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33525267046468835098218787 50287900569703252647328181)
      ·
        refine ⟨4714490678409679935687017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50287900569703252647328181 4714490678409679935687017)
        ·
          refine ⟨3535868008807259951765263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4714490678409679935687017 3535868008807259951765263)
          ·
            refine ⟨5303802013210889927647895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535868008807259951765263 5303802013210889927647895)
            ·
              refine ⟨7955703019816334891471843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5303802013210889927647895 7955703019816334891471843)
              ·
                refine ⟨11933554529724502337207765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7955703019816334891471843 11933554529724502337207765)
                ·
                  refine ⟨279692684290418023528307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11933554529724502337207765 279692684290418023528307)
                  ·
                    rfl

theorem cell22_2451148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_2451148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451148 prefixEnd_2451148 := by exact prefixLift 2451148
  have htrace : WordTrace (prefixWord ++ tailWord_2451148) baseStart_2451148 baseEnd_2451148 := by
    simpa [prefixWord, tailWord_2451148, baseEnd_2451148] using wordTrace_append hprefix tailTrace_2451148
  have hstable : (prefixWord ++ tailWord_2451148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451148).length < 2 ^ (prefixWord ++ tailWord_2451148).sum := by decide
  have hdescent : baseEnd_2451148 < baseStart_2451148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451178 : List Nat := [3, 1, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_2451178 : Nat := 118140960795 + 2451178 * 2 ^ 59
def prefixEnd_2451178 : Nat := 4983230072969 + 3 ^ 40 * 2451178 * 2
def baseEnd_2451178 : Nat := 839088322484343992334829

theorem tailTrace_2451178 : CollatzResearch.WordTrace tailWord_2451178 prefixEnd_2451178 839088322484343992334829 := by
  unfold tailWord_2451178
  simp only [CollatzResearch.WordTrace]
  refine ⟨22350451578452052179710547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59601204209205472479228125 22350451578452052179710547)
  ·
    refine ⟨33525677367678078269565821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22350451578452052179710547 33525677367678078269565821)
    ·
      refine ⟨12572129012879279351087183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33525677367678078269565821 12572129012879279351087183)
      ·
        refine ⟨18858193519318919026630775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12572129012879279351087183 18858193519318919026630775)
        ·
          refine ⟨28287290278978378539946163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18858193519318919026630775 28287290278978378539946163)
          ·
            refine ⟨42430935418467567809919245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28287290278978378539946163 42430935418467567809919245)
            ·
              refine ⟨15911600781925337928719717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42430935418467567809919245 15911600781925337928719717)
              ·
                refine ⟨2983425146611000861634947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15911600781925337928719717 2983425146611000861634947)
                ·
                  refine ⟨4475137719916501292452421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983425146611000861634947 4475137719916501292452421)
                  ·
                    refine ⟨839088322484343992334829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4475137719916501292452421 839088322484343992334829)
                    ·
                      rfl

theorem cell22_2451178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_2451178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451178 prefixEnd_2451178 := by exact prefixLift 2451178
  have htrace : WordTrace (prefixWord ++ tailWord_2451178) baseStart_2451178 baseEnd_2451178 := by
    simpa [prefixWord, tailWord_2451178, baseEnd_2451178] using wordTrace_append hprefix tailTrace_2451178
  have hstable : (prefixWord ++ tailWord_2451178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451178).length < 2 ^ (prefixWord ++ tailWord_2451178).sum := by decide
  have hdescent : baseEnd_2451178 < baseStart_2451178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451191 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 1, 5]
def baseStart_2451191 : Nat := 118140960795 + 2451191 * 2 ^ 59
def prefixEnd_2451191 : Nat := 4983230072969 + 3 ^ 40 * 2451191 * 2
def baseEnd_2451191 : Nat := 839092772650016291759789

theorem tailTrace_2451191 : CollatzResearch.WordTrace tailWord_2451191 prefixEnd_2451191 839092772650016291759789 := by
  unfold tailWord_2451191
  simp only [CollatzResearch.WordTrace]
  refine ⟨89402280462761111939065427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59601520308507407959376951 89402280462761111939065427)
  ·
    refine ⟨134103420694141667908598141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89402280462761111939065427 134103420694141667908598141)
    ·
      refine ⟨50288782760303125465724303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134103420694141667908598141 50288782760303125465724303)
      ·
        refine ⟨75433174140454688198586455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50288782760303125465724303 75433174140454688198586455)
        ·
          refine ⟨113149761210682032297879683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75433174140454688198586455 113149761210682032297879683)
          ·
            refine ⟨169724641816023048446819525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113149761210682032297879683 169724641816023048446819525)
            ·
              refine ⟨31823370340504321583778661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169724641816023048446819525 31823370340504321583778661)
              ·
                refine ⟨5966881938844560296958499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31823370340504321583778661 5966881938844560296958499)
                ·
                  refine ⟨8950322908266840445437749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5966881938844560296958499 8950322908266840445437749)
                  ·
                    refine ⟨839092772650016291759789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8950322908266840445437749 839092772650016291759789)
                    ·
                      rfl

theorem cell22_2451191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_2451191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451191 prefixEnd_2451191 := by exact prefixLift 2451191
  have htrace : WordTrace (prefixWord ++ tailWord_2451191) baseStart_2451191 baseEnd_2451191 := by
    simpa [prefixWord, tailWord_2451191, baseEnd_2451191] using wordTrace_append hprefix tailTrace_2451191
  have hstable : (prefixWord ++ tailWord_2451191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451191).length < 2 ^ (prefixWord ++ tailWord_2451191).sum := by decide
  have hdescent : baseEnd_2451191 < baseStart_2451191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451208 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 4, 3]
def baseStart_2451208 : Nat := 118140960795 + 2451208 * 2 ^ 59
def prefixEnd_2451208 : Nat := 4983230072969 + 3 ^ 40 * 2451208 * 2
def baseEnd_2451208 : Nat := 839098592097433914084737

theorem tailTrace_2451208 : CollatzResearch.WordTrace tailWord_2451208 prefixEnd_2451208 839098592097433914084737 := by
  unfold tailWord_2451208
  simp only [CollatzResearch.WordTrace]
  refine ⟨44701450251849761921217139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59601933669133015894956185 44701450251849761921217139)
  ·
    refine ⟨67052175377774642881825709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44701450251849761921217139 67052175377774642881825709)
    ·
      refine ⟨25144565766665491080684641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67052175377774642881825709 25144565766665491080684641)
      ·
        refine ⟨18858424324999118310513481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25144565766665491080684641 18858424324999118310513481)
        ·
          refine ⟨14143818243749338732885111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18858424324999118310513481 14143818243749338732885111)
          ·
            refine ⟨21215727365624008099327667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14143818243749338732885111 21215727365624008099327667)
            ·
              refine ⟨31823591048436012148991501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21215727365624008099327667 31823591048436012148991501)
              ·
                refine ⟨11933846643163504555871813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31823591048436012148991501 11933846643163504555871813)
                ·
                  refine ⟨2237596245593157104225965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11933846643163504555871813 2237596245593157104225965)
                  ·
                    refine ⟨839098592097433914084737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2237596245593157104225965 839098592097433914084737)
                    ·
                      rfl

theorem cell22_2451208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_2451208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451208 prefixEnd_2451208 := by exact prefixLift 2451208
  have htrace : WordTrace (prefixWord ++ tailWord_2451208) baseStart_2451208 baseEnd_2451208 := by
    simpa [prefixWord, tailWord_2451208, baseEnd_2451208] using wordTrace_append hprefix tailTrace_2451208
  have hstable : (prefixWord ++ tailWord_2451208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451208).length < 2 ^ (prefixWord ++ tailWord_2451208).sum := by decide
  have hdescent : baseEnd_2451208 < baseStart_2451208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451221 : List Nat := [1, 3, 2, 1, 2, 3, 1, 9]
def baseStart_2451221 : Nat := 118140960795 + 2451221 * 2 ^ 59
def prefixEnd_2451221 : Nat := 4983230072969 + 3 ^ 40 * 2451221 * 2
def baseEnd_2451221 : Nat := 93233671362567357056633

theorem tailTrace_2451221 : CollatzResearch.WordTrace tailWord_2451221 prefixEnd_2451221 93233671362567357056633 := by
  unfold tailWord_2451221
  simp only [CollatzResearch.WordTrace]
  refine ⟨89403374652652427062657517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59602249768434951375105011 89403374652652427062657517)
  ·
    refine ⟨33526265494744660148496569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89403374652652427062657517 33526265494744660148496569)
    ·
      refine ⟨25144699121058495111372427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33526265494744660148496569 25144699121058495111372427)
      ·
        refine ⟨37717048681587742667058641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25144699121058495111372427 37717048681587742667058641)
        ·
          refine ⟨28287786511190807000293981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37717048681587742667058641 28287786511190807000293981)
          ·
            refine ⟨10607919941696552625110243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28287786511190807000293981 10607919941696552625110243)
            ·
              refine ⟨15911879912544828937665365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10607919941696552625110243 15911879912544828937665365)
              ·
                refine ⟨93233671362567357056633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15911879912544828937665365 93233671362567357056633)
                ·
                  rfl

theorem cell22_2451221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 9].length) (baseStart_2451221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451221 prefixEnd_2451221 := by exact prefixLift 2451221
  have htrace : WordTrace (prefixWord ++ tailWord_2451221) baseStart_2451221 baseEnd_2451221 := by
    simpa [prefixWord, tailWord_2451221, baseEnd_2451221] using wordTrace_append hprefix tailTrace_2451221
  have hstable : (prefixWord ++ tailWord_2451221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451221).length < 2 ^ (prefixWord ++ tailWord_2451221).sum := by decide
  have hdescent : baseEnd_2451221 < baseStart_2451221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451240 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2451240 : Nat := 118140960795 + 2451240 * 2 ^ 59
def prefixEnd_2451240 : Nat := 4983230072969 + 3 ^ 40 * 2451240 * 2
def baseEnd_2451240 : Nat := 839109546351396497284639

theorem tailTrace_2451240 : CollatzResearch.WordTrace tailWord_2451240 prefixEnd_2451240 839109546351396497284639 := by
  unfold tailWord_2451240
  simp only [CollatzResearch.WordTrace]
  refine ⟨44702033819791796653799587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59602711759722395538399449 44702033819791796653799587)
  ·
    refine ⟨67053050729687694980699381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44702033819791796653799587 67053050729687694980699381)
    ·
      refine ⟨6286223505908221404440567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67053050729687694980699381 6286223505908221404440567)
      ·
        refine ⟨9429335258862332106660851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6286223505908221404440567 9429335258862332106660851)
        ·
          refine ⟨14144002888293498159991277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9429335258862332106660851 14144002888293498159991277)
          ·
            refine ⟨5304001083110061809996729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14144002888293498159991277 5304001083110061809996729)
            ·
              refine ⟨3978000812332546357497547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5304001083110061809996729 3978000812332546357497547)
              ·
                refine ⟨5967001218498819536246321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978000812332546357497547 5967001218498819536246321)
                ·
                  refine ⟨4475250913874114652184741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5967001218498819536246321 4475250913874114652184741)
                  ·
                    refine ⟨839109546351396497284639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4475250913874114652184741 839109546351396497284639)
                    ·
                      rfl

theorem cell22_2451240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2451240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451240 prefixEnd_2451240 := by exact prefixLift 2451240
  have htrace : WordTrace (prefixWord ++ tailWord_2451240) baseStart_2451240 baseEnd_2451240 := by
    simpa [prefixWord, tailWord_2451240, baseEnd_2451240] using wordTrace_append hprefix tailTrace_2451240
  have hstable : (prefixWord ++ tailWord_2451240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451240).length < 2 ^ (prefixWord ++ tailWord_2451240).sum := by decide
  have hdescent : baseEnd_2451240 < baseStart_2451240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451328 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 6]
def baseStart_2451328 : Nat := 118140960795 + 2451328 * 2 ^ 59
def prefixEnd_2451328 : Nat := 4983230072969 + 3 ^ 40 * 2451328 * 2
def baseEnd_2451328 : Nat := 279713223516597867028123

theorem tailTrace_2451328 : CollatzResearch.WordTrace tailWord_2451328 prefixEnd_2451328 279713223516597867028123 := by
  unfold tailWord_2451328
  simp only [CollatzResearch.WordTrace]
  refine ⟨44703638631632392168401319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59604851508843189557868425 44703638631632392168401319)
  ·
    refine ⟨67055457947448588252601979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44703638631632392168401319 67055457947448588252601979)
    ·
      refine ⟨100583186921172882378902969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67055457947448588252601979 100583186921172882378902969)
      ·
        refine ⟨75437390190879661784177227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100583186921172882378902969 75437390190879661784177227)
        ·
          refine ⟨113156085286319492676265841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75437390190879661784177227 113156085286319492676265841)
          ·
            refine ⟨84867063964739619507199381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113156085286319492676265841 84867063964739619507199381)
            ·
              refine ⟨3978143623347169664399971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84867063964739619507199381 3978143623347169664399971)
              ·
                refine ⟨5967215435020754496599957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978143623347169664399971 5967215435020754496599957)
                ·
                  refine ⟨279713223516597867028123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5967215435020754496599957 279713223516597867028123)
                  ·
                    rfl

theorem cell22_2451328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_2451328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451328 prefixEnd_2451328 := by exact prefixLift 2451328
  have htrace : WordTrace (prefixWord ++ tailWord_2451328) baseStart_2451328 baseEnd_2451328 := by
    simpa [prefixWord, tailWord_2451328, baseEnd_2451328] using wordTrace_append hprefix tailTrace_2451328
  have hstable : (prefixWord ++ tailWord_2451328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451328).length < 2 ^ (prefixWord ++ tailWord_2451328).sum := by decide
  have hdescent : baseEnd_2451328 < baseStart_2451328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451390 : List Nat := [4, 2, 1, 1, 1, 4, 2, 7]
def baseStart_2451390 : Nat := 118140960795 + 2451390 * 2 ^ 59
def prefixEnd_2451390 : Nat := 4983230072969 + 3 ^ 40 * 2451390 * 2
def baseEnd_2451390 : Nat := 93240099379649567337131

theorem tailTrace_2451390 : CollatzResearch.WordTrace tailWord_2451390 prefixEnd_2451390 93240099379649567337131 := by
  unfold tailWord_2451390
  simp only [CollatzResearch.WordTrace]
  refine ⟨11176192323630021115694953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59606359059360112617039749 11176192323630021115694953)
  ·
    refine ⟨8382144242722515836771215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11176192323630021115694953 8382144242722515836771215)
    ·
      refine ⟨12573216364083773755156823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8382144242722515836771215 12573216364083773755156823)
      ·
        refine ⟨18859824546125660632735235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12573216364083773755156823 18859824546125660632735235)
        ·
          refine ⟨28289736819188490949102853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18859824546125660632735235 28289736819188490949102853)
          ·
            refine ⟨5304325653597842052956785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28289736819188490949102853 5304325653597842052956785)
            ·
              refine ⟨3978244240198381539717589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5304325653597842052956785 3978244240198381539717589)
              ·
                refine ⟨93240099379649567337131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3978244240198381539717589 93240099379649567337131)
                ·
                  rfl

theorem cell22_2451390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_2451390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451390 prefixEnd_2451390 := by exact prefixLift 2451390
  have htrace : WordTrace (prefixWord ++ tailWord_2451390) baseStart_2451390 baseEnd_2451390 := by
    simpa [prefixWord, tailWord_2451390, baseEnd_2451390] using wordTrace_append hprefix tailTrace_2451390
  have hstable : (prefixWord ++ tailWord_2451390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451390).length < 2 ^ (prefixWord ++ tailWord_2451390).sum := by decide
  have hdescent : baseEnd_2451390 < baseStart_2451390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451482 : List Nat := [3, 1, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_2451482 : Nat := 118140960795 + 2451482 * 2 ^ 59
def prefixEnd_2451482 : Nat := 4983230072969 + 3 ^ 40 * 2451482 * 2
def baseEnd_2451482 : Nat := 839192387896988532733897

theorem tailTrace_2451482 : CollatzResearch.WordTrace tailWord_2451482 prefixEnd_2451482 839192387896988532733897 := by
  unfold tailWord_2451482
  simp only [CollatzResearch.WordTrace]
  refine ⟨22353223526176717159477175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59608596069804579091939133 22353223526176717159477175)
  ·
    refine ⟨33529835289265075739215763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22353223526176717159477175 33529835289265075739215763)
    ·
      refine ⟨50294752933897613608823645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33529835289265075739215763 50294752933897613608823645)
      ·
        refine ⟨18860532350211605103308867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50294752933897613608823645 18860532350211605103308867)
        ·
          refine ⟨28290798525317407654963301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18860532350211605103308867 28290798525317407654963301)
          ·
            refine ⟨5304524723497013935305619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28290798525317407654963301 5304524723497013935305619)
            ·
              refine ⟨7956787085245520902958429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5304524723497013935305619 7956787085245520902958429)
              ·
                refine ⟨2983795156967070338609411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7956787085245520902958429 2983795156967070338609411)
                ·
                  refine ⟨4475692735450605507914117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983795156967070338609411 4475692735450605507914117)
                  ·
                    refine ⟨839192387896988532733897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4475692735450605507914117 839192387896988532733897)
                    ·
                      rfl

theorem cell22_2451482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_2451482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451482 prefixEnd_2451482 := by exact prefixLift 2451482
  have htrace : WordTrace (prefixWord ++ tailWord_2451482) baseStart_2451482 baseEnd_2451482 := by
    simpa [prefixWord, tailWord_2451482, baseEnd_2451482] using wordTrace_append hprefix tailTrace_2451482
  have hstable : (prefixWord ++ tailWord_2451482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451482).length < 2 ^ (prefixWord ++ tailWord_2451482).sum := by decide
  have hdescent : baseEnd_2451482 < baseStart_2451482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451602 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2451602 : Nat := 118140960795 + 2451602 * 2 ^ 59
def prefixEnd_2451602 : Nat := 4983230072969 + 3 ^ 40 * 2451602 * 2
def baseEnd_2451602 : Nat := 839233466349348219733529

theorem tailTrace_2451602 : CollatzResearch.WordTrace tailWord_2451602 prefixEnd_2451602 839233466349348219733529 := by
  unfold tailWord_2451602
  simp only [CollatzResearch.WordTrace]
  refine ⟨22354317716068032283069265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59611513909514752754851373 22354317716068032283069265)
  ·
    refine ⟨16765738287051024212301949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22354317716068032283069265 16765738287051024212301949)
    ·
      refine ⟨6287151857644134079613231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16765738287051024212301949 6287151857644134079613231)
      ·
        refine ⟨9430727786466201119419847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6287151857644134079613231 9430727786466201119419847)
        ·
          refine ⟨14146091679699301679129771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9430727786466201119419847 14146091679699301679129771)
          ·
            refine ⟨21219137519548952518694657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14146091679699301679129771 21219137519548952518694657)
            ·
              refine ⟨15914353139661714389020993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21219137519548952518694657 15914353139661714389020993)
              ·
                refine ⟨11935764854746285791765745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15914353139661714389020993 11935764854746285791765745)
                ·
                  refine ⟨8951823641059714343824309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11935764854746285791765745 8951823641059714343824309)
                  ·
                    refine ⟨839233466349348219733529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8951823641059714343824309 839233466349348219733529)
                    ·
                      rfl

theorem cell22_2451602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2451602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451602 prefixEnd_2451602 := by exact prefixLift 2451602
  have htrace : WordTrace (prefixWord ++ tailWord_2451602) baseStart_2451602 baseEnd_2451602 := by
    simpa [prefixWord, tailWord_2451602, baseEnd_2451602] using wordTrace_append hprefix tailTrace_2451602
  have hstable : (prefixWord ++ tailWord_2451602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451602).length < 2 ^ (prefixWord ++ tailWord_2451602).sum := by decide
  have hdescent : baseEnd_2451602 < baseStart_2451602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451617 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 3, 4]
def baseStart_2451617 : Nat := 118140960795 + 2451617 * 2 ^ 59
def prefixEnd_2451617 : Nat := 4983230072969 + 3 ^ 40 * 2451617 * 2
def baseEnd_2451617 : Nat := 839238601155893180608483

theorem tailTrace_2451617 : CollatzResearch.WordTrace tailWord_2451617 prefixEnd_2451617 839238601155893180608483 := by
  unfold tailWord_2451617
  simp only [CollatzResearch.WordTrace]
  refine ⟨89417817959217786694073105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59611878639478524462715403 89417817959217786694073105)
  ·
    refine ⟨67063363469413340020554829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89417817959217786694073105 67063363469413340020554829)
    ·
      refine ⟨25148761301030002507708061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67063363469413340020554829 25148761301030002507708061)
      ·
        refine ⟨9430785487886250940390523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25148761301030002507708061 9430785487886250940390523)
        ·
          refine ⟨14146178231829376410585785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9430785487886250940390523 14146178231829376410585785)
          ·
            refine ⟨10609633673872032307939339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14146178231829376410585785 10609633673872032307939339)
            ·
              refine ⟨15914450510808048461909009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10609633673872032307939339 15914450510808048461909009)
              ·
                refine ⟨11935837883106036346431757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15914450510808048461909009 11935837883106036346431757)
                ·
                  refine ⟨4475939206164763629911909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11935837883106036346431757 4475939206164763629911909)
                  ·
                    refine ⟨839238601155893180608483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4475939206164763629911909 839238601155893180608483)
                    ·
                      rfl

theorem cell22_2451617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_2451617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451617 prefixEnd_2451617 := by exact prefixLift 2451617
  have htrace : WordTrace (prefixWord ++ tailWord_2451617) baseStart_2451617 baseEnd_2451617 := by
    simpa [prefixWord, tailWord_2451617, baseEnd_2451617] using wordTrace_append hprefix tailTrace_2451617
  have hstable : (prefixWord ++ tailWord_2451617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451617).length < 2 ^ (prefixWord ++ tailWord_2451617).sum := by decide
  have hdescent : baseEnd_2451617 < baseStart_2451617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451647 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 4, 3]
def baseStart_2451647 : Nat := 118140960795 + 2451647 * 2 ^ 59
def prefixEnd_2451647 : Nat := 4983230072969 + 3 ^ 40 * 2451647 * 2
def baseEnd_2451647 : Nat := 839248870768983102358391

theorem tailTrace_2451647 : CollatzResearch.WordTrace tailWord_2451647 prefixEnd_2451647 839248870768983102358391 := by
  unfold tailWord_2451647
  simp only [CollatzResearch.WordTrace]
  refine ⟨89418912149109101817665195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59612608099406067878443463 89418912149109101817665195)
  ·
    refine ⟨134128368223663652726497793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89418912149109101817665195 134128368223663652726497793)
    ·
      refine ⟨100596276167747739544873345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134128368223663652726497793 100596276167747739544873345)
      ·
        refine ⟨75447207125810804658655009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100596276167747739544873345 75447207125810804658655009)
        ·
          refine ⟨56585405344358103493991257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75447207125810804658655009 56585405344358103493991257)
          ·
            refine ⟨42439054008268577620493443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56585405344358103493991257 42439054008268577620493443)
            ·
              refine ⟨63658581012402866430740165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42439054008268577620493443 63658581012402866430740165)
              ·
                refine ⟨11935983939825537455763781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63658581012402866430740165 11935983939825537455763781)
                ·
                  refine ⟨2237996988717288272955709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11935983939825537455763781 2237996988717288272955709)
                  ·
                    refine ⟨839248870768983102358391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2237996988717288272955709 839248870768983102358391)
                    ·
                      rfl

theorem cell22_2451647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 3].length) (baseStart_2451647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451647 prefixEnd_2451647 := by exact prefixLift 2451647
  have htrace : WordTrace (prefixWord ++ tailWord_2451647) baseStart_2451647 baseEnd_2451647 := by
    simpa [prefixWord, tailWord_2451647, baseEnd_2451647] using wordTrace_append hprefix tailTrace_2451647
  have hstable : (prefixWord ++ tailWord_2451647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451647).length < 2 ^ (prefixWord ++ tailWord_2451647).sum := by decide
  have hdescent : baseEnd_2451647 < baseStart_2451647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451675 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 2, 7]
def baseStart_2451675 : Nat := 118140960795 + 2451675 * 2 ^ 59
def prefixEnd_2451675 : Nat := 4983230072969 + 3 ^ 40 * 2451675 * 2
def baseEnd_2451675 : Nat := 839258455741200362658305

theorem tailTrace_2451675 : CollatzResearch.WordTrace tailWord_2451675 prefixEnd_2451675 839258455741200362658305 := by
  unfold tailWord_2451675
  simp only [CollatzResearch.WordTrace]
  refine ⟨89419933393007662599684479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59613288928671775066456319 89419933393007662599684479)
  ·
    refine ⟨134129900089511493899526719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89419933393007662599684479 134129900089511493899526719)
    ·
      refine ⟨201194850134267240849290079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134129900089511493899526719 201194850134267240849290079)
      ·
        refine ⟨301792275201400861273935119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201194850134267240849290079 301792275201400861273935119)
        ·
          refine ⟨452688412802101291910902679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301792275201400861273935119 452688412802101291910902679)
          ·
            refine ⟨679032619203151937866354019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452688412802101291910902679 679032619203151937866354019)
            ·
              refine ⟨1018548928804727906799531029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679032619203151937866354019 1018548928804727906799531029)
              ·
                refine ⟨47744481037721620631228017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1018548928804727906799531029 47744481037721620631228017)
                ·
                  refine ⟨35808360778291215473421013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47744481037721620631228017 35808360778291215473421013)
                  ·
                    refine ⟨839258455741200362658305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35808360778291215473421013 839258455741200362658305)
                    ·
                      rfl

theorem cell22_2451675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_2451675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451675 prefixEnd_2451675 := by exact prefixLift 2451675
  have htrace : WordTrace (prefixWord ++ tailWord_2451675) baseStart_2451675 baseEnd_2451675 := by
    simpa [prefixWord, tailWord_2451675, baseEnd_2451675] using wordTrace_append hprefix tailTrace_2451675
  have hstable : (prefixWord ++ tailWord_2451675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451675).length < 2 ^ (prefixWord ++ tailWord_2451675).sum := by decide
  have hdescent : baseEnd_2451675 < baseStart_2451675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451681 : List Nat := [1, 2, 3, 1, 3, 1, 5, 1, 2, 3]
def baseStart_2451681 : Nat := 118140960795 + 2451681 * 2 ^ 59
def prefixEnd_2451681 : Nat := 4983230072969 + 3 ^ 40 * 2451681 * 2
def baseEnd_2451681 : Nat := 839260509663818347008287

theorem tailTrace_2451681 : CollatzResearch.WordTrace tailWord_2451681 prefixEnd_2451681 839260509663818347008287 := by
  unfold tailWord_2451681
  simp only [CollatzResearch.WordTrace]
  refine ⟨89420152230985925624402897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59613434820657283749601931 89420152230985925624402897)
  ·
    refine ⟨67065114173239444218302173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89420152230985925624402897 67065114173239444218302173)
    ·
      refine ⟨25149417814964791581863315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67065114173239444218302173 25149417814964791581863315)
      ·
        refine ⟨37724126722447187372794973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25149417814964791581863315 37724126722447187372794973)
        ·
          refine ⟨14146547520917695264798115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37724126722447187372794973 14146547520917695264798115)
          ·
            refine ⟨21219821281376542897197173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14146547520917695264798115 21219821281376542897197173)
            ·
              refine ⟨1989358245129050896612235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21219821281376542897197173 1989358245129050896612235)
              ·
                refine ⟨2984037367693576344918353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989358245129050896612235 2984037367693576344918353)
                ·
                  refine ⟨2238028025770182258688765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2984037367693576344918353 2238028025770182258688765)
                  ·
                    refine ⟨839260509663818347008287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2238028025770182258688765 839260509663818347008287)
                    ·
                      rfl

theorem cell22_2451681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_2451681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451681 prefixEnd_2451681 := by exact prefixLift 2451681
  have htrace : WordTrace (prefixWord ++ tailWord_2451681) baseStart_2451681 baseEnd_2451681 := by
    simpa [prefixWord, tailWord_2451681, baseEnd_2451681] using wordTrace_append hprefix tailTrace_2451681
  have hstable : (prefixWord ++ tailWord_2451681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451681).length < 2 ^ (prefixWord ++ tailWord_2451681).sum := by decide
  have hdescent : baseEnd_2451681 < baseStart_2451681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451722 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 7]
def baseStart_2451722 : Nat := 118140960795 + 2451722 * 2 ^ 59
def prefixEnd_2451722 : Nat := 4983230072969 + 3 ^ 40 * 2451722 * 2
def baseEnd_2451722 : Nat := 279758181600569302244387

theorem tailTrace_2451722 : CollatzResearch.WordTrace tailWord_2451722 prefixEnd_2451722 279758181600569302244387 := by
  unfold tailWord_2451722
  simp only [CollatzResearch.WordTrace]
  refine ⟨22355411905959347406661355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59614431749224926417763613 22355411905959347406661355)
  ·
    refine ⟨33533117858939021109992033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22355411905959347406661355 33533117858939021109992033)
    ·
      refine ⟨25149838394204265832494025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33533117858939021109992033 25149838394204265832494025)
      ·
        refine ⟨18862378795653199374370519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25149838394204265832494025 18862378795653199374370519)
        ·
          refine ⟨28293568193479799061555779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18862378795653199374370519 28293568193479799061555779)
          ·
            refine ⟨42440352290219698592333669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28293568193479799061555779 42440352290219698592333669)
            ·
              refine ⟨7957566054416193486062563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42440352290219698592333669 7957566054416193486062563)
              ·
                refine ⟨11936349081624290229093845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7957566054416193486062563 11936349081624290229093845)
                ·
                  refine ⟨279758181600569302244387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11936349081624290229093845 279758181600569302244387)
                  ·
                    rfl

theorem cell22_2451722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_2451722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451722 prefixEnd_2451722 := by exact prefixLift 2451722
  have htrace : WordTrace (prefixWord ++ tailWord_2451722) baseStart_2451722 baseEnd_2451722 := by
    simpa [prefixWord, tailWord_2451722, baseEnd_2451722] using wordTrace_append hprefix tailTrace_2451722
  have hstable : (prefixWord ++ tailWord_2451722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451722).length < 2 ^ (prefixWord ++ tailWord_2451722).sum := by decide
  have hdescent : baseEnd_2451722 < baseStart_2451722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451739 : List Nat := [1, 1, 1, 1, 1, 1, 10, 1, 5]
def baseStart_2451739 : Nat := 118140960795 + 2451739 * 2 ^ 59
def prefixEnd_2451739 : Nat := 4983230072969 + 3 ^ 40 * 2451739 * 2
def baseEnd_2451739 : Nat := 279760121416375176352703

theorem tailTrace_2451739 : CollatzResearch.WordTrace tailWord_2451739 prefixEnd_2451739 279760121416375176352703 := by
  unfold tailWord_2451739
  simp only [CollatzResearch.WordTrace]
  refine ⟨89422267664775801530014271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59614845109850534353342847 89422267664775801530014271)
  ·
    refine ⟨134133401497163702295021407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89422267664775801530014271 134133401497163702295021407)
    ·
      refine ⟨201200102245745553442532111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134133401497163702295021407 201200102245745553442532111)
      ·
        refine ⟨301800153368618330163798167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201200102245745553442532111 301800153368618330163798167)
        ·
          refine ⟨452700230052927495245697251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301800153368618330163798167 452700230052927495245697251)
          ·
            refine ⟨679050345079391242868545877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452700230052927495245697251 679050345079391242868545877)
            ·
              refine ⟨1989405307849779031841443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 679050345079391242868545877 1989405307849779031841443)
              ·
                refine ⟨2984107961774668547762165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989405307849779031841443 2984107961774668547762165)
                ·
                  refine ⟨279760121416375176352703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2984107961774668547762165 279760121416375176352703)
                  ·
                    rfl

theorem cell22_2451739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 5].length) (baseStart_2451739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451739 prefixEnd_2451739 := by exact prefixLift 2451739
  have htrace : WordTrace (prefixWord ++ tailWord_2451739) baseStart_2451739 baseEnd_2451739 := by
    simpa [prefixWord, tailWord_2451739, baseEnd_2451739] using wordTrace_append hprefix tailTrace_2451739
  have hstable : (prefixWord ++ tailWord_2451739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451739).length < 2 ^ (prefixWord ++ tailWord_2451739).sum := by decide
  have hdescent : baseEnd_2451739 < baseStart_2451739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451777 : List Nat := [1, 2, 5, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2451777 : Nat := 118140960795 + 2451777 * 2 ^ 59
def prefixEnd_2451777 : Nat := 4983230072969 + 3 ^ 40 * 2451777 * 2
def baseEnd_2451777 : Nat := 839293372425706096607993

theorem tailTrace_2451777 : CollatzResearch.WordTrace tailWord_2451777 prefixEnd_2451777 839293372425706096607993 := by
  unfold tailWord_2451777
  simp only [CollatzResearch.WordTrace]
  refine ⟨89423653638638134019897585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59615769092425422679931723 89423653638638134019897585)
  ·
    refine ⟨67067740228978600514923189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89423653638638134019897585 67067740228978600514923189)
    ·
      refine ⟨6287600646466743798274049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67067740228978600514923189 6287600646466743798274049)
      ·
        refine ⟨4715700484850057848705537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6287600646466743798274049 4715700484850057848705537)
        ·
          refine ⟨3536775363637543386529153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4715700484850057848705537 3536775363637543386529153)
          ·
            refine ⟨2652581522728157539896865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3536775363637543386529153 2652581522728157539896865)
            ·
              refine ⟨1989436142046118154922649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2652581522728157539896865 1989436142046118154922649)
              ·
                refine ⟨1492077106534588616191987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989436142046118154922649 1492077106534588616191987)
                ·
                  refine ⟨2238115659801882924287981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492077106534588616191987 2238115659801882924287981)
                  ·
                    refine ⟨839293372425706096607993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2238115659801882924287981 839293372425706096607993)
                    ·
                      rfl

theorem cell22_2451777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2451777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451777 prefixEnd_2451777 := by exact prefixLift 2451777
  have htrace : WordTrace (prefixWord ++ tailWord_2451777) baseStart_2451777 baseEnd_2451777 := by
    simpa [prefixWord, tailWord_2451777, baseEnd_2451777] using wordTrace_append hprefix tailTrace_2451777
  have hstable : (prefixWord ++ tailWord_2451777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451777).length < 2 ^ (prefixWord ++ tailWord_2451777).sum := by decide
  have hdescent : baseEnd_2451777 < baseStart_2451777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451799 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 1, 5]
def baseStart_2451799 : Nat := 118140960795 + 2451799 * 2 ^ 59
def prefixEnd_2451799 : Nat := 4983230072969 + 3 ^ 40 * 2451799 * 2
def baseEnd_2451799 : Nat := 839300903475305372557925

theorem tailTrace_2451799 : CollatzResearch.WordTrace tailWord_2451799 prefixEnd_2451799 839300903475305372557925 := by
  unfold tailWord_2451799
  simp only [CollatzResearch.WordTrace]
  refine ⟨89424456044558431777198451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59616304029705621184798967 89424456044558431777198451)
  ·
    refine ⟨134136684066837647665797677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89424456044558431777198451 134136684066837647665797677)
    ·
      refine ⟨50301256525064117874674129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134136684066837647665797677 50301256525064117874674129)
      ·
        refine ⟨37725942393798088406005597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50301256525064117874674129 37725942393798088406005597)
        ·
          refine ⟨14147228397674283152252099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37725942393798088406005597 14147228397674283152252099)
          ·
            refine ⟨21220842596511424728378149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14147228397674283152252099 21220842596511424728378149)
            ·
              refine ⟨3978907986845892136570903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21220842596511424728378149 3978907986845892136570903)
              ·
                refine ⟨5968361980268838204856355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978907986845892136570903 5968361980268838204856355)
                ·
                  refine ⟨8952542970403257307284533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5968361980268838204856355 8952542970403257307284533)
                  ·
                    refine ⟨839300903475305372557925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8952542970403257307284533 839300903475305372557925)
                    ·
                      rfl

theorem cell22_2451799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_2451799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451799 prefixEnd_2451799 := by exact prefixLift 2451799
  have htrace : WordTrace (prefixWord ++ tailWord_2451799) baseStart_2451799 baseEnd_2451799 := by
    simpa [prefixWord, tailWord_2451799, baseEnd_2451799] using wordTrace_append hprefix tailTrace_2451799
  have hstable : (prefixWord ++ tailWord_2451799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451799).length < 2 ^ (prefixWord ++ tailWord_2451799).sum := by decide
  have hdescent : baseEnd_2451799 < baseStart_2451799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451818 : List Nat := [3, 1, 3, 3, 1, 2, 2, 3, 4]
def baseStart_2451818 : Nat := 118140960795 + 2451818 * 2 ^ 59
def prefixEnd_2451818 : Nat := 4983230072969 + 3 ^ 40 * 2451818 * 2
def baseEnd_2451818 : Nat := 279769135854531885444289

theorem tailTrace_2451818 : CollatzResearch.WordTrace tailWord_2451818 prefixEnd_2451818 279769135854531885444289 := by
  unfold tailWord_2451818
  simp only [CollatzResearch.WordTrace]
  refine ⟨22356287257872399505535027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59616766020993065348093405 22356287257872399505535027)
  ·
    refine ⟨33534430886808599258302541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22356287257872399505535027 33534430886808599258302541)
    ·
      refine ⟨12575411582553224721863453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33534430886808599258302541 12575411582553224721863453)
      ·
        refine ⟨4715779343457459270698795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12575411582553224721863453 4715779343457459270698795)
        ·
          refine ⟨7073669015186188906048193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4715779343457459270698795 7073669015186188906048193)
          ·
            refine ⟨5305251761389641679536145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7073669015186188906048193 5305251761389641679536145)
            ·
              refine ⟨3978938821042231259652109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5305251761389641679536145 3978938821042231259652109)
              ·
                refine ⟨1492102057890836722369541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3978938821042231259652109 1492102057890836722369541)
                ·
                  refine ⟨279769135854531885444289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1492102057890836722369541 279769135854531885444289)
                  ·
                    rfl

theorem cell22_2451818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_2451818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451818 prefixEnd_2451818 := by exact prefixLift 2451818
  have htrace : WordTrace (prefixWord ++ tailWord_2451818) baseStart_2451818 baseEnd_2451818 := by
    simpa [prefixWord, tailWord_2451818, baseEnd_2451818] using wordTrace_append hprefix tailTrace_2451818
  have hstable : (prefixWord ++ tailWord_2451818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451818).length < 2 ^ (prefixWord ++ tailWord_2451818).sum := by decide
  have hdescent : baseEnd_2451818 < baseStart_2451818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451820 : List Nat := [2, 2, 1, 1, 7, 1, 2, 1, 1, 4]
def baseStart_2451820 : Nat := 118140960795 + 2451820 * 2 ^ 59
def prefixEnd_2451820 : Nat := 4983230072969 + 3 ^ 40 * 2451820 * 2
def baseEnd_2451820 : Nat := 839308092204468317782861

theorem tailTrace_2451820 : CollatzResearch.WordTrace tailWord_2451820 prefixEnd_2451820 839308092204468317782861 := by
  unfold tailWord_2451820
  simp only [CollatzResearch.WordTrace]
  refine ⟨44712610988741176181856457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59616814651654901575808609 44712610988741176181856457)
  ·
    refine ⟨33534458241555882136392343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44712610988741176181856457 33534458241555882136392343)
    ·
      refine ⟨50301687362333823204588515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33534458241555882136392343 50301687362333823204588515)
      ·
        refine ⟨75452531043500734806882773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50301687362333823204588515 75452531043500734806882773)
        ·
          refine ⟨1768418696332048472036315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 75452531043500734806882773 1768418696332048472036315)
          ·
            refine ⟨2652628044498072708054473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768418696332048472036315 2652628044498072708054473)
            ·
              refine ⟨1989471033373554531040855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2652628044498072708054473 1989471033373554531040855)
              ·
                refine ⟨2984206550060331796561283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989471033373554531040855 2984206550060331796561283)
                ·
                  refine ⟨4476309825090497694841925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984206550060331796561283 4476309825090497694841925)
                  ·
                    refine ⟨839308092204468317782861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4476309825090497694841925 839308092204468317782861)
                    ·
                      rfl

theorem cell22_2451820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_2451820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451820 prefixEnd_2451820 := by exact prefixLift 2451820
  have htrace : WordTrace (prefixWord ++ tailWord_2451820) baseStart_2451820 baseEnd_2451820 := by
    simpa [prefixWord, tailWord_2451820, baseEnd_2451820] using wordTrace_append hprefix tailTrace_2451820
  have hstable : (prefixWord ++ tailWord_2451820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451820).length < 2 ^ (prefixWord ++ tailWord_2451820).sum := by decide
  have hdescent : baseEnd_2451820 < baseStart_2451820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451829 : List Nat := [1, 3, 4, 1, 2, 2, 9]
def baseStart_2451829 : Nat := 118140960795 + 2451829 * 2 ^ 59
def prefixEnd_2451829 : Nat := 4983230072969 + 3 ^ 40 * 2451829 * 2
def baseEnd_2451829 : Nat := 31085599003273899789179

theorem tailTrace_2451829 : CollatzResearch.WordTrace tailWord_2451829 prefixEnd_2451829 31085599003273899789179 := by
  unfold tailWord_2451829
  simp only [CollatzResearch.WordTrace]
  refine ⟨89425550234449746900790541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59617033489633164600527027 89425550234449746900790541)
  ·
    refine ⟨33534581337918655087796453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89425550234449746900790541 33534581337918655087796453)
    ·
      refine ⟨6287734000859747828961835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33534581337918655087796453 6287734000859747828961835)
      ·
        refine ⟨9431601001289621743442753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6287734000859747828961835 9431601001289621743442753)
        ·
          refine ⟨7073700750967216307582065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9431601001289621743442753 7073700750967216307582065)
          ·
            refine ⟨5305275563225412230686549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7073700750967216307582065 5305275563225412230686549)
            ·
              refine ⟨31085599003273899789179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5305275563225412230686549 31085599003273899789179)
              ·
                rfl

theorem cell22_2451829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 9].length) (baseStart_2451829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451829 prefixEnd_2451829 := by exact prefixLift 2451829
  have htrace : WordTrace (prefixWord ++ tailWord_2451829) baseStart_2451829 baseEnd_2451829 := by
    simpa [prefixWord, tailWord_2451829, baseEnd_2451829] using wordTrace_append hprefix tailTrace_2451829
  have hstable : (prefixWord ++ tailWord_2451829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451829).length < 2 ^ (prefixWord ++ tailWord_2451829).sum := by decide
  have hdescent : baseEnd_2451829 < baseStart_2451829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451850 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 1, 5]
def baseStart_2451850 : Nat := 118140960795 + 2451850 * 2 ^ 59
def prefixEnd_2451850 : Nat := 4983230072969 + 3 ^ 40 * 2451850 * 2
def baseEnd_2451850 : Nat := 839318361817558239532769

theorem tailTrace_2451850 : CollatzResearch.WordTrace tailWord_2451850 prefixEnd_2451850 839318361817558239532769 := by
  unfold tailWord_2451850
  simp only [CollatzResearch.WordTrace]
  refine ⟨22356579041843416871826251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59617544111582444991536669 22356579041843416871826251)
  ·
    refine ⟨33534868562765125307739377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22356579041843416871826251 33534868562765125307739377)
    ·
      refine ⟨25151151422073843980804533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33534868562765125307739377 25151151422073843980804533)
      ·
        refine ⟨2357920445819422873200425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25151151422073843980804533 2357920445819422873200425)
        ·
          refine ⟨1768440334364567154900319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2357920445819422873200425 1768440334364567154900319)
          ·
            refine ⟨2652660501546850732350479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768440334364567154900319 2652660501546850732350479)
            ·
              refine ⟨3978990752320276098525719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652660501546850732350479 3978990752320276098525719)
              ·
                refine ⟨5968486128480414147788579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978990752320276098525719 5968486128480414147788579)
                ·
                  refine ⟨8952729192720621221682869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5968486128480414147788579 8952729192720621221682869)
                  ·
                    refine ⟨839318361817558239532769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8952729192720621221682869 839318361817558239532769)
                    ·
                      rfl

theorem cell22_2451850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_2451850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451850 prefixEnd_2451850 := by exact prefixLift 2451850
  have htrace : WordTrace (prefixWord ++ tailWord_2451850) baseStart_2451850 baseEnd_2451850 := by
    simpa [prefixWord, tailWord_2451850, baseEnd_2451850] using wordTrace_append hprefix tailTrace_2451850
  have hstable : (prefixWord ++ tailWord_2451850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451850).length < 2 ^ (prefixWord ++ tailWord_2451850).sum := by decide
  have hdescent : baseEnd_2451850 < baseStart_2451850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451857 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 11]
def baseStart_2451857 : Nat := 118140960795 + 2451857 * 2 ^ 59
def prefixEnd_2451857 : Nat := 4983230072969 + 3 ^ 40 * 2451857 * 2
def baseEnd_2451857 : Nat := 279773586020204184869249

theorem tailTrace_2451857 : CollatzResearch.WordTrace tailWord_2451857 prefixEnd_2451857 279773586020204184869249 := by
  unfold tailWord_2451857
  simp only [CollatzResearch.WordTrace]
  refine ⟨89426571478348307682809825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59617714318898871788539883 89426571478348307682809825)
  ·
    refine ⟨67069928608761230762107369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89426571478348307682809825 67069928608761230762107369)
    ·
      refine ⟨50302446456570923071580527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67069928608761230762107369 50302446456570923071580527)
      ·
        refine ⟨75453669684856384607370791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50302446456570923071580527 75453669684856384607370791)
        ·
          refine ⟨113180504527284576911056187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75453669684856384607370791 113180504527284576911056187)
          ·
            refine ⟨169770756790926865366584281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113180504527284576911056187 169770756790926865366584281)
            ·
              refine ⟨127328067593195149024938211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169770756790926865366584281 127328067593195149024938211)
              ·
                refine ⟨190992101389792723537407317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127328067593195149024938211 190992101389792723537407317)
                ·
                  refine ⟨279773586020204184869249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 190992101389792723537407317 279773586020204184869249)
                  ·
                    rfl

theorem cell22_2451857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_2451857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451857 prefixEnd_2451857 := by exact prefixLift 2451857
  have htrace : WordTrace (prefixWord ++ tailWord_2451857) baseStart_2451857 baseEnd_2451857 := by
    simpa [prefixWord, tailWord_2451857, baseEnd_2451857] using wordTrace_append hprefix tailTrace_2451857
  have hstable : (prefixWord ++ tailWord_2451857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451857).length < 2 ^ (prefixWord ++ tailWord_2451857).sum := by decide
  have hdescent : baseEnd_2451857 < baseStart_2451857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451874 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 9]
def baseStart_2451874 : Nat := 118140960795 + 2451874 * 2 ^ 59
def prefixEnd_2451874 : Nat := 4983230072969 + 3 ^ 40 * 2451874 * 2
def baseEnd_2451874 : Nat := 279775525836010058977565

theorem tailTrace_2451874 : CollatzResearch.WordTrace tailWord_2451874 prefixEnd_2451874 279775525836010058977565 := by
  unfold tailWord_2451874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22356797879821679896544669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59618127679524479724119117 22356797879821679896544669)
  ·
    refine ⟨8383799204933129961204251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22356797879821679896544669 8383799204933129961204251)
    ·
      refine ⟨12575698807399694941806377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8383799204933129961204251 12575698807399694941806377)
      ·
        refine ⟨9431774105549771206354783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12575698807399694941806377 9431774105549771206354783)
        ·
          refine ⟨14147661158324656809532175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9431774105549771206354783 14147661158324656809532175)
          ·
            refine ⟨21221491737486985214298263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14147661158324656809532175 21221491737486985214298263)
            ·
              refine ⟨31832237606230477821447395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21221491737486985214298263 31832237606230477821447395)
              ·
                refine ⟨47748356409345716732171093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31832237606230477821447395 47748356409345716732171093)
                ·
                  refine ⟨279775525836010058977565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47748356409345716732171093 279775525836010058977565)
                  ·
                    rfl

theorem cell22_2451874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_2451874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451874 prefixEnd_2451874 := by exact prefixLift 2451874
  have htrace : WordTrace (prefixWord ++ tailWord_2451874) baseStart_2451874 baseEnd_2451874 := by
    simpa [prefixWord, tailWord_2451874, baseEnd_2451874] using wordTrace_append hprefix tailTrace_2451874
  have hstable : (prefixWord ++ tailWord_2451874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451874).length < 2 ^ (prefixWord ++ tailWord_2451874).sum := by decide
  have hdescent : baseEnd_2451874 < baseStart_2451874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
