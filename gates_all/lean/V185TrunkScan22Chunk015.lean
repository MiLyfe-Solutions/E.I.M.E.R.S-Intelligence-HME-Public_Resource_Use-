import V185TrunkScan22Chunk014

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_132460 : List Nat := [2, 2, 1, 1, 5, 2, 3, 6]
def baseStart_132460 : Nat := 118140960795 + 132460 * 2 ^ 59
def prefixEnd_132460 : Nat := 4983230072969 + 3 ^ 40 * 132460 * 2
def baseEnd_132460 : Nat := 5038196110715332099321

theorem tailTrace_132460 : CollatzResearch.WordTrace tailWord_132460 prefixEnd_132460 5038196110715332099321 := by
  unfold tailWord_132460
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415606550063758606025417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3220808733418344808033889 2415606550063758606025417)
  ·
    refine ⟨1811704912547818954519063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2415606550063758606025417 1811704912547818954519063)
    ·
      refine ⟨2717557368821728431778595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1811704912547818954519063 2717557368821728431778595)
      ·
        refine ⟨4076336053232592647667893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2717557368821728431778595 4076336053232592647667893)
        ·
          refine ⟨382156504990555560718865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4076336053232592647667893 382156504990555560718865)
          ·
            refine ⟨286617378742916670539149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382156504990555560718865 286617378742916670539149)
            ·
              refine ⟨107481517028593751452181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286617378742916670539149 107481517028593751452181)
              ·
                refine ⟨5038196110715332099321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107481517028593751452181 5038196110715332099321)
                ·
                  rfl

theorem cell22_132460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 6].length) (baseStart_132460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132460 prefixEnd_132460 := by exact prefixLift 132460
  have htrace : WordTrace (prefixWord ++ tailWord_132460) baseStart_132460 baseEnd_132460 := by
    simpa [prefixWord, tailWord_132460, baseEnd_132460] using wordTrace_append hprefix tailTrace_132460
  have hstable : (prefixWord ++ tailWord_132460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132460).length < 2 ^ (prefixWord ++ tailWord_132460).sum := by decide
  have hdescent : baseEnd_132460 < baseStart_132460 := by decide
  rcases family_descends (prefixWord ++ tailWord_132460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132462 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_132462 : Nat := 118140960795 + 132462 * 2 ^ 59
def prefixEnd_132462 : Nat := 4983230072969 + 3 ^ 40 * 132462 * 2
def baseEnd_132462 : Nat := 45344449637310650343883

theorem tailTrace_132462 : CollatzResearch.WordTrace tailWord_132462 prefixEnd_132462 45344449637310650343883 := by
  unfold tailWord_132462
  simp only [CollatzResearch.WordTrace]
  refine ⟨603910755765033944202955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3220857364080181035749093 603910755765033944202955)
  ·
    refine ⟨905866133647550916304433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 603910755765033944202955 905866133647550916304433)
    ·
      refine ⟨679399600235663187228325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 905866133647550916304433 679399600235663187228325)
      ·
        refine ⟨127387425044186847605311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 679399600235663187228325 127387425044186847605311)
        ·
          refine ⟨191081137566280271407967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127387425044186847605311 191081137566280271407967)
          ·
            refine ⟨286621706349420407111951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191081137566280271407967 286621706349420407111951)
            ·
              refine ⟨429932559524130610667927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286621706349420407111951 429932559524130610667927)
              ·
                refine ⟨644898839286195916001891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429932559524130610667927 644898839286195916001891)
                ·
                  refine ⟨967348258929293874002837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644898839286195916001891 967348258929293874002837)
                  ·
                    refine ⟨45344449637310650343883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 967348258929293874002837 45344449637310650343883)
                    ·
                      rfl

theorem cell22_132462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_132462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132462 prefixEnd_132462 := by exact prefixLift 132462
  have htrace : WordTrace (prefixWord ++ tailWord_132462) baseStart_132462 baseEnd_132462 := by
    simpa [prefixWord, tailWord_132462, baseEnd_132462] using wordTrace_append hprefix tailTrace_132462
  have hstable : (prefixWord ++ tailWord_132462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132462).length < 2 ^ (prefixWord ++ tailWord_132462).sum := by decide
  have hdescent : baseEnd_132462 < baseStart_132462 := by decide
  rcases family_descends (prefixWord ++ tailWord_132462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132481 : List Nat := [1, 2, 4, 3, 3, 1, 1, 2, 2, 3]
def baseStart_132481 : Nat := 118140960795 + 132481 * 2 ^ 59
def prefixEnd_132481 : Nat := 4983230072969 + 3 ^ 40 * 132481 * 2
def baseEnd_132481 : Nat := 45350953725600934118825

theorem tailTrace_132481 : CollatzResearch.WordTrace tailWord_132481 prefixEnd_132481 45350953725600934118825 := by
  unfold tailWord_132481
  simp only [CollatzResearch.WordTrace]
  refine ⟨4831979033051437798565297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3221319355367625199043531 4831979033051437798565297)
  ·
    refine ⟨3623984274788578348923973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4831979033051437798565297 3623984274788578348923973)
    ·
      refine ⟨679497051522858440423245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3623984274788578348923973 679497051522858440423245)
      ·
        refine ⟨254811394321071915158717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 679497051522858440423245 254811394321071915158717)
        ·
          refine ⟨95554272870401968184519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254811394321071915158717 95554272870401968184519)
          ·
            refine ⟨143331409305602952276779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95554272870401968184519 143331409305602952276779)
            ·
              refine ⟨214997113958404428415169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143331409305602952276779 214997113958404428415169)
              ·
                refine ⟨161247835468803321311377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214997113958404428415169 161247835468803321311377)
                ·
                  refine ⟨120935876601602490983533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161247835468803321311377 120935876601602490983533)
                  ·
                    refine ⟨45350953725600934118825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120935876601602490983533 45350953725600934118825)
                    ·
                      rfl

theorem cell22_132481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_132481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132481 prefixEnd_132481 := by exact prefixLift 132481
  have htrace : WordTrace (prefixWord ++ tailWord_132481) baseStart_132481 baseEnd_132481 := by
    simpa [prefixWord, tailWord_132481, baseEnd_132481] using wordTrace_append hprefix tailTrace_132481
  have hstable : (prefixWord ++ tailWord_132481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132481).length < 2 ^ (prefixWord ++ tailWord_132481).sum := by decide
  have hdescent : baseEnd_132481 < baseStart_132481 := by decide
  rcases family_descends (prefixWord ++ tailWord_132481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132492 : List Nat := [2, 2, 1, 2, 1, 3, 1, 6, 1, 3]
def baseStart_132492 : Nat := 118140960795 + 132492 * 2 ^ 59
def prefixEnd_132492 : Nat := 4983230072969 + 3 ^ 40 * 132492 * 2
def baseEnd_132492 : Nat := 45354719250400572093791

theorem tailTrace_132492 : CollatzResearch.WordTrace tailWord_132492 prefixEnd_132492 45354719250400572093791 := by
  unfold tailWord_132492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2416190118005793338607865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3221586824007724451477153 2416190118005793338607865)
  ·
    refine ⟨1812142588504345003955899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2416190118005793338607865 1812142588504345003955899)
    ·
      refine ⟨2718213882756517505933849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1812142588504345003955899 2718213882756517505933849)
      ·
        refine ⟨2038660412067388129450387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2718213882756517505933849 2038660412067388129450387)
        ·
          refine ⟨3057990618101082194175581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038660412067388129450387 3057990618101082194175581)
          ·
            refine ⟨1146746481787905822815843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3057990618101082194175581 1146746481787905822815843)
            ·
              refine ⟨1720119722681858734223765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146746481787905822815843 1720119722681858734223765)
              ·
                refine ⟨80630612000712128166739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1720119722681858734223765 80630612000712128166739)
                ·
                  refine ⟨120945918001068192250109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80630612000712128166739 120945918001068192250109)
                  ·
                    refine ⟨45354719250400572093791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120945918001068192250109 45354719250400572093791)
                    ·
                      rfl

theorem cell22_132492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_132492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132492 prefixEnd_132492 := by exact prefixLift 132492
  have htrace : WordTrace (prefixWord ++ tailWord_132492) baseStart_132492 baseEnd_132492 := by
    simpa [prefixWord, tailWord_132492, baseEnd_132492] using wordTrace_append hprefix tailTrace_132492
  have hstable : (prefixWord ++ tailWord_132492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132492).length < 2 ^ (prefixWord ++ tailWord_132492).sum := by decide
  have hdescent : baseEnd_132492 < baseStart_132492 := by decide
  rcases family_descends (prefixWord ++ tailWord_132492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132535 : List Nat := [1, 1, 3, 1, 3, 2, 1, 5, 1, 4]
def baseStart_132535 : Nat := 118140960795 + 132535 * 2 ^ 59
def prefixEnd_132535 : Nat := 4983230072969 + 3 ^ 40 * 132535 * 2
def baseEnd_132535 : Nat := 45369439029162793268659

theorem tailTrace_132535 : CollatzResearch.WordTrace tailWord_132535 prefixEnd_132535 45369439029162793268659 := by
  unfold tailWord_132535
  simp only [CollatzResearch.WordTrace]
  refine ⟨4833948574855805021031059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3222632383237203347354039 4833948574855805021031059)
  ·
    refine ⟨7250922862283707531546589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4833948574855805021031059 7250922862283707531546589)
    ·
      refine ⟨2719096073356390324329971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7250922862283707531546589 2719096073356390324329971)
      ·
        refine ⟨4078644110034585486494957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2719096073356390324329971 4078644110034585486494957)
        ·
          refine ⟨1529491541262969557435609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4078644110034585486494957 1529491541262969557435609)
          ·
            refine ⟨1147118655947227168076707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1529491541262969557435609 1147118655947227168076707)
            ·
              refine ⟨1720677983920840752115061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147118655947227168076707 1720677983920840752115061)
              ·
                refine ⟨161313560992578820510787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1720677983920840752115061 161313560992578820510787)
                ·
                  refine ⟨241970341488868230766181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161313560992578820510787 241970341488868230766181)
                  ·
                    refine ⟨45369439029162793268659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241970341488868230766181 45369439029162793268659)
                    ·
                      rfl

theorem cell22_132535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_132535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132535 prefixEnd_132535 := by exact prefixLift 132535
  have htrace : WordTrace (prefixWord ++ tailWord_132535) baseStart_132535 baseEnd_132535 := by
    simpa [prefixWord, tailWord_132535, baseEnd_132535] using wordTrace_append hprefix tailTrace_132535
  have hstable : (prefixWord ++ tailWord_132535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132535).length < 2 ^ (prefixWord ++ tailWord_132535).sum := by decide
  have hdescent : baseEnd_132535 < baseStart_132535 := by decide
  rcases family_descends (prefixWord ++ tailWord_132535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132565 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_132565 : Nat := 118140960795 + 132565 * 2 ^ 59
def prefixEnd_132565 : Nat := 4983230072969 + 3 ^ 40 * 132565 * 2
def baseEnd_132565 : Nat := 45379708642252715018567

theorem tailTrace_132565 : CollatzResearch.WordTrace tailWord_132565 prefixEnd_132565 45379708642252715018567 := by
  unfold tailWord_132565
  simp only [CollatzResearch.WordTrace]
  refine ⟨4835042764747120144623149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3223361843164746763082099 4835042764747120144623149)
  ·
    refine ⟨1813141036780170054233681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4835042764747120144623149 1813141036780170054233681)
    ·
      refine ⟨1359855777585127540675261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1813141036780170054233681 1359855777585127540675261)
      ·
        refine ⟨509945916594422827753223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1359855777585127540675261 509945916594422827753223)
        ·
          refine ⟨764918874891634241629835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509945916594422827753223 764918874891634241629835)
          ·
            refine ⟨1147378312337451362444753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764918874891634241629835 1147378312337451362444753)
            ·
              refine ⟨860533734253088521833565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1147378312337451362444753 860533734253088521833565)
              ·
                refine ⟨322700150344908195687587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 860533734253088521833565 322700150344908195687587)
                ·
                  refine ⟨484050225517362293531381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322700150344908195687587 484050225517362293531381)
                  ·
                    refine ⟨45379708642252715018567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 484050225517362293531381 45379708642252715018567)
                    ·
                      rfl

theorem cell22_132565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_132565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132565 prefixEnd_132565 := by exact prefixLift 132565
  have htrace : WordTrace (prefixWord ++ tailWord_132565) baseStart_132565 baseEnd_132565 := by
    simpa [prefixWord, tailWord_132565, baseEnd_132565] using wordTrace_append hprefix tailTrace_132565
  have hstable : (prefixWord ++ tailWord_132565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132565).length < 2 ^ (prefixWord ++ tailWord_132565).sum := by decide
  have hdescent : baseEnd_132565 < baseStart_132565 := by decide
  rcases family_descends (prefixWord ++ tailWord_132565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132627 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 3, 3]
def baseStart_132627 : Nat := 118140960795 + 132627 * 2 ^ 59
def prefixEnd_132627 : Nat := 4983230072969 + 3 ^ 40 * 132627 * 2
def baseEnd_132627 : Nat := 45400932509305219968377

theorem tailTrace_132627 : CollatzResearch.WordTrace tailWord_132627 prefixEnd_132627 45400932509305219968377 := by
  unfold tailWord_132627
  simp only [CollatzResearch.WordTrace]
  refine ⟨4837304090522504733380135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3224869393681669822253423 4837304090522504733380135)
  ·
    refine ⟨7255956135783757100070203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4837304090522504733380135 7255956135783757100070203)
    ·
      refine ⟨10883934203675635650105305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7255956135783757100070203 10883934203675635650105305)
      ·
        refine ⟨8162950652756726737578979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10883934203675635650105305 8162950652756726737578979)
        ·
          refine ⟨12244425979135090106368469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8162950652756726737578979 12244425979135090106368469)
          ·
            refine ⟨286978733885978674368011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 12244425979135090106368469 286978733885978674368011)
            ·
              refine ⟨430468100828968011552017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286978733885978674368011 430468100828968011552017)
              ·
                refine ⟨322851075621726008664013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430468100828968011552017 322851075621726008664013)
                ·
                  refine ⟨121069153358147253249005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322851075621726008664013 121069153358147253249005)
                  ·
                    refine ⟨45400932509305219968377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121069153358147253249005 45400932509305219968377)
                    ·
                      rfl

theorem cell22_132627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 3].length) (baseStart_132627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132627 prefixEnd_132627 := by exact prefixLift 132627
  have htrace : WordTrace (prefixWord ++ tailWord_132627) baseStart_132627 baseEnd_132627 := by
    simpa [prefixWord, tailWord_132627, baseEnd_132627] using wordTrace_append hprefix tailTrace_132627
  have hstable : (prefixWord ++ tailWord_132627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132627).length < 2 ^ (prefixWord ++ tailWord_132627).sum := by decide
  have hdescent : baseEnd_132627 < baseStart_132627 := by decide
  rcases family_descends (prefixWord ++ tailWord_132627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132745 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 2, 7]
def baseStart_132745 : Nat := 118140960795 + 132745 * 2 ^ 59
def prefixEnd_132745 : Nat := 4983230072969 + 3 ^ 40 * 132745 * 2
def baseEnd_132745 : Nat := 45441326320792245518015

theorem tailTrace_132745 : CollatzResearch.WordTrace tailWord_132745 prefixEnd_132745 45441326320792245518015 := by
  unfold tailWord_132745
  simp only [CollatzResearch.WordTrace]
  refine ⟨4841607904095010886175689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3227738602730007257450459 4841607904095010886175689)
  ·
    refine ⟨3631205928071258164631767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4841607904095010886175689 3631205928071258164631767)
    ·
      refine ⟨5446808892106887246947651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631205928071258164631767 5446808892106887246947651)
      ·
        refine ⟨8170213338160330870421477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5446808892106887246947651 8170213338160330870421477)
        ·
          refine ⟨1531915000905062038204027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8170213338160330870421477 1531915000905062038204027)
          ·
            refine ⟨2297872501357593057306041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531915000905062038204027 2297872501357593057306041)
            ·
              refine ⟨1723404376018194792979531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2297872501357593057306041 1723404376018194792979531)
              ·
                refine ⟨2585106564027292189469297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723404376018194792979531 2585106564027292189469297)
                ·
                  refine ⟨1938829923020469142101973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2585106564027292189469297 1938829923020469142101973)
                  ·
                    refine ⟨45441326320792245518015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1938829923020469142101973 45441326320792245518015)
                    ·
                      rfl

theorem cell22_132745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_132745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132745 prefixEnd_132745 := by exact prefixLift 132745
  have htrace : WordTrace (prefixWord ++ tailWord_132745) baseStart_132745 baseEnd_132745 := by
    simpa [prefixWord, tailWord_132745, baseEnd_132745] using wordTrace_append hprefix tailTrace_132745
  have hstable : (prefixWord ++ tailWord_132745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132745).length < 2 ^ (prefixWord ++ tailWord_132745).sum := by decide
  have hdescent : baseEnd_132745 < baseStart_132745 := by decide
  rcases family_descends (prefixWord ++ tailWord_132745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132770 : List Nat := [3, 3, 1, 4, 1, 2, 2, 2, 4]
def baseStart_132770 : Nat := 118140960795 + 132770 * 2 ^ 59
def prefixEnd_132770 : Nat := 4983230072969 + 3 ^ 40 * 132770 * 2
def baseEnd_132770 : Nat := 15149961443900171214313

theorem tailTrace_132770 : CollatzResearch.WordTrace tailWord_132770 prefixEnd_132770 15149961443900171214313 := by
  unfold tailWord_132770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1210629932251110038958941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3228346486002960103890509 1210629932251110038958941)
  ·
    refine ⟨453986224594166264609603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1210629932251110038958941 453986224594166264609603)
    ·
      refine ⟨680979336891249396914405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453986224594166264609603 680979336891249396914405)
      ·
        refine ⟨127683625667109261921451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 680979336891249396914405 127683625667109261921451)
        ·
          refine ⟨191525438500663892882177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127683625667109261921451 191525438500663892882177)
          ·
            refine ⟨143644078875497919661633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191525438500663892882177 143644078875497919661633)
            ·
              refine ⟨107733059156623439746225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143644078875497919661633 107733059156623439746225)
              ·
                refine ⟨80799794367467579809669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107733059156623439746225 80799794367467579809669)
                ·
                  refine ⟨15149961443900171214313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80799794367467579809669 15149961443900171214313)
                  ·
                    rfl

theorem cell22_132770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_132770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132770 prefixEnd_132770 := by exact prefixLift 132770
  have htrace : WordTrace (prefixWord ++ tailWord_132770) baseStart_132770 baseEnd_132770 := by
    simpa [prefixWord, tailWord_132770, baseEnd_132770] using wordTrace_append hprefix tailTrace_132770
  have hstable : (prefixWord ++ tailWord_132770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132770).length < 2 ^ (prefixWord ++ tailWord_132770).sum := by decide
  have hdescent : baseEnd_132770 < baseStart_132770 := by decide
  rcases family_descends (prefixWord ++ tailWord_132770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132854 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_132854 : Nat := 118140960795 + 132854 * 2 ^ 59
def prefixEnd_132854 : Nat := 4983230072969 + 3 ^ 40 * 132854 * 2
def baseEnd_132854 : Nat := 15159546416117431514227

theorem tailTrace_132854 : CollatzResearch.WordTrace tailWord_132854 prefixEnd_132854 15159546416117431514227 := by
  unfold tailWord_132854
  simp only [CollatzResearch.WordTrace]
  refine ⟨302848966293757656368351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3230388973800081667929077 302848966293757656368351)
  ·
    refine ⟨454273449440636484552527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302848966293757656368351 454273449440636484552527)
    ·
      refine ⟨681410174160954726828791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454273449440636484552527 681410174160954726828791)
      ·
        refine ⟨1022115261241432090243187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681410174160954726828791 1022115261241432090243187)
        ·
          refine ⟨1533172891862148135364781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022115261241432090243187 1533172891862148135364781)
          ·
            refine ⟨574939834448305550761793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1533172891862148135364781 574939834448305550761793)
            ·
              refine ⟨431204875836229163071345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574939834448305550761793 431204875836229163071345)
              ·
                refine ⟨323403656877171872303509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431204875836229163071345 323403656877171872303509)
                ·
                  refine ⟨15159546416117431514227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 323403656877171872303509 15159546416117431514227)
                  ·
                    rfl

theorem cell22_132854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_132854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132854 prefixEnd_132854 := by exact prefixLift 132854
  have htrace : WordTrace (prefixWord ++ tailWord_132854) baseStart_132854 baseEnd_132854 := by
    simpa [prefixWord, tailWord_132854, baseEnd_132854] using wordTrace_append hprefix tailTrace_132854
  have hstable : (prefixWord ++ tailWord_132854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132854).length < 2 ^ (prefixWord ++ tailWord_132854).sum := by decide
  have hdescent : baseEnd_132854 < baseStart_132854 := by decide
  rcases family_descends (prefixWord ++ tailWord_132854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132867 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 1, 6]
def baseStart_132867 : Nat := 118140960795 + 132867 * 2 ^ 59
def prefixEnd_132867 : Nat := 4983230072969 + 3 ^ 40 * 132867 * 2
def baseEnd_132867 : Nat := 45483089414024593967641

theorem tailTrace_132867 : CollatzResearch.WordTrace tailWord_132867 prefixEnd_132867 45483089414024593967641 := by
  unfold tailWord_132867
  simp only [CollatzResearch.WordTrace]
  refine ⟨4846057609653025722116855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3230705073102017148077903 4846057609653025722116855)
  ·
    refine ⟨7269086414479538583175283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4846057609653025722116855 7269086414479538583175283)
    ·
      refine ⟨10903629621719307874762925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7269086414479538583175283 10903629621719307874762925)
      ·
        refine ⟨4088861108144740453036097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10903629621719307874762925 4088861108144740453036097)
        ·
          refine ⟨3066645831108555339777073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4088861108144740453036097 3066645831108555339777073)
          ·
            refine ⟨2299984373331416504832805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3066645831108555339777073 2299984373331416504832805)
            ·
              refine ⟨431247069999640594656151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2299984373331416504832805 431247069999640594656151)
              ·
                refine ⟨646870604999460891984227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431247069999640594656151 646870604999460891984227)
                ·
                  refine ⟨970305907499191337976341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646870604999460891984227 970305907499191337976341)
                  ·
                    refine ⟨45483089414024593967641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 970305907499191337976341 45483089414024593967641)
                    ·
                      rfl

theorem cell22_132867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 6].length) (baseStart_132867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132867 prefixEnd_132867 := by exact prefixLift 132867
  have htrace : WordTrace (prefixWord ++ tailWord_132867) baseStart_132867 baseEnd_132867 := by
    simpa [prefixWord, tailWord_132867, baseEnd_132867] using wordTrace_append hprefix tailTrace_132867
  have hstable : (prefixWord ++ tailWord_132867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132867).length < 2 ^ (prefixWord ++ tailWord_132867).sum := by decide
  have hdescent : baseEnd_132867 < baseStart_132867 := by decide
  rcases family_descends (prefixWord ++ tailWord_132867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132918 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_132918 : Nat := 118140960795 + 132918 * 2 ^ 59
def prefixEnd_132918 : Nat := 4983230072969 + 3 ^ 40 * 132918 * 2
def baseEnd_132918 : Nat := 45500547756277460942485

theorem tailTrace_132918 : CollatzResearch.WordTrace tailWord_132918 prefixEnd_132918 45500547756277460942485 := by
  unfold tailWord_132918
  simp only [CollatzResearch.WordTrace]
  refine ⟨302994858279266339513963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3231945154978840954815605 302994858279266339513963)
  ·
    refine ⟨454492287418899509270945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302994858279266339513963 454492287418899509270945)
    ·
      refine ⟨340869215564174631953209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454492287418899509270945 340869215564174631953209)
      ·
        refine ⟨255651911673130973964907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340869215564174631953209 255651911673130973964907)
        ·
          refine ⟨383477867509696460947361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255651911673130973964907 383477867509696460947361)
          ·
            refine ⟨287608400632272345710521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383477867509696460947361 287608400632272345710521)
            ·
              refine ⟨215706300474204259282891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287608400632272345710521 215706300474204259282891)
              ·
                refine ⟨323559450711306388924337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215706300474204259282891 323559450711306388924337)
                ·
                  refine ⟨242669588033479791693253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323559450711306388924337 242669588033479791693253)
                  ·
                    refine ⟨45500547756277460942485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242669588033479791693253 45500547756277460942485)
                    ·
                      rfl

theorem cell22_132918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_132918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132918 prefixEnd_132918 := by exact prefixLift 132918
  have htrace : WordTrace (prefixWord ++ tailWord_132918) baseStart_132918 baseEnd_132918 := by
    simpa [prefixWord, tailWord_132918, baseEnd_132918] using wordTrace_append hprefix tailTrace_132918
  have hstable : (prefixWord ++ tailWord_132918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132918).length < 2 ^ (prefixWord ++ tailWord_132918).sum := by decide
  have hdescent : baseEnd_132918 < baseStart_132918 := by decide
  rcases family_descends (prefixWord ++ tailWord_132918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132959 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 2, 5]
def baseStart_132959 : Nat := 118140960795 + 132959 * 2 ^ 59
def prefixEnd_132959 : Nat := 4983230072969 + 3 ^ 40 * 132959 * 2
def baseEnd_132959 : Nat := 45514582894167020667359

theorem tailTrace_132959 : CollatzResearch.WordTrace tailWord_132959 prefixEnd_132959 45514582894167020667359 := by
  unfold tailWord_132959
  simp only [CollatzResearch.WordTrace]
  refine ⟨4849413125319725434465931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3232942083546483622977287 4849413125319725434465931)
  ·
    refine ⟨7274119687979588151698897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4849413125319725434465931 7274119687979588151698897)
    ·
      refine ⟨5455589765984691113774173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7274119687979588151698897 5455589765984691113774173)
      ·
        refine ⟨2045846162244259167665315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5455589765984691113774173 2045846162244259167665315)
        ·
          refine ⟨3068769243366388751497973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2045846162244259167665315 3068769243366388751497973)
          ·
            refine ⟨287697116565598945452935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3068769243366388751497973 287697116565598945452935)
            ·
              refine ⟨431545674848398418179403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287697116565598945452935 431545674848398418179403)
              ·
                refine ⟨647318512272597627269105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431545674848398418179403 647318512272597627269105)
                ·
                  refine ⟨485488884204448220451829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 647318512272597627269105 485488884204448220451829)
                  ·
                    refine ⟨45514582894167020667359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 485488884204448220451829 45514582894167020667359)
                    ·
                      rfl

theorem cell22_132959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_132959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132959 prefixEnd_132959 := by exact prefixLift 132959
  have htrace : WordTrace (prefixWord ++ tailWord_132959) baseStart_132959 baseEnd_132959 := by
    simpa [prefixWord, tailWord_132959, baseEnd_132959] using wordTrace_append hprefix tailTrace_132959
  have hstable : (prefixWord ++ tailWord_132959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132959).length < 2 ^ (prefixWord ++ tailWord_132959).sum := by decide
  have hdescent : baseEnd_132959 < baseStart_132959 := by decide
  rcases family_descends (prefixWord ++ tailWord_132959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132982 : List Nat := [5, 1, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_132982 : Nat := 118140960795 + 132982 * 2 ^ 59
def prefixEnd_132982 : Nat := 4983230072969 + 3 ^ 40 * 132982 * 2
def baseEnd_132982 : Nat := 45522456264202627342289

theorem tailTrace_132982 : CollatzResearch.WordTrace tailWord_132982 prefixEnd_132982 45522456264202627342289 := by
  unfold tailWord_132982
  simp only [CollatzResearch.WordTrace]
  refine ⟨303140750264775022659575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3233501336157600241702133 303140750264775022659575)
  ·
    refine ⟨454711125397162533989363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303140750264775022659575 454711125397162533989363)
    ·
      refine ⟨682066688095743800984045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454711125397162533989363 682066688095743800984045)
      ·
        refine ⟨255775008035903925369017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 682066688095743800984045 255775008035903925369017)
        ·
          refine ⟨191831256026927944026763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255775008035903925369017 191831256026927944026763)
          ·
            refine ⟨287746884040391916040145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191831256026927944026763 287746884040391916040145)
            ·
              refine ⟨215810163030293937030109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287746884040391916040145 215810163030293937030109)
              ·
                refine ⟨80928811136360226386291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215810163030293937030109 80928811136360226386291)
                ·
                  refine ⟨121393216704540339579437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80928811136360226386291 121393216704540339579437)
                  ·
                    refine ⟨45522456264202627342289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121393216704540339579437 45522456264202627342289)
                    ·
                      rfl

theorem cell22_132982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_132982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132982 prefixEnd_132982 := by exact prefixLift 132982
  have htrace : WordTrace (prefixWord ++ tailWord_132982) baseStart_132982 baseEnd_132982 := by
    simpa [prefixWord, tailWord_132982, baseEnd_132982] using wordTrace_append hprefix tailTrace_132982
  have hstable : (prefixWord ++ tailWord_132982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132982).length < 2 ^ (prefixWord ++ tailWord_132982).sum := by decide
  have hdescent : baseEnd_132982 < baseStart_132982 := by decide
  rcases family_descends (prefixWord ++ tailWord_132982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133021 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_133021 : Nat := 118140960795 + 133021 * 2 ^ 59
def prefixEnd_133021 : Nat := 4983230072969 + 3 ^ 40 * 133021 * 2
def baseEnd_133021 : Nat := 45535806761219525617169

theorem tailTrace_133021 : CollatzResearch.WordTrace tailWord_133021 prefixEnd_133021 45535806761219525617169 := by
  unfold tailWord_133021
  simp only [CollatzResearch.WordTrace]
  refine ⟨4851674451095110023222917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3234449634063406682148611 4851674451095110023222917)
  ·
    refine ⟨909688959580333129354297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4851674451095110023222917 909688959580333129354297)
    ·
      refine ⟨682266719685249847015723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 909688959580333129354297 682266719685249847015723)
      ·
        refine ⟨1023400079527874770523585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682266719685249847015723 1023400079527874770523585)
        ·
          refine ⟨767550059645906077892689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1023400079527874770523585 767550059645906077892689)
          ·
            refine ⟨575662544734429558419517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767550059645906077892689 575662544734429558419517)
            ·
              refine ⟨215873454275411084407319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575662544734429558419517 215873454275411084407319)
              ·
                refine ⟨323810181413116626610979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215873454275411084407319 323810181413116626610979)
                ·
                  refine ⟨485715272119674939916469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323810181413116626610979 485715272119674939916469)
                  ·
                    refine ⟨45535806761219525617169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 485715272119674939916469 45535806761219525617169)
                    ·
                      rfl

theorem cell22_133021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_133021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133021 prefixEnd_133021 := by exact prefixLift 133021
  have htrace : WordTrace (prefixWord ++ tailWord_133021) baseStart_133021 baseEnd_133021 := by
    simpa [prefixWord, tailWord_133021, baseEnd_133021] using wordTrace_append hprefix tailTrace_133021
  have hstable : (prefixWord ++ tailWord_133021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133021).length < 2 ^ (prefixWord ++ tailWord_133021).sum := by decide
  have hdescent : baseEnd_133021 < baseStart_133021 := by decide
  rcases family_descends (prefixWord ++ tailWord_133021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133171 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 2, 4]
def baseStart_133171 : Nat := 118140960795 + 133171 * 2 ^ 59
def prefixEnd_133171 : Nat := 4983230072969 + 3 ^ 40 * 133171 * 2
def baseEnd_133171 : Nat := 45587154826669134366709

theorem tailTrace_133171 : CollatzResearch.WordTrace tailWord_133171 prefixEnd_133171 45587154826669134366709 := by
  unfold tailWord_133171
  simp only [CollatzResearch.WordTrace]
  refine ⟨4857145400551685641183367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3238096933701123760788911 4857145400551685641183367)
  ·
    refine ⟨7285718100827528461775051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4857145400551685641183367 7285718100827528461775051)
    ·
      refine ⟨10928577151241292692662577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7285718100827528461775051 10928577151241292692662577)
      ·
        refine ⟨8196432863430969519496933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10928577151241292692662577 8196432863430969519496933)
        ·
          refine ⟨1536831161893306784905675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8196432863430969519496933 1536831161893306784905675)
          ·
            refine ⟨2305246742839960177358513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1536831161893306784905675 2305246742839960177358513)
            ·
              refine ⟨1728935057129970133018885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2305246742839960177358513 1728935057129970133018885)
              ·
                refine ⟨324175323211869399941041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1728935057129970133018885 324175323211869399941041)
                ·
                  refine ⟨243131492408902049955781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324175323211869399941041 243131492408902049955781)
                  ·
                    refine ⟨45587154826669134366709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 243131492408902049955781 45587154826669134366709)
                    ·
                      rfl

theorem cell22_133171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 4].length) (baseStart_133171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133171 prefixEnd_133171 := by exact prefixLift 133171
  have htrace : WordTrace (prefixWord ++ tailWord_133171) baseStart_133171 baseEnd_133171 := by
    simpa [prefixWord, tailWord_133171, baseEnd_133171] using wordTrace_append hprefix tailTrace_133171
  have hstable : (prefixWord ++ tailWord_133171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133171).length < 2 ^ (prefixWord ++ tailWord_133171).sum := by decide
  have hdescent : baseEnd_133171 < baseStart_133171 := by decide
  rcases family_descends (prefixWord ++ tailWord_133171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133231 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 7]
def baseStart_133231 : Nat := 118140960795 + 133231 * 2 ^ 59
def prefixEnd_133231 : Nat := 4983230072969 + 3 ^ 40 * 133231 * 2
def baseEnd_133231 : Nat := 15202564684282992622175

theorem tailTrace_133231 : CollatzResearch.WordTrace tailWord_133231 prefixEnd_133231 15202564684282992622175 := by
  unfold tailWord_133231
  simp only [CollatzResearch.WordTrace]
  refine ⟨4859333780334315888367547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3239555853556210592245031 4859333780334315888367547)
  ·
    refine ⟨7289000670501473832551321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4859333780334315888367547 7289000670501473832551321)
    ·
      refine ⟨5466750502876105374413491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7289000670501473832551321 5466750502876105374413491)
      ·
        refine ⟨8200125754314158061620237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5466750502876105374413491 8200125754314158061620237)
        ·
          refine ⟨3075047157867809273107589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8200125754314158061620237 3075047157867809273107589)
          ·
            refine ⟨576571342100214238707673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3075047157867809273107589 576571342100214238707673)
            ·
              refine ⟨432428506575160679030755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576571342100214238707673 432428506575160679030755)
              ·
                refine ⟨648642759862741018546133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432428506575160679030755 648642759862741018546133)
                ·
                  refine ⟨15202564684282992622175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 648642759862741018546133 15202564684282992622175)
                  ·
                    rfl

theorem cell22_133231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 7].length) (baseStart_133231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133231 prefixEnd_133231 := by exact prefixLift 133231
  have htrace : WordTrace (prefixWord ++ tailWord_133231) baseStart_133231 baseEnd_133231 := by
    simpa [prefixWord, tailWord_133231, baseEnd_133231] using wordTrace_append hprefix tailTrace_133231
  have hstable : (prefixWord ++ tailWord_133231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133231).length < 2 ^ (prefixWord ++ tailWord_133231).sum := by decide
  have hdescent : baseEnd_133231 < baseStart_133231 := by decide
  rcases family_descends (prefixWord ++ tailWord_133231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133310 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_133310 : Nat := 118140960795 + 133310 * 2 ^ 59
def prefixEnd_133310 : Nat := 4983230072969 + 3 ^ 40 * 133310 * 2
def baseEnd_133310 : Nat := 15211579122439701713761

theorem tailTrace_133310 : CollatzResearch.WordTrace tailWord_133310 prefixEnd_133310 15211579122439701713761 := by
  unfold tailWord_133310
  simp only [CollatzResearch.WordTrace]
  refine ⟨607776893381014047561673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3241476764698741586995589 607776893381014047561673)
  ·
    refine ⟨455832670035760535671255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 607776893381014047561673 455832670035760535671255)
    ·
      refine ⟨683749005053640803506883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455832670035760535671255 683749005053640803506883)
      ·
        refine ⟨1025623507580461205260325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683749005053640803506883 1025623507580461205260325)
        ·
          refine ⟨192304407671336475986311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1025623507580461205260325 192304407671336475986311)
          ·
            refine ⟨288456611507004713979467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192304407671336475986311 288456611507004713979467)
            ·
              refine ⟨432684917260507070969201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288456611507004713979467 432684917260507070969201)
              ·
                refine ⟨324513687945380303226901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432684917260507070969201 324513687945380303226901)
                ·
                  refine ⟨15211579122439701713761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 324513687945380303226901 15211579122439701713761)
                  ·
                    rfl

theorem cell22_133310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_133310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133310 prefixEnd_133310 := by exact prefixLift 133310
  have htrace : WordTrace (prefixWord ++ tailWord_133310) baseStart_133310 baseEnd_133310 := by
    simpa [prefixWord, tailWord_133310, baseEnd_133310] using wordTrace_append hprefix tailTrace_133310
  have hstable : (prefixWord ++ tailWord_133310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133310).length < 2 ^ (prefixWord ++ tailWord_133310).sum := by decide
  have hdescent : baseEnd_133310 < baseStart_133310 := by decide
  rcases family_descends (prefixWord ++ tailWord_133310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133353 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 7, 3]
def baseStart_133353 : Nat := 118140960795 + 133353 * 2 ^ 59
def prefixEnd_133353 : Nat := 4983230072969 + 3 ^ 40 * 133353 * 2
def baseEnd_133353 : Nat := 45649457146081326316151

theorem tailTrace_133353 : CollatzResearch.WordTrace tailWord_133353 prefixEnd_133353 45649457146081326316151 := by
  unfold tailWord_133353
  simp only [CollatzResearch.WordTrace]
  refine ⟨4863783485892330724308713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3242522323928220482872475 4863783485892330724308713)
  ·
    refine ⟨3647837614419248043231535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4863783485892330724308713 3647837614419248043231535)
    ·
      refine ⟨5471756421628872064847303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3647837614419248043231535 5471756421628872064847303)
      ·
        refine ⟨8207634632443308097270955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5471756421628872064847303 8207634632443308097270955)
        ·
          refine ⟨12311451948664962145906433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8207634632443308097270955 12311451948664962145906433)
          ·
            refine ⟨9233588961498721609429825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12311451948664962145906433 9233588961498721609429825)
            ·
              refine ⟨6925191721124041207072369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9233588961498721609429825 6925191721124041207072369)
              ·
                refine ⟨5193893790843030905304277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6925191721124041207072369 5193893790843030905304277)
                ·
                  refine ⟨121731885722883536843069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5193893790843030905304277 121731885722883536843069)
                  ·
                    refine ⟨45649457146081326316151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121731885722883536843069 45649457146081326316151)
                    ·
                      rfl

theorem cell22_133353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 3].length) (baseStart_133353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133353 prefixEnd_133353 := by exact prefixLift 133353
  have htrace : WordTrace (prefixWord ++ tailWord_133353) baseStart_133353 baseEnd_133353 := by
    simpa [prefixWord, tailWord_133353, baseEnd_133353] using wordTrace_append hprefix tailTrace_133353
  have hstable : (prefixWord ++ tailWord_133353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133353).length < 2 ^ (prefixWord ++ tailWord_133353).sum := by decide
  have hdescent : baseEnd_133353 < baseStart_133353 := by decide
  rcases family_descends (prefixWord ++ tailWord_133353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133370 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 3, 3]
def baseStart_133370 : Nat := 118140960795 + 133370 * 2 ^ 59
def prefixEnd_133370 : Nat := 4983230072969 + 3 ^ 40 * 133370 * 2
def baseEnd_133370 : Nat := 45655276593498948641099

theorem tailTrace_133370 : CollatzResearch.WordTrace tailWord_133370 prefixEnd_133370 45655276593498948641099 := by
  unfold tailWord_133370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1216100881707685656919391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3242935684553828418451709 1216100881707685656919391)
  ·
    refine ⟨1824151322561528485379087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1216100881707685656919391 1824151322561528485379087)
    ·
      refine ⟨2736226983842292728068631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1824151322561528485379087 2736226983842292728068631)
      ·
        refine ⟨4104340475763439092102947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2736226983842292728068631 4104340475763439092102947)
        ·
          refine ⟨6156510713645158638154421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4104340475763439092102947 6156510713645158638154421)
          ·
            refine ⟨577172879404233622326977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6156510713645158638154421 577172879404233622326977)
            ·
              refine ⟨432879659553175216745233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577172879404233622326977 432879659553175216745233)
              ·
                refine ⟨324659744664881412558925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432879659553175216745233 324659744664881412558925)
                ·
                  refine ⟨121747404249330529709597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324659744664881412558925 121747404249330529709597)
                  ·
                    refine ⟨45655276593498948641099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121747404249330529709597 45655276593498948641099)
                    ·
                      rfl

theorem cell22_133370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_133370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133370 prefixEnd_133370 := by exact prefixLift 133370
  have htrace : WordTrace (prefixWord ++ tailWord_133370) baseStart_133370 baseEnd_133370 := by
    simpa [prefixWord, tailWord_133370, baseEnd_133370] using wordTrace_append hprefix tailTrace_133370
  have hstable : (prefixWord ++ tailWord_133370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133370).length < 2 ^ (prefixWord ++ tailWord_133370).sum := by decide
  have hdescent : baseEnd_133370 < baseStart_133370 := by decide
  rcases family_descends (prefixWord ++ tailWord_133370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133443 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 3, 5]
def baseStart_133443 : Nat := 118140960795 + 133443 * 2 ^ 59
def prefixEnd_133443 : Nat := 4983230072969 + 3 ^ 40 * 133443 * 2
def baseEnd_133443 : Nat := 45680265985351091565875

theorem tailTrace_133443 : CollatzResearch.WordTrace tailWord_133443 prefixEnd_133443 45680265985351091565875 := by
  unfold tailWord_133443
  simp only [CollatzResearch.WordTrace]
  refine ⟨4867066055566276095084983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3244710703710850730056655 4867066055566276095084983)
  ·
    refine ⟨7300599083349414142627475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4867066055566276095084983 7300599083349414142627475)
    ·
      refine ⟨10950898625024121213941213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7300599083349414142627475 10950898625024121213941213)
      ·
        refine ⟨4106586984384045455227955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10950898625024121213941213 4106586984384045455227955)
        ·
          refine ⟨6159880476576068182841933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4106586984384045455227955 6159880476576068182841933)
          ·
            refine ⟨2309955178716025568565725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6159880476576068182841933 2309955178716025568565725)
            ·
              refine ⟨866233192018509588212147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2309955178716025568565725 866233192018509588212147)
              ·
                refine ⟨1299349788027764382318221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866233192018509588212147 1299349788027764382318221)
                ·
                  refine ⟨487256170510411643369333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1299349788027764382318221 487256170510411643369333)
                  ·
                    refine ⟨45680265985351091565875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 487256170510411643369333 45680265985351091565875)
                    ·
                      rfl

theorem cell22_133443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_133443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133443 prefixEnd_133443 := by exact prefixLift 133443
  have htrace : WordTrace (prefixWord ++ tailWord_133443) baseStart_133443 baseEnd_133443 := by
    simpa [prefixWord, tailWord_133443, baseEnd_133443] using wordTrace_append hprefix tailTrace_133443
  have hstable : (prefixWord ++ tailWord_133443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133443).length < 2 ^ (prefixWord ++ tailWord_133443).sum := by decide
  have hdescent : baseEnd_133443 < baseStart_133443 := by decide
  rcases family_descends (prefixWord ++ tailWord_133443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133447 : List Nat := [1, 1, 4, 1, 2, 2, 5, 1, 1, 4]
def baseStart_133447 : Nat := 118140960795 + 133447 * 2 ^ 59
def prefixEnd_133447 : Nat := 4983230072969 + 3 ^ 40 * 133447 * 2
def baseEnd_133447 : Nat := 45681635267096414465863

theorem tailTrace_133447 : CollatzResearch.WordTrace tailWord_133447 prefixEnd_133447 45681635267096414465863 := by
  unfold tailWord_133447
  simp only [CollatzResearch.WordTrace]
  refine ⟨4867211947551784778230595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3244807965034523185487063 4867211947551784778230595)
  ·
    refine ⟨7300817921327677167345893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4867211947551784778230595 7300817921327677167345893)
    ·
      refine ⟨1368903360248939468877355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7300817921327677167345893 1368903360248939468877355)
      ·
        refine ⟨2053355040373409203316033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1368903360248939468877355 2053355040373409203316033)
        ·
          refine ⟨1540016280280056902487025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2053355040373409203316033 1540016280280056902487025)
          ·
            refine ⟨1155012210210042676865269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1540016280280056902487025 1155012210210042676865269)
            ·
              refine ⟨108282394707191500956119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1155012210210042676865269 108282394707191500956119)
              ·
                refine ⟨162423592060787251434179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108282394707191500956119 162423592060787251434179)
                ·
                  refine ⟨243635388091180877151269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162423592060787251434179 243635388091180877151269)
                  ·
                    refine ⟨45681635267096414465863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 243635388091180877151269 45681635267096414465863)
                    ·
                      rfl

theorem cell22_133447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_133447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133447 prefixEnd_133447 := by exact prefixLift 133447
  have htrace : WordTrace (prefixWord ++ tailWord_133447) baseStart_133447 baseEnd_133447 := by
    simpa [prefixWord, tailWord_133447, baseEnd_133447] using wordTrace_append hprefix tailTrace_133447
  have hstable : (prefixWord ++ tailWord_133447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133447).length < 2 ^ (prefixWord ++ tailWord_133447).sum := by decide
  have hdescent : baseEnd_133447 < baseStart_133447 := by decide
  rcases family_descends (prefixWord ++ tailWord_133447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133477 : List Nat := [1, 3, 1, 3, 1, 3, 2, 3, 2, 3]
def baseStart_133477 : Nat := 118140960795 + 133477 * 2 ^ 59
def prefixEnd_133477 : Nat := 4983230072969 + 3 ^ 40 * 133477 * 2
def baseEnd_133477 : Nat := 45691904880186336215771

theorem tailTrace_133477 : CollatzResearch.WordTrace tailWord_133477 prefixEnd_133477 45691904880186336215771 := by
  unfold tailWord_133477
  simp only [CollatzResearch.WordTrace]
  refine ⟨4868306137443099901822685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3245537424962066601215123 4868306137443099901822685)
  ·
    refine ⟨1825614801541162463183507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4868306137443099901822685 1825614801541162463183507)
    ·
      refine ⟨2738422202311743694775261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1825614801541162463183507 2738422202311743694775261)
      ·
        refine ⟨1026908325866903885540723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2738422202311743694775261 1026908325866903885540723)
        ·
          refine ⟨1540362488800355828311085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026908325866903885540723 1540362488800355828311085)
          ·
            refine ⟨577635933300133435616657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1540362488800355828311085 577635933300133435616657)
            ·
              refine ⟨433226949975100076712493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577635933300133435616657 433226949975100076712493)
              ·
                refine ⟨162460106240662528767185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433226949975100076712493 162460106240662528767185)
                ·
                  refine ⟨121845079680496896575389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162460106240662528767185 121845079680496896575389)
                  ·
                    refine ⟨45691904880186336215771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121845079680496896575389 45691904880186336215771)
                    ·
                      rfl

theorem cell22_133477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_133477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133477 prefixEnd_133477 := by exact prefixLift 133477
  have htrace : WordTrace (prefixWord ++ tailWord_133477) baseStart_133477 baseEnd_133477 := by
    simpa [prefixWord, tailWord_133477, baseEnd_133477] using wordTrace_append hprefix tailTrace_133477
  have hstable : (prefixWord ++ tailWord_133477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133477).length < 2 ^ (prefixWord ++ tailWord_133477).sum := by decide
  have hdescent : baseEnd_133477 < baseStart_133477 := by decide
  rcases family_descends (prefixWord ++ tailWord_133477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133503 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 4, 6]
def baseStart_133503 : Nat := 118140960795 + 133503 * 2 ^ 59
def prefixEnd_133503 : Nat := 4983230072969 + 3 ^ 40 * 133503 * 2
def baseEnd_133503 : Nat := 45700805211530935065691

theorem tailTrace_133503 : CollatzResearch.WordTrace tailWord_133503 prefixEnd_133503 45700805211530935065691 := by
  unfold tailWord_133503
  simp only [CollatzResearch.WordTrace]
  refine ⟨4869254435348906342269163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3246169623565937561512775 4869254435348906342269163)
  ·
    refine ⟨7303881653023359513403745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4869254435348906342269163 7303881653023359513403745)
    ·
      refine ⟨5477911239767519635052809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7303881653023359513403745 5477911239767519635052809)
      ·
        refine ⟨4108433429825639726289607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5477911239767519635052809 4108433429825639726289607)
        ·
          refine ⟨6162650144738459589434411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4108433429825639726289607 6162650144738459589434411)
          ·
            refine ⟨9243975217107689384151617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6162650144738459589434411 9243975217107689384151617)
            ·
              refine ⟨6932981412830767038113713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9243975217107689384151617 6932981412830767038113713)
              ·
                refine ⟨5199736059623075278585285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6932981412830767038113713 5199736059623075278585285)
                ·
                  refine ⟨974950511179326614734741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5199736059623075278585285 974950511179326614734741)
                  ·
                    refine ⟨45700805211530935065691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 974950511179326614734741 45700805211530935065691)
                    ·
                      rfl

theorem cell22_133503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_133503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133503 prefixEnd_133503 := by exact prefixLift 133503
  have htrace : WordTrace (prefixWord ++ tailWord_133503) baseStart_133503 baseEnd_133503 := by
    simpa [prefixWord, tailWord_133503, baseEnd_133503] using wordTrace_append hprefix tailTrace_133503
  have hstable : (prefixWord ++ tailWord_133503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133503).length < 2 ^ (prefixWord ++ tailWord_133503).sum := by decide
  have hdescent : baseEnd_133503 < baseStart_133503 := by decide
  rcases family_descends (prefixWord ++ tailWord_133503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133599 : List Nat := [1, 1, 2, 3, 3, 4, 1, 2, 1, 4]
def baseStart_133599 : Nat := 118140960795 + 133599 * 2 ^ 59
def prefixEnd_133599 : Nat := 4983230072969 + 3 ^ 40 * 133599 * 2
def baseEnd_133599 : Nat := 45733667973418684665397

theorem tailTrace_133599 : CollatzResearch.WordTrace tailWord_133599 prefixEnd_133599 45733667973418684665397 := by
  unfold tailWord_133599
  simp only [CollatzResearch.WordTrace]
  refine ⟨4872755843001114737763851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3248503895334076491842567 4872755843001114737763851)
  ·
    refine ⟨7309133764501672106645777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4872755843001114737763851 7309133764501672106645777)
    ·
      refine ⟨5481850323376254079984333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7309133764501672106645777 5481850323376254079984333)
      ·
        refine ⟨2055693871266095279994125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5481850323376254079984333 2055693871266095279994125)
        ·
          refine ⟨770885201724785729997797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2055693871266095279994125 770885201724785729997797)
          ·
            refine ⟨144540975323397324374587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 770885201724785729997797 144540975323397324374587)
            ·
              refine ⟨216811462985095986561881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144540975323397324374587 216811462985095986561881)
              ·
                refine ⟨162608597238821989921411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216811462985095986561881 162608597238821989921411)
                ·
                  refine ⟨243912895858232984882117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162608597238821989921411 243912895858232984882117)
                  ·
                    refine ⟨45733667973418684665397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 243912895858232984882117 45733667973418684665397)
                    ·
                      rfl

theorem cell22_133599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 4].length) (baseStart_133599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133599 prefixEnd_133599 := by exact prefixLift 133599
  have htrace : WordTrace (prefixWord ++ tailWord_133599) baseStart_133599 baseEnd_133599 := by
    simpa [prefixWord, tailWord_133599, baseEnd_133599] using wordTrace_append hprefix tailTrace_133599
  have hstable : (prefixWord ++ tailWord_133599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133599).length < 2 ^ (prefixWord ++ tailWord_133599).sum := by decide
  have hdescent : baseEnd_133599 < baseStart_133599 := by decide
  rcases family_descends (prefixWord ++ tailWord_133599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133629 : List Nat := [1, 4, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_133629 : Nat := 118140960795 + 133629 * 2 ^ 59
def prefixEnd_133629 : Nat := 4983230072969 + 3 ^ 40 * 133629 * 2
def baseEnd_133629 : Nat := 45743937586508606415305

theorem tailTrace_133629 : CollatzResearch.WordTrace tailWord_133629 prefixEnd_133629 45743937586508606415305 := by
  unfold tailWord_133629
  simp only [CollatzResearch.WordTrace]
  refine ⟨4873850032892429861355941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3249233355261619907570627 4873850032892429861355941)
  ·
    refine ⟨913846881167330599004239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4873850032892429861355941 913846881167330599004239)
    ·
      refine ⟨1370770321750995898506359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 913846881167330599004239 1370770321750995898506359)
      ·
        refine ⟨2056155482626493847759539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1370770321750995898506359 2056155482626493847759539)
        ·
          refine ⟨3084233223939740771639309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2056155482626493847759539 3084233223939740771639309)
          ·
            refine ⟨1156587458977402789364741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3084233223939740771639309 1156587458977402789364741)
            ·
              refine ⟨216860148558263023005889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1156587458977402789364741 216860148558263023005889)
              ·
                refine ⟨162645111418697267254417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216860148558263023005889 162645111418697267254417)
                ·
                  refine ⟨121983833564022950440813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162645111418697267254417 121983833564022950440813)
                  ·
                    refine ⟨45743937586508606415305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121983833564022950440813 45743937586508606415305)
                    ·
                      rfl

theorem cell22_133629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_133629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133629 prefixEnd_133629 := by exact prefixLift 133629
  have htrace : WordTrace (prefixWord ++ tailWord_133629) baseStart_133629 baseEnd_133629 := by
    simpa [prefixWord, tailWord_133629, baseEnd_133629] using wordTrace_append hprefix tailTrace_133629
  have hstable : (prefixWord ++ tailWord_133629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133629).length < 2 ^ (prefixWord ++ tailWord_133629).sum := by decide
  have hdescent : baseEnd_133629 < baseStart_133629 := by decide
  rcases family_descends (prefixWord ++ tailWord_133629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133640 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 2, 7]
def baseStart_133640 : Nat := 118140960795 + 133640 * 2 ^ 59
def prefixEnd_133640 : Nat := 4983230072969 + 3 ^ 40 * 133640 * 2
def baseEnd_133640 : Nat := 45747703111308244390271

theorem tailTrace_133640 : CollatzResearch.WordTrace tailWord_133640 prefixEnd_133640 45747703111308244390271 := by
  unfold tailWord_133640
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437125617926289370003187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3249500823901719160004249 2437125617926289370003187)
  ·
    refine ⟨3655688426889434055004781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2437125617926289370003187 3655688426889434055004781)
    ·
      refine ⟨1370883160083537770626793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3655688426889434055004781 1370883160083537770626793)
      ·
        refine ⟨1028162370062653327970095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1370883160083537770626793 1028162370062653327970095)
        ·
          refine ⟨1542243555093979991955143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028162370062653327970095 1542243555093979991955143)
          ·
            refine ⟨2313365332640969987932715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542243555093979991955143 2313365332640969987932715)
            ·
              refine ⟨3470047998961454981899073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313365332640969987932715 3470047998961454981899073)
              ·
                refine ⟨2602535999221091236424305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3470047998961454981899073 2602535999221091236424305)
                ·
                  refine ⟨1951901999415818427318229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2602535999221091236424305 1951901999415818427318229)
                  ·
                    refine ⟨45747703111308244390271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1951901999415818427318229 45747703111308244390271)
                    ·
                      rfl

theorem cell22_133640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_133640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133640 prefixEnd_133640 := by exact prefixLift 133640
  have htrace : WordTrace (prefixWord ++ tailWord_133640) baseStart_133640 baseEnd_133640 := by
    simpa [prefixWord, tailWord_133640, baseEnd_133640] using wordTrace_append hprefix tailTrace_133640
  have hstable : (prefixWord ++ tailWord_133640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133640).length < 2 ^ (prefixWord ++ tailWord_133640).sum := by decide
  have hdescent : baseEnd_133640 < baseStart_133640 := by decide
  rcases family_descends (prefixWord ++ tailWord_133640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133657 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 3, 3]
def baseStart_133657 : Nat := 118140960795 + 133657 * 2 ^ 59
def prefixEnd_133657 : Nat := 4983230072969 + 3 ^ 40 * 133657 * 2
def baseEnd_133657 : Nat := 45753522558725866715219

theorem tailTrace_133657 : CollatzResearch.WordTrace tailWord_133657 prefixEnd_133657 45753522558725866715219 := by
  unfold tailWord_133657
  simp only [CollatzResearch.WordTrace]
  refine ⟨4874871276790990643375225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3249914184527327095583483 4874871276790990643375225)
  ·
    refine ⟨3656153457593242982531419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4874871276790990643375225 3656153457593242982531419)
    ·
      refine ⟨5484230186389864473797129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3656153457593242982531419 5484230186389864473797129)
      ·
        refine ⟨4113172639792398355347847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5484230186389864473797129 4113172639792398355347847)
        ·
          refine ⟨6169758959688597533021771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113172639792398355347847 6169758959688597533021771)
          ·
            refine ⟨9254638439532896299532657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6169758959688597533021771 9254638439532896299532657)
            ·
              refine ⟨6940978829649672224649493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9254638439532896299532657 6940978829649672224649493)
              ·
                refine ⟨325358382639828385530445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6940978829649672224649493 325358382639828385530445)
                ·
                  refine ⟨122009393489935644573917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325358382639828385530445 122009393489935644573917)
                  ·
                    refine ⟨45753522558725866715219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122009393489935644573917 45753522558725866715219)
                    ·
                      rfl

theorem cell22_133657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 3].length) (baseStart_133657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133657 prefixEnd_133657 := by exact prefixLift 133657
  have htrace : WordTrace (prefixWord ++ tailWord_133657) baseStart_133657 baseEnd_133657 := by
    simpa [prefixWord, tailWord_133657, baseEnd_133657] using wordTrace_append hprefix tailTrace_133657
  have hstable : (prefixWord ++ tailWord_133657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133657).length < 2 ^ (prefixWord ++ tailWord_133657).sum := by decide
  have hdescent : baseEnd_133657 < baseStart_133657 := by decide
  rcases family_descends (prefixWord ++ tailWord_133657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133717 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_133717 : Nat := 118140960795 + 133717 * 2 ^ 59
def prefixEnd_133717 : Nat := 4983230072969 + 3 ^ 40 * 133717 * 2
def baseEnd_133717 : Nat := 45774061784905710215035

theorem tailTrace_133717 : CollatzResearch.WordTrace tailWord_133717 prefixEnd_133717 45774061784905710215035 := by
  unfold tailWord_133717
  simp only [CollatzResearch.WordTrace]
  refine ⟨4877059656573620890559405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3251373104382413927039603 4877059656573620890559405)
  ·
    refine ⟨1828897371215107833959777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4877059656573620890559405 1828897371215107833959777)
    ·
      refine ⟨1371673028411330875469833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1828897371215107833959777 1371673028411330875469833)
      ·
        refine ⟨1028754771308498156602375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1371673028411330875469833 1028754771308498156602375)
        ·
          refine ⟨1543132156962747234903563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028754771308498156602375 1543132156962747234903563)
          ·
            refine ⟨2314698235444120852355345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1543132156962747234903563 2314698235444120852355345)
            ·
              refine ⟨1736023676583090639266509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2314698235444120852355345 1736023676583090639266509)
              ·
                refine ⟨651008878718658989724941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1736023676583090639266509 651008878718658989724941)
                ·
                  refine ⟨244128329519497121146853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651008878718658989724941 244128329519497121146853)
                  ·
                    refine ⟨45774061784905710215035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 244128329519497121146853 45774061784905710215035)
                    ·
                      rfl

theorem cell22_133717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_133717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133717 prefixEnd_133717 := by exact prefixLift 133717
  have htrace : WordTrace (prefixWord ++ tailWord_133717) baseStart_133717 baseEnd_133717 := by
    simpa [prefixWord, tailWord_133717, baseEnd_133717] using wordTrace_append hprefix tailTrace_133717
  have hstable : (prefixWord ++ tailWord_133717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133717).length < 2 ^ (prefixWord ++ tailWord_133717).sum := by decide
  have hdescent : baseEnd_133717 < baseStart_133717 := by decide
  rcases family_descends (prefixWord ++ tailWord_133717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133807 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 2, 6]
def baseStart_133807 : Nat := 118140960795 + 133807 * 2 ^ 59
def prefixEnd_133807 : Nat := 4983230072969 + 3 ^ 40 * 133807 * 2
def baseEnd_133807 : Nat := 45804870624175475464759

theorem tailTrace_133807 : CollatzResearch.WordTrace tailWord_133807 prefixEnd_133807 45804870624175475464759 := by
  unfold tailWord_133807
  simp only [CollatzResearch.WordTrace]
  refine ⟨4880342226247566261335675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3253561484165044174223783 4880342226247566261335675)
  ·
    refine ⟨7320513339371349392003513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4880342226247566261335675 7320513339371349392003513)
    ·
      refine ⟨5490385004528512044002635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7320513339371349392003513 5490385004528512044002635)
      ·
        refine ⟨8235577506792768066003953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5490385004528512044002635 8235577506792768066003953)
        ·
          refine ⟨6176683130094576049502965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8235577506792768066003953 6176683130094576049502965)
          ·
            refine ⟨579064043446366504640903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6176683130094576049502965 579064043446366504640903)
            ·
              refine ⟨868596065169549756961355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579064043446366504640903 868596065169549756961355)
              ·
                refine ⟨1302894097754324635442033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868596065169549756961355 1302894097754324635442033)
                ·
                  refine ⟨977170573315743476581525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1302894097754324635442033 977170573315743476581525)
                  ·
                    refine ⟨45804870624175475464759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 977170573315743476581525 45804870624175475464759)
                    ·
                      rfl

theorem cell22_133807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_133807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133807 prefixEnd_133807 := by exact prefixLift 133807
  have htrace : WordTrace (prefixWord ++ tailWord_133807) baseStart_133807 baseEnd_133807 := by
    simpa [prefixWord, tailWord_133807, baseEnd_133807] using wordTrace_append hprefix tailTrace_133807
  have hstable : (prefixWord ++ tailWord_133807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133807).length < 2 ^ (prefixWord ++ tailWord_133807).sum := by decide
  have hdescent : baseEnd_133807 < baseStart_133807 := by decide
  rcases family_descends (prefixWord ++ tailWord_133807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133884 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 6]
def baseStart_133884 : Nat := 118140960795 + 133884 * 2 ^ 59
def prefixEnd_133884 : Nat := 4983230072969 + 3 ^ 40 * 133884 * 2
def baseEnd_133884 : Nat := 15277076432590980429841

theorem tailTrace_133884 : CollatzResearch.WordTrace tailWord_133884 prefixEnd_133884 15277076432590980429841 := by
  unfold tailWord_133884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2441575323484304205944353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3255433764645738941259137 2441575323484304205944353)
  ·
    refine ⟨1831181492613228154458265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2441575323484304205944353 1831181492613228154458265)
    ·
      refine ⟨1373386119459921115843699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1831181492613228154458265 1373386119459921115843699)
      ·
        refine ⟨2060079179189881673765549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1373386119459921115843699 2060079179189881673765549)
        ·
          refine ⟨772529692196205627662081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2060079179189881673765549 772529692196205627662081)
          ·
            refine ⟨579397269147154220746561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772529692196205627662081 579397269147154220746561)
            ·
              refine ⟨434547951860365665559921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579397269147154220746561 434547951860365665559921)
              ·
                refine ⟨325910963895274249169941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434547951860365665559921 325910963895274249169941)
                ·
                  refine ⟨15277076432590980429841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 325910963895274249169941 15277076432590980429841)
                  ·
                    rfl

theorem cell22_133884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_133884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133884 prefixEnd_133884 := by exact prefixLift 133884
  have htrace : WordTrace (prefixWord ++ tailWord_133884) baseStart_133884 baseEnd_133884 := by
    simpa [prefixWord, tailWord_133884, baseEnd_133884] using wordTrace_append hprefix tailTrace_133884
  have hstable : (prefixWord ++ tailWord_133884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133884).length < 2 ^ (prefixWord ++ tailWord_133884).sum := by decide
  have hdescent : baseEnd_133884 < baseStart_133884 := by decide
  rcases family_descends (prefixWord ++ tailWord_133884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133916 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 4, 3]
def baseStart_133916 : Nat := 118140960795 + 133916 * 2 ^ 59
def prefixEnd_133916 : Nat := 4983230072969 + 3 ^ 40 * 133916 * 2
def baseEnd_133916 : Nat := 45842183551735524489425

theorem tailTrace_133916 : CollatzResearch.WordTrace tailWord_133916 prefixEnd_133916 45842183551735524489425 := by
  unfold tailWord_133916
  simp only [CollatzResearch.WordTrace]
  refine ⟨2442158891426338938526801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3256211855235118584702401 2442158891426338938526801)
  ·
    refine ⟨1831619168569754203895101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2442158891426338938526801 1831619168569754203895101)
    ·
      refine ⟨686857188213657826460663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1831619168569754203895101 686857188213657826460663)
      ·
        refine ⟨1030285782320486739690995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686857188213657826460663 1030285782320486739690995)
        ·
          refine ⟨1545428673480730109536493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030285782320486739690995 1545428673480730109536493)
          ·
            refine ⟨579535752555273791076185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1545428673480730109536493 579535752555273791076185)
            ·
              refine ⟨434651814416455343307139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579535752555273791076185 434651814416455343307139)
              ·
                refine ⟨651977721624683014960709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434651814416455343307139 651977721624683014960709)
                ·
                  refine ⟨122245822804628065305133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 651977721624683014960709 122245822804628065305133)
                  ·
                    refine ⟨45842183551735524489425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122245822804628065305133 45842183551735524489425)
                    ·
                      rfl

theorem cell22_133916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_133916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133916 prefixEnd_133916 := by exact prefixLift 133916
  have htrace : WordTrace (prefixWord ++ tailWord_133916) baseStart_133916 baseEnd_133916 := by
    simpa [prefixWord, tailWord_133916, baseEnd_133916] using wordTrace_append hprefix tailTrace_133916
  have hstable : (prefixWord ++ tailWord_133916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133916).length < 2 ^ (prefixWord ++ tailWord_133916).sum := by decide
  have hdescent : baseEnd_133916 < baseStart_133916 := by decide
  rcases family_descends (prefixWord ++ tailWord_133916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133989 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_133989 : Nat := 118140960795 + 133989 * 2 ^ 59
def prefixEnd_133989 : Nat := 4983230072969 + 3 ^ 40 * 133989 * 2
def baseEnd_133989 : Nat := 45867172943587667414201

theorem tailTrace_133989 : CollatzResearch.WordTrace tailWord_133989 prefixEnd_133989 45867172943587667414201 := by
  unfold tailWord_133989
  simp only [CollatzResearch.WordTrace]
  refine ⟨4886980311588211344461021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3257986874392140896307347 4886980311588211344461021)
  ·
    refine ⟨1832617616845579254172883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4886980311588211344461021 1832617616845579254172883)
    ·
      refine ⟨2748926425268368881259325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1832617616845579254172883 2748926425268368881259325)
      ·
        refine ⟨1030847409475638330472247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2748926425268368881259325 1030847409475638330472247)
        ·
          refine ⟨1546271114213457495708371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030847409475638330472247 1546271114213457495708371)
          ·
            refine ⟨2319406671320186243562557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1546271114213457495708371 2319406671320186243562557)
            ·
              refine ⟨869777501745069841335959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2319406671320186243562557 869777501745069841335959)
              ·
                refine ⟨1304666252617604762003939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869777501745069841335959 1304666252617604762003939)
                ·
                  refine ⟨1956999378926407143005909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304666252617604762003939 1956999378926407143005909)
                  ·
                    refine ⟨45867172943587667414201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1956999378926407143005909 45867172943587667414201)
                    ·
                      rfl

theorem cell22_133989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_133989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133989 prefixEnd_133989 := by exact prefixLift 133989
  have htrace : WordTrace (prefixWord ++ tailWord_133989) baseStart_133989 baseEnd_133989 := by
    simpa [prefixWord, tailWord_133989, baseEnd_133989] using wordTrace_append hprefix tailTrace_133989
  have hstable : (prefixWord ++ tailWord_133989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133989).length < 2 ^ (prefixWord ++ tailWord_133989).sum := by decide
  have hdescent : baseEnd_133989 < baseStart_133989 := by decide
  rcases family_descends (prefixWord ++ tailWord_133989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133991 : List Nat := [1, 1, 5, 1, 2, 2, 2, 3, 5]
def baseStart_133991 : Nat := 118140960795 + 133991 * 2 ^ 59
def prefixEnd_133991 : Nat := 4983230072969 + 3 ^ 40 * 133991 * 2
def baseEnd_133991 : Nat := 15289285861486776288065

theorem tailTrace_133991 : CollatzResearch.WordTrace tailWord_133991 prefixEnd_133991 15289285861486776288065 := by
  unfold tailWord_133991
  simp only [CollatzResearch.WordTrace]
  refine ⟨4887053257580965686033827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3258035505053977124022551 4887053257580965686033827)
  ·
    refine ⟨7330579886371448529050741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4887053257580965686033827 7330579886371448529050741)
    ·
      refine ⟨687241864347323299598507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7330579886371448529050741 687241864347323299598507)
      ·
        refine ⟨1030862796520984949397761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687241864347323299598507 1030862796520984949397761)
        ·
          refine ⟨773147097390738712048321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030862796520984949397761 773147097390738712048321)
          ·
            refine ⟨579860323043054034036241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 773147097390738712048321 579860323043054034036241)
            ·
              refine ⟨434895242282290525527181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579860323043054034036241 434895242282290525527181)
              ·
                refine ⟨163085715855858947072693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434895242282290525527181 163085715855858947072693)
                ·
                  refine ⟨15289285861486776288065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 163085715855858947072693 15289285861486776288065)
                  ·
                    rfl

theorem cell22_133991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 5].length) (baseStart_133991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_133991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_133991 prefixEnd_133991 := by exact prefixLift 133991
  have htrace : WordTrace (prefixWord ++ tailWord_133991) baseStart_133991 baseEnd_133991 := by
    simpa [prefixWord, tailWord_133991, baseEnd_133991] using wordTrace_append hprefix tailTrace_133991
  have hstable : (prefixWord ++ tailWord_133991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133991).length < 2 ^ (prefixWord ++ tailWord_133991).sum := by decide
  have hdescent : baseEnd_133991 < baseStart_133991 := by decide
  rcases family_descends (prefixWord ++ tailWord_133991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134019 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 8]
def baseStart_134019 : Nat := 118140960795 + 134019 * 2 ^ 59
def prefixEnd_134019 : Nat := 4983230072969 + 3 ^ 40 * 134019 * 2
def baseEnd_134019 : Nat := 15292480852225863054703

theorem tailTrace_134019 : CollatzResearch.WordTrace tailWord_134019 prefixEnd_134019 15292480852225863054703 := by
  unfold tailWord_134019
  simp only [CollatzResearch.WordTrace]
  refine ⟨4888074501479526468053111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3258716334319684312035407 4888074501479526468053111)
  ·
    refine ⟨7332111752219289702079667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4888074501479526468053111 7332111752219289702079667)
    ·
      refine ⟨10998167628328934553119501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7332111752219289702079667 10998167628328934553119501)
      ·
        refine ⟨4124312860623350457419813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10998167628328934553119501 4124312860623350457419813)
        ·
          refine ⟨773308661366878210766215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4124312860623350457419813 773308661366878210766215)
          ·
            refine ⟨1159962992050317316149323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773308661366878210766215 1159962992050317316149323)
            ·
              refine ⟨1739944488075475974223985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159962992050317316149323 1739944488075475974223985)
              ·
                refine ⟨1304958366056606980667989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1739944488075475974223985 1304958366056606980667989)
                ·
                  refine ⟨15292480852225863054703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1304958366056606980667989 15292480852225863054703)
                  ·
                    rfl

theorem cell22_134019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 8].length) (baseStart_134019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134019 prefixEnd_134019 := by exact prefixLift 134019
  have htrace : WordTrace (prefixWord ++ tailWord_134019) baseStart_134019 baseEnd_134019 := by
    simpa [prefixWord, tailWord_134019, baseEnd_134019] using wordTrace_append hprefix tailTrace_134019
  have hstable : (prefixWord ++ tailWord_134019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134019).length < 2 ^ (prefixWord ++ tailWord_134019).sum := by decide
  have hdescent : baseEnd_134019 < baseStart_134019 := by decide
  rcases family_descends (prefixWord ++ tailWord_134019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134051 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 1, 5]
def baseStart_134051 : Nat := 118140960795 + 134051 * 2 ^ 59
def prefixEnd_134051 : Nat := 4983230072969 + 3 ^ 40 * 134051 * 2
def baseEnd_134051 : Nat := 45888396810640172364011

theorem tailTrace_134051 : CollatzResearch.WordTrace tailWord_134051 prefixEnd_134051 45888396810640172364011 := by
  unfold tailWord_134051
  simp only [CollatzResearch.WordTrace]
  refine ⟨4889241637363595933218007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3259494424909063955478671 4889241637363595933218007)
  ·
    refine ⟨7333862456045393899827011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4889241637363595933218007 7333862456045393899827011)
    ·
      refine ⟨11000793684068090849740517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7333862456045393899827011 11000793684068090849740517)
      ·
        refine ⟨2062648815762767034326347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11000793684068090849740517 2062648815762767034326347)
        ·
          refine ⟨3093973223644150551489521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062648815762767034326347 3093973223644150551489521)
          ·
            refine ⟨2320479917733112913617141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3093973223644150551489521 2320479917733112913617141)
            ·
              refine ⟨217544992287479335651607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2320479917733112913617141 217544992287479335651607)
              ·
                refine ⟨326317488431219003477411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217544992287479335651607 326317488431219003477411)
                ·
                  refine ⟨489476232646828505216117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326317488431219003477411 489476232646828505216117)
                  ·
                    refine ⟨45888396810640172364011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 489476232646828505216117 45888396810640172364011)
                    ·
                      rfl

theorem cell22_134051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 5].length) (baseStart_134051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134051 prefixEnd_134051 := by exact prefixLift 134051
  have htrace : WordTrace (prefixWord ++ tailWord_134051) baseStart_134051 baseEnd_134051 := by
    simpa [prefixWord, tailWord_134051, baseEnd_134051] using wordTrace_append hprefix tailTrace_134051
  have hstable : (prefixWord ++ tailWord_134051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134051).length < 2 ^ (prefixWord ++ tailWord_134051).sum := by decide
  have hdescent : baseEnd_134051 < baseStart_134051 := by decide
  rcases family_descends (prefixWord ++ tailWord_134051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134055 : List Nat := [1, 1, 6, 1, 3, 1, 2, 2, 1, 4]
def baseStart_134055 : Nat := 118140960795 + 134055 * 2 ^ 59
def prefixEnd_134055 : Nat := 4983230072969 + 3 ^ 40 * 134055 * 2
def baseEnd_134055 : Nat := 45889766092385495263999

theorem tailTrace_134055 : CollatzResearch.WordTrace tailWord_134055 prefixEnd_134055 45889766092385495263999 := by
  unfold tailWord_134055
  simp only [CollatzResearch.WordTrace]
  refine ⟨4889387529349104616363619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3259591686232736410909079 4889387529349104616363619)
  ·
    refine ⟨7334081294023656924545429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4889387529349104616363619 7334081294023656924545429)
    ·
      refine ⟨343785060657358918338067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7334081294023656924545429 343785060657358918338067)
      ·
        refine ⟨515677590986038377507101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343785060657358918338067 515677590986038377507101)
        ·
          refine ⟨193379096619764391565163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515677590986038377507101 193379096619764391565163)
          ·
            refine ⟨290068644929646587347745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193379096619764391565163 290068644929646587347745)
            ·
              refine ⟨217551483697234940510809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290068644929646587347745 217551483697234940510809)
              ·
                refine ⟨163163612772926205383107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217551483697234940510809 163163612772926205383107)
                ·
                  refine ⟨244745419159389308074661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163163612772926205383107 244745419159389308074661)
                  ·
                    refine ⟨45889766092385495263999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 244745419159389308074661 45889766092385495263999)
                    ·
                      rfl

theorem cell22_134055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_134055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134055 prefixEnd_134055 := by exact prefixLift 134055
  have htrace : WordTrace (prefixWord ++ tailWord_134055) baseStart_134055 baseEnd_134055 := by
    simpa [prefixWord, tailWord_134055, baseEnd_134055] using wordTrace_append hprefix tailTrace_134055
  have hstable : (prefixWord ++ tailWord_134055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134055).length < 2 ^ (prefixWord ++ tailWord_134055).sum := by decide
  have hdescent : baseEnd_134055 < baseStart_134055 := by decide
  rcases family_descends (prefixWord ++ tailWord_134055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134098 : List Nat := [3, 2, 2, 3, 1, 2, 2, 7]
def baseStart_134098 : Nat := 118140960795 + 134098 * 2 ^ 59
def prefixEnd_134098 : Nat := 4983230072969 + 3 ^ 40 * 134098 * 2
def baseEnd_134098 : Nat := 5100498430127524048763

theorem tailTrace_134098 : CollatzResearch.WordTrace tailWord_134098 prefixEnd_134098 5100498430127524048763 := by
  unfold tailWord_134098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222738967048330740044737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3260637245462215306785965 1222738967048330740044737)
  ·
    refine ⟨917054225286248055033553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1222738967048330740044737 917054225286248055033553)
    ·
      refine ⟨687790668964686041275165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 917054225286248055033553 687790668964686041275165)
      ·
        refine ⟨257921500861757265478187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 687790668964686041275165 257921500861757265478187)
        ·
          refine ⟨386882251292635898217281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257921500861757265478187 386882251292635898217281)
          ·
            refine ⟨290161688469476923662961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386882251292635898217281 290161688469476923662961)
            ·
              refine ⟨217621266352107692747221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290161688469476923662961 217621266352107692747221)
              ·
                refine ⟨5100498430127524048763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 217621266352107692747221 5100498430127524048763)
                ·
                  rfl

theorem cell22_134098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_134098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134098 prefixEnd_134098 := by exact prefixLift 134098
  have htrace : WordTrace (prefixWord ++ tailWord_134098) baseStart_134098 baseEnd_134098 := by
    simpa [prefixWord, tailWord_134098, baseEnd_134098] using wordTrace_append hprefix tailTrace_134098
  have hstable : (prefixWord ++ tailWord_134098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134098).length < 2 ^ (prefixWord ++ tailWord_134098).sum := by decide
  have hdescent : baseEnd_134098 < baseStart_134098 := by decide
  rcases family_descends (prefixWord ++ tailWord_134098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134102 : List Nat := [5, 2, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_134102 : Nat := 118140960795 + 134102 * 2 ^ 59
def prefixEnd_134102 : Nat := 4983230072969 + 3 ^ 40 * 134102 * 2
def baseEnd_134102 : Nat := 45905855152893039338855

theorem tailTrace_134102 : CollatzResearch.WordTrace tailWord_134102 prefixEnd_134102 45905855152893039338855 := by
  unfold tailWord_134102
  simp only [CollatzResearch.WordTrace]
  refine ⟨305693860011176977707785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3260734506785887762216373 305693860011176977707785)
  ·
    refine ⟨229270395008382733280839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305693860011176977707785 229270395008382733280839)
    ·
      refine ⟨343905592512574099921259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229270395008382733280839 343905592512574099921259)
      ·
        refine ⟨515858388768861149881889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343905592512574099921259 515858388768861149881889)
        ·
          refine ⟨386893791576645862411417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515858388768861149881889 386893791576645862411417)
          ·
            refine ⟨290170343682484396808563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386893791576645862411417 290170343682484396808563)
            ·
              refine ⟨435255515523726595212845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290170343682484396808563 435255515523726595212845)
              ·
                refine ⟨163220818321397473204817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435255515523726595212845 163220818321397473204817)
                ·
                  refine ⟨122415613741048104903613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163220818321397473204817 122415613741048104903613)
                  ·
                    refine ⟨45905855152893039338855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122415613741048104903613 45905855152893039338855)
                    ·
                      rfl

theorem cell22_134102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_134102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134102 prefixEnd_134102 := by exact prefixLift 134102
  have htrace : WordTrace (prefixWord ++ tailWord_134102) baseStart_134102 baseEnd_134102 := by
    simpa [prefixWord, tailWord_134102, baseEnd_134102] using wordTrace_append hprefix tailTrace_134102
  have hstable : (prefixWord ++ tailWord_134102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134102).length < 2 ^ (prefixWord ++ tailWord_134102).sum := by decide
  have hdescent : baseEnd_134102 < baseStart_134102 := by decide
  rcases family_descends (prefixWord ++ tailWord_134102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134132 : List Nat := [2, 6, 2, 1, 1, 10]
def baseStart_134132 : Nat := 118140960795 + 134132 * 2 ^ 59
def prefixEnd_134132 : Nat := 4983230072969 + 3 ^ 40 * 134132 * 2
def baseEnd_134132 : Nat := 566865737851641494923

theorem tailTrace_134132 : CollatzResearch.WordTrace tailWord_134132 prefixEnd_134132 566865737851641494923 := by
  unfold tailWord_134132
  simp only [CollatzResearch.WordTrace]
  refine ⟨2446097975035073383458325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3261463966713431177944433 2446097975035073383458325)
  ·
    refine ⟨114660842579769064849609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2446097975035073383458325 114660842579769064849609)
    ·
      refine ⟨85995631934826798637207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114660842579769064849609 85995631934826798637207)
      ·
        refine ⟨128993447902240197955811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85995631934826798637207 128993447902240197955811)
        ·
          refine ⟨193490171853360296933717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128993447902240197955811 193490171853360296933717)
          ·
            refine ⟨566865737851641494923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 193490171853360296933717 566865737851641494923)
            ·
              rfl

theorem cell22_134132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 10].length) (baseStart_134132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134132 prefixEnd_134132 := by exact prefixLift 134132
  have htrace : WordTrace (prefixWord ++ tailWord_134132) baseStart_134132 baseEnd_134132 := by
    simpa [prefixWord, tailWord_134132, baseEnd_134132] using wordTrace_append hprefix tailTrace_134132
  have hstable : (prefixWord ++ tailWord_134132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134132).length < 2 ^ (prefixWord ++ tailWord_134132).sum := by decide
  have hdescent : baseEnd_134132 < baseStart_134132 := by decide
  rcases family_descends (prefixWord ++ tailWord_134132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134141 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_134141 : Nat := 118140960795 + 134141 * 2 ^ 59
def prefixEnd_134141 : Nat := 4983230072969 + 3 ^ 40 * 134141 * 2
def baseEnd_134141 : Nat := 45919205649909937613735

theorem tailTrace_134141 : CollatzResearch.WordTrace tailWord_134141 prefixEnd_134141 45919205649909937613735 := by
  unfold tailWord_134141
  simp only [CollatzResearch.WordTrace]
  refine ⟨4892524207037541303994277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3261682804691694202662851 4892524207037541303994277)
  ·
    refine ⟨917348288819538994498927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4892524207037541303994277 917348288819538994498927)
    ·
      refine ⟨1376022433229308491748391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 917348288819538994498927 1376022433229308491748391)
      ·
        refine ⟨2064033649843962737622587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1376022433229308491748391 2064033649843962737622587)
        ·
          refine ⟨3096050474765944106433881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2064033649843962737622587 3096050474765944106433881)
          ·
            refine ⟨2322037856074458079825411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3096050474765944106433881 2322037856074458079825411)
            ·
              refine ⟨3483056784111687119738117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2322037856074458079825411 3483056784111687119738117)
              ·
                refine ⟨653073147020941334950897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3483056784111687119738117 653073147020941334950897)
                ·
                  refine ⟨489804860265706001213173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 653073147020941334950897 489804860265706001213173)
                  ·
                    refine ⟨45919205649909937613735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 489804860265706001213173 45919205649909937613735)
                    ·
                      rfl

theorem cell22_134141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_134141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134141 prefixEnd_134141 := by exact prefixLift 134141
  have htrace : WordTrace (prefixWord ++ tailWord_134141) baseStart_134141 baseEnd_134141 := by
    simpa [prefixWord, tailWord_134141, baseEnd_134141] using wordTrace_append hprefix tailTrace_134141
  have hstable : (prefixWord ++ tailWord_134141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134141).length < 2 ^ (prefixWord ++ tailWord_134141).sum := by decide
  have hdescent : baseEnd_134141 < baseStart_134141 := by decide
  rcases family_descends (prefixWord ++ tailWord_134141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134158 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_134158 : Nat := 118140960795 + 134158 * 2 ^ 59
def prefixEnd_134158 : Nat := 4983230072969 + 3 ^ 40 * 134158 * 2
def baseEnd_134158 : Nat := 45925025097327559938683

theorem tailTrace_134158 : CollatzResearch.WordTrace tailWord_134158 prefixEnd_134158 45925025097327559938683 := by
  unfold tailWord_134158
  simp only [CollatzResearch.WordTrace]
  refine ⟨611643030996994150920391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3262096165317302138242085 611643030996994150920391)
  ·
    refine ⟨917464546495491226380587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 611643030996994150920391 917464546495491226380587)
    ·
      refine ⟨1376196819743236839570881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 917464546495491226380587 1376196819743236839570881)
      ·
        refine ⟨1032147614807427629678161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1376196819743236839570881 1032147614807427629678161)
        ·
          refine ⟨774110711105570722258621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032147614807427629678161 774110711105570722258621)
          ·
            refine ⟨290291516664589020846983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 774110711105570722258621 290291516664589020846983)
            ·
              refine ⟨435437274996883531270475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290291516664589020846983 435437274996883531270475)
              ·
                refine ⟨653155912495325296905713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435437274996883531270475 653155912495325296905713)
                ·
                  refine ⟨489866934371493972679285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 653155912495325296905713 489866934371493972679285)
                  ·
                    refine ⟨45925025097327559938683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 489866934371493972679285 45925025097327559938683)
                    ·
                      rfl

theorem cell22_134158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_134158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134158 prefixEnd_134158 := by exact prefixLift 134158
  have htrace : WordTrace (prefixWord ++ tailWord_134158) baseStart_134158 baseEnd_134158 := by
    simpa [prefixWord, tailWord_134158, baseEnd_134158] using wordTrace_append hprefix tailTrace_134158
  have hstable : (prefixWord ++ tailWord_134158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134158).length < 2 ^ (prefixWord ++ tailWord_134158).sum := by decide
  have hdescent : baseEnd_134158 < baseStart_134158 := by decide
  rcases family_descends (prefixWord ++ tailWord_134158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134190 : List Nat := [4, 1, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_134190 : Nat := 118140960795 + 134190 * 2 ^ 59
def prefixEnd_134190 : Nat := 4983230072969 + 3 ^ 40 * 134190 * 2
def baseEnd_134190 : Nat := 45935979351290143138585

theorem tailTrace_134190 : CollatzResearch.WordTrace tailWord_134190 prefixEnd_134190 45935979351290143138585 := by
  unfold tailWord_134190
  simp only [CollatzResearch.WordTrace]
  refine ⟨611788922982502834066003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3262874255906681781685349 611788922982502834066003)
  ·
    refine ⟨917683384473754251099005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 611788922982502834066003 917683384473754251099005)
    ·
      refine ⟨344131269177657844162127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 917683384473754251099005 344131269177657844162127)
      ·
        refine ⟨516196903766486766243191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344131269177657844162127 516196903766486766243191)
        ·
          refine ⟨774295355649730149364787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516196903766486766243191 774295355649730149364787)
          ·
            refine ⟨1161443033474595224047181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774295355649730149364787 1161443033474595224047181)
            ·
              refine ⟨435541137552973209017693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1161443033474595224047181 435541137552973209017693)
              ·
                refine ⟨163327926582364953381635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435541137552973209017693 163327926582364953381635)
                ·
                  refine ⟨244991889873547430072453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163327926582364953381635 244991889873547430072453)
                  ·
                    refine ⟨45935979351290143138585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 244991889873547430072453 45935979351290143138585)
                    ·
                      rfl

theorem cell22_134190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_134190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134190 prefixEnd_134190 := by exact prefixLift 134190
  have htrace : WordTrace (prefixWord ++ tailWord_134190) baseStart_134190 baseEnd_134190 := by
    simpa [prefixWord, tailWord_134190, baseEnd_134190] using wordTrace_append hprefix tailTrace_134190
  have hstable : (prefixWord ++ tailWord_134190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134190).length < 2 ^ (prefixWord ++ tailWord_134190).sum := by decide
  have hdescent : baseEnd_134190 < baseStart_134190 := by decide
  rcases family_descends (prefixWord ++ tailWord_134190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134205 : List Nat := [1, 4, 1, 3, 1, 2, 2, 4, 4]
def baseStart_134205 : Nat := 118140960795 + 134205 * 2 ^ 59
def prefixEnd_134205 : Nat := 4983230072969 + 3 ^ 40 * 134205 * 2
def baseEnd_134205 : Nat := 15313704719278368004513

theorem tailTrace_134205 : CollatzResearch.WordTrace tailWord_134205 prefixEnd_134205 15313704719278368004513 := by
  unfold tailWord_134205
  simp only [CollatzResearch.WordTrace]
  refine ⟨4894858478805680234324069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3263238985870453489549379 4894858478805680234324069)
  ·
    refine ⟨917785964776065043935763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4894858478805680234324069 917785964776065043935763)
    ·
      refine ⟨1376678947164097565903645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 917785964776065043935763 1376678947164097565903645)
      ·
        refine ⟨516254605186536587213867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1376678947164097565903645 516254605186536587213867)
        ·
          refine ⟨774381907779804880820801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516254605186536587213867 774381907779804880820801)
          ·
            refine ⟨580786430834853660615601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774381907779804880820801 580786430834853660615601)
            ·
              refine ⟨435589823126140245461701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580786430834853660615601 435589823126140245461701)
              ·
                refine ⟨81673091836151296024069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 435589823126140245461701 81673091836151296024069)
                ·
                  refine ⟨15313704719278368004513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81673091836151296024069 15313704719278368004513)
                  ·
                    rfl

theorem cell22_134205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_134205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134205 prefixEnd_134205 := by exact prefixLift 134205
  have htrace : WordTrace (prefixWord ++ tailWord_134205) baseStart_134205 baseEnd_134205 := by
    simpa [prefixWord, tailWord_134205, baseEnd_134205] using wordTrace_append hprefix tailTrace_134205
  have hstable : (prefixWord ++ tailWord_134205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134205).length < 2 ^ (prefixWord ++ tailWord_134205).sum := by decide
  have hdescent : baseEnd_134205 < baseStart_134205 := by decide
  rcases family_descends (prefixWord ++ tailWord_134205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134216 : List Nat := [2, 1, 3, 1, 1, 1, 4, 9]
def baseStart_134216 : Nat := 118140960795 + 134216 * 2 ^ 59
def prefixEnd_134216 : Nat := 4983230072969 + 3 ^ 40 * 134216 * 2
def baseEnd_134216 : Nat := 5104986631403860220945

theorem tailTrace_134216 : CollatzResearch.WordTrace tailWord_134216 prefixEnd_134216 5104986631403860220945 := by
  unfold tailWord_134216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2447629840882914556487251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3263506454510552741983001 2447629840882914556487251)
  ·
    refine ⟨3671444761324371834730877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2447629840882914556487251 3671444761324371834730877)
    ·
      refine ⟨1376791785496639438024079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3671444761324371834730877 1376791785496639438024079)
      ·
        refine ⟨2065187678244959157036119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1376791785496639438024079 2065187678244959157036119)
        ·
          refine ⟨3097781517367438735554179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065187678244959157036119 3097781517367438735554179)
          ·
            refine ⟨4646672276051158103331269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097781517367438735554179 4646672276051158103331269)
            ·
              refine ⟨871251051759592144374613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4646672276051158103331269 871251051759592144374613)
              ·
                refine ⟨5104986631403860220945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 871251051759592144374613 5104986631403860220945)
                ·
                  rfl

theorem cell22_134216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 9].length) (baseStart_134216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134216 prefixEnd_134216 := by exact prefixLift 134216
  have htrace : WordTrace (prefixWord ++ tailWord_134216) baseStart_134216 baseEnd_134216 := by
    simpa [prefixWord, tailWord_134216, baseEnd_134216] using wordTrace_append hprefix tailTrace_134216
  have hstable : (prefixWord ++ tailWord_134216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134216).length < 2 ^ (prefixWord ++ tailWord_134216).sum := by decide
  have hdescent : baseEnd_134216 < baseStart_134216 := by decide
  rcases family_descends (prefixWord ++ tailWord_134216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134231 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 1, 9]
def baseStart_134231 : Nat := 118140960795 + 134231 * 2 ^ 59
def prefixEnd_134231 : Nat := 4983230072969 + 3 ^ 40 * 134231 * 2
def baseEnd_134231 : Nat := 45950014489179702863459

theorem tailTrace_134231 : CollatzResearch.WordTrace tailWord_134231 prefixEnd_134231 45950014489179702863459 := by
  unfold tailWord_134231
  simp only [CollatzResearch.WordTrace]
  refine ⟨4895806776711486674770547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3263871184474324449847031 4895806776711486674770547)
  ·
    refine ⟨7343710165067230012155821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4895806776711486674770547 7343710165067230012155821)
    ·
      refine ⟨2753891311900211254558433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7343710165067230012155821 2753891311900211254558433)
      ·
        refine ⟨2065418483925158440918825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2753891311900211254558433 2065418483925158440918825)
        ·
          refine ⟨1549063862943868830689119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2065418483925158440918825 1549063862943868830689119)
          ·
            refine ⟨2323595794415803246033679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549063862943868830689119 2323595794415803246033679)
            ·
              refine ⟨3485393691623704869050519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2323595794415803246033679 3485393691623704869050519)
              ·
                refine ⟨5228090537435557303575779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3485393691623704869050519 5228090537435557303575779)
                ·
                  refine ⟨7842135806153335955363669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5228090537435557303575779 7842135806153335955363669)
                  ·
                    refine ⟨45950014489179702863459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 7842135806153335955363669 45950014489179702863459)
                    ·
                      rfl

theorem cell22_134231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_134231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134231 prefixEnd_134231 := by exact prefixLift 134231
  have htrace : WordTrace (prefixWord ++ tailWord_134231) baseStart_134231 baseEnd_134231 := by
    simpa [prefixWord, tailWord_134231, baseEnd_134231] using wordTrace_append hprefix tailTrace_134231
  have hstable : (prefixWord ++ tailWord_134231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134231).length < 2 ^ (prefixWord ++ tailWord_134231).sum := by decide
  have hdescent : baseEnd_134231 < baseStart_134231 := by decide
  rcases family_descends (prefixWord ++ tailWord_134231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134357 : List Nat := [1, 3, 2, 4, 1, 1, 1, 5, 4]
def baseStart_134357 : Nat := 118140960795 + 134357 * 2 ^ 59
def prefixEnd_134357 : Nat := 4983230072969 + 3 ^ 40 * 134357 * 2
def baseEnd_134357 : Nat := 15331048954719124737691

theorem tailTrace_134357 : CollatzResearch.WordTrace tailWord_134357 prefixEnd_134357 15331048954719124737691 := by
  unfold tailWord_134357
  simp only [CollatzResearch.WordTrace]
  refine ⟨4900402374255010193857325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3266934916170006795904883 4900402374255010193857325)
  ·
    refine ⟨1837650890345628822696497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4900402374255010193857325 1837650890345628822696497)
    ·
      refine ⟨1378238167759221617022373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1837650890345628822696497 1378238167759221617022373)
      ·
        refine ⟨258419656454854053191695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1378238167759221617022373 258419656454854053191695)
        ·
          refine ⟨387629484682281079787543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258419656454854053191695 387629484682281079787543)
          ·
            refine ⟨581444227023421619681315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387629484682281079787543 581444227023421619681315)
            ·
              refine ⟨872166340535132429521973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581444227023421619681315 872166340535132429521973)
              ·
                refine ⟨81765594425168665267685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 872166340535132429521973 81765594425168665267685)
                ·
                  refine ⟨15331048954719124737691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81765594425168665267685 15331048954719124737691)
                  ·
                    rfl

theorem cell22_134357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_134357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134357 prefixEnd_134357 := by exact prefixLift 134357
  have htrace : WordTrace (prefixWord ++ tailWord_134357) baseStart_134357 baseEnd_134357 := by
    simpa [prefixWord, tailWord_134357, baseEnd_134357] using wordTrace_append hprefix tailTrace_134357
  have hstable : (prefixWord ++ tailWord_134357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134357).length < 2 ^ (prefixWord ++ tailWord_134357).sum := by decide
  have hdescent : baseEnd_134357 < baseStart_134357 := by decide
  rcases family_descends (prefixWord ++ tailWord_134357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134368 : List Nat := [2, 1, 1, 3, 1, 5, 9]
def baseStart_134368 : Nat := 118140960795 + 134368 * 2 ^ 59
def prefixEnd_134368 : Nat := 4983230072969 + 3 ^ 40 * 134368 * 2
def baseEnd_134368 : Nat := 1703589347739148599557

theorem tailTrace_134368 : CollatzResearch.WordTrace tailWord_134368 prefixEnd_134368 1703589347739148599557 := by
  unfold tailWord_134368
  simp only [CollatzResearch.WordTrace]
  refine ⟨2450401788607579536253879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3267202384810106048338505 2450401788607579536253879)
  ·
    refine ⟨3675602682911369304380819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2450401788607579536253879 3675602682911369304380819)
    ·
      refine ⟨5513404024367053956571229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3675602682911369304380819 5513404024367053956571229)
      ·
        refine ⟨2067526509137645233714211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5513404024367053956571229 2067526509137645233714211)
        ·
          refine ⟨3101289763706467850571317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2067526509137645233714211 3101289763706467850571317)
          ·
            refine ⟨290745915347481360991061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3101289763706467850571317 290745915347481360991061)
            ·
              refine ⟨1703589347739148599557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 290745915347481360991061 1703589347739148599557)
              ·
                rfl

theorem cell22_134368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 9].length) (baseStart_134368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134368 prefixEnd_134368 := by exact prefixLift 134368
  have htrace : WordTrace (prefixWord ++ tailWord_134368) baseStart_134368 baseEnd_134368 := by
    simpa [prefixWord, tailWord_134368, baseEnd_134368] using wordTrace_append hprefix tailTrace_134368
  have hstable : (prefixWord ++ tailWord_134368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134368).length < 2 ^ (prefixWord ++ tailWord_134368).sum := by decide
  have hdescent : baseEnd_134368 < baseStart_134368 := by decide
  rcases family_descends (prefixWord ++ tailWord_134368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134372 : List Nat := [2, 3, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_134372 : Nat := 118140960795 + 134372 * 2 ^ 59
def prefixEnd_134372 : Nat := 4983230072969 + 3 ^ 40 * 134372 * 2
def baseEnd_134372 : Nat := 45998281670702335088027

theorem tailTrace_134372 : CollatzResearch.WordTrace tailWord_134372 prefixEnd_134372 45998281670702335088027 := by
  unfold tailWord_134372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2450474734600333877826685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3267299646133778503768913 2450474734600333877826685)
  ·
    refine ⟨918928025475125204185007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2450474734600333877826685 918928025475125204185007)
    ·
      refine ⟨1378392038212687806277511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 918928025475125204185007 1378392038212687806277511)
      ·
        refine ⟨2067588057319031709416267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1378392038212687806277511 2067588057319031709416267)
        ·
          refine ⟨3101382085978547564124401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2067588057319031709416267 3101382085978547564124401)
          ·
            refine ⟨2326036564483910673093301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3101382085978547564124401 2326036564483910673093301)
            ·
              refine ⟨218065927920366625602497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2326036564483910673093301 218065927920366625602497)
              ·
                refine ⟨163549445940274969201873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218065927920366625602497 163549445940274969201873)
                ·
                  refine ⟨122662084455206226901405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163549445940274969201873 122662084455206226901405)
                  ·
                    refine ⟨45998281670702335088027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122662084455206226901405 45998281670702335088027)
                    ·
                      rfl

theorem cell22_134372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_134372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134372 prefixEnd_134372 := by exact prefixLift 134372
  have htrace : WordTrace (prefixWord ++ tailWord_134372) baseStart_134372 baseEnd_134372 := by
    simpa [prefixWord, tailWord_134372, baseEnd_134372] using wordTrace_append hprefix tailTrace_134372
  have hstable : (prefixWord ++ tailWord_134372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134372).length < 2 ^ (prefixWord ++ tailWord_134372).sum := by decide
  have hdescent : baseEnd_134372 < baseStart_134372 := by decide
  rcases family_descends (prefixWord ++ tailWord_134372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134402 : List Nat := [3, 4, 1, 1, 3, 1, 1, 8]
def baseStart_134402 : Nat := 118140960795 + 134402 * 2 ^ 59
def prefixEnd_134402 : Nat := 4983230072969 + 3 ^ 40 * 134402 * 2
def baseEnd_134402 : Nat := 5112061253754695204215

theorem tailTrace_134402 : CollatzResearch.WordTrace tailWord_134402 prefixEnd_134402 5112061253754695204215 := by
  unfold tailWord_134402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225510914772995719811365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3268029106061321919496973 1225510914772995719811365)
  ·
    refine ⟨229783296519936697464631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1225510914772995719811365 229783296519936697464631)
    ·
      refine ⟨344674944779905046196947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229783296519936697464631 344674944779905046196947)
      ·
        refine ⟨517012417169857569295421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344674944779905046196947 517012417169857569295421)
        ·
          refine ⟨193879656438696588485783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 517012417169857569295421 193879656438696588485783)
          ·
            refine ⟨290819484658044882728675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193879656438696588485783 290819484658044882728675)
            ·
              refine ⟨436229226987067324093013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290819484658044882728675 436229226987067324093013)
              ·
                refine ⟨5112061253754695204215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 436229226987067324093013 5112061253754695204215)
                ·
                  rfl

theorem cell22_134402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_134402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134402 prefixEnd_134402 := by exact prefixLift 134402
  have htrace : WordTrace (prefixWord ++ tailWord_134402) baseStart_134402 baseEnd_134402 := by
    simpa [prefixWord, tailWord_134402, baseEnd_134402] using wordTrace_append hprefix tailTrace_134402
  have hstable : (prefixWord ++ tailWord_134402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134402).length < 2 ^ (prefixWord ++ tailWord_134402).sum := by decide
  have hdescent : baseEnd_134402 < baseStart_134402 := by decide
  rcases family_descends (prefixWord ++ tailWord_134402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134558 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_134558 : Nat := 118140960795 + 134558 * 2 ^ 59
def prefixEnd_134558 : Nat := 4983230072969 + 3 ^ 40 * 134558 * 2
def baseEnd_134558 : Nat := 46061953271859849937457

theorem tailTrace_134558 : CollatzResearch.WordTrace tailWord_134558 prefixEnd_134558 46061953271859849937457 := by
  unfold tailWord_134558
  simp only [CollatzResearch.WordTrace]
  refine ⟨613466680815852690240541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3271822297684547681282885 613466680815852690240541)
  ·
    refine ⟨230050005305944758840203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 613466680815852690240541 230050005305944758840203)
    ·
      refine ⟨345075007958917138260305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230050005305944758840203 345075007958917138260305)
      ·
        refine ⟨258806255969187853695229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345075007958917138260305 258806255969187853695229)
        ·
          refine ⟨97052345988445445135711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258806255969187853695229 97052345988445445135711)
          ·
            refine ⟨145578518982668167703567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97052345988445445135711 145578518982668167703567)
            ·
              refine ⟨218367778474002251555351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145578518982668167703567 218367778474002251555351)
              ·
                refine ⟨327551667711003377333027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218367778474002251555351 327551667711003377333027)
                ·
                  refine ⟨491327501566505065999541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327551667711003377333027 491327501566505065999541)
                  ·
                    refine ⟨46061953271859849937457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 491327501566505065999541 46061953271859849937457)
                    ·
                      rfl

theorem cell22_134558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_134558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134558 prefixEnd_134558 := by exact prefixLift 134558
  have htrace : WordTrace (prefixWord ++ tailWord_134558) baseStart_134558 baseEnd_134558 := by
    simpa [prefixWord, tailWord_134558, baseEnd_134558] using wordTrace_append hprefix tailTrace_134558
  have hstable : (prefixWord ++ tailWord_134558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134558).length < 2 ^ (prefixWord ++ tailWord_134558).sum := by decide
  have hdescent : baseEnd_134558 < baseStart_134558 := by decide
  rcases family_descends (prefixWord ++ tailWord_134558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134629 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_134629 : Nat := 118140960795 + 134629 * 2 ^ 59
def prefixEnd_134629 : Nat := 4983230072969 + 3 ^ 40 * 134629 * 2
def baseEnd_134629 : Nat := 46086258022839331412239

theorem tailTrace_134629 : CollatzResearch.WordTrace tailWord_134629 prefixEnd_134629 46086258022839331412239 := by
  unfold tailWord_134629
  simp only [CollatzResearch.WordTrace]
  refine ⟨4910323029269600647758941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3273548686179733765172627 4910323029269600647758941)
  ·
    refine ⟨1841371135976100242909603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4910323029269600647758941 1841371135976100242909603)
    ·
      refine ⟨2762056703964150364364405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1841371135976100242909603 2762056703964150364364405)
      ·
        refine ⟨258942815996639096659163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2762056703964150364364405 258942815996639096659163)
        ·
          refine ⟨388414223994958644988745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258942815996639096659163 388414223994958644988745)
          ·
            refine ⟨291310667996218983741559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 388414223994958644988745 291310667996218983741559)
            ·
              refine ⟨436966001994328475612339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291310667996218983741559 436966001994328475612339)
              ·
                refine ⟨655449002991492713418509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436966001994328475612339 655449002991492713418509)
                ·
                  refine ⟨245793376121809767531941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655449002991492713418509 245793376121809767531941)
                  ·
                    refine ⟨46086258022839331412239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 245793376121809767531941 46086258022839331412239)
                    ·
                      rfl

theorem cell22_134629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_134629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134629 prefixEnd_134629 := by exact prefixLift 134629
  have htrace : WordTrace (prefixWord ++ tailWord_134629) baseStart_134629 baseEnd_134629 := by
    simpa [prefixWord, tailWord_134629, baseEnd_134629] using wordTrace_append hprefix tailTrace_134629
  have hstable : (prefixWord ++ tailWord_134629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134629).length < 2 ^ (prefixWord ++ tailWord_134629).sum := by decide
  have hdescent : baseEnd_134629 < baseStart_134629 := by decide
  rcases family_descends (prefixWord ++ tailWord_134629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134654 : List Nat := [4, 2, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_134654 : Nat := 118140960795 + 134654 * 2 ^ 59
def prefixEnd_134654 : Nat := 4983230072969 + 3 ^ 40 * 134654 * 2
def baseEnd_134654 : Nat := 46094816033747599537163

theorem tailTrace_134654 : CollatzResearch.WordTrace tailWord_134654 prefixEnd_134654 46094816033747599537163 := by
  unfold tailWord_134654
  simp only [CollatzResearch.WordTrace]
  refine ⟨613904356772378739677377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3274156569452686611612677 613904356772378739677377)
  ·
    refine ⟨460428267579284054758033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 613904356772378739677377 460428267579284054758033)
    ·
      refine ⟨345321200684463041068525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 460428267579284054758033 345321200684463041068525)
      ·
        refine ⟨129495450256673640400697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 345321200684463041068525 129495450256673640400697)
        ·
          refine ⟨97121587692505230300523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129495450256673640400697 97121587692505230300523)
          ·
            refine ⟨145682381538757845450785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97121587692505230300523 145682381538757845450785)
            ·
              refine ⟨109261786154068384088089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145682381538757845450785 109261786154068384088089)
              ·
                refine ⟨81946339615551288066067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109261786154068384088089 81946339615551288066067)
                ·
                  refine ⟨122919509423326932099101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81946339615551288066067 122919509423326932099101)
                  ·
                    refine ⟨46094816033747599537163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122919509423326932099101 46094816033747599537163)
                    ·
                      rfl

theorem cell22_134654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_134654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134654 prefixEnd_134654 := by exact prefixLift 134654
  have htrace : WordTrace (prefixWord ++ tailWord_134654) baseStart_134654 baseEnd_134654 := by
    simpa [prefixWord, tailWord_134654, baseEnd_134654] using wordTrace_append hprefix tailTrace_134654
  have hstable : (prefixWord ++ tailWord_134654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134654).length < 2 ^ (prefixWord ++ tailWord_134654).sum := by decide
  have hdescent : baseEnd_134654 < baseStart_134654 := by decide
  rcases family_descends (prefixWord ++ tailWord_134654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134689 : List Nat := [1, 2, 3, 2, 2, 3, 3, 6]
def baseStart_134689 : Nat := 118140960795 + 134689 * 2 ^ 59
def prefixEnd_134689 : Nat := 4983230072969 + 3 ^ 40 * 134689 * 2
def baseEnd_134689 : Nat := 5122977472113241656895

theorem tailTrace_134689 : CollatzResearch.WordTrace tailWord_134689 prefixEnd_134689 5122977472113241656895 := by
  unfold tailWord_134689
  simp only [CollatzResearch.WordTrace]
  refine ⟨4912511409052230894943121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3275007606034820596628747 4912511409052230894943121)
  ·
    refine ⟨3684383556789173171207341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4912511409052230894943121 3684383556789173171207341)
    ·
      refine ⟨1381643833795939939202753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3684383556789173171207341 1381643833795939939202753)
      ·
        refine ⟨1036232875346954954402065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1381643833795939939202753 1036232875346954954402065)
        ·
          refine ⟨777174656510216215801549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1036232875346954954402065 777174656510216215801549)
          ·
            refine ⟨291440496191331080925581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 777174656510216215801549 291440496191331080925581)
            ·
              refine ⟨109290186071749155347093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 291440496191331080925581 109290186071749155347093)
              ·
                refine ⟨5122977472113241656895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109290186071749155347093 5122977472113241656895)
                ·
                  rfl

theorem cell22_134689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 6].length) (baseStart_134689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134689 prefixEnd_134689 := by exact prefixLift 134689
  have htrace : WordTrace (prefixWord ++ tailWord_134689) baseStart_134689 baseEnd_134689 := by
    simpa [prefixWord, tailWord_134689, baseEnd_134689] using wordTrace_append hprefix tailTrace_134689
  have hstable : (prefixWord ++ tailWord_134689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134689).length < 2 ^ (prefixWord ++ tailWord_134689).sum := by decide
  have hdescent : baseEnd_134689 < baseStart_134689 := by decide
  rcases family_descends (prefixWord ++ tailWord_134689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134691 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 2, 4]
def baseStart_134691 : Nat := 118140960795 + 134691 * 2 ^ 59
def prefixEnd_134691 : Nat := 4983230072969 + 3 ^ 40 * 134691 * 2
def baseEnd_134691 : Nat := 46107481889891836362049

theorem tailTrace_134691 : CollatzResearch.WordTrace tailWord_134691 prefixEnd_134691 46107481889891836362049 := by
  unfold tailWord_134691
  simp only [CollatzResearch.WordTrace]
  refine ⟨4912584355044985236515927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3275056236696656824343951 4912584355044985236515927)
  ·
    refine ⟨7368876532567477854773891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4912584355044985236515927 7368876532567477854773891)
    ·
      refine ⟨11053314798851216782160837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7368876532567477854773891 11053314798851216782160837)
      ·
        refine ⟨2072496524784603146655157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11053314798851216782160837 2072496524784603146655157)
        ·
          refine ⟨194296549198556544998921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2072496524784603146655157 194296549198556544998921)
          ·
            refine ⟨145722411898917408749191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194296549198556544998921 145722411898917408749191)
            ·
              refine ⟨218583617848376113123787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145722411898917408749191 218583617848376113123787)
              ·
                refine ⟨327875426772564169685681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218583617848376113123787 327875426772564169685681)
                ·
                  refine ⟨245906570079423127264261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327875426772564169685681 245906570079423127264261)
                  ·
                    refine ⟨46107481889891836362049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 245906570079423127264261 46107481889891836362049)
                    ·
                      rfl

theorem cell22_134691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 4].length) (baseStart_134691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134691 prefixEnd_134691 := by exact prefixLift 134691
  have htrace : WordTrace (prefixWord ++ tailWord_134691) baseStart_134691 baseEnd_134691 := by
    simpa [prefixWord, tailWord_134691, baseEnd_134691] using wordTrace_append hprefix tailTrace_134691
  have hstable : (prefixWord ++ tailWord_134691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134691).length < 2 ^ (prefixWord ++ tailWord_134691).sum := by decide
  have hdescent : baseEnd_134691 < baseStart_134691 := by decide
  rcases family_descends (prefixWord ++ tailWord_134691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134710 : List Nat := [5, 1, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_134710 : Nat := 118140960795 + 134710 * 2 ^ 59
def prefixEnd_134710 : Nat := 4983230072969 + 3 ^ 40 * 134710 * 2
def baseEnd_134710 : Nat := 46113985978182120136991

theorem tailTrace_134710 : CollatzResearch.WordTrace tailWord_134710 prefixEnd_134710 46113985978182120136991 := by
  unfold tailWord_134710
  simp only [CollatzResearch.WordTrace]
  refine ⟨307079833873509467591099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3275518227984100987638389 307079833873509467591099)
  ·
    refine ⟨460619750810264201386649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 307079833873509467591099 460619750810264201386649)
    ·
      refine ⟨345464813107698151039987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 460619750810264201386649 345464813107698151039987)
      ·
        refine ⟨518197219661547226559981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345464813107698151039987 518197219661547226559981)
        ·
          refine ⟨194323957373080209959993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 518197219661547226559981 194323957373080209959993)
          ·
            refine ⟨145742968029810157469995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194323957373080209959993 145742968029810157469995)
            ·
              refine ⟨218614452044715236204993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145742968029810157469995 218614452044715236204993)
              ·
                refine ⟨163960839033536427153745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218614452044715236204993 163960839033536427153745)
                ·
                  refine ⟨122970629275152320365309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163960839033536427153745 122970629275152320365309)
                  ·
                    refine ⟨46113985978182120136991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122970629275152320365309 46113985978182120136991)
                    ·
                      rfl

theorem cell22_134710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_134710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134710 prefixEnd_134710 := by exact prefixLift 134710
  have htrace : WordTrace (prefixWord ++ tailWord_134710) baseStart_134710 baseEnd_134710 := by
    simpa [prefixWord, tailWord_134710, baseEnd_134710] using wordTrace_append hprefix tailTrace_134710
  have hstable : (prefixWord ++ tailWord_134710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134710).length < 2 ^ (prefixWord ++ tailWord_134710).sum := by decide
  have hdescent : baseEnd_134710 < baseStart_134710 := by decide
  rcases family_descends (prefixWord ++ tailWord_134710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134721 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 3, 3]
def baseStart_134721 : Nat := 118140960795 + 134721 * 2 ^ 59
def prefixEnd_134721 : Nat := 4983230072969 + 3 ^ 40 * 134721 * 2
def baseEnd_134721 : Nat := 46117751502981758111957

theorem tailTrace_134721 : CollatzResearch.WordTrace tailWord_134721 prefixEnd_134721 46117751502981758111957 := by
  unfold tailWord_134721
  simp only [CollatzResearch.WordTrace]
  refine ⟨4913678544936300360108017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3275785696624200240072011 4913678544936300360108017)
  ·
    refine ⟨3685258908702225270081013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4913678544936300360108017 3685258908702225270081013)
    ·
      refine ⟨345493022690833619070095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3685258908702225270081013 345493022690833619070095)
      ·
        refine ⟨518239534036250428605143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345493022690833619070095 518239534036250428605143)
        ·
          refine ⟨777359301054375642907715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518239534036250428605143 777359301054375642907715)
          ·
            refine ⟨1166038951581563464361573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777359301054375642907715 1166038951581563464361573)
            ·
              refine ⟨218632303421543149567795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1166038951581563464361573 218632303421543149567795)
              ·
                refine ⟨327948455132314724351693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218632303421543149567795 327948455132314724351693)
                ·
                  refine ⟨122980670674618021631885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327948455132314724351693 122980670674618021631885)
                  ·
                    refine ⟨46117751502981758111957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122980670674618021631885 46117751502981758111957)
                    ·
                      rfl

theorem cell22_134721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_134721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134721 prefixEnd_134721 := by exact prefixLift 134721
  have htrace : WordTrace (prefixWord ++ tailWord_134721) baseStart_134721 baseEnd_134721 := by
    simpa [prefixWord, tailWord_134721, baseEnd_134721] using wordTrace_append hprefix tailTrace_134721
  have hstable : (prefixWord ++ tailWord_134721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134721).length < 2 ^ (prefixWord ++ tailWord_134721).sum := by decide
  have hdescent : baseEnd_134721 < baseStart_134721 := by decide
  rcases family_descends (prefixWord ++ tailWord_134721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134798 : List Nat := [4, 1, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_134798 : Nat := 118140960795 + 134798 * 2 ^ 59
def prefixEnd_134798 : Nat := 4983230072969 + 3 ^ 40 * 134798 * 2
def baseEnd_134798 : Nat := 46144110176579223936721

theorem tailTrace_134798 : CollatzResearch.WordTrace tailWord_134798 prefixEnd_134798 46144110176579223936721 := by
  unfold tailWord_134798
  simp only [CollatzResearch.WordTrace]
  refine ⟨614560870707167813832631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3277657977104895007107365 614560870707167813832631)
  ·
    refine ⟨921841306060751720748947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 614560870707167813832631 921841306060751720748947)
    ·
      refine ⟨1382761959091127581123421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 921841306060751720748947 1382761959091127581123421)
      ·
        refine ⟨518535734659172842921283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1382761959091127581123421 518535734659172842921283)
        ·
          refine ⟨777803601988759264381925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518535734659172842921283 777803601988759264381925)
          ·
            refine ⟨145838175372892362071611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 777803601988759264381925 145838175372892362071611)
            ·
              refine ⟨218757263059338543107417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145838175372892362071611 218757263059338543107417)
              ·
                refine ⟨164067947294503907330563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218757263059338543107417 164067947294503907330563)
                ·
                  refine ⟨246101920941755860995845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164067947294503907330563 246101920941755860995845)
                  ·
                    refine ⟨46144110176579223936721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 246101920941755860995845 46144110176579223936721)
                    ·
                      rfl

theorem cell22_134798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_134798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134798 prefixEnd_134798 := by exact prefixLift 134798
  have htrace : WordTrace (prefixWord ++ tailWord_134798) baseStart_134798 baseEnd_134798 := by
    simpa [prefixWord, tailWord_134798, baseEnd_134798] using wordTrace_append hprefix tailTrace_134798
  have hstable : (prefixWord ++ tailWord_134798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134798).length < 2 ^ (prefixWord ++ tailWord_134798).sum := by decide
  have hdescent : baseEnd_134798 < baseStart_134798 := by decide
  rcases family_descends (prefixWord ++ tailWord_134798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134815 : List Nat := [1, 1, 2, 7, 1, 1, 3, 1, 1, 4]
def baseStart_134815 : Nat := 118140960795 + 134815 * 2 ^ 59
def prefixEnd_134815 : Nat := 4983230072969 + 3 ^ 40 * 134815 * 2
def baseEnd_134815 : Nat := 46149929623996846261669

theorem tailTrace_134815 : CollatzResearch.WordTrace tailWord_134815 prefixEnd_134815 46149929623996846261669 := by
  unfold tailWord_134815
  simp only [CollatzResearch.WordTrace]
  refine ⟨4917107006595754414029899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3278071337730502942686599 4917107006595754414029899)
  ·
    refine ⟨7375660509893631621044849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4917107006595754414029899 7375660509893631621044849)
    ·
      refine ⟨5531745382420223715783637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7375660509893631621044849 5531745382420223715783637)
      ·
        refine ⟨129650282400473993338679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 5531745382420223715783637 129650282400473993338679)
        ·
          refine ⟨194475423600710990008019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129650282400473993338679 194475423600710990008019)
          ·
            refine ⟨291713135401066485012029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194475423600710990008019 291713135401066485012029)
            ·
              refine ⟨109392425775399931879511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 291713135401066485012029 109392425775399931879511)
              ·
                refine ⟨164088638663099897819267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109392425775399931879511 164088638663099897819267)
                ·
                  refine ⟨246132957994649846728901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164088638663099897819267 246132957994649846728901)
                  ·
                    refine ⟨46149929623996846261669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 246132957994649846728901 46149929623996846261669)
                    ·
                      rfl

theorem cell22_134815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 1, 4].length) (baseStart_134815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134815 prefixEnd_134815 := by exact prefixLift 134815
  have htrace : WordTrace (prefixWord ++ tailWord_134815) baseStart_134815 baseEnd_134815 := by
    simpa [prefixWord, tailWord_134815, baseEnd_134815] using wordTrace_append hprefix tailTrace_134815
  have hstable : (prefixWord ++ tailWord_134815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134815).length < 2 ^ (prefixWord ++ tailWord_134815).sum := by decide
  have hdescent : baseEnd_134815 < baseStart_134815 := by decide
  rcases family_descends (prefixWord ++ tailWord_134815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134830 : List Nat := [4, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_134830 : Nat := 118140960795 + 134830 * 2 ^ 59
def prefixEnd_134830 : Nat := 4983230072969 + 3 ^ 40 * 134830 * 2
def baseEnd_134830 : Nat := 15385021476847269045541

theorem tailTrace_134830 : CollatzResearch.WordTrace tailWord_134830 prefixEnd_134830 15385021476847269045541 := by
  unfold tailWord_134830
  simp only [CollatzResearch.WordTrace]
  refine ⟨614706762692676496978243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3278436067694274650550629 614706762692676496978243)
  ·
    refine ⟨922060144039014745467365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 614706762692676496978243 922060144039014745467365)
    ·
      refine ⟨172886277007315264775131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 922060144039014745467365 172886277007315264775131)
      ·
        refine ⟨259329415510972897162697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172886277007315264775131 259329415510972897162697)
        ·
          refine ⟨194497061633229672872023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259329415510972897162697 194497061633229672872023)
          ·
            refine ⟨291745592449844509308035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194497061633229672872023 291745592449844509308035)
            ·
              refine ⟨437618388674766763962053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291745592449844509308035 437618388674766763962053)
              ·
                refine ⟨82053447876518768242885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 437618388674766763962053 82053447876518768242885)
                ·
                  refine ⟨15385021476847269045541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82053447876518768242885 15385021476847269045541)
                  ·
                    rfl

theorem cell22_134830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_134830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134830 prefixEnd_134830 := by exact prefixLift 134830
  have htrace : WordTrace (prefixWord ++ tailWord_134830) baseStart_134830 baseEnd_134830 := by
    simpa [prefixWord, tailWord_134830, baseEnd_134830] using wordTrace_append hprefix tailTrace_134830
  have hstable : (prefixWord ++ tailWord_134830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134830).length < 2 ^ (prefixWord ++ tailWord_134830).sum := by decide
  have hdescent : baseEnd_134830 < baseStart_134830 := by decide
  rcases family_descends (prefixWord ++ tailWord_134830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134856 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 3, 3]
def baseStart_134856 : Nat := 118140960795 + 134856 * 2 ^ 59
def prefixEnd_134856 : Nat := 4983230072969 + 3 ^ 40 * 134856 * 2
def baseEnd_134856 : Nat := 46163964761886405986543

theorem tailTrace_134856 : CollatzResearch.WordTrace tailWord_134856 prefixEnd_134856 46163964761886405986543 := by
  unfold tailWord_134856
  simp only [CollatzResearch.WordTrace]
  refine ⟨2459301199723609208136211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3279068266298145610848281 2459301199723609208136211)
  ·
    refine ⟨3688951799585413812204317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2459301199723609208136211 3688951799585413812204317)
    ·
      refine ⟨1383356924844530179576619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3688951799585413812204317 1383356924844530179576619)
      ·
        refine ⟨2075035387266795269364929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1383356924844530179576619 2075035387266795269364929)
        ·
          refine ⟨1556276540450096452023697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2075035387266795269364929 1556276540450096452023697)
          ·
            refine ⟨1167207405337572339017773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1556276540450096452023697 1167207405337572339017773)
            ·
              refine ⟨437702777001589627131665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1167207405337572339017773 437702777001589627131665)
              ·
                refine ⟨328277082751192220348749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437702777001589627131665 328277082751192220348749)
                ·
                  refine ⟨123103906031697082630781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328277082751192220348749 123103906031697082630781)
                  ·
                    refine ⟨46163964761886405986543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 123103906031697082630781 46163964761886405986543)
                    ·
                      rfl

theorem cell22_134856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_134856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134856 prefixEnd_134856 := by exact prefixLift 134856
  have htrace : WordTrace (prefixWord ++ tailWord_134856) baseStart_134856 baseEnd_134856 := by
    simpa [prefixWord, tailWord_134856, baseEnd_134856] using wordTrace_append hprefix tailTrace_134856
  have hstable : (prefixWord ++ tailWord_134856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134856).length < 2 ^ (prefixWord ++ tailWord_134856).sum := by decide
  have hdescent : baseEnd_134856 < baseStart_134856 := by decide
  rcases family_descends (prefixWord ++ tailWord_134856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134860 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 2, 4]
def baseStart_134860 : Nat := 118140960795 + 134860 * 2 ^ 59
def prefixEnd_134860 : Nat := 4983230072969 + 3 ^ 40 * 134860 * 2
def baseEnd_134860 : Nat := 46165334043631728886531

theorem tailTrace_134860 : CollatzResearch.WordTrace tailWord_134860 prefixEnd_134860 46165334043631728886531 := by
  unfold tailWord_134860
  simp only [CollatzResearch.WordTrace]
  refine ⟨2459374145716363549709017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3279165527621818066278689 2459374145716363549709017)
  ·
    refine ⟨1844530609287272662281763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2459374145716363549709017 1844530609287272662281763)
    ·
      refine ⟨2766795913930908993422645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1844530609287272662281763 2766795913930908993422645)
      ·
        refine ⟨259387116931022718133373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2766795913930908993422645 259387116931022718133373)
        ·
          refine ⟨97270168849133519300015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259387116931022718133373 97270168849133519300015)
          ·
            refine ⟨145905253273700278950023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97270168849133519300015 145905253273700278950023)
            ·
              refine ⟨218857879910550418425035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145905253273700278950023 218857879910550418425035)
              ·
                refine ⟨328286819865825627637553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218857879910550418425035 328286819865825627637553)
                ·
                  refine ⟨246215114899369220728165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328286819865825627637553 246215114899369220728165)
                  ·
                    refine ⟨46165334043631728886531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 246215114899369220728165 46165334043631728886531)
                    ·
                      rfl

theorem cell22_134860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_134860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134860 prefixEnd_134860 := by exact prefixLift 134860
  have htrace : WordTrace (prefixWord ++ tailWord_134860) baseStart_134860 baseEnd_134860 := by
    simpa [prefixWord, tailWord_134860, baseEnd_134860] using wordTrace_append hprefix tailTrace_134860
  have hstable : (prefixWord ++ tailWord_134860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134860).length < 2 ^ (prefixWord ++ tailWord_134860).sum := by decide
  have hdescent : baseEnd_134860 < baseStart_134860 := by decide
  rcases family_descends (prefixWord ++ tailWord_134860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134873 : List Nat := [1, 2, 1, 2, 3, 3, 1, 5, 1, 3]
def baseStart_134873 : Nat := 118140960795 + 134873 * 2 ^ 59
def prefixEnd_134873 : Nat := 4983230072969 + 3 ^ 40 * 134873 * 2
def baseEnd_134873 : Nat := 46169784209304028311491

theorem tailTrace_134873 : CollatzResearch.WordTrace tailWord_134873 prefixEnd_134873 46169784209304028311491 := by
  unfold tailWord_134873
  simp only [CollatzResearch.WordTrace]
  refine ⟨4919222440385630319641273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3279481626923753546427515 4919222440385630319641273)
  ·
    refine ⟨3689416830289222739730955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4919222440385630319641273 3689416830289222739730955)
    ·
      refine ⟨5534125245433834109596433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3689416830289222739730955 5534125245433834109596433)
      ·
        refine ⟨4150593934075375582197325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5534125245433834109596433 4150593934075375582197325)
        ·
          refine ⟨1556472725278265843323997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4150593934075375582197325 1556472725278265843323997)
          ·
            refine ⟨583677271979349691246499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1556472725278265843323997 583677271979349691246499)
            ·
              refine ⟨875515907969024536869749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583677271979349691246499 875515907969024536869749)
              ·
                refine ⟨82079616372096050331539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 875515907969024536869749 82079616372096050331539)
                ·
                  refine ⟨123119424558144075497309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82079616372096050331539 123119424558144075497309)
                  ·
                    refine ⟨46169784209304028311491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 123119424558144075497309 46169784209304028311491)
                    ·
                      rfl

theorem cell22_134873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 1, 3].length) (baseStart_134873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134873 prefixEnd_134873 := by exact prefixLift 134873
  have htrace : WordTrace (prefixWord ++ tailWord_134873) baseStart_134873 baseEnd_134873 := by
    simpa [prefixWord, tailWord_134873, baseEnd_134873] using wordTrace_append hprefix tailTrace_134873
  have hstable : (prefixWord ++ tailWord_134873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134873).length < 2 ^ (prefixWord ++ tailWord_134873).sum := by decide
  have hdescent : baseEnd_134873 < baseStart_134873 := by decide
  rcases family_descends (prefixWord ++ tailWord_134873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134884 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_134884 : Nat := 118140960795 + 134884 * 2 ^ 59
def prefixEnd_134884 : Nat := 4983230072969 + 3 ^ 40 * 134884 * 2
def baseEnd_134884 : Nat := 46173549734103666286457

theorem tailTrace_134884 : CollatzResearch.WordTrace tailWord_134884 prefixEnd_134884 46173549734103666286457 := by
  unfold tailWord_134884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2459811821672889599145853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3279749095563852798861137 2459811821672889599145853)
  ·
    refine ⟨922429433127333599679695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2459811821672889599145853 922429433127333599679695)
    ·
      refine ⟨1383644149691000399519543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 922429433127333599679695 1383644149691000399519543)
      ·
        refine ⟨2075466224536500599279315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1383644149691000399519543 2075466224536500599279315)
        ·
          refine ⟨3113199336804750898918973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2075466224536500599279315 3113199336804750898918973)
          ·
            refine ⟨1167449751301781587094615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3113199336804750898918973 1167449751301781587094615)
            ·
              refine ⟨1751174626952672380641923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167449751301781587094615 1751174626952672380641923)
              ·
                refine ⟨2626761940429008570962885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751174626952672380641923 2626761940429008570962885)
                ·
                  refine ⟨492517863830439107055541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2626761940429008570962885 492517863830439107055541)
                  ·
                    refine ⟨46173549734103666286457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 492517863830439107055541 46173549734103666286457)
                    ·
                      rfl

theorem cell22_134884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_134884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134884 prefixEnd_134884 := by exact prefixLift 134884
  have htrace : WordTrace (prefixWord ++ tailWord_134884) baseStart_134884 baseEnd_134884 := by
    simpa [prefixWord, tailWord_134884, baseEnd_134884] using wordTrace_append hprefix tailTrace_134884
  have hstable : (prefixWord ++ tailWord_134884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134884).length < 2 ^ (prefixWord ++ tailWord_134884).sum := by decide
  have hdescent : baseEnd_134884 < baseStart_134884 := by decide
  rcases family_descends (prefixWord ++ tailWord_134884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134899 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 5, 4]
def baseStart_134899 : Nat := 118140960795 + 134899 * 2 ^ 59
def prefixEnd_134899 : Nat := 4983230072969 + 3 ^ 40 * 134899 * 2
def baseEnd_134899 : Nat := 46178684540648627161411

theorem tailTrace_134899 : CollatzResearch.WordTrace tailWord_134899 prefixEnd_134899 46178684540648627161411 := by
  unfold tailWord_134899
  simp only [CollatzResearch.WordTrace]
  refine ⟨4920170738291436760087751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3280113825527624506725167 4920170738291436760087751)
  ·
    refine ⟨7380256107437155140131627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4920170738291436760087751 7380256107437155140131627)
    ·
      refine ⟨11070384161155732710197441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7380256107437155140131627 11070384161155732710197441)
      ·
        refine ⟨8302788120866799532648081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11070384161155732710197441 8302788120866799532648081)
        ·
          refine ⟨6227091090650099649486061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8302788120866799532648081 6227091090650099649486061)
          ·
            refine ⟨2335159158993787368557273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6227091090650099649486061 2335159158993787368557273)
            ·
              refine ⟨1751369369245340526417955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2335159158993787368557273 1751369369245340526417955)
              ·
                refine ⟨2627054053868010789626933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751369369245340526417955 2627054053868010789626933)
                ·
                  refine ⟨246286317550126011527525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2627054053868010789626933 246286317550126011527525)
                  ·
                    refine ⟨46178684540648627161411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 246286317550126011527525 46178684540648627161411)
                    ·
                      rfl

theorem cell22_134899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 4].length) (baseStart_134899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134899 prefixEnd_134899 := by exact prefixLift 134899
  have htrace : WordTrace (prefixWord ++ tailWord_134899) baseStart_134899 baseEnd_134899 := by
    simpa [prefixWord, tailWord_134899, baseEnd_134899] using wordTrace_append hprefix tailTrace_134899
  have hstable : (prefixWord ++ tailWord_134899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134899).length < 2 ^ (prefixWord ++ tailWord_134899).sum := by decide
  have hdescent : baseEnd_134899 < baseStart_134899 := by decide
  rcases family_descends (prefixWord ++ tailWord_134899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134929 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 3, 5]
def baseStart_134929 : Nat := 118140960795 + 134929 * 2 ^ 59
def prefixEnd_134929 : Nat := 4983230072969 + 3 ^ 40 * 134929 * 2
def baseEnd_134929 : Nat := 46188954153738548911319

theorem tailTrace_134929 : CollatzResearch.WordTrace tailWord_134929 prefixEnd_134929 46188954153738548911319 := by
  unfold tailWord_134929
  simp only [CollatzResearch.WordTrace]
  refine ⟨4921264928182751883679841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3280843285455167922453227 4921264928182751883679841)
  ·
    refine ⟨3690948696137063912759881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4921264928182751883679841 3690948696137063912759881)
    ·
      refine ⟨2768211522102797934569911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3690948696137063912759881 2768211522102797934569911)
      ·
        refine ⟨4152317283154196901854867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2768211522102797934569911 4152317283154196901854867)
        ·
          refine ⟨6228475924731295352782301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4152317283154196901854867 6228475924731295352782301)
          ·
            refine ⟨2335678471774235757293363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6228475924731295352782301 2335678471774235757293363)
            ·
              refine ⟨3503517707661353635940045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335678471774235757293363 3503517707661353635940045)
              ·
                refine ⟨1313819140373007613477517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3503517707661353635940045 1313819140373007613477517)
                ·
                  refine ⟨492682177639877855054069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1313819140373007613477517 492682177639877855054069)
                  ·
                    refine ⟨46188954153738548911319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 492682177639877855054069 46188954153738548911319)
                    ·
                      rfl

theorem cell22_134929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_134929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134929 prefixEnd_134929 := by exact prefixLift 134929
  have htrace : WordTrace (prefixWord ++ tailWord_134929) baseStart_134929 baseEnd_134929 := by
    simpa [prefixWord, tailWord_134929, baseEnd_134929] using wordTrace_append hprefix tailTrace_134929
  have hstable : (prefixWord ++ tailWord_134929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134929).length < 2 ^ (prefixWord ++ tailWord_134929).sum := by decide
  have hdescent : baseEnd_134929 < baseStart_134929 := by decide
  rcases family_descends (prefixWord ++ tailWord_134929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134931 : List Nat := [1, 1, 1, 2, 1, 3, 2, 7, 4]
def baseStart_134931 : Nat := 118140960795 + 134931 * 2 ^ 59
def prefixEnd_134931 : Nat := 4983230072969 + 3 ^ 40 * 134931 * 2
def baseEnd_134931 : Nat := 15396546264870403453771

theorem tailTrace_134931 : CollatzResearch.WordTrace tailWord_134931 prefixEnd_134931 15396546264870403453771 := by
  unfold tailWord_134931
  simp only [CollatzResearch.WordTrace]
  refine ⟨4921337874175506225252647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3280891916117004150168431 4921337874175506225252647)
  ·
    refine ⟨7382006811263259337878971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4921337874175506225252647 7382006811263259337878971)
    ·
      refine ⟨11073010216894889006818457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7382006811263259337878971 11073010216894889006818457)
      ·
        refine ⟨8304757662671166755113843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11073010216894889006818457 8304757662671166755113843)
        ·
          refine ⟨12457136494006750132670765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8304757662671166755113843 12457136494006750132670765)
          ·
            refine ⟨4671426185252531299751537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12457136494006750132670765 4671426185252531299751537)
            ·
              refine ⟨3503569638939398474813653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4671426185252531299751537 3503569638939398474813653)
              ·
                refine ⟨82114913412642151753445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3503569638939398474813653 82114913412642151753445)
                ·
                  refine ⟨15396546264870403453771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82114913412642151753445 15396546264870403453771)
                  ·
                    rfl

theorem cell22_134931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 4].length) (baseStart_134931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134931 prefixEnd_134931 := by exact prefixLift 134931
  have htrace : WordTrace (prefixWord ++ tailWord_134931) baseStart_134931 baseEnd_134931 := by
    simpa [prefixWord, tailWord_134931, baseEnd_134931] using wordTrace_append hprefix tailTrace_134931
  have hstable : (prefixWord ++ tailWord_134931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134931).length < 2 ^ (prefixWord ++ tailWord_134931).sum := by decide
  have hdescent : baseEnd_134931 < baseStart_134931 := by decide
  rcases family_descends (prefixWord ++ tailWord_134931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134948 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 6]
def baseStart_134948 : Nat := 118140960795 + 134948 * 2 ^ 59
def prefixEnd_134948 : Nat := 4983230072969 + 3 ^ 40 * 134948 * 2
def baseEnd_134948 : Nat := 15398486080676277562087

theorem tailTrace_134948 : CollatzResearch.WordTrace tailWord_134948 prefixEnd_134948 15398486080676277562087 := by
  unfold tailWord_134948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460978957556959064310749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3281305276742612085747665 2460978957556959064310749)
  ·
    refine ⟨922867109083859649116531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2460978957556959064310749 922867109083859649116531)
    ·
      refine ⟨1384300663625789473674797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 922867109083859649116531 1384300663625789473674797)
      ·
        refine ⟨519112748859671052628049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1384300663625789473674797 519112748859671052628049)
        ·
          refine ⟨389334561644753289471037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 519112748859671052628049 389334561644753289471037)
          ·
            refine ⟨146000460616782483551639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 389334561644753289471037 146000460616782483551639)
            ·
              refine ⟨219000690925173725327459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146000460616782483551639 219000690925173725327459)
              ·
                refine ⟨328501036387760587991189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219000690925173725327459 328501036387760587991189)
                ·
                  refine ⟨15398486080676277562087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 328501036387760587991189 15398486080676277562087)
                  ·
                    rfl

theorem cell22_134948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_134948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_134948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_134948 prefixEnd_134948 := by exact prefixLift 134948
  have htrace : WordTrace (prefixWord ++ tailWord_134948) baseStart_134948 baseEnd_134948 := by
    simpa [prefixWord, tailWord_134948, baseEnd_134948] using wordTrace_append hprefix tailTrace_134948
  have hstable : (prefixWord ++ tailWord_134948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134948).length < 2 ^ (prefixWord ++ tailWord_134948).sum := by decide
  have hdescent : baseEnd_134948 < baseStart_134948 := by decide
  rcases family_descends (prefixWord ++ tailWord_134948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135081 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 1, 5]
def baseStart_135081 : Nat := 118140960795 + 135081 * 2 ^ 59
def prefixEnd_135081 : Nat := 4983230072969 + 3 ^ 40 * 135081 * 2
def baseEnd_135081 : Nat := 46240986860060819110853

theorem tailTrace_135081 : CollatzResearch.WordTrace tailWord_135081 prefixEnd_135081 46240986860060819110853 := by
  unfold tailWord_135081
  simp only [CollatzResearch.WordTrace]
  refine ⟨4926808823632081843213097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3284539215754721228808731 4926808823632081843213097)
  ·
    refine ⟨3695106617724061382409823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4926808823632081843213097 3695106617724061382409823)
    ·
      refine ⟨5542659926586092073614735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3695106617724061382409823 5542659926586092073614735)
      ·
        refine ⟨8313989889879138110422103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5542659926586092073614735 8313989889879138110422103)
        ·
          refine ⟨12470984834818707165633155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8313989889879138110422103 12470984834818707165633155)
          ·
            refine ⟨18706477252228060748449733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12470984834818707165633155 18706477252228060748449733)
            ·
              refine ⟨3507464484792761390334325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18706477252228060748449733 3507464484792761390334325)
              ·
                refine ⟨328824795449321380343843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3507464484792761390334325 328824795449321380343843)
                ·
                  refine ⟨493237193173982070515765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328824795449321380343843 493237193173982070515765)
                  ·
                    refine ⟨46240986860060819110853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 493237193173982070515765 46240986860060819110853)
                    ·
                      rfl

theorem cell22_135081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_135081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135081 prefixEnd_135081 := by exact prefixLift 135081
  have htrace : WordTrace (prefixWord ++ tailWord_135081) baseStart_135081 baseEnd_135081 := by
    simpa [prefixWord, tailWord_135081, baseEnd_135081] using wordTrace_append hprefix tailTrace_135081
  have hstable : (prefixWord ++ tailWord_135081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135081).length < 2 ^ (prefixWord ++ tailWord_135081).sum := by decide
  have hdescent : baseEnd_135081 < baseStart_135081 := by decide
  rcases family_descends (prefixWord ++ tailWord_135081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135096 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 1, 6]
def baseStart_135096 : Nat := 118140960795 + 135096 * 2 ^ 59
def prefixEnd_135096 : Nat := 4983230072969 + 3 ^ 40 * 135096 * 2
def baseEnd_135096 : Nat := 46246121666605779985807

theorem tailTrace_135096 : CollatzResearch.WordTrace tailWord_135096 prefixEnd_135096 46246121666605779985807 := by
  unfold tailWord_135096
  simp only [CollatzResearch.WordTrace]
  refine ⟨2463677959288869702504571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3284903945718492936672761 2463677959288869702504571)
  ·
    refine ⟨3695516938933304553756857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2463677959288869702504571 3695516938933304553756857)
    ·
      refine ⟨2771637704199978415317643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3695516938933304553756857 2771637704199978415317643)
      ·
        refine ⟨4157456556299967622976465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2771637704199978415317643 4157456556299967622976465)
        ·
          refine ⟨3118092417224975717232349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4157456556299967622976465 3118092417224975717232349)
          ·
            refine ⟨1169284656459365893962131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3118092417224975717232349 1169284656459365893962131)
            ·
              refine ⟨1753926984689048840943197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169284656459365893962131 1753926984689048840943197)
              ·
                refine ⟨657722619258393315353699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1753926984689048840943197 657722619258393315353699)
                ·
                  refine ⟨986583928887589973030549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657722619258393315353699 986583928887589973030549)
                  ·
                    refine ⟨46246121666605779985807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 986583928887589973030549 46246121666605779985807)
                    ·
                      rfl

theorem cell22_135096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_135096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135096 prefixEnd_135096 := by exact prefixLift 135096
  have htrace : WordTrace (prefixWord ++ tailWord_135096) baseStart_135096 baseEnd_135096 := by
    simpa [prefixWord, tailWord_135096, baseEnd_135096] using wordTrace_append hprefix tailTrace_135096
  have hstable : (prefixWord ++ tailWord_135096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135096).length < 2 ^ (prefixWord ++ tailWord_135096).sum := by decide
  have hdescent : baseEnd_135096 < baseStart_135096 := by decide
  rcases family_descends (prefixWord ++ tailWord_135096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135171 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 3, 7]
def baseStart_135171 : Nat := 118140960795 + 135171 * 2 ^ 59
def prefixEnd_135171 : Nat := 4983230072969 + 3 ^ 40 * 135171 * 2
def baseEnd_135171 : Nat := 46271795699330584360577

theorem tailTrace_135171 : CollatzResearch.WordTrace tailWord_135171 prefixEnd_135171 46271795699330584360577 := by
  unfold tailWord_135171
  simp only [CollatzResearch.WordTrace]
  refine ⟨4930091393306027213989367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3286727595537351475992911 4930091393306027213989367)
  ·
    refine ⟨7395137089959040820984051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4930091393306027213989367 7395137089959040820984051)
    ·
      refine ⟨11092705634938561231476077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7395137089959040820984051 11092705634938561231476077)
      ·
        refine ⟨4159764613101960461803529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11092705634938561231476077 4159764613101960461803529)
        ·
          refine ⟨3119823459826470346352647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4159764613101960461803529 3119823459826470346352647)
          ·
            refine ⟨4679735189739705519528971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3119823459826470346352647 4679735189739705519528971)
            ·
              refine ⟨7019602784609558279293457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4679735189739705519528971 7019602784609558279293457)
              ·
                refine ⟨5264702088457168709470093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7019602784609558279293457 5264702088457168709470093)
                ·
                  refine ⟨1974263283171438266051285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5264702088457168709470093 1974263283171438266051285)
                  ·
                    refine ⟨46271795699330584360577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1974263283171438266051285 46271795699330584360577)
                    ·
                      rfl

theorem cell22_135171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_135171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135171 prefixEnd_135171 := by exact prefixLift 135171
  have htrace : WordTrace (prefixWord ++ tailWord_135171) baseStart_135171 baseEnd_135171 := by
    simpa [prefixWord, tailWord_135171, baseEnd_135171] using wordTrace_append hprefix tailTrace_135171
  have hstable : (prefixWord ++ tailWord_135171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135171).length < 2 ^ (prefixWord ++ tailWord_135171).sum := by decide
  have hdescent : baseEnd_135171 < baseStart_135171 := by decide
  rcases family_descends (prefixWord ++ tailWord_135171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135173 : List Nat := [1, 3, 1, 1, 2, 4, 1, 4, 5]
def baseStart_135173 : Nat := 118140960795 + 135173 * 2 ^ 59
def prefixEnd_135173 : Nat := 4983230072969 + 3 ^ 40 * 135173 * 2
def baseEnd_135173 : Nat := 15424160113401081936857

theorem tailTrace_135173 : CollatzResearch.WordTrace tailWord_135173 prefixEnd_135173 15424160113401081936857 := by
  unfold tailWord_135173
  simp only [CollatzResearch.WordTrace]
  refine ⟨4930164339298781555562173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3286776226199187703708115 4930164339298781555562173)
  ·
    refine ⟨1848811627237043083335815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4930164339298781555562173 1848811627237043083335815)
    ·
      refine ⟨2773217440855564625003723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848811627237043083335815 2773217440855564625003723)
      ·
        refine ⟨4159826161283346937505585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2773217440855564625003723 4159826161283346937505585)
        ·
          refine ⟨3119869620962510203129189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4159826161283346937505585 3119869620962510203129189)
          ·
            refine ⟨584975553930470663086723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3119869620962510203129189 584975553930470663086723)
            ·
              refine ⟨877463330895705994630085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584975553930470663086723 877463330895705994630085)
              ·
                refine ⟨164524374542944873993141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 877463330895705994630085 164524374542944873993141)
                ·
                  refine ⟨15424160113401081936857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 164524374542944873993141 15424160113401081936857)
                  ·
                    rfl

theorem cell22_135173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_135173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135173 prefixEnd_135173 := by exact prefixLift 135173
  have htrace : WordTrace (prefixWord ++ tailWord_135173) baseStart_135173 baseEnd_135173 := by
    simpa [prefixWord, tailWord_135173, baseEnd_135173] using wordTrace_append hprefix tailTrace_135173
  have hstable : (prefixWord ++ tailWord_135173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135173).length < 2 ^ (prefixWord ++ tailWord_135173).sum := by decide
  have hdescent : baseEnd_135173 < baseStart_135173 := by decide
  rcases family_descends (prefixWord ++ tailWord_135173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135203 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 3, 4]
def baseStart_135203 : Nat := 118140960795 + 135203 * 2 ^ 59
def prefixEnd_135203 : Nat := 4983230072969 + 3 ^ 40 * 135203 * 2
def baseEnd_135203 : Nat := 46282749953293167560479

theorem tailTrace_135203 : CollatzResearch.WordTrace tailWord_135203 prefixEnd_135203 46282749953293167560479 := by
  unfold tailWord_135203
  simp only [CollatzResearch.WordTrace]
  refine ⟨4931258529190096679154263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3287505686126731119436175 4931258529190096679154263)
  ·
    refine ⟨7396887793785145018731395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4931258529190096679154263 7396887793785145018731395)
    ·
      refine ⟨11095331690677717528097093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7396887793785145018731395 11095331690677717528097093)
      ·
        refine ⟨2080374692002072036518205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11095331690677717528097093 2080374692002072036518205)
        ·
          refine ⟨780140509500777013694327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2080374692002072036518205 780140509500777013694327)
          ·
            refine ⟨1170210764251165520541491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780140509500777013694327 1170210764251165520541491)
            ·
              refine ⟨1755316146376748280812237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170210764251165520541491 1755316146376748280812237)
              ·
                refine ⟨658243554891280605304589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1755316146376748280812237 658243554891280605304589)
                ·
                  refine ⟨246841333084230226989221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658243554891280605304589 246841333084230226989221)
                  ·
                    refine ⟨46282749953293167560479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 246841333084230226989221 46282749953293167560479)
                    ·
                      rfl

theorem cell22_135203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 4].length) (baseStart_135203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135203 prefixEnd_135203 := by exact prefixLift 135203
  have htrace : WordTrace (prefixWord ++ tailWord_135203) baseStart_135203 baseEnd_135203 := by
    simpa [prefixWord, tailWord_135203, baseEnd_135203] using wordTrace_append hprefix tailTrace_135203
  have hstable : (prefixWord ++ tailWord_135203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135203).length < 2 ^ (prefixWord ++ tailWord_135203).sum := by decide
  have hdescent : baseEnd_135203 < baseStart_135203 := by decide
  rcases family_descends (prefixWord ++ tailWord_135203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135254 : List Nat := [5, 2, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_135254 : Nat := 118140960795 + 135254 * 2 ^ 59
def prefixEnd_135254 : Nat := 4983230072969 + 3 ^ 40 * 135254 * 2
def baseEnd_135254 : Nat := 46300208295546034535323

theorem tailTrace_135254 : CollatzResearch.WordTrace tailWord_135254 prefixEnd_135254 46300208295546034535323 := by
  unfold tailWord_135254
  simp only [CollatzResearch.WordTrace]
  refine ⟨308319915750333274328801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3288745768003554926173877 308319915750333274328801)
  ·
    refine ⟨231239936812749955746601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 308319915750333274328801 231239936812749955746601)
    ·
      refine ⟨173429952609562466809951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231239936812749955746601 173429952609562466809951)
      ·
        refine ⟨260144928914343700214927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173429952609562466809951 260144928914343700214927)
        ·
          refine ⟨390217393371515550322391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260144928914343700214927 390217393371515550322391)
          ·
            refine ⟨585326090057273325483587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390217393371515550322391 585326090057273325483587)
            ·
              refine ⟨877989135085909988225381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585326090057273325483587 877989135085909988225381)
              ·
                refine ⟨164622962828608122792259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 877989135085909988225381 164622962828608122792259)
                ·
                  refine ⟨246934444242912184188389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164622962828608122792259 246934444242912184188389)
                  ·
                    refine ⟨46300208295546034535323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 246934444242912184188389 46300208295546034535323)
                    ·
                      rfl

theorem cell22_135254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_135254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135254 prefixEnd_135254 := by exact prefixLift 135254
  have htrace : WordTrace (prefixWord ++ tailWord_135254) baseStart_135254 baseEnd_135254 := by
    simpa [prefixWord, tailWord_135254, baseEnd_135254] using wordTrace_append hprefix tailTrace_135254
  have hstable : (prefixWord ++ tailWord_135254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135254).length < 2 ^ (prefixWord ++ tailWord_135254).sum := by decide
  have hdescent : baseEnd_135254 < baseStart_135254 := by decide
  rcases family_descends (prefixWord ++ tailWord_135254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135318 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_135318 : Nat := 118140960795 + 135318 * 2 ^ 59
def prefixEnd_135318 : Nat := 4983230072969 + 3 ^ 40 * 135318 * 2
def baseEnd_135318 : Nat := 46322116803471200935127

theorem tailTrace_135318 : CollatzResearch.WordTrace tailWord_135318 prefixEnd_135318 46322116803471200935127 := by
  unfold tailWord_135318
  simp only [CollatzResearch.WordTrace]
  refine ⟨308465807735841957474413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3290301949182314213060405 308465807735841957474413)
  ·
    refine ⟨115674677900940734052905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 308465807735841957474413 115674677900940734052905)
    ·
      refine ⟨86756008425705550539679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115674677900940734052905 86756008425705550539679)
      ·
        refine ⟨130134012638558325809519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86756008425705550539679 130134012638558325809519)
        ·
          refine ⟨195201018957837488714279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130134012638558325809519 195201018957837488714279)
          ·
            refine ⟨292801528436756233071419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195201018957837488714279 292801528436756233071419)
            ·
              refine ⟨439202292655134349607129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292801528436756233071419 439202292655134349607129)
              ·
                refine ⟨329401719491350762205347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439202292655134349607129 329401719491350762205347)
                ·
                  refine ⟨494102579237026143308021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329401719491350762205347 494102579237026143308021)
                  ·
                    refine ⟨46322116803471200935127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 494102579237026143308021 46322116803471200935127)
                    ·
                      rfl

theorem cell22_135318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_135318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135318 prefixEnd_135318 := by exact prefixLift 135318
  have htrace : WordTrace (prefixWord ++ tailWord_135318) baseStart_135318 baseEnd_135318 := by
    simpa [prefixWord, tailWord_135318, baseEnd_135318] using wordTrace_append hprefix tailTrace_135318
  have hstable : (prefixWord ++ tailWord_135318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135318).length < 2 ^ (prefixWord ++ tailWord_135318).sum := by decide
  have hdescent : baseEnd_135318 < baseStart_135318 := by decide
  rcases family_descends (prefixWord ++ tailWord_135318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135348 : List Nat := [2, 5, 3, 1, 2, 1, 1, 7]
def baseStart_135348 : Nat := 118140960795 + 135348 * 2 ^ 59
def prefixEnd_135348 : Nat := 4983230072969 + 3 ^ 40 * 135348 * 2
def baseEnd_135348 : Nat := 5148042935173458076115

theorem tailTrace_135348 : CollatzResearch.WordTrace tailWord_135348 prefixEnd_135348 5148042935173458076115 := by
  unfold tailWord_135348
  simp only [CollatzResearch.WordTrace]
  refine ⟨2468273556832393221591349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3291031409109857628788465 2468273556832393221591349)
  ·
    refine ⟨231400645953036864524189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2468273556832393221591349 231400645953036864524189)
    ·
      refine ⟨86775242232388824196571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231400645953036864524189 86775242232388824196571)
      ·
        refine ⟨130162863348583236294857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86775242232388824196571 130162863348583236294857)
        ·
          refine ⟨97622147511437427221143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130162863348583236294857 97622147511437427221143)
          ·
            refine ⟨146433221267156140831715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97622147511437427221143 146433221267156140831715)
            ·
              refine ⟨219649831900734211247573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146433221267156140831715 219649831900734211247573)
              ·
                refine ⟨5148042935173458076115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 219649831900734211247573 5148042935173458076115)
                ·
                  rfl

theorem cell22_135348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 7].length) (baseStart_135348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135348 prefixEnd_135348 := by exact prefixLift 135348
  have htrace : WordTrace (prefixWord ++ tailWord_135348) baseStart_135348 baseEnd_135348 := by
    simpa [prefixWord, tailWord_135348, baseEnd_135348] using wordTrace_append hprefix tailTrace_135348
  have hstable : (prefixWord ++ tailWord_135348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135348).length < 2 ^ (prefixWord ++ tailWord_135348).sum := by decide
  have hdescent : baseEnd_135348 < baseStart_135348 := by decide
  rcases family_descends (prefixWord ++ tailWord_135348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135370 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 6]
def baseStart_135370 : Nat := 118140960795 + 135370 * 2 ^ 59
def prefixEnd_135370 : Nat := 4983230072969 + 3 ^ 40 * 135370 * 2
def baseEnd_135370 : Nat := 15446639155386799544989

theorem tailTrace_135370 : CollatzResearch.WordTrace tailWord_135370 prefixEnd_135370 15446639155386799544989 := by
  unfold tailWord_135370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234337379896271050120891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3291566346390056133655709 1234337379896271050120891)
  ·
    refine ⟨1851506069844406575181337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1234337379896271050120891 1851506069844406575181337)
    ·
      refine ⟨1388629552383304931386003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1851506069844406575181337 1388629552383304931386003)
      ·
        refine ⟨2082944328574957397079005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1388629552383304931386003 2082944328574957397079005)
        ·
          refine ⟨781104123215609023904627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2082944328574957397079005 781104123215609023904627)
          ·
            refine ⟨1171656184823413535856941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781104123215609023904627 1171656184823413535856941)
            ·
              refine ⟨439371069308780075946353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1171656184823413535856941 439371069308780075946353)
              ·
                refine ⟨329528301981585056959765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439371069308780075946353 329528301981585056959765)
                ·
                  refine ⟨15446639155386799544989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 329528301981585056959765 15446639155386799544989)
                  ·
                    rfl

theorem cell22_135370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_135370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135370 prefixEnd_135370 := by exact prefixLift 135370
  have htrace : WordTrace (prefixWord ++ tailWord_135370) baseStart_135370 baseEnd_135370 := by
    simpa [prefixWord, tailWord_135370, baseEnd_135370] using wordTrace_append hprefix tailTrace_135370
  have hstable : (prefixWord ++ tailWord_135370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135370).length < 2 ^ (prefixWord ++ tailWord_135370).sum := by decide
  have hdescent : baseEnd_135370 < baseStart_135370 := by decide
  rcases family_descends (prefixWord ++ tailWord_135370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135385 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 1, 5]
def baseStart_135385 : Nat := 118140960795 + 135385 * 2 ^ 59
def prefixEnd_135385 : Nat := 4983230072969 + 3 ^ 40 * 135385 * 2
def baseEnd_135385 : Nat := 46345052272705359509921

theorem tailTrace_135385 : CollatzResearch.WordTrace tailWord_135385 prefixEnd_135385 46345052272705359509921 := by
  unfold tailWord_135385
  simp only [CollatzResearch.WordTrace]
  refine ⟨4937896614530741762279609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3291931076353827841519739 4937896614530741762279609)
  ·
    refine ⟨3703422460898056321709707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4937896614530741762279609 3703422460898056321709707)
    ·
      refine ⟨5555133691347084482564561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3703422460898056321709707 5555133691347084482564561)
      ·
        refine ⟨4166350268510313361923421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5555133691347084482564561 4166350268510313361923421)
        ·
          refine ⟨1562381350691367510721283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4166350268510313361923421 1562381350691367510721283)
          ·
            refine ⟨2343572026037051266081925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562381350691367510721283 2343572026037051266081925)
            ·
              refine ⟨439419754881947112390361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2343572026037051266081925 439419754881947112390361)
              ·
                refine ⟨329564816161460334292771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439419754881947112390361 329564816161460334292771)
                ·
                  refine ⟨494347224242190501439157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329564816161460334292771 494347224242190501439157)
                  ·
                    refine ⟨46345052272705359509921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 494347224242190501439157 46345052272705359509921)
                    ·
                      rfl

theorem cell22_135385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_135385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135385 prefixEnd_135385 := by exact prefixLift 135385
  have htrace : WordTrace (prefixWord ++ tailWord_135385) baseStart_135385 baseEnd_135385 := by
    simpa [prefixWord, tailWord_135385, baseEnd_135385] using wordTrace_append hprefix tailTrace_135385
  have hstable : (prefixWord ++ tailWord_135385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135385).length < 2 ^ (prefixWord ++ tailWord_135385).sum := by decide
  have hdescent : baseEnd_135385 < baseStart_135385 := by decide
  rcases family_descends (prefixWord ++ tailWord_135385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135389 : List Nat := [1, 4, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_135389 : Nat := 118140960795 + 135389 * 2 ^ 59
def prefixEnd_135389 : Nat := 4983230072969 + 3 ^ 40 * 135389 * 2
def baseEnd_135389 : Nat := 46346421554450682409909

theorem tailTrace_135389 : CollatzResearch.WordTrace tailWord_135389 prefixEnd_135389 46346421554450682409909 := by
  unfold tailWord_135389
  simp only [CollatzResearch.WordTrace]
  refine ⟨4938042506516250445425221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3292028337677500296950147 4938042506516250445425221)
  ·
    refine ⟨925882969971796958517229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4938042506516250445425221 925882969971796958517229)
    ·
      refine ⟨347206113739423859443961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 925882969971796958517229 347206113739423859443961)
      ·
        refine ⟨260404585304567894582971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347206113739423859443961 260404585304567894582971)
        ·
          refine ⟨390606877956851841874457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260404585304567894582971 390606877956851841874457)
          ·
            refine ⟨292955158467638881405843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390606877956851841874457 292955158467638881405843)
            ·
              refine ⟨439432737701458322108765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292955158467638881405843 439432737701458322108765)
              ·
                refine ⟨164787276638046870790787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 439432737701458322108765 164787276638046870790787)
                ·
                  refine ⟨247180914957070306186181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164787276638046870790787 247180914957070306186181)
                  ·
                    refine ⟨46346421554450682409909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 247180914957070306186181 46346421554450682409909)
                    ·
                      rfl

theorem cell22_135389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_135389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135389 prefixEnd_135389 := by exact prefixLift 135389
  have htrace : WordTrace (prefixWord ++ tailWord_135389) baseStart_135389 baseEnd_135389 := by
    simpa [prefixWord, tailWord_135389, baseEnd_135389] using wordTrace_append hprefix tailTrace_135389
  have hstable : (prefixWord ++ tailWord_135389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135389).length < 2 ^ (prefixWord ++ tailWord_135389).sum := by decide
  have hdescent : baseEnd_135389 < baseStart_135389 := by decide
  rcases family_descends (prefixWord ++ tailWord_135389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135402 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 4, 3]
def baseStart_135402 : Nat := 118140960795 + 135402 * 2 ^ 59
def prefixEnd_135402 : Nat := 4983230072969 + 3 ^ 40 * 135402 * 2
def baseEnd_135402 : Nat := 46350871720122981834869

theorem tailTrace_135402 : CollatzResearch.WordTrace tailWord_135402 prefixEnd_135402 46350871720122981834869 := by
  unfold tailWord_135402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234629163867288416412115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3292344436979435777098973 1234629163867288416412115)
  ·
    refine ⟨1851943745800932624618173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1234629163867288416412115 1851943745800932624618173)
    ·
      refine ⟨694478904675349734231815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1851943745800932624618173 694478904675349734231815)
      ·
        refine ⟨1041718357013024601347723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694478904675349734231815 1041718357013024601347723)
        ·
          refine ⟨1562577535519536902021585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041718357013024601347723 1562577535519536902021585)
          ·
            refine ⟨1171933151639652676516189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1562577535519536902021585 1171933151639652676516189)
            ·
              refine ⟨439474931864869753693571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1171933151639652676516189 439474931864869753693571)
              ·
                refine ⟨659212397797304630540357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439474931864869753693571 659212397797304630540357)
                ·
                  refine ⟨123602324586994618226317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 659212397797304630540357 123602324586994618226317)
                  ·
                    refine ⟨46350871720122981834869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 123602324586994618226317 46350871720122981834869)
                    ·
                      rfl

theorem cell22_135402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_135402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135402 prefixEnd_135402 := by exact prefixLift 135402
  have htrace : WordTrace (prefixWord ++ tailWord_135402) baseStart_135402 baseEnd_135402 := by
    simpa [prefixWord, tailWord_135402, baseEnd_135402] using wordTrace_append hprefix tailTrace_135402
  have hstable : (prefixWord ++ tailWord_135402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135402).length < 2 ^ (prefixWord ++ tailWord_135402).sum := by decide
  have hdescent : baseEnd_135402 < baseStart_135402 := by decide
  rcases family_descends (prefixWord ++ tailWord_135402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135432 : List Nat := [2, 1, 3, 2, 3, 1, 4, 6]
def baseStart_135432 : Nat := 118140960795 + 135432 * 2 ^ 59
def prefixEnd_135432 : Nat := 4983230072969 + 3 ^ 40 * 135432 * 2
def baseEnd_135432 : Nat := 5151237925912544842753

theorem tailTrace_135432 : CollatzResearch.WordTrace tailWord_135432 prefixEnd_135432 5151237925912544842753 := by
  unfold tailWord_135432
  simp only [CollatzResearch.WordTrace]
  refine ⟨2469805422680234394620275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3293073896906979192827033 2469805422680234394620275)
  ·
    refine ⟨3704708134020351591930413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2469805422680234394620275 3704708134020351591930413)
    ·
      refine ⟨1389265550257631846973905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3704708134020351591930413 1389265550257631846973905)
      ·
        refine ⟨1041949162693223885230429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1389265550257631846973905 1041949162693223885230429)
        ·
          refine ⟨390730936009958956961411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1041949162693223885230429 390730936009958956961411)
          ·
            refine ⟨586096404014938435442117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390730936009958956961411 586096404014938435442117)
            ·
              refine ⟨109893075752800956645397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 586096404014938435442117 109893075752800956645397)
              ·
                refine ⟨5151237925912544842753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109893075752800956645397 5151237925912544842753)
                ·
                  rfl

theorem cell22_135432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 6].length) (baseStart_135432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135432 prefixEnd_135432 := by exact prefixLift 135432
  have htrace : WordTrace (prefixWord ++ tailWord_135432) baseStart_135432 baseEnd_135432 := by
    simpa [prefixWord, tailWord_135432, baseEnd_135432] using wordTrace_append hprefix tailTrace_135432
  have hstable : (prefixWord ++ tailWord_135432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135432).length < 2 ^ (prefixWord ++ tailWord_135432).sum := by decide
  have hdescent : baseEnd_135432 < baseStart_135432 := by decide
  rcases family_descends (prefixWord ++ tailWord_135432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135470 : List Nat := [4, 1, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_135470 : Nat := 118140960795 + 135470 * 2 ^ 59
def prefixEnd_135470 : Nat := 4983230072969 + 3 ^ 40 * 135470 * 2
def baseEnd_135470 : Nat := 46374149509793471134661

theorem tailTrace_135470 : CollatzResearch.WordTrace tailWord_135470 prefixEnd_135470 46374149509793471134661 := by
  unfold tailWord_135470
  simp only [CollatzResearch.WordTrace]
  refine ⟨617624602402850159890483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3293997879481867519415909 617624602402850159890483)
  ·
    refine ⟨926436903604275239835725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 617624602402850159890483 926436903604275239835725)
    ·
      refine ⟨347413838851603214938397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 926436903604275239835725 347413838851603214938397)
      ·
        refine ⟨130280189569351205601899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347413838851603214938397 130280189569351205601899)
        ·
          refine ⟨195420284354026808402849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130280189569351205601899 195420284354026808402849)
          ·
            refine ⟨146565213265520106302137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195420284354026808402849 146565213265520106302137)
            ·
              refine ⟨109923909949140079726603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146565213265520106302137 109923909949140079726603)
              ·
                refine ⟨164885864923710119589905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109923909949140079726603 164885864923710119589905)
                ·
                  refine ⟨123664398692782589692429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164885864923710119589905 123664398692782589692429)
                  ·
                    refine ⟨46374149509793471134661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 123664398692782589692429 46374149509793471134661)
                    ·
                      rfl

theorem cell22_135470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_135470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135470 prefixEnd_135470 := by exact prefixLift 135470
  have htrace : WordTrace (prefixWord ++ tailWord_135470) baseStart_135470 baseEnd_135470 := by
    simpa [prefixWord, tailWord_135470, baseEnd_135470] using wordTrace_append hprefix tailTrace_135470
  have hstable : (prefixWord ++ tailWord_135470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135470).length < 2 ^ (prefixWord ++ tailWord_135470).sum := by decide
  have hdescent : baseEnd_135470 < baseStart_135470 := by decide
  rcases family_descends (prefixWord ++ tailWord_135470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135475 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 1, 7]
def baseStart_135475 : Nat := 118140960795 + 135475 * 2 ^ 59
def prefixEnd_135475 : Nat := 4983230072969 + 3 ^ 40 * 135475 * 2
def baseEnd_135475 : Nat := 46375861111975124759645

theorem tailTrace_135475 : CollatzResearch.WordTrace tailWord_135475 prefixEnd_135475 46375861111975124759645 := by
  unfold tailWord_135475
  simp only [CollatzResearch.WordTrace]
  refine ⟨4941179184204687133055879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3294119456136458088703919 4941179184204687133055879)
  ·
    refine ⟨7411768776307030699583819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4941179184204687133055879 7411768776307030699583819)
    ·
      refine ⟨11117653164460546049375729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7411768776307030699583819 11117653164460546049375729)
      ·
        refine ⟨8338239873345409537031797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11117653164460546049375729 8338239873345409537031797)
        ·
          refine ⟨781709988126132144096731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8338239873345409537031797 781709988126132144096731)
          ·
            refine ⟨1172564982189198216145097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781709988126132144096731 1172564982189198216145097)
            ·
              refine ⟨879423736641898662108823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172564982189198216145097 879423736641898662108823)
              ·
                refine ⟨1319135604962847993163235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879423736641898662108823 1319135604962847993163235)
                ·
                  refine ⟨1978703407444271989744853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319135604962847993163235 1978703407444271989744853)
                  ·
                    refine ⟨46375861111975124759645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1978703407444271989744853 46375861111975124759645)
                    ·
                      rfl

theorem cell22_135475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_135475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135475 prefixEnd_135475 := by exact prefixLift 135475
  have htrace : WordTrace (prefixWord ++ tailWord_135475) baseStart_135475 baseEnd_135475 := by
    simpa [prefixWord, tailWord_135475, baseEnd_135475] using wordTrace_append hprefix tailTrace_135475
  have hstable : (prefixWord ++ tailWord_135475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135475).length < 2 ^ (prefixWord ++ tailWord_135475).sum := by decide
  have hdescent : baseEnd_135475 < baseStart_135475 := by decide
  rcases family_descends (prefixWord ++ tailWord_135475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135477 : List Nat := [1, 3, 3, 1, 2, 1, 3, 3, 5]
def baseStart_135477 : Nat := 118140960795 + 135477 * 2 ^ 59
def prefixEnd_135477 : Nat := 4983230072969 + 3 ^ 40 * 135477 * 2
def baseEnd_135477 : Nat := 15458848584282595403213

theorem tailTrace_135477 : CollatzResearch.WordTrace tailWord_135477 prefixEnd_135477 15458848584282595403213 := by
  unfold tailWord_135477
  simp only [CollatzResearch.WordTrace]
  refine ⟨4941252130197441474628685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3294168086798294316419123 4941252130197441474628685)
  ·
    refine ⟨1852969548824040552985757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4941252130197441474628685 1852969548824040552985757)
    ·
      refine ⟨694863580809015207369659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1852969548824040552985757 694863580809015207369659)
      ·
        refine ⟨1042295371213522811054489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694863580809015207369659 1042295371213522811054489)
        ·
          refine ⟨781721528410142108290867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042295371213522811054489 781721528410142108290867)
          ·
            refine ⟨1172582292615213162436301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781721528410142108290867 1172582292615213162436301)
            ·
              refine ⟨439718359730704935913613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1172582292615213162436301 439718359730704935913613)
              ·
                refine ⟨164894384899014350967605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 439718359730704935913613 164894384899014350967605)
                ·
                  refine ⟨15458848584282595403213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 164894384899014350967605 15458848584282595403213)
                  ·
                    rfl

theorem cell22_135477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_135477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135477 prefixEnd_135477 := by exact prefixLift 135477
  have htrace : WordTrace (prefixWord ++ tailWord_135477) baseStart_135477 baseEnd_135477 := by
    simpa [prefixWord, tailWord_135477, baseEnd_135477] using wordTrace_append hprefix tailTrace_135477
  have hstable : (prefixWord ++ tailWord_135477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135477).length < 2 ^ (prefixWord ++ tailWord_135477).sum := by decide
  have hdescent : baseEnd_135477 < baseStart_135477 := by decide
  rcases family_descends (prefixWord ++ tailWord_135477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135537 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 6, 3]
def baseStart_135537 : Nat := 118140960795 + 135537 * 2 ^ 59
def prefixEnd_135537 : Nat := 4983230072969 + 3 ^ 40 * 135537 * 2
def baseEnd_135537 : Nat := 46397084979027629709455

theorem tailTrace_135537 : CollatzResearch.WordTrace tailWord_135537 prefixEnd_135537 46397084979027629709455 := by
  unfold tailWord_135537
  simp only [CollatzResearch.WordTrace]
  refine ⟨4943440509980071721812865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3295627006653381147875243 4943440509980071721812865)
  ·
    refine ⟨3707580382485053791359649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4943440509980071721812865 3707580382485053791359649)
    ·
      refine ⟨2780685286863790343519737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3707580382485053791359649 2780685286863790343519737)
      ·
        refine ⟨2085513965147842757639803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2780685286863790343519737 2085513965147842757639803)
        ·
          refine ⟨3128270947721764136459705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2085513965147842757639803 3128270947721764136459705)
          ·
            refine ⟨2346203210791323102344779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3128270947721764136459705 2346203210791323102344779)
            ·
              refine ⟨3519304816186984653517169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346203210791323102344779 3519304816186984653517169)
              ·
                refine ⟨2639478612140238490137877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3519304816186984653517169 2639478612140238490137877)
                ·
                  refine ⟨123725559944073679225213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2639478612140238490137877 123725559944073679225213)
                  ·
                    refine ⟨46397084979027629709455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 123725559944073679225213 46397084979027629709455)
                    ·
                      rfl

theorem cell22_135537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_135537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135537 prefixEnd_135537 := by exact prefixLift 135537
  have htrace : WordTrace (prefixWord ++ tailWord_135537) baseStart_135537 baseEnd_135537 := by
    simpa [prefixWord, tailWord_135537, baseEnd_135537] using wordTrace_append hprefix tailTrace_135537
  have hstable : (prefixWord ++ tailWord_135537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135537).length < 2 ^ (prefixWord ++ tailWord_135537).sum := by decide
  have hdescent : baseEnd_135537 < baseStart_135537 := by decide
  rcases family_descends (prefixWord ++ tailWord_135537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135691 : List Nat := [1, 1, 1, 1, 7, 2, 1, 4, 4]
def baseStart_135691 : Nat := 118140960795 + 135691 * 2 ^ 59
def prefixEnd_135691 : Nat := 4983230072969 + 3 ^ 40 * 135691 * 2
def baseEnd_135691 : Nat := 15483267442074187119661

theorem tailTrace_135691 : CollatzResearch.WordTrace tailWord_135691 prefixEnd_135691 15483267442074187119661 := by
  unfold tailWord_135691
  simp only [CollatzResearch.WordTrace]
  refine ⟨4949057351422156022918927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3299371567614770681945951 4949057351422156022918927)
  ·
    refine ⟨7423586027133234034378391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4949057351422156022918927 7423586027133234034378391)
    ·
      refine ⟨11135379040699851051567587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7423586027133234034378391 11135379040699851051567587)
      ·
        refine ⟨16703068561049776577351381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11135379040699851051567587 16703068561049776577351381)
        ·
          refine ⟨391478169399604138531673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16703068561049776577351381 391478169399604138531673)
          ·
            refine ⟨293608627049703103898755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391478169399604138531673 293608627049703103898755)
            ·
              refine ⟨440412940574554655848133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293608627049703103898755 440412940574554655848133)
              ·
                refine ⟨82577426357728997971525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 440412940574554655848133 82577426357728997971525)
                ·
                  refine ⟨15483267442074187119661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82577426357728997971525 15483267442074187119661)
                  ·
                    rfl

theorem cell22_135691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 4].length) (baseStart_135691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135691 prefixEnd_135691 := by exact prefixLift 135691
  have htrace : WordTrace (prefixWord ++ tailWord_135691) baseStart_135691 baseEnd_135691 := by
    simpa [prefixWord, tailWord_135691, baseEnd_135691] using wordTrace_append hprefix tailTrace_135691
  have hstable : (prefixWord ++ tailWord_135691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135691).length < 2 ^ (prefixWord ++ tailWord_135691).sum := by decide
  have hdescent : baseEnd_135691 < baseStart_135691 := by decide
  rcases family_descends (prefixWord ++ tailWord_135691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135693 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_135693 : Nat := 118140960795 + 135693 * 2 ^ 59
def prefixEnd_135693 : Nat := 4983230072969 + 3 ^ 40 * 135693 * 2
def baseEnd_135693 : Nat := 46450486967095222808977

theorem tailTrace_135693 : CollatzResearch.WordTrace tailWord_135693 prefixEnd_135693 46450486967095222808977 := by
  unfold tailWord_135693
  simp only [CollatzResearch.WordTrace]
  refine ⟨4949130297414910364491733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3299420198276606909661155 4949130297414910364491733)
  ·
    refine ⟨115995241345661961667775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 4949130297414910364491733 115995241345661961667775)
    ·
      refine ⟨173992862018492942501663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115995241345661961667775 173992862018492942501663)
      ·
        refine ⟨260989293027739413752495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173992862018492942501663 260989293027739413752495)
        ·
          refine ⟨391483939541609120628743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260989293027739413752495 391483939541609120628743)
          ·
            refine ⟨587225909312413680943115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391483939541609120628743 587225909312413680943115)
            ·
              refine ⟨880838863968620521414673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587225909312413680943115 880838863968620521414673)
              ·
                refine ⟨660629147976465391061005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 880838863968620521414673 660629147976465391061005)
                ·
                  refine ⟨247735930491174521647877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660629147976465391061005 247735930491174521647877)
                  ·
                    refine ⟨46450486967095222808977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 247735930491174521647877 46450486967095222808977)
                    ·
                      rfl

theorem cell22_135693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_135693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135693 prefixEnd_135693 := by exact prefixLift 135693
  have htrace : WordTrace (prefixWord ++ tailWord_135693) baseStart_135693 baseEnd_135693 := by
    simpa [prefixWord, tailWord_135693, baseEnd_135693] using wordTrace_append hprefix tailTrace_135693
  have hstable : (prefixWord ++ tailWord_135693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135693).length < 2 ^ (prefixWord ++ tailWord_135693).sum := by decide
  have hdescent : baseEnd_135693 < baseStart_135693 := by decide
  rcases family_descends (prefixWord ++ tailWord_135693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135706 : List Nat := [3, 1, 1, 3, 1, 1, 4, 3, 2, 3]
def baseStart_135706 : Nat := 118140960795 + 135706 * 2 ^ 59
def prefixEnd_135706 : Nat := 4983230072969 + 3 ^ 40 * 135706 * 2
def baseEnd_135706 : Nat := 46454937132767522233937

theorem tailTrace_135706 : CollatzResearch.WordTrace tailWord_135706 prefixEnd_135706 46454937132767522233937 := by
  unfold tailWord_135706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1237401111591953396178743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3299736297578542389809981 1237401111591953396178743)
  ·
    refine ⟨1856101667387930094268115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1237401111591953396178743 1856101667387930094268115)
    ·
      refine ⟨2784152501081895141402173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1856101667387930094268115 2784152501081895141402173)
      ·
        refine ⟨1044057187905710678025815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2784152501081895141402173 1044057187905710678025815)
        ·
          refine ⟨1566085781858566017038723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044057187905710678025815 1566085781858566017038723)
          ·
            refine ⟨2349128672787849025558085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566085781858566017038723 2349128672787849025558085)
            ·
              refine ⟨440461626147721692292141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2349128672787849025558085 440461626147721692292141)
              ·
                refine ⟨165173109805395634609553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 440461626147721692292141 165173109805395634609553)
                ·
                  refine ⟨123879832354046725957165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165173109805395634609553 123879832354046725957165)
                  ·
                    refine ⟨46454937132767522233937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 123879832354046725957165 46454937132767522233937)
                    ·
                      rfl

theorem cell22_135706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_135706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135706 prefixEnd_135706 := by exact prefixLift 135706
  have htrace : WordTrace (prefixWord ++ tailWord_135706) baseStart_135706 baseEnd_135706 := by
    simpa [prefixWord, tailWord_135706, baseEnd_135706] using wordTrace_append hprefix tailTrace_135706
  have hstable : (prefixWord ++ tailWord_135706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135706).length < 2 ^ (prefixWord ++ tailWord_135706).sum := by decide
  have hdescent : baseEnd_135706 < baseStart_135706 := by decide
  rcases family_descends (prefixWord ++ tailWord_135706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135751 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 3, 3]
def baseStart_135751 : Nat := 118140960795 + 135751 * 2 ^ 59
def prefixEnd_135751 : Nat := 4983230072969 + 3 ^ 40 * 135751 * 2
def baseEnd_135751 : Nat := 46470341552402404858799

theorem tailTrace_135751 : CollatzResearch.WordTrace tailWord_135751 prefixEnd_135751 46470341552402404858799 := by
  unfold tailWord_135751
  simp only [CollatzResearch.WordTrace]
  refine ⟨4951245731204786270103107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3300830487469857513402071 4951245731204786270103107)
  ·
    refine ⟨7426868596807179405154661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4951245731204786270103107 7426868596807179405154661)
    ·
      refine ⟨1392537861901346138466499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7426868596807179405154661 1392537861901346138466499)
      ·
        refine ⟨2088806792852019207699749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392537861901346138466499 2088806792852019207699749)
        ·
          refine ⟨391651273659753601443703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2088806792852019207699749 391651273659753601443703)
          ·
            refine ⟨587476910489630402165555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391651273659753601443703 587476910489630402165555)
            ·
              refine ⟨881215365734445603248333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587476910489630402165555 881215365734445603248333)
              ·
                refine ⟨330455762150417101218125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 881215365734445603248333 330455762150417101218125)
                ·
                  refine ⟨123920910806406412956797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330455762150417101218125 123920910806406412956797)
                  ·
                    refine ⟨46470341552402404858799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 123920910806406412956797 46470341552402404858799)
                    ·
                      rfl

theorem cell22_135751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_135751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135751 prefixEnd_135751 := by exact prefixLift 135751
  have htrace : WordTrace (prefixWord ++ tailWord_135751) baseStart_135751 baseEnd_135751 := by
    simpa [prefixWord, tailWord_135751, baseEnd_135751] using wordTrace_append hprefix tailTrace_135751
  have hstable : (prefixWord ++ tailWord_135751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135751).length < 2 ^ (prefixWord ++ tailWord_135751).sum := by decide
  have hdescent : baseEnd_135751 < baseStart_135751 := by decide
  rcases family_descends (prefixWord ++ tailWord_135751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135828 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_135828 : Nat := 118140960795 + 135828 * 2 ^ 59
def prefixEnd_135828 : Nat := 4983230072969 + 3 ^ 40 * 135828 * 2
def baseEnd_135828 : Nat := 46496700225999870683563

theorem tailTrace_135828 : CollatzResearch.WordTrace tailWord_135828 prefixEnd_135828 46496700225999870683563 := by
  unfold tailWord_135828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2477027075962914210328069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3302702767950552280437425 2477027075962914210328069)
  ·
    refine ⟨464442576743046414436513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2477027075962914210328069 464442576743046414436513)
    ·
      refine ⟨348331932557284810827385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 464442576743046414436513 348331932557284810827385)
      ·
        refine ⟨261248949417963608120539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348331932557284810827385 261248949417963608120539)
        ·
          refine ⟨391873424126945412180809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261248949417963608120539 391873424126945412180809)
          ·
            refine ⟨293905068095209059135607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391873424126945412180809 293905068095209059135607)
            ·
              refine ⟨440857602142813588703411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293905068095209059135607 440857602142813588703411)
              ·
                refine ⟨661286403214220383055117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440857602142813588703411 661286403214220383055117)
                ·
                  refine ⟨247982401205332643645669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661286403214220383055117 247982401205332643645669)
                  ·
                    refine ⟨46496700225999870683563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 247982401205332643645669 46496700225999870683563)
                    ·
                      rfl

theorem cell22_135828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_135828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135828 prefixEnd_135828 := by exact prefixLift 135828
  have htrace : WordTrace (prefixWord ++ tailWord_135828) baseStart_135828 baseEnd_135828 := by
    simpa [prefixWord, tailWord_135828, baseEnd_135828] using wordTrace_append hprefix tailTrace_135828
  have hstable : (prefixWord ++ tailWord_135828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135828).length < 2 ^ (prefixWord ++ tailWord_135828).sum := by decide
  have hdescent : baseEnd_135828 < baseStart_135828 := by decide
  rcases family_descends (prefixWord ++ tailWord_135828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135871 : List Nat := [1, 1, 2, 2, 2, 6, 1, 7]
def baseStart_135871 : Nat := 118140960795 + 135871 * 2 ^ 59
def prefixEnd_135871 : Nat := 4983230072969 + 3 ^ 40 * 135871 * 2
def baseEnd_135871 : Nat := 5167935556084676873159

theorem tailTrace_135871 : CollatzResearch.WordTrace tailWord_135871 prefixEnd_135871 5167935556084676873159 := by
  unfold tailWord_135871
  simp only [CollatzResearch.WordTrace]
  refine ⟨4955622490770046764471467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3303748327180031176314311 4955622490770046764471467)
  ·
    refine ⟨7433433736155070146707201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4955622490770046764471467 7433433736155070146707201)
    ·
      refine ⟨5575075302116302610030401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7433433736155070146707201 5575075302116302610030401)
      ·
        refine ⟨4181306476587226957522801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5575075302116302610030401 4181306476587226957522801)
        ·
          refine ⟨3135979857440420218142101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4181306476587226957522801 3135979857440420218142101)
          ·
            refine ⟨146999055817519697725411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3135979857440420218142101 146999055817519697725411)
            ·
              refine ⟨220498583726279546588117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146999055817519697725411 220498583726279546588117)
              ·
                refine ⟨5167935556084676873159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 220498583726279546588117 5167935556084676873159)
                ·
                  rfl

theorem cell22_135871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 7].length) (baseStart_135871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135871 prefixEnd_135871 := by exact prefixLift 135871
  have htrace : WordTrace (prefixWord ++ tailWord_135871) baseStart_135871 baseEnd_135871 := by
    simpa [prefixWord, tailWord_135871, baseEnd_135871] using wordTrace_append hprefix tailTrace_135871
  have hstable : (prefixWord ++ tailWord_135871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135871).length < 2 ^ (prefixWord ++ tailWord_135871).sum := by decide
  have hdescent : baseEnd_135871 < baseStart_135871 := by decide
  rcases family_descends (prefixWord ++ tailWord_135871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135890 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_135890 : Nat := 118140960795 + 135890 * 2 ^ 59
def prefixEnd_135890 : Nat := 4983230072969 + 3 ^ 40 * 135890 * 2
def baseEnd_135890 : Nat := 46517924093052375633373

theorem tailTrace_135890 : CollatzResearch.WordTrace tailWord_135890 prefixEnd_135890 46517924093052375633373 := by
  unfold tailWord_135890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1239078869425303252353281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3304210318467475339608749 1239078869425303252353281)
  ·
    refine ⟨929309152068977439264961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1239078869425303252353281 929309152068977439264961)
    ·
      refine ⟨696981864051733079448721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 929309152068977439264961 696981864051733079448721)
      ·
        refine ⟨522736398038799809586541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 696981864051733079448721 522736398038799809586541)
        ·
          refine ⟨196026149264549928594953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 522736398038799809586541 196026149264549928594953)
          ·
            refine ⟨147019611948412446446215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196026149264549928594953 147019611948412446446215)
            ·
              refine ⟨220529417922618669669323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147019611948412446446215 220529417922618669669323)
              ·
                refine ⟨330794126883928004503985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220529417922618669669323 330794126883928004503985)
                ·
                  refine ⟨248095595162946003377989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330794126883928004503985 248095595162946003377989)
                  ·
                    refine ⟨46517924093052375633373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 248095595162946003377989 46517924093052375633373)
                    ·
                      rfl

theorem cell22_135890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_135890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135890 prefixEnd_135890 := by exact prefixLift 135890
  have htrace : WordTrace (prefixWord ++ tailWord_135890) baseStart_135890 baseEnd_135890 := by
    simpa [prefixWord, tailWord_135890, baseEnd_135890] using wordTrace_append hprefix tailTrace_135890
  have hstable : (prefixWord ++ tailWord_135890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135890).length < 2 ^ (prefixWord ++ tailWord_135890).sum := by decide
  have hdescent : baseEnd_135890 < baseStart_135890 := by decide
  rcases family_descends (prefixWord ++ tailWord_135890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135933 : List Nat := [1, 4, 1, 1, 1, 1, 7, 1, 5]
def baseStart_135933 : Nat := 118140960795 + 135933 * 2 ^ 59
def prefixEnd_135933 : Nat := 4983230072969 + 3 ^ 40 * 135933 * 2
def baseEnd_135933 : Nat := 15510881290604865602747

theorem tailTrace_135933 : CollatzResearch.WordTrace tailWord_135933 prefixEnd_135933 15510881290604865602747 := by
  unfold tailWord_135933
  simp only [CollatzResearch.WordTrace]
  refine ⟨4957883816545431353228453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3305255877696954235485635 4957883816545431353228453)
  ·
    refine ⟨929603215602268378730335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4957883816545431353228453 929603215602268378730335)
    ·
      refine ⟨1394404823403402568095503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 929603215602268378730335 1394404823403402568095503)
      ·
        refine ⟨2091607235105103852143255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1394404823403402568095503 2091607235105103852143255)
        ·
          refine ⟨3137410852657655778214883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2091607235105103852143255 3137410852657655778214883)
          ·
            refine ⟨4706116278986483667322325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137410852657655778214883 4706116278986483667322325)
            ·
              refine ⟨110299600288745710952867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4706116278986483667322325 110299600288745710952867)
              ·
                refine ⟨165449400433118566429301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110299600288745710952867 165449400433118566429301)
                ·
                  refine ⟨15510881290604865602747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165449400433118566429301 15510881290604865602747)
                  ·
                    rfl

theorem cell22_135933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_135933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135933 prefixEnd_135933 := by exact prefixLift 135933
  have htrace : WordTrace (prefixWord ++ tailWord_135933) baseStart_135933 baseEnd_135933 := by
    simpa [prefixWord, tailWord_135933, baseEnd_135933] using wordTrace_append hprefix tailTrace_135933
  have hstable : (prefixWord ++ tailWord_135933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135933).length < 2 ^ (prefixWord ++ tailWord_135933).sum := by decide
  have hdescent : baseEnd_135933 < baseStart_135933 := by decide
  rcases family_descends (prefixWord ++ tailWord_135933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135991 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 4, 4]
def baseStart_135991 : Nat := 118140960795 + 135991 * 2 ^ 59
def prefixEnd_135991 : Nat := 4983230072969 + 3 ^ 40 * 135991 * 2
def baseEnd_135991 : Nat := 46552498457121778858063

theorem tailTrace_135991 : CollatzResearch.WordTrace tailWord_135991 prefixEnd_135991 46552498457121778858063 := by
  unfold tailWord_135991
  simp only [CollatzResearch.WordTrace]
  refine ⟨4959999250335307258839827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3306666166890204839226551 4959999250335307258839827)
  ·
    refine ⟨7439998875502960888259741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4959999250335307258839827 7439998875502960888259741)
    ·
      refine ⟨2789999578313610333097403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7439998875502960888259741 2789999578313610333097403)
      ·
        refine ⟨4184999367470415499646105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2789999578313610333097403 4184999367470415499646105)
        ·
          refine ⟨3138749525602811624734579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4184999367470415499646105 3138749525602811624734579)
          ·
            refine ⟨4708124288404217437101869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3138749525602811624734579 4708124288404217437101869)
            ·
              refine ⟨1765546608151581538913201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4708124288404217437101869 1765546608151581538913201)
              ·
                refine ⟨1324159956113686154184901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1765546608151581538913201 1324159956113686154184901)
                ·
                  refine ⟨248279991771316153909669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1324159956113686154184901 248279991771316153909669)
                  ·
                    refine ⟨46552498457121778858063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 248279991771316153909669 46552498457121778858063)
                    ·
                      rfl

theorem cell22_135991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_135991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135991 prefixEnd_135991 := by exact prefixLift 135991
  have htrace : WordTrace (prefixWord ++ tailWord_135991) baseStart_135991 baseEnd_135991 := by
    simpa [prefixWord, tailWord_135991, baseEnd_135991] using wordTrace_append hprefix tailTrace_135991
  have hstable : (prefixWord ++ tailWord_135991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135991).length < 2 ^ (prefixWord ++ tailWord_135991).sum := by decide
  have hdescent : baseEnd_135991 < baseStart_135991 := by decide
  rcases family_descends (prefixWord ++ tailWord_135991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135997 : List Nat := [1, 4, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_135997 : Nat := 118140960795 + 135997 * 2 ^ 59
def prefixEnd_135997 : Nat := 4983230072969 + 3 ^ 40 * 135997 * 2
def baseEnd_135997 : Nat := 46554552379739763208045

theorem tailTrace_135997 : CollatzResearch.WordTrace tailWord_135997 prefixEnd_135997 46554552379739763208045 := by
  unfold tailWord_135997
  simp only [CollatzResearch.WordTrace]
  refine ⟨4960218088313570283558245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3306812058875713522372163 4960218088313570283558245)
  ·
    refine ⟨930040891558794428167171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4960218088313570283558245 930040891558794428167171)
    ·
      refine ⟨1395061337338191642250757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930040891558794428167171 1395061337338191642250757)
      ·
        refine ⟨261574000750910932922017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1395061337338191642250757 261574000750910932922017)
        ·
          refine ⟨196180500563183199691513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261574000750910932922017 196180500563183199691513)
          ·
            refine ⟨147135375422387399768635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196180500563183199691513 147135375422387399768635)
            ·
              refine ⟨220703063133581099652953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147135375422387399768635 220703063133581099652953)
              ·
                refine ⟨165527297350185824739715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220703063133581099652953 165527297350185824739715)
                ·
                  refine ⟨248290946025278737109573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165527297350185824739715 248290946025278737109573)
                  ·
                    refine ⟨46554552379739763208045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 248290946025278737109573 46554552379739763208045)
                    ·
                      rfl

theorem cell22_135997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_135997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_135997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_135997 prefixEnd_135997 := by exact prefixLift 135997
  have htrace : WordTrace (prefixWord ++ tailWord_135997) baseStart_135997 baseEnd_135997 := by
    simpa [prefixWord, tailWord_135997, baseEnd_135997] using wordTrace_append hprefix tailTrace_135997
  have hstable : (prefixWord ++ tailWord_135997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135997).length < 2 ^ (prefixWord ++ tailWord_135997).sum := by decide
  have hdescent : baseEnd_135997 < baseStart_135997 := by decide
  rcases family_descends (prefixWord ++ tailWord_135997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136008 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 2, 4]
def baseStart_136008 : Nat := 118140960795 + 136008 * 2 ^ 59
def prefixEnd_136008 : Nat := 4983230072969 + 3 ^ 40 * 136008 * 2
def baseEnd_136008 : Nat := 46558317904539401183011

theorem tailTrace_136008 : CollatzResearch.WordTrace tailWord_136008 prefixEnd_136008 46558317904539401183011 := by
  unfold tailWord_136008
  simp only [CollatzResearch.WordTrace]
  refine ⟨2480309645636859581104339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3307079527515812774805785 2480309645636859581104339)
  ·
    refine ⟨3720464468455289371656509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2480309645636859581104339 3720464468455289371656509)
    ·
      refine ⟨1395174175670733514371191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3720464468455289371656509 1395174175670733514371191)
      ·
        refine ⟨2092761263506100271556787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395174175670733514371191 2092761263506100271556787)
        ·
          refine ⟨3139141895259150407335181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2092761263506100271556787 3139141895259150407335181)
          ·
            refine ⟨1177178210722181402750693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3139141895259150407335181 1177178210722181402750693)
            ·
              refine ⟨220720914510409013015755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1177178210722181402750693 220720914510409013015755)
              ·
                refine ⟨331081371765613519523633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220720914510409013015755 331081371765613519523633)
                ·
                  refine ⟨248311028824210139642725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331081371765613519523633 248311028824210139642725)
                  ·
                    refine ⟨46558317904539401183011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 248311028824210139642725 46558317904539401183011)
                    ·
                      rfl

theorem cell22_136008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_136008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136008 prefixEnd_136008 := by exact prefixLift 136008
  have htrace : WordTrace (prefixWord ++ tailWord_136008) baseStart_136008 baseEnd_136008 := by
    simpa [prefixWord, tailWord_136008, baseEnd_136008] using wordTrace_append hprefix tailTrace_136008
  have hstable : (prefixWord ++ tailWord_136008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136008).length < 2 ^ (prefixWord ++ tailWord_136008).sum := by decide
  have hdescent : baseEnd_136008 < baseStart_136008 := by decide
  rcases family_descends (prefixWord ++ tailWord_136008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136072 : List Nat := [2, 1, 3, 3, 2, 1, 1, 5, 1, 3]
def baseStart_136072 : Nat := 118140960795 + 136072 * 2 ^ 59
def prefixEnd_136072 : Nat := 4983230072969 + 3 ^ 40 * 136072 * 2
def baseEnd_136072 : Nat := 46580226412464567582815

theorem tailTrace_136072 : CollatzResearch.WordTrace tailWord_136072 prefixEnd_136072 46580226412464567582815 := by
  unfold tailWord_136072
  simp only [CollatzResearch.WordTrace]
  refine ⟨2481476781520929046269235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3308635708694572061692313 2481476781520929046269235)
  ·
    refine ⟨3722215172281393569403853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2481476781520929046269235 3722215172281393569403853)
    ·
      refine ⟨1395830689605522588526445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3722215172281393569403853 1395830689605522588526445)
      ·
        refine ⟨523436508602070970697417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1395830689605522588526445 523436508602070970697417)
        ·
          refine ⟨392577381451553228023063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523436508602070970697417 392577381451553228023063)
          ·
            refine ⟨588866072177329842034595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392577381451553228023063 588866072177329842034595)
            ·
              refine ⟨883299108265994763051893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588866072177329842034595 883299108265994763051893)
              ·
                refine ⟨82809291399937009036115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 883299108265994763051893 82809291399937009036115)
                ·
                  refine ⟨124213937099905513554173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82809291399937009036115 124213937099905513554173)
                  ·
                    refine ⟨46580226412464567582815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 124213937099905513554173 46580226412464567582815)
                    ·
                      rfl

theorem cell22_136072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_136072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136072 prefixEnd_136072 := by exact prefixLift 136072
  have htrace : WordTrace (prefixWord ++ tailWord_136072) baseStart_136072 baseEnd_136072 := by
    simpa [prefixWord, tailWord_136072, baseEnd_136072] using wordTrace_append hprefix tailTrace_136072
  have hstable : (prefixWord ++ tailWord_136072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136072).length < 2 ^ (prefixWord ++ tailWord_136072).sum := by decide
  have hdescent : baseEnd_136072 < baseStart_136072 := by decide
  rcases family_descends (prefixWord ++ tailWord_136072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136085 : List Nat := [1, 3, 2, 1, 1, 6, 1, 2, 5]
def baseStart_136085 : Nat := 118140960795 + 136085 * 2 ^ 59
def prefixEnd_136085 : Nat := 4983230072969 + 3 ^ 40 * 136085 * 2
def baseEnd_136085 : Nat := 15528225526045622335925

theorem tailTrace_136085 : CollatzResearch.WordTrace tailWord_136085 prefixEnd_136085 15528225526045622335925 := by
  unfold tailWord_136085
  simp only [CollatzResearch.WordTrace]
  refine ⟨4963427711994761312761709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3308951807996507541841139 4963427711994761312761709)
  ·
    refine ⟨1861285391998035492285641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4963427711994761312761709 1861285391998035492285641)
    ·
      refine ⟨1395964043998526619214231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1861285391998035492285641 1395964043998526619214231)
      ·
        refine ⟨2093946065997789928821347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395964043998526619214231 2093946065997789928821347)
        ·
          refine ⟨3140919098996684893232021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093946065997789928821347 3140919098996684893232021)
          ·
            refine ⟨147230582765469604370251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3140919098996684893232021 147230582765469604370251)
            ·
              refine ⟨220845874148204406555377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147230582765469604370251 220845874148204406555377)
              ·
                refine ⟨165634405611153304916533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220845874148204406555377 165634405611153304916533)
                ·
                  refine ⟨15528225526045622335925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165634405611153304916533 15528225526045622335925)
                  ·
                    rfl

theorem cell22_136085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_136085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136085 prefixEnd_136085 := by exact prefixLift 136085
  have htrace : WordTrace (prefixWord ++ tailWord_136085) baseStart_136085 baseEnd_136085 := by
    simpa [prefixWord, tailWord_136085, baseEnd_136085] using wordTrace_append hprefix tailTrace_136085
  have hstable : (prefixWord ++ tailWord_136085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136085).length < 2 ^ (prefixWord ++ tailWord_136085).sum := by decide
  have hdescent : baseEnd_136085 < baseStart_136085 := by decide
  rcases family_descends (prefixWord ++ tailWord_136085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136143 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 4, 4]
def baseStart_136143 : Nat := 118140960795 + 136143 * 2 ^ 59
def prefixEnd_136143 : Nat := 4983230072969 + 3 ^ 40 * 136143 * 2
def baseEnd_136143 : Nat := 46604531163444049057597

theorem tailTrace_136143 : CollatzResearch.WordTrace tailWord_136143 prefixEnd_136143 46604531163444049057597 := by
  unfold tailWord_136143
  simp only [CollatzResearch.WordTrace]
  refine ⟨4965543145784637218373083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3310362097189758145582055 4965543145784637218373083)
  ·
    refine ⟨7448314718676955827559625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4965543145784637218373083 7448314718676955827559625)
    ·
      refine ⟨5586236039007716870669719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7448314718676955827559625 5586236039007716870669719)
      ·
        refine ⟨8379354058511575306004579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5586236039007716870669719 8379354058511575306004579)
        ·
          refine ⟨12569031087767362959006869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8379354058511575306004579 12569031087767362959006869)
          ·
            refine ⟨589173332239095138703447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12569031087767362959006869 589173332239095138703447)
            ·
              refine ⟨883759998358642708055171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589173332239095138703447 883759998358642708055171)
              ·
                refine ⟨1325639997537964062082757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883759998358642708055171 1325639997537964062082757)
                ·
                  refine ⟨248557499538368261640517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1325639997537964062082757 248557499538368261640517)
                  ·
                    refine ⟨46604531163444049057597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 248557499538368261640517 46604531163444049057597)
                    ·
                      rfl

theorem cell22_136143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_136143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136143 prefixEnd_136143 := by exact prefixLift 136143
  have htrace : WordTrace (prefixWord ++ tailWord_136143) baseStart_136143 baseEnd_136143 := by
    simpa [prefixWord, tailWord_136143, baseEnd_136143] using wordTrace_append hprefix tailTrace_136143
  have hstable : (prefixWord ++ tailWord_136143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136143).length < 2 ^ (prefixWord ++ tailWord_136143).sum := by decide
  have hdescent : baseEnd_136143 < baseStart_136143 := by decide
  rcases family_descends (prefixWord ++ tailWord_136143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136145 : List Nat := [1, 2, 2, 1, 2, 1, 4, 4, 2, 3]
def baseStart_136145 : Nat := 118140960795 + 136145 * 2 ^ 59
def prefixEnd_136145 : Nat := 4983230072969 + 3 ^ 40 * 136145 * 2
def baseEnd_136145 : Nat := 46605215804316710507591

theorem tailTrace_136145 : CollatzResearch.WordTrace tailWord_136145 prefixEnd_136145 46605215804316710507591 := by
  unfold tailWord_136145
  simp only [CollatzResearch.WordTrace]
  refine ⟨4965616091777391559945889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3310410727851594373297259 4965616091777391559945889)
  ·
    refine ⟨3724212068833043669959417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4965616091777391559945889 3724212068833043669959417)
    ·
      refine ⟨2793159051624782752469563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3724212068833043669959417 2793159051624782752469563)
      ·
        refine ⟨4189738577437174128704345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2793159051624782752469563 4189738577437174128704345)
        ·
          refine ⟨3142303933077880596528259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4189738577437174128704345 3142303933077880596528259)
          ·
            refine ⟨4713455899616820894792389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3142303933077880596528259 4713455899616820894792389)
            ·
              refine ⟨883772981178153917773573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4713455899616820894792389 883772981178153917773573)
              ·
                refine ⟨165707433970903859582545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 883772981178153917773573 165707433970903859582545)
                ·
                  refine ⟨124280575478177894686909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165707433970903859582545 124280575478177894686909)
                  ·
                    refine ⟨46605215804316710507591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 124280575478177894686909 46605215804316710507591)
                    ·
                      rfl

theorem cell22_136145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_136145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136145 prefixEnd_136145 := by exact prefixLift 136145
  have htrace : WordTrace (prefixWord ++ tailWord_136145) baseStart_136145 baseEnd_136145 := by
    simpa [prefixWord, tailWord_136145, baseEnd_136145] using wordTrace_append hprefix tailTrace_136145
  have hstable : (prefixWord ++ tailWord_136145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136145).length < 2 ^ (prefixWord ++ tailWord_136145).sum := by decide
  have hdescent : baseEnd_136145 < baseStart_136145 := by decide
  rcases family_descends (prefixWord ++ tailWord_136145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136224 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 3, 3]
def baseStart_136224 : Nat := 118140960795 + 136224 * 2 ^ 59
def prefixEnd_136224 : Nat := 4983230072969 + 3 ^ 40 * 136224 * 2
def baseEnd_136224 : Nat := 46632259118786837782349

theorem tailTrace_136224 : CollatzResearch.WordTrace tailWord_136224 prefixEnd_136224 46632259118786837782349 := by
  unfold tailWord_136224
  simp only [CollatzResearch.WordTrace]
  refine ⟨2484248729245594026035863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3312331638994125368047817 2484248729245594026035863)
  ·
    refine ⟨3726373093868391039053795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2484248729245594026035863 3726373093868391039053795)
    ·
      refine ⟨5589559640802586558580693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726373093868391039053795 5589559640802586558580693)
      ·
        refine ⟨131005304081310622466735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 5589559640802586558580693 131005304081310622466735)
        ·
          refine ⟨196507956121965933700103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131005304081310622466735 196507956121965933700103)
          ·
            refine ⟨294761934182948900550155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196507956121965933700103 294761934182948900550155)
            ·
              refine ⟨442142901274423350825233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294761934182948900550155 442142901274423350825233)
              ·
                refine ⟨331607175955817513118925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442142901274423350825233 331607175955817513118925)
                ·
                  refine ⟨124352690983431567419597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331607175955817513118925 124352690983431567419597)
                  ·
                    refine ⟨46632259118786837782349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 124352690983431567419597 46632259118786837782349)
                    ·
                      rfl

theorem cell22_136224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 3, 3].length) (baseStart_136224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136224 prefixEnd_136224 := by exact prefixLift 136224
  have htrace : WordTrace (prefixWord ++ tailWord_136224) baseStart_136224 baseEnd_136224 := by
    simpa [prefixWord, tailWord_136224, baseEnd_136224] using wordTrace_append hprefix tailTrace_136224
  have hstable : (prefixWord ++ tailWord_136224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136224).length < 2 ^ (prefixWord ++ tailWord_136224).sum := by decide
  have hdescent : baseEnd_136224 < baseStart_136224 := by decide
  rcases family_descends (prefixWord ++ tailWord_136224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136254 : List Nat := [4, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_136254 : Nat := 118140960795 + 136254 * 2 ^ 59
def prefixEnd_136254 : Nat := 4983230072969 + 3 ^ 40 * 136254 * 2
def baseEnd_136254 : Nat := 15547509577292253177419

theorem tailTrace_136254 : CollatzResearch.WordTrace tailWord_136254 prefixEnd_136254 15547509577292253177419 := by
  unfold tailWord_136254
  simp only [CollatzResearch.WordTrace]
  refine ⟨621198956047812896957977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3313061098921668783775877 621198956047812896957977)
  ·
    refine ⟨465899217035859672718483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 621198956047812896957977 465899217035859672718483)
    ·
      refine ⟨698848825553789509077725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 465899217035859672718483 698848825553789509077725)
      ·
        refine ⟨262068309582671065904147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 698848825553789509077725 262068309582671065904147)
        ·
          refine ⟨393102464374006598856221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262068309582671065904147 393102464374006598856221)
          ·
            refine ⟨147413424140252474571083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 393102464374006598856221 147413424140252474571083)
            ·
              refine ⟨221120136210378711856625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147413424140252474571083 221120136210378711856625)
              ·
                refine ⟨165840102157784033892469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221120136210378711856625 165840102157784033892469)
                ·
                  refine ⟨15547509577292253177419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165840102157784033892469 15547509577292253177419)
                  ·
                    rfl

theorem cell22_136254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_136254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136254 prefixEnd_136254 := by exact prefixLift 136254
  have htrace : WordTrace (prefixWord ++ tailWord_136254) baseStart_136254 baseEnd_136254 := by
    simpa [prefixWord, tailWord_136254, baseEnd_136254] using wordTrace_append hprefix tailTrace_136254
  have hstable : (prefixWord ++ tailWord_136254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136254).length < 2 ^ (prefixWord ++ tailWord_136254).sum := by decide
  have hdescent : baseEnd_136254 < baseStart_136254 := by decide
  rcases family_descends (prefixWord ++ tailWord_136254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136295 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 1, 6]
def baseStart_136295 : Nat := 118140960795 + 136295 * 2 ^ 59
def prefixEnd_136295 : Nat := 4983230072969 + 3 ^ 40 * 136295 * 2
def baseEnd_136295 : Nat := 46656563869766319257131

theorem tailTrace_136295 : CollatzResearch.WordTrace tailWord_136295 prefixEnd_136295 46656563869766319257131 := by
  unfold tailWord_136295
  simp only [CollatzResearch.WordTrace]
  refine ⟨4971087041233967177906339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3314058027489311451937559 4971087041233967177906339)
  ·
    refine ⟨7456630561850950766859509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4971087041233967177906339 7456630561850950766859509)
    ·
      refine ⟨699059115173526634393079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7456630561850950766859509 699059115173526634393079)
      ·
        refine ⟨1048588672760289951589619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699059115173526634393079 1048588672760289951589619)
        ·
          refine ⟨1572883009140434927384429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048588672760289951589619 1572883009140434927384429)
          ·
            refine ⟨589831128427663097769161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1572883009140434927384429 589831128427663097769161)
            ·
              refine ⟨442373346320747323326871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 589831128427663097769161 442373346320747323326871)
              ·
                refine ⟨663560019481120984990307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442373346320747323326871 663560019481120984990307)
                ·
                  refine ⟨995340029221681477485461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663560019481120984990307 995340029221681477485461)
                  ·
                    refine ⟨46656563869766319257131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 995340029221681477485461 46656563869766319257131)
                    ·
                      rfl

theorem cell22_136295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_136295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136295 prefixEnd_136295 := by exact prefixLift 136295
  have htrace : WordTrace (prefixWord ++ tailWord_136295) baseStart_136295 baseEnd_136295 := by
    simpa [prefixWord, tailWord_136295, baseEnd_136295] using wordTrace_append hprefix tailTrace_136295
  have hstable : (prefixWord ++ tailWord_136295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136295).length < 2 ^ (prefixWord ++ tailWord_136295).sum := by decide
  have hdescent : baseEnd_136295 < baseStart_136295 := by decide
  rcases family_descends (prefixWord ++ tailWord_136295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136402 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_136402 : Nat := 118140960795 + 136402 * 2 ^ 59
def prefixEnd_136402 : Nat := 4983230072969 + 3 ^ 40 * 136402 * 2
def baseEnd_136402 : Nat := 46693192156453706831803

theorem tailTrace_136402 : CollatzResearch.WordTrace tailWord_136402 prefixEnd_136402 46693192156453706831803 := by
  unfold tailWord_136402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1243747412961581113012865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3316659767897549634700973 1243747412961581113012865)
  ·
    refine ⟨932810559721185834759649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1243747412961581113012865 932810559721185834759649)
    ·
      refine ⟨699607919790889376069737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 932810559721185834759649 699607919790889376069737)
      ·
        refine ⟨524705939843167032052303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 699607919790889376069737 524705939843167032052303)
        ·
          refine ⟨787058909764750548078455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524705939843167032052303 787058909764750548078455)
          ·
            refine ⟨1180588364647125822117683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787058909764750548078455 1180588364647125822117683)
            ·
              refine ⟨1770882546970688733176525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180588364647125822117683 1770882546970688733176525)
              ·
                refine ⟨664080955114008274941197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1770882546970688733176525 664080955114008274941197)
                ·
                  refine ⟨249030358167753103102949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664080955114008274941197 249030358167753103102949)
                  ·
                    refine ⟨46693192156453706831803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 249030358167753103102949 46693192156453706831803)
                    ·
                      rfl

theorem cell22_136402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_136402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136402 prefixEnd_136402 := by exact prefixLift 136402
  have htrace : WordTrace (prefixWord ++ tailWord_136402) baseStart_136402 baseEnd_136402 := by
    simpa [prefixWord, tailWord_136402, baseEnd_136402] using wordTrace_append hprefix tailTrace_136402
  have hstable : (prefixWord ++ tailWord_136402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136402).length < 2 ^ (prefixWord ++ tailWord_136402).sum := by decide
  have hdescent : baseEnd_136402 < baseStart_136402 := by decide
  rcases family_descends (prefixWord ++ tailWord_136402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136434 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 6]
def baseStart_136434 : Nat := 118140960795 + 136434 * 2 ^ 59
def prefixEnd_136434 : Nat := 4983230072969 + 3 ^ 40 * 136434 * 2
def baseEnd_136434 : Nat := 15568048803472096677235

theorem tailTrace_136434 : CollatzResearch.WordTrace tailWord_136434 prefixEnd_136434 15568048803472096677235 := by
  unfold tailWord_136434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1244039196932598479304089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3317437858486929278144237 1244039196932598479304089)
  ·
    refine ⟨933029397699448859478067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1244039196932598479304089 933029397699448859478067)
    ·
      refine ⟨1399544096549173289217101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 933029397699448859478067 1399544096549173289217101)
      ·
        refine ⟨524829036205939983456413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1399544096549173289217101 524829036205939983456413)
        ·
          refine ⟨196810888577227493796155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 524829036205939983456413 196810888577227493796155)
          ·
            refine ⟨295216332865841240694233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196810888577227493796155 295216332865841240694233)
            ·
              refine ⟨221412249649380930520675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295216332865841240694233 221412249649380930520675)
              ·
                refine ⟨332118374474071395781013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221412249649380930520675 332118374474071395781013)
                ·
                  refine ⟨15568048803472096677235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 332118374474071395781013 15568048803472096677235)
                  ·
                    rfl

theorem cell22_136434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_136434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136434 prefixEnd_136434 := by exact prefixLift 136434
  have htrace : WordTrace (prefixWord ++ tailWord_136434) baseStart_136434 baseEnd_136434 := by
    simpa [prefixWord, tailWord_136434, baseEnd_136434] using wordTrace_append hprefix tailTrace_136434
  have hstable : (prefixWord ++ tailWord_136434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136434).length < 2 ^ (prefixWord ++ tailWord_136434).sum := by decide
  have hdescent : baseEnd_136434 < baseStart_136434 := by decide
  rcases family_descends (prefixWord ++ tailWord_136434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136449 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 1, 5]
def baseStart_136449 : Nat := 118140960795 + 136449 * 2 ^ 59
def prefixEnd_136449 : Nat := 4983230072969 + 3 ^ 40 * 136449 * 2
def baseEnd_136449 : Nat := 46709281216961250906659

theorem tailTrace_136449 : CollatzResearch.WordTrace tailWord_136449 prefixEnd_136449 46709281216961250906659 := by
  unfold tailWord_136449
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976703882676051479012401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3317802588450700986008267 4976703882676051479012401)
  ·
    refine ⟨3732527912007038609259301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4976703882676051479012401 3732527912007038609259301)
    ·
      refine ⟨699848983501319739236119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3732527912007038609259301 699848983501319739236119)
      ·
        refine ⟨1049773475251979608854179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699848983501319739236119 1049773475251979608854179)
        ·
          refine ⟨1574660212877969413281269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049773475251979608854179 1574660212877969413281269)
          ·
            refine ⟨147624394957309632495119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1574660212877969413281269 147624394957309632495119)
            ·
              refine ⟨221436592435964448742679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147624394957309632495119 221436592435964448742679)
              ·
                refine ⟨332154888653946673114019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221436592435964448742679 332154888653946673114019)
                ·
                  refine ⟨498232332980920009671029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332154888653946673114019 498232332980920009671029)
                  ·
                    refine ⟨46709281216961250906659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 498232332980920009671029 46709281216961250906659)
                    ·
                      rfl

theorem cell22_136449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_136449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136449 prefixEnd_136449 := by exact prefixLift 136449
  have htrace : WordTrace (prefixWord ++ tailWord_136449) baseStart_136449 baseEnd_136449 := by
    simpa [prefixWord, tailWord_136449, baseEnd_136449] using wordTrace_append hprefix tailTrace_136449
  have hstable : (prefixWord ++ tailWord_136449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136449).length < 2 ^ (prefixWord ++ tailWord_136449).sum := by decide
  have hdescent : baseEnd_136449 < baseStart_136449 := by decide
  rcases family_descends (prefixWord ++ tailWord_136449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136462 : List Nat := [4, 1, 1, 2, 1, 4, 1, 8]
def baseStart_136462 : Nat := 118140960795 + 136462 * 2 ^ 59
def prefixEnd_136462 : Nat := 4983230072969 + 3 ^ 40 * 136462 * 2
def baseEnd_136462 : Nat := 5190414598070394481291

theorem tailTrace_136462 : CollatzResearch.WordTrace tailWord_136462 prefixEnd_136462 5190414598070394481291 := by
  unfold tailWord_136462
  simp only [CollatzResearch.WordTrace]
  refine ⟨622147253953619337404455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3318118687752636466157093 622147253953619337404455)
  ·
    refine ⟨933220880930429006106683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 622147253953619337404455 933220880930429006106683)
    ·
      refine ⟨1399831321395643509160025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 933220880930429006106683 1399831321395643509160025)
      ·
        refine ⟨1049873491046732631870019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1399831321395643509160025 1049873491046732631870019)
        ·
          refine ⟨1574810236570098947805029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049873491046732631870019 1574810236570098947805029)
          ·
            refine ⟨295276919356893552713443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1574810236570098947805029 295276919356893552713443)
            ·
              refine ⟨442915379035340329070165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295276919356893552713443 442915379035340329070165)
              ·
                refine ⟨5190414598070394481291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 442915379035340329070165 5190414598070394481291)
                ·
                  rfl

theorem cell22_136462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_136462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136462 prefixEnd_136462 := by exact prefixLift 136462
  have htrace : WordTrace (prefixWord ++ tailWord_136462) baseStart_136462 baseEnd_136462 := by
    simpa [prefixWord, tailWord_136462, baseEnd_136462] using wordTrace_append hprefix tailTrace_136462
  have hstable : (prefixWord ++ tailWord_136462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136462).length < 2 ^ (prefixWord ++ tailWord_136462).sum := by decide
  have hdescent : baseEnd_136462 < baseStart_136462 := by decide
  rcases family_descends (prefixWord ++ tailWord_136462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136475 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 1, 8]
def baseStart_136475 : Nat := 118140960795 + 136475 * 2 ^ 59
def prefixEnd_136475 : Nat := 4983230072969 + 3 ^ 40 * 136475 * 2
def baseEnd_136475 : Nat := 46718181548305849756579

theorem tailTrace_136475 : CollatzResearch.WordTrace tailWord_136475 prefixEnd_136475 46718181548305849756579 := by
  unfold tailWord_136475
  simp only [CollatzResearch.WordTrace]
  refine ⟨4977652180581857919458879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3318434787054571946305919 4977652180581857919458879)
  ·
    refine ⟨7466478270872786879188319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4977652180581857919458879 7466478270872786879188319)
    ·
      refine ⟨11199717406309180318782479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7466478270872786879188319 11199717406309180318782479)
      ·
        refine ⟨16799576109463770478173719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11199717406309180318782479 16799576109463770478173719)
        ·
          refine ⟨25199364164195655717260579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16799576109463770478173719 25199364164195655717260579)
          ·
            refine ⟨37799046246293483575890869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25199364164195655717260579 37799046246293483575890869)
            ·
              refine ⟨3543660585590014085239769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37799046246293483575890869 3543660585590014085239769)
              ·
                refine ⟨2657745439192510563929827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3543660585590014085239769 2657745439192510563929827)
                ·
                  refine ⟨3986618158788765845894741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657745439192510563929827 3986618158788765845894741)
                  ·
                    refine ⟨46718181548305849756579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3986618158788765845894741 46718181548305849756579)
                    ·
                      rfl

theorem cell22_136475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_136475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136475 prefixEnd_136475 := by exact prefixLift 136475
  have htrace : WordTrace (prefixWord ++ tailWord_136475) baseStart_136475 baseEnd_136475 := by
    simpa [prefixWord, tailWord_136475, baseEnd_136475] using wordTrace_append hprefix tailTrace_136475
  have hstable : (prefixWord ++ tailWord_136475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136475).length < 2 ^ (prefixWord ++ tailWord_136475).sum := by decide
  have hdescent : baseEnd_136475 < baseStart_136475 := by decide
  rcases family_descends (prefixWord ++ tailWord_136475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136479 : List Nat := [1, 1, 2, 4, 5, 1, 8]
def baseStart_136479 : Nat := 118140960795 + 136479 * 2 ^ 59
def prefixEnd_136479 : Nat := 4983230072969 + 3 ^ 40 * 136479 * 2
def baseEnd_136479 : Nat := 1730353734446339728021

theorem tailTrace_136479 : CollatzResearch.WordTrace tailWord_136479 prefixEnd_136479 1730353734446339728021 := by
  unfold tailWord_136479
  simp only [CollatzResearch.WordTrace]
  refine ⟨4977798072567366602604491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3318532048378244401736327 4977798072567366602604491)
  ·
    refine ⟨7466697108851049903906737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4977798072567366602604491 7466697108851049903906737)
    ·
      refine ⟨5600022831638287427930053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7466697108851049903906737 5600022831638287427930053)
      ·
        refine ⟨1050004280932178892736885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5600022831638287427930053 1050004280932178892736885)
        ·
          refine ⟨98437901337391771194083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1050004280932178892736885 98437901337391771194083)
          ·
            refine ⟨147656852006087656791125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98437901337391771194083 147656852006087656791125)
            ·
              refine ⟨1730353734446339728021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 147656852006087656791125 1730353734446339728021)
              ·
                rfl

theorem cell22_136479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 8].length) (baseStart_136479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136479 prefixEnd_136479 := by exact prefixLift 136479
  have htrace : WordTrace (prefixWord ++ tailWord_136479) baseStart_136479 baseEnd_136479 := by
    simpa [prefixWord, tailWord_136479, baseEnd_136479] using wordTrace_append hprefix tailTrace_136479
  have hstable : (prefixWord ++ tailWord_136479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136479).length < 2 ^ (prefixWord ++ tailWord_136479).sum := by decide
  have hdescent : baseEnd_136479 < baseStart_136479 := by decide
  rcases family_descends (prefixWord ++ tailWord_136479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136584 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 1, 5]
def baseStart_136584 : Nat := 118140960795 + 136584 * 2 ^ 59
def prefixEnd_136584 : Nat := 4983230072969 + 3 ^ 40 * 136584 * 2
def baseEnd_136584 : Nat := 46755494475865898781245

theorem tailTrace_136584 : CollatzResearch.WordTrace tailWord_136584 prefixEnd_136584 46755494475865898781245 := by
  unfold tailWord_136584
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490813868593484767588403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3321085158124646356784537 2490813868593484767588403)
  ·
    refine ⟨3736220802890227151382605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2490813868593484767588403 3736220802890227151382605)
    ·
      refine ⟨1401082801083835181768477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3736220802890227151382605 1401082801083835181768477)
      ·
        refine ⟨525406050406438193163179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1401082801083835181768477 525406050406438193163179)
        ·
          refine ⟨788109075609657289744769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525406050406438193163179 788109075609657289744769)
          ·
            refine ⟨591081806707242967308577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 788109075609657289744769 591081806707242967308577)
            ·
              refine ⟨443311355030432225481433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591081806707242967308577 443311355030432225481433)
              ·
                refine ⟨332483516272824169111075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443311355030432225481433 332483516272824169111075)
                ·
                  refine ⟨498725274409236253666613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332483516272824169111075 498725274409236253666613)
                  ·
                    refine ⟨46755494475865898781245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 498725274409236253666613 46755494475865898781245)
                    ·
                      rfl

theorem cell22_136584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_136584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136584 prefixEnd_136584 := by exact prefixLift 136584
  have htrace : WordTrace (prefixWord ++ tailWord_136584) baseStart_136584 baseEnd_136584 := by
    simpa [prefixWord, tailWord_136584, baseEnd_136584] using wordTrace_append hprefix tailTrace_136584
  have hstable : (prefixWord ++ tailWord_136584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136584).length < 2 ^ (prefixWord ++ tailWord_136584).sum := by decide
  have hdescent : baseEnd_136584 < baseStart_136584 := by decide
  rcases family_descends (prefixWord ++ tailWord_136584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136601 : List Nat := [1, 2, 1, 2, 1, 5, 3, 2, 2, 3]
def baseStart_136601 : Nat := 118140960795 + 136601 * 2 ^ 59
def prefixEnd_136601 : Nat := 4983230072969 + 3 ^ 40 * 136601 * 2
def baseEnd_136601 : Nat := 46761313923283521106193

theorem tailTrace_136601 : CollatzResearch.WordTrace tailWord_136601 prefixEnd_136601 46761313923283521106193 := by
  unfold tailWord_136601
  simp only [CollatzResearch.WordTrace]
  refine ⟨4982247778125381438545657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3321498518750254292363771 4982247778125381438545657)
  ·
    refine ⟨3736685833594036078909243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4982247778125381438545657 3736685833594036078909243)
    ·
      refine ⟨5605028750391054118363865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3736685833594036078909243 5605028750391054118363865)
      ·
        refine ⟨4203771562793290588772899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5605028750391054118363865 4203771562793290588772899)
        ·
          refine ⟨6305657344189935883159349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4203771562793290588772899 6305657344189935883159349)
          ·
            refine ⟨591155376017806489046189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6305657344189935883159349 591155376017806489046189)
            ·
              refine ⟨221683266006677433392321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 591155376017806489046189 221683266006677433392321)
              ·
                refine ⟨166262449505008075044241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221683266006677433392321 166262449505008075044241)
                ·
                  refine ⟨124696837128756056283181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166262449505008075044241 124696837128756056283181)
                  ·
                    refine ⟨46761313923283521106193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 124696837128756056283181 46761313923283521106193)
                    ·
                      rfl

theorem cell22_136601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 3].length) (baseStart_136601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136601 prefixEnd_136601 := by exact prefixLift 136601
  have htrace : WordTrace (prefixWord ++ tailWord_136601) baseStart_136601 baseEnd_136601 := by
    simpa [prefixWord, tailWord_136601, baseEnd_136601] using wordTrace_append hprefix tailTrace_136601
  have hstable : (prefixWord ++ tailWord_136601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136601).length < 2 ^ (prefixWord ++ tailWord_136601).sum := by decide
  have hdescent : baseEnd_136601 < baseStart_136601 := by decide
  rcases family_descends (prefixWord ++ tailWord_136601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136627 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 2, 6]
def baseStart_136627 : Nat := 118140960795 + 136627 * 2 ^ 59
def prefixEnd_136627 : Nat := 4983230072969 + 3 ^ 40 * 136627 * 2
def baseEnd_136627 : Nat := 46770214254628119956113

theorem tailTrace_136627 : CollatzResearch.WordTrace tailWord_136627 prefixEnd_136627 46770214254628119956113 := by
  unfold tailWord_136627
  simp only [CollatzResearch.WordTrace]
  refine ⟨4983196076031187878992135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3322130717354125252661423 4983196076031187878992135)
  ·
    refine ⟨7474794114046781818488203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4983196076031187878992135 7474794114046781818488203)
    ·
      refine ⟨11212191171070172727732305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7474794114046781818488203 11212191171070172727732305)
      ·
        refine ⟨8409143378302629545799229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11212191171070172727732305 8409143378302629545799229)
        ·
          refine ⟨3153428766863486079674711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8409143378302629545799229 3153428766863486079674711)
          ·
            refine ⟨4730143150295229119512067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153428766863486079674711 4730143150295229119512067)
            ·
              refine ⟨7095214725442843679268101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4730143150295229119512067 7095214725442843679268101)
              ·
                refine ⟨1330352761020533189862769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7095214725442843679268101 1330352761020533189862769)
                ·
                  refine ⟨997764570765399892397077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1330352761020533189862769 997764570765399892397077)
                  ·
                    refine ⟨46770214254628119956113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 997764570765399892397077 46770214254628119956113)
                    ·
                      rfl

theorem cell22_136627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_136627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136627 prefixEnd_136627 := by exact prefixLift 136627
  have htrace : WordTrace (prefixWord ++ tailWord_136627) baseStart_136627 baseEnd_136627 := by
    simpa [prefixWord, tailWord_136627, baseEnd_136627] using wordTrace_append hprefix tailTrace_136627
  have hstable : (prefixWord ++ tailWord_136627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136627).length < 2 ^ (prefixWord ++ tailWord_136627).sum := by decide
  have hdescent : baseEnd_136627 < baseStart_136627 := by decide
  rcases family_descends (prefixWord ++ tailWord_136627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136721 : List Nat := [1, 2, 2, 1, 1, 2, 5, 4, 4]
def baseStart_136721 : Nat := 118140960795 + 136721 * 2 ^ 59
def prefixEnd_136721 : Nat := 4983230072969 + 3 ^ 40 * 136721 * 2
def baseEnd_136721 : Nat := 15600797458547736035275

theorem tailTrace_136721 : CollatzResearch.WordTrace tailWord_136721 prefixEnd_136721 15600797458547736035275 := by
  unfold tailWord_136721
  simp only [CollatzResearch.WordTrace]
  refine ⟨4986624537690641932914017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3324416358460427955276011 4986624537690641932914017)
  ·
    refine ⟨3739968403267981449685513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4986624537690641932914017 3739968403267981449685513)
    ·
      refine ⟨2804976302450986087264135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3739968403267981449685513 2804976302450986087264135)
      ·
        refine ⟨4207464453676479130896203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2804976302450986087264135 4207464453676479130896203)
        ·
          refine ⟨6311196680514718696344305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4207464453676479130896203 6311196680514718696344305)
          ·
            refine ⟨4733397510386039022258229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6311196680514718696344305 4733397510386039022258229)
            ·
              refine ⟨443756016598691158336709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4733397510386039022258229 443756016598691158336709)
              ·
                refine ⟨83204253112254592188133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 443756016598691158336709 83204253112254592188133)
                ·
                  refine ⟨15600797458547736035275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83204253112254592188133 15600797458547736035275)
                  ·
                    rfl

theorem cell22_136721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 4].length) (baseStart_136721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136721 prefixEnd_136721 := by exact prefixLift 136721
  have htrace : WordTrace (prefixWord ++ tailWord_136721) baseStart_136721 baseEnd_136721 := by
    simpa [prefixWord, tailWord_136721, baseEnd_136721] using wordTrace_append hprefix tailTrace_136721
  have hstable : (prefixWord ++ tailWord_136721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136721).length < 2 ^ (prefixWord ++ tailWord_136721).sum := by decide
  have hdescent : baseEnd_136721 < baseStart_136721 := by decide
  rcases family_descends (prefixWord ++ tailWord_136721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136736 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 1, 5]
def baseStart_136736 : Nat := 118140960795 + 136736 * 2 ^ 59
def prefixEnd_136736 : Nat := 4983230072969 + 3 ^ 40 * 136736 * 2
def baseEnd_136736 : Nat := 46807527182188168980779

theorem tailTrace_136736 : CollatzResearch.WordTrace tailWord_136736 prefixEnd_136736 46807527182188168980779 := by
  unfold tailWord_136736
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493585816318149747355031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3324781088424199663140041 2493585816318149747355031)
  ·
    refine ⟨3740378724477224621032547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2493585816318149747355031 3740378724477224621032547)
    ·
      refine ⟨5610568086715836931548821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3740378724477224621032547 5610568086715836931548821)
      ·
        refine ⟨262995379064804856166351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5610568086715836931548821 262995379064804856166351)
        ·
          refine ⟨394493068597207284249527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262995379064804856166351 394493068597207284249527)
          ·
            refine ⟨591739602895810926374291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394493068597207284249527 591739602895810926374291)
            ·
              refine ⟨887609404343716389561437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591739602895810926374291 887609404343716389561437)
              ·
                refine ⟨332853526628893646085539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 887609404343716389561437 332853526628893646085539)
                ·
                  refine ⟨499280289943340469128309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332853526628893646085539 499280289943340469128309)
                  ·
                    refine ⟨46807527182188168980779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 499280289943340469128309 46807527182188168980779)
                    ·
                      rfl

theorem cell22_136736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_136736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136736 prefixEnd_136736 := by exact prefixLift 136736
  have htrace : WordTrace (prefixWord ++ tailWord_136736) baseStart_136736 baseEnd_136736 := by
    simpa [prefixWord, tailWord_136736, baseEnd_136736] using wordTrace_append hprefix tailTrace_136736
  have hstable : (prefixWord ++ tailWord_136736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136736).length < 2 ^ (prefixWord ++ tailWord_136736).sum := by decide
  have hdescent : baseEnd_136736 < baseStart_136736 := by decide
  rcases family_descends (prefixWord ++ tailWord_136736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136809 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 1, 7]
def baseStart_136809 : Nat := 118140960795 + 136809 * 2 ^ 59
def prefixEnd_136809 : Nat := 4983230072969 + 3 ^ 40 * 136809 * 2
def baseEnd_136809 : Nat := 46832516574040311905555

theorem tailTrace_136809 : CollatzResearch.WordTrace tailWord_136809 prefixEnd_136809 46832516574040311905555 := by
  unfold tailWord_136809
  simp only [CollatzResearch.WordTrace]
  refine ⟨4989834161371832962117481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3326556107581221974744987 4989834161371832962117481)
  ·
    refine ⟨3742375621028874721588111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4989834161371832962117481 3742375621028874721588111)
    ·
      refine ⟨5613563431543312082382167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3742375621028874721588111 5613563431543312082382167)
      ·
        refine ⟨8420345147314968123573251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5613563431543312082382167 8420345147314968123573251)
        ·
          refine ⟨12630517720972452185359877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8420345147314968123573251 12630517720972452185359877)
          ·
            refine ⟨2368222072682334784754977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12630517720972452185359877 2368222072682334784754977)
            ·
              refine ⟨1776166554511751088566233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2368222072682334784754977 1776166554511751088566233)
              ·
                refine ⟨1332124915883813316424675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1776166554511751088566233 1332124915883813316424675)
                ·
                  refine ⟨1998187373825719974637013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332124915883813316424675 1998187373825719974637013)
                  ·
                    refine ⟨46832516574040311905555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1998187373825719974637013 46832516574040311905555)
                    ·
                      rfl

theorem cell22_136809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_136809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136809 prefixEnd_136809 := by exact prefixLift 136809
  have htrace : WordTrace (prefixWord ++ tailWord_136809) baseStart_136809 baseEnd_136809 := by
    simpa [prefixWord, tailWord_136809, baseEnd_136809] using wordTrace_append hprefix tailTrace_136809
  have hstable : (prefixWord ++ tailWord_136809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136809).length < 2 ^ (prefixWord ++ tailWord_136809).sum := by decide
  have hdescent : baseEnd_136809 < baseStart_136809 := by decide
  rcases family_descends (prefixWord ++ tailWord_136809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136890 : List Nat := [3, 1, 1, 1, 2, 4, 4, 2, 4]
def baseStart_136890 : Nat := 118140960795 + 136890 * 2 ^ 59
def prefixEnd_136890 : Nat := 4983230072969 + 3 ^ 40 * 136890 * 2
def baseEnd_136890 : Nat := 15620081509794366876769

theorem tailTrace_136890 : CollatzResearch.WordTrace tailWord_136890 prefixEnd_136890 15620081509794366876769 := by
  unfold tailWord_136890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1248197118519595948954031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3328525649385589197210749 1248197118519595948954031)
  ·
    refine ⟨1872295677779393923431047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1248197118519595948954031 1872295677779393923431047)
    ·
      refine ⟨2808443516669090885146571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1872295677779393923431047 2808443516669090885146571)
      ·
        refine ⟨4212665275003636327719857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2808443516669090885146571 4212665275003636327719857)
        ·
          refine ⟨3159498956252727245789893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4212665275003636327719857 3159498956252727245789893)
          ·
            refine ⟨592406054297386358585605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3159498956252727245789893 592406054297386358585605)
            ·
              refine ⟨111076135180759942234801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 592406054297386358585605 111076135180759942234801)
              ·
                refine ⟨83307101385569956676101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111076135180759942234801 83307101385569956676101)
                ·
                  refine ⟨15620081509794366876769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83307101385569956676101 15620081509794366876769)
                  ·
                    rfl

theorem cell22_136890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_136890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136890 prefixEnd_136890 := by exact prefixLift 136890
  have htrace : WordTrace (prefixWord ++ tailWord_136890) baseStart_136890 baseEnd_136890 := by
    simpa [prefixWord, tailWord_136890, baseEnd_136890] using wordTrace_append hprefix tailTrace_136890
  have hstable : (prefixWord ++ tailWord_136890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136890).length < 2 ^ (prefixWord ++ tailWord_136890).sum := by decide
  have hdescent : baseEnd_136890 < baseStart_136890 := by decide
  rcases family_descends (prefixWord ++ tailWord_136890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136933 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 5, 3]
def baseStart_136933 : Nat := 118140960795 + 136933 * 2 ^ 59
def prefixEnd_136933 : Nat := 4983230072969 + 3 ^ 40 * 136933 * 2
def baseEnd_136933 : Nat := 46874964308145321805175

theorem tailTrace_136933 : CollatzResearch.WordTrace tailWord_136933 prefixEnd_136933 46874964308145321805175 := by
  unfold tailWord_136933
  simp only [CollatzResearch.WordTrace]
  refine ⟨4994356812922602139631453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3329571208615068093087635 4994356812922602139631453)
  ·
    refine ⟨1872883804845975802361795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4994356812922602139631453 1872883804845975802361795)
    ·
      refine ⟨2809325707268963703542693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1872883804845975802361795 2809325707268963703542693)
      ·
        refine ⟨526748570112930694414255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2809325707268963703542693 526748570112930694414255)
        ·
          refine ⟨790122855169396041621383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526748570112930694414255 790122855169396041621383)
          ·
            refine ⟨1185184282754094062432075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790122855169396041621383 1185184282754094062432075)
            ·
              refine ⟨1777776424131141093648113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185184282754094062432075 1777776424131141093648113)
              ·
                refine ⟨1333332318098355820236085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1777776424131141093648113 1333332318098355820236085)
                ·
                  refine ⟨124999904821720858147133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1333332318098355820236085 124999904821720858147133)
                  ·
                    refine ⟨46874964308145321805175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 124999904821720858147133 46874964308145321805175)
                    ·
                      rfl

theorem cell22_136933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_136933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136933 prefixEnd_136933 := by exact prefixLift 136933
  have htrace : WordTrace (prefixWord ++ tailWord_136933) baseStart_136933 baseEnd_136933 := by
    simpa [prefixWord, tailWord_136933, baseEnd_136933] using wordTrace_append hprefix tailTrace_136933
  have hstable : (prefixWord ++ tailWord_136933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136933).length < 2 ^ (prefixWord ++ tailWord_136933).sum := by decide
  have hdescent : baseEnd_136933 < baseStart_136933 := by decide
  rcases family_descends (prefixWord ++ tailWord_136933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136950 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_136950 : Nat := 118140960795 + 136950 * 2 ^ 59
def prefixEnd_136950 : Nat := 4983230072969 + 3 ^ 40 * 136950 * 2
def baseEnd_136950 : Nat := 46880783755562944130123

theorem tailTrace_136950 : CollatzResearch.WordTrace tailWord_136950 prefixEnd_136950 46880783755562944130123 := by
  unfold tailWord_136950
  simp only [CollatzResearch.WordTrace]
  refine ⟨312186053366313377687519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3329984569240676028666869 312186053366313377687519)
  ·
    refine ⟨468279080049470066531279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 312186053366313377687519 468279080049470066531279)
    ·
      refine ⟨702418620074205099796919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 468279080049470066531279 702418620074205099796919)
      ·
        refine ⟨1053627930111307649695379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 702418620074205099796919 1053627930111307649695379)
        ·
          refine ⟨1580441895166961474543069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053627930111307649695379 1580441895166961474543069)
          ·
            refine ⟨592665710687610552953651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1580441895166961474543069 592665710687610552953651)
            ·
              refine ⟨888998566031415829430477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592665710687610552953651 888998566031415829430477)
              ·
                refine ⟨333374462261780936036429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 888998566031415829430477 333374462261780936036429)
                ·
                  refine ⟨125015423348167851013661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333374462261780936036429 125015423348167851013661)
                  ·
                    refine ⟨46880783755562944130123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125015423348167851013661 46880783755562944130123)
                    ·
                      rfl

theorem cell22_136950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_136950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_136950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_136950 prefixEnd_136950 := by exact prefixLift 136950
  have htrace : WordTrace (prefixWord ++ tailWord_136950) baseStart_136950 baseEnd_136950 := by
    simpa [prefixWord, tailWord_136950, baseEnd_136950] using wordTrace_append hprefix tailTrace_136950
  have hstable : (prefixWord ++ tailWord_136950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136950).length < 2 ^ (prefixWord ++ tailWord_136950).sum := by decide
  have hdescent : baseEnd_136950 < baseStart_136950 := by decide
  rcases family_descends (prefixWord ++ tailWord_136950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137014 : List Nat := [5, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_137014 : Nat := 118140960795 + 137014 * 2 ^ 59
def prefixEnd_137014 : Nat := 4983230072969 + 3 ^ 40 * 137014 * 2
def baseEnd_137014 : Nat := 15634230754496036843309

theorem tailTrace_137014 : CollatzResearch.WordTrace tailWord_137014 prefixEnd_137014 15634230754496036843309 := by
  unfold tailWord_137014
  simp only [CollatzResearch.WordTrace]
  refine ⟨312331945351822060833131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3331540750419435315553397 312331945351822060833131)
  ·
    refine ⟨468497918027733091249697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 312331945351822060833131 468497918027733091249697)
    ·
      refine ⟨351373438520799818437273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 468497918027733091249697 351373438520799818437273)
      ·
        refine ⟨263530078890599863827955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351373438520799818437273 263530078890599863827955)
        ·
          refine ⟨395295118335899795741933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263530078890599863827955 395295118335899795741933)
          ·
            refine ⟨148235669375962423403225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 395295118335899795741933 148235669375962423403225)
            ·
              refine ⟨111176752031971817552419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148235669375962423403225 111176752031971817552419)
              ·
                refine ⟨166765128047957726328629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111176752031971817552419 166765128047957726328629)
                ·
                  refine ⟨15634230754496036843309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 166765128047957726328629 15634230754496036843309)
                  ·
                    rfl

theorem cell22_137014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_137014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137014 prefixEnd_137014 := by exact prefixLift 137014
  have htrace : WordTrace (prefixWord ++ tailWord_137014) baseStart_137014 baseEnd_137014 := by
    simpa [prefixWord, tailWord_137014, baseEnd_137014] using wordTrace_append hprefix tailTrace_137014
  have hstable : (prefixWord ++ tailWord_137014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137014).length < 2 ^ (prefixWord ++ tailWord_137014).sum := by decide
  have hdescent : baseEnd_137014 < baseStart_137014 := by decide
  rcases family_descends (prefixWord ++ tailWord_137014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137059 : List Nat := [1, 1, 1, 5, 4, 2, 2, 2, 4]
def baseStart_137059 : Nat := 118140960795 + 137059 * 2 ^ 59
def prefixEnd_137059 : Nat := 4983230072969 + 3 ^ 40 * 137059 * 2
def baseEnd_137059 : Nat := 15639365561040997718263

theorem tailTrace_137059 : CollatzResearch.WordTrace tailWord_137059 prefixEnd_137059 15639365561040997718263 := by
  unfold tailWord_137059
  simp only [CollatzResearch.WordTrace]
  refine ⟨4998952410466125658718231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3332634940310750439145487 4998952410466125658718231)
  ·
    refine ⟨7498428615699188488077347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4998952410466125658718231 7498428615699188488077347)
    ·
      refine ⟨11247642923548782732116021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7498428615699188488077347 11247642923548782732116021)
      ·
        refine ⟨1054466524082698381135877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11247642923548782732116021 1054466524082698381135877)
        ·
          refine ⟨197712473265505946462977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1054466524082698381135877 197712473265505946462977)
          ·
            refine ⟨148284354949129459847233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197712473265505946462977 148284354949129459847233)
            ·
              refine ⟨111213266211847094885425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148284354949129459847233 111213266211847094885425)
              ·
                refine ⟨83409949658885321164069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111213266211847094885425 83409949658885321164069)
                ·
                  refine ⟨15639365561040997718263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83409949658885321164069 15639365561040997718263)
                  ·
                    rfl

theorem cell22_137059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 4].length) (baseStart_137059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137059 prefixEnd_137059 := by exact prefixLift 137059
  have htrace : WordTrace (prefixWord ++ tailWord_137059) baseStart_137059 baseEnd_137059 := by
    simpa [prefixWord, tailWord_137059, baseEnd_137059] using wordTrace_append hprefix tailTrace_137059
  have hstable : (prefixWord ++ tailWord_137059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137059).length < 2 ^ (prefixWord ++ tailWord_137059).sum := by decide
  have hdescent : baseEnd_137059 < baseStart_137059 := by decide
  rcases family_descends (prefixWord ++ tailWord_137059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137070 : List Nat := [4, 1, 2, 3, 1, 1, 3, 7]
def baseStart_137070 : Nat := 118140960795 + 137070 * 2 ^ 59
def prefixEnd_137070 : Nat := 4983230072969 + 3 ^ 40 * 137070 * 2
def baseEnd_137070 : Nat := 5213540245324736792195

theorem tailTrace_137070 : CollatzResearch.WordTrace tailWord_137070 prefixEnd_137070 5213540245324736792195 := by
  unfold tailWord_137070
  simp only [CollatzResearch.WordTrace]
  refine ⟨624919201678284317171083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3332902408950849691579109 624919201678284317171083)
  ·
    refine ⟨937378802517426475756625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 624919201678284317171083 937378802517426475756625)
    ·
      refine ⟨703034101888069856817469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 937378802517426475756625 703034101888069856817469)
      ·
        refine ⟨263637788208026196306551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 703034101888069856817469 263637788208026196306551)
        ·
          refine ⟨395456682312039294459827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263637788208026196306551 395456682312039294459827)
          ·
            refine ⟨593185023468058941689741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395456682312039294459827 593185023468058941689741)
            ·
              refine ⟨222444383800522103133653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 593185023468058941689741 222444383800522103133653)
              ·
                refine ⟨5213540245324736792195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 222444383800522103133653 5213540245324736792195)
                ·
                  rfl

theorem cell22_137070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_137070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137070 prefixEnd_137070 := by exact prefixLift 137070
  have htrace : WordTrace (prefixWord ++ tailWord_137070) baseStart_137070 baseEnd_137070 := by
    simpa [prefixWord, tailWord_137070, baseEnd_137070] using wordTrace_append hprefix tailTrace_137070
  have hstable : (prefixWord ++ tailWord_137070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137070).length < 2 ^ (prefixWord ++ tailWord_137070).sum := by decide
  have hdescent : baseEnd_137070 < baseStart_137070 := by decide
  rcases family_descends (prefixWord ++ tailWord_137070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137089 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 2, 4]
def baseStart_137089 : Nat := 118140960795 + 137089 * 2 ^ 59
def prefixEnd_137089 : Nat := 4983230072969 + 3 ^ 40 * 137089 * 2
def baseEnd_137089 : Nat := 46928366296212914904697

theorem tailTrace_137089 : CollatzResearch.WordTrace tailWord_137089 prefixEnd_137089 46928366296212914904697 := by
  unfold tailWord_137089
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000046600357440782310321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3333364400238293854873547 5000046600357440782310321)
  ·
    refine ⟨3750034950268080586732741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5000046600357440782310321 3750034950268080586732741)
    ·
      refine ⟨703131553175265110012389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3750034950268080586732741 703131553175265110012389)
      ·
        refine ⟨131837166220362208127323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 703131553175265110012389 131837166220362208127323)
        ·
          refine ⟨197755749330543312190985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131837166220362208127323 197755749330543312190985)
          ·
            refine ⟨148316811997907484143239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197755749330543312190985 148316811997907484143239)
            ·
              refine ⟨222475217996861226214859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148316811997907484143239 222475217996861226214859)
              ·
                refine ⟨333712826995291839322289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222475217996861226214859 333712826995291839322289)
                ·
                  refine ⟨250284620246468879491717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333712826995291839322289 250284620246468879491717)
                  ·
                    refine ⟨46928366296212914904697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 250284620246468879491717 46928366296212914904697)
                    ·
                      rfl

theorem cell22_137089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_137089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137089 prefixEnd_137089 := by exact prefixLift 137089
  have htrace : WordTrace (prefixWord ++ tailWord_137089) baseStart_137089 baseEnd_137089 := by
    simpa [prefixWord, tailWord_137089, baseEnd_137089] using wordTrace_append hprefix tailTrace_137089
  have hstable : (prefixWord ++ tailWord_137089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137089).length < 2 ^ (prefixWord ++ tailWord_137089).sum := by decide
  have hdescent : baseEnd_137089 < baseStart_137089 := by decide
  rcases family_descends (prefixWord ++ tailWord_137089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137113 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 2, 5]
def baseStart_137113 : Nat := 118140960795 + 137113 * 2 ^ 59
def prefixEnd_137113 : Nat := 4983230072969 + 3 ^ 40 * 137113 * 2
def baseEnd_137113 : Nat := 46936581986684852304623

theorem tailTrace_137113 : CollatzResearch.WordTrace tailWord_137113 prefixEnd_137113 46936581986684852304623 := by
  unfold tailWord_137113
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000921952270492881183993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3333947968180328587455995 5000921952270492881183993)
  ·
    refine ⟨3750691464202869660887995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5000921952270492881183993 3750691464202869660887995)
    ·
      refine ⟨5626037196304304491331993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3750691464202869660887995 5626037196304304491331993)
      ·
        refine ⟨4219527897228228368498995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5626037196304304491331993 4219527897228228368498995)
        ·
          refine ⟨6329291845842342552748493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219527897228228368498995 6329291845842342552748493)
          ·
            refine ⟨2373484442190878457280685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6329291845842342552748493 2373484442190878457280685)
            ·
              refine ⟨890056665821579421480257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2373484442190878457280685 890056665821579421480257)
              ·
                refine ⟨667542499366184566110193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890056665821579421480257 667542499366184566110193)
                ·
                  refine ⟨500656874524638424582645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 667542499366184566110193 500656874524638424582645)
                  ·
                    refine ⟨46936581986684852304623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 500656874524638424582645 46936581986684852304623)
                    ·
                      rfl

theorem cell22_137113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_137113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137113 prefixEnd_137113 := by exact prefixLift 137113
  have htrace : WordTrace (prefixWord ++ tailWord_137113) baseStart_137113 baseEnd_137113 := by
    simpa [prefixWord, tailWord_137113, baseEnd_137113] using wordTrace_append hprefix tailTrace_137113
  have hstable : (prefixWord ++ tailWord_137113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137113).length < 2 ^ (prefixWord ++ tailWord_137113).sum := by decide
  have hdescent : baseEnd_137113 < baseStart_137113 := by decide
  rcases family_descends (prefixWord ++ tailWord_137113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137175 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 4, 3]
def baseStart_137175 : Nat := 118140960795 + 137175 * 2 ^ 59
def prefixEnd_137175 : Nat := 4983230072969 + 3 ^ 40 * 137175 * 2
def baseEnd_137175 : Nat := 46957805853737357254433

theorem tailTrace_137175 : CollatzResearch.WordTrace tailWord_137175 prefixEnd_137175 46957805853737357254433 := by
  unfold tailWord_137175
  simp only [CollatzResearch.WordTrace]
  refine ⟨5003183278045877469940979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3335455518697251646627319 5003183278045877469940979)
  ·
    refine ⟨7504774917068816204911469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5003183278045877469940979 7504774917068816204911469)
    ·
      refine ⟨2814290593900806076841801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7504774917068816204911469 2814290593900806076841801)
      ·
        refine ⟨2110717945425604557631351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2814290593900806076841801 2110717945425604557631351)
        ·
          refine ⟨3166076918138406836447027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2110717945425604557631351 3166076918138406836447027)
          ·
            refine ⟨4749115377207610254670541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3166076918138406836447027 4749115377207610254670541)
            ·
              refine ⟨1780918266452853845501453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4749115377207610254670541 1780918266452853845501453)
              ·
                refine ⟨667844349919820192063045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1780918266452853845501453 667844349919820192063045)
                ·
                  refine ⟨125220815609966286011821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 667844349919820192063045 125220815609966286011821)
                  ·
                    refine ⟨46957805853737357254433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125220815609966286011821 46957805853737357254433)
                    ·
                      rfl

theorem cell22_137175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_137175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137175 prefixEnd_137175 := by exact prefixLift 137175
  have htrace : WordTrace (prefixWord ++ tailWord_137175) baseStart_137175 baseEnd_137175 := by
    simpa [prefixWord, tailWord_137175, baseEnd_137175] using wordTrace_append hprefix tailTrace_137175
  have hstable : (prefixWord ++ tailWord_137175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137175).length < 2 ^ (prefixWord ++ tailWord_137175).sum := by decide
  have hdescent : baseEnd_137175 < baseStart_137175 := by decide
  rcases family_descends (prefixWord ++ tailWord_137175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137177 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 6]
def baseStart_137177 : Nat := 118140960795 + 137177 * 2 ^ 59
def prefixEnd_137177 : Nat := 4983230072969 + 3 ^ 40 * 137177 * 2
def baseEnd_137177 : Nat := 15652830164870006234809

theorem tailTrace_137177 : CollatzResearch.WordTrace tailWord_137177 prefixEnd_137177 15652830164870006234809 := by
  unfold tailWord_137177
  simp only [CollatzResearch.WordTrace]
  refine ⟨5003256224038631811513785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3335504149359087874342523 5003256224038631811513785)
  ·
    refine ⟨3752442168028973858635339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5003256224038631811513785 3752442168028973858635339)
    ·
      refine ⟨5628663252043460787953009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3752442168028973858635339 5628663252043460787953009)
      ·
        refine ⟨4221497439032595590964757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5628663252043460787953009 4221497439032595590964757)
        ·
          refine ⟨197882692454652918326473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4221497439032595590964757 197882692454652918326473)
          ·
            refine ⟨148412019340989688744855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197882692454652918326473 148412019340989688744855)
            ·
              refine ⟨222618029011484533117283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148412019340989688744855 222618029011484533117283)
              ·
                refine ⟨333927043517226799675925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222618029011484533117283 333927043517226799675925)
                ·
                  refine ⟨15652830164870006234809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 333927043517226799675925 15652830164870006234809)
                  ·
                    rfl

theorem cell22_137177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 6].length) (baseStart_137177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137177 prefixEnd_137177 := by exact prefixLift 137177
  have htrace : WordTrace (prefixWord ++ tailWord_137177) baseStart_137177 baseEnd_137177 := by
    simpa [prefixWord, tailWord_137177, baseEnd_137177] using wordTrace_append hprefix tailTrace_137177
  have hstable : (prefixWord ++ tailWord_137177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137177).length < 2 ^ (prefixWord ++ tailWord_137177).sum := by decide
  have hdescent : baseEnd_137177 < baseStart_137177 := by decide
  rcases family_descends (prefixWord ++ tailWord_137177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137203 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 2, 7]
def baseStart_137203 : Nat := 118140960795 + 137203 * 2 ^ 59
def prefixEnd_137203 : Nat := 4983230072969 + 3 ^ 40 * 137203 * 2
def baseEnd_137203 : Nat := 46967390825954617554347

theorem tailTrace_137203 : CollatzResearch.WordTrace tailWord_137203 prefixEnd_137203 46967390825954617554347 := by
  unfold tailWord_137203
  simp only [CollatzResearch.WordTrace]
  refine ⟨5004204521944438251960263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3336136347962958834640175 5004204521944438251960263)
  ·
    refine ⟨7506306782916657377940395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5004204521944438251960263 7506306782916657377940395)
    ·
      refine ⟨11259460174374986066910593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7506306782916657377940395 11259460174374986066910593)
      ·
        refine ⟨8444595130781239550182945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11259460174374986066910593 8444595130781239550182945)
        ·
          refine ⟨6333446348085929662637209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8444595130781239550182945 6333446348085929662637209)
          ·
            refine ⟨4750084761064447246977907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6333446348085929662637209 4750084761064447246977907)
            ·
              refine ⟨7125127141596670870466861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4750084761064447246977907 7125127141596670870466861)
              ·
                refine ⟨2671922678098751576425073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7125127141596670870466861 2671922678098751576425073)
                ·
                  refine ⟨2003942008574063682318805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2671922678098751576425073 2003942008574063682318805)
                  ·
                    refine ⟨46967390825954617554347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2003942008574063682318805 46967390825954617554347)
                    ·
                      rfl

theorem cell22_137203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_137203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137203 prefixEnd_137203 := by exact prefixLift 137203
  have htrace : WordTrace (prefixWord ++ tailWord_137203) baseStart_137203 baseEnd_137203 := by
    simpa [prefixWord, tailWord_137203, baseEnd_137203] using wordTrace_append hprefix tailTrace_137203
  have hstable : (prefixWord ++ tailWord_137203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137203).length < 2 ^ (prefixWord ++ tailWord_137203).sum := by decide
  have hdescent : baseEnd_137203 < baseStart_137203 := by decide
  rcases family_descends (prefixWord ++ tailWord_137203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137239 : List Nat := [1, 1, 3, 5, 3, 1, 1, 7]
def baseStart_137239 : Nat := 118140960795 + 137239 * 2 ^ 59
def prefixEnd_137239 : Nat := 4983230072969 + 3 ^ 40 * 137239 * 2
def baseEnd_137239 : Nat := 5219968262406947072693

theorem tailTrace_137239 : CollatzResearch.WordTrace tailWord_137239 prefixEnd_137239 5219968262406947072693 := by
  unfold tailWord_137239
  simp only [CollatzResearch.WordTrace]
  refine ⟨5005517549814016400270771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3337011699876010933513847 5005517549814016400270771)
  ·
    refine ⟨7508276324721024600406157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5005517549814016400270771 7508276324721024600406157)
    ·
      refine ⟨2815603621770384225152309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7508276324721024600406157 2815603621770384225152309)
      ·
        refine ⟨263962839540973521108029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2815603621770384225152309 263962839540973521108029)
        ·
          refine ⟨98986064827865070415511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263962839540973521108029 98986064827865070415511)
          ·
            refine ⟨148479097241797605623267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98986064827865070415511 148479097241797605623267)
            ·
              refine ⟨222718645862696408434901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148479097241797605623267 222718645862696408434901)
              ·
                refine ⟨5219968262406947072693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 222718645862696408434901 5219968262406947072693)
                ·
                  rfl

theorem cell22_137239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 7].length) (baseStart_137239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137239 prefixEnd_137239 := by exact prefixLift 137239
  have htrace : WordTrace (prefixWord ++ tailWord_137239) baseStart_137239 baseEnd_137239 := by
    simpa [prefixWord, tailWord_137239, baseEnd_137239] using wordTrace_append hprefix tailTrace_137239
  have hstable : (prefixWord ++ tailWord_137239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137239).length < 2 ^ (prefixWord ++ tailWord_137239).sum := by decide
  have hdescent : baseEnd_137239 < baseStart_137239 := by decide
  rcases family_descends (prefixWord ++ tailWord_137239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137327 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 4, 3]
def baseStart_137327 : Nat := 118140960795 + 137327 * 2 ^ 59
def prefixEnd_137327 : Nat := 4983230072969 + 3 ^ 40 * 137327 * 2
def baseEnd_137327 : Nat := 47009838560059627453967

theorem tailTrace_137327 : CollatzResearch.WordTrace tailWord_137327 prefixEnd_137327 47009838560059627453967 := by
  unfold tailWord_137327
  simp only [CollatzResearch.WordTrace]
  refine ⟨5008727173495207429474235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3339151448996804952982823 5008727173495207429474235)
  ·
    refine ⟨7513090760242811144211353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5008727173495207429474235 7513090760242811144211353)
    ·
      refine ⟨5634818070182108358158515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7513090760242811144211353 5634818070182108358158515)
      ·
        refine ⟨8452227105273162537237773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5634818070182108358158515 8452227105273162537237773)
        ·
          refine ⟨3169585164477435951464165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8452227105273162537237773 3169585164477435951464165)
          ·
            refine ⟨594297218339519240899531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3169585164477435951464165 594297218339519240899531)
            ·
              refine ⟨891445827509278861349297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594297218339519240899531 891445827509278861349297)
              ·
                refine ⟨668584370631959146011973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891445827509278861349297 668584370631959146011973)
                ·
                  refine ⟨125359569493492339877245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 668584370631959146011973 125359569493492339877245)
                  ·
                    refine ⟨47009838560059627453967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125359569493492339877245 47009838560059627453967)
                    ·
                      rfl

theorem cell22_137327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 3].length) (baseStart_137327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137327 prefixEnd_137327 := by exact prefixLift 137327
  have htrace : WordTrace (prefixWord ++ tailWord_137327) baseStart_137327 baseEnd_137327 := by
    simpa [prefixWord, tailWord_137327, baseEnd_137327] using wordTrace_append hprefix tailTrace_137327
  have hstable : (prefixWord ++ tailWord_137327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137327).length < 2 ^ (prefixWord ++ tailWord_137327).sum := by decide
  have hdescent : baseEnd_137327 < baseStart_137327 := by decide
  rcases family_descends (prefixWord ++ tailWord_137327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137340 : List Nat := [2, 2, 2, 1, 1, 4, 10]
def baseStart_137340 : Nat := 118140960795 + 137340 * 2 ^ 59
def prefixEnd_137340 : Nat := 4983230072969 + 3 ^ 40 * 137340 * 2
def baseEnd_137340 : Nat := 1741269952804886180701

theorem tailTrace_137340 : CollatzResearch.WordTrace tailWord_137340 prefixEnd_137340 1741269952804886180701 := by
  unfold tailWord_137340
  simp only [CollatzResearch.WordTrace]
  refine ⟨2504600661224055324848737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3339467548298740433131649 2504600661224055324848737)
  ·
    refine ⟨1878450495918041493636553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2504600661224055324848737 1878450495918041493636553)
    ·
      refine ⟨1408837871938531120227415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1878450495918041493636553 1408837871938531120227415)
      ·
        refine ⟨2113256807907796680341123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408837871938531120227415 2113256807907796680341123)
        ·
          refine ⟨3169885211861695020511685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2113256807907796680341123 3169885211861695020511685)
          ·
            refine ⟨594353477224067816345941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3169885211861695020511685 594353477224067816345941)
            ·
              refine ⟨1741269952804886180701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 594353477224067816345941 1741269952804886180701)
              ·
                rfl

theorem cell22_137340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 10].length) (baseStart_137340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137340 prefixEnd_137340 := by exact prefixLift 137340
  have htrace : WordTrace (prefixWord ++ tailWord_137340) baseStart_137340 baseEnd_137340 := by
    simpa [prefixWord, tailWord_137340, baseEnd_137340] using wordTrace_append hprefix tailTrace_137340
  have hstable : (prefixWord ++ tailWord_137340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137340).length < 2 ^ (prefixWord ++ tailWord_137340).sum := by decide
  have hdescent : baseEnd_137340 < baseStart_137340 := by decide
  rcases family_descends (prefixWord ++ tailWord_137340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137402 : List Nat := [3, 1, 1, 1, 2, 2, 3, 4, 5]
def baseStart_137402 : Nat := 118140960795 + 137402 * 2 ^ 59
def prefixEnd_137402 : Nat := 4983230072969 + 3 ^ 40 * 137402 * 2
def baseEnd_137402 : Nat := 15678504197594810609579

theorem tailTrace_137402 : CollatzResearch.WordTrace tailWord_137402 prefixEnd_137402 15678504197594810609579 := by
  unfold tailWord_137402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1252865662055873809613615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3340975098815663492302973 1252865662055873809613615)
  ·
    refine ⟨1879298493083810714420423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1252865662055873809613615 1879298493083810714420423)
    ·
      refine ⟨2818947739625716071630635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1879298493083810714420423 2818947739625716071630635)
      ·
        refine ⟨4228421609438574107445953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2818947739625716071630635 4228421609438574107445953)
        ·
          refine ⟨3171316207078930580584465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4228421609438574107445953 3171316207078930580584465)
          ·
            refine ⟨2378487155309197935438349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3171316207078930580584465 2378487155309197935438349)
            ·
              refine ⟨891932683240949225789381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2378487155309197935438349 891932683240949225789381)
              ·
                refine ⟨167237378107677979835509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 891932683240949225789381 167237378107677979835509)
                ·
                  refine ⟨15678504197594810609579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167237378107677979835509 15678504197594810609579)
                  ·
                    rfl

theorem cell22_137402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_137402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137402 prefixEnd_137402 := by exact prefixLift 137402
  have htrace : WordTrace (prefixWord ++ tailWord_137402) baseStart_137402 baseEnd_137402 := by
    simpa [prefixWord, tailWord_137402, baseEnd_137402] using wordTrace_append hprefix tailTrace_137402
  have hstable : (prefixWord ++ tailWord_137402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137402).length < 2 ^ (prefixWord ++ tailWord_137402).sum := by decide
  have hdescent : baseEnd_137402 < baseStart_137402 := by decide
  rcases family_descends (prefixWord ++ tailWord_137402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137453 : List Nat := [1, 5, 1, 2, 4, 1, 1, 2, 5]
def baseStart_137453 : Nat := 118140960795 + 137453 * 2 ^ 59
def prefixEnd_137453 : Nat := 4983230072969 + 3 ^ 40 * 137453 * 2
def baseEnd_137453 : Nat := 15684323645012432934527

theorem tailTrace_137453 : CollatzResearch.WordTrace tailWord_137453 prefixEnd_137453 15684323645012432934527 := by
  unfold tailWord_137453
  simp only [CollatzResearch.WordTrace]
  refine ⟨5013322771038730948561013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3342215180692487299040675 5013322771038730948561013)
  ·
    refine ⟨469999009784881026427595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5013322771038730948561013 469999009784881026427595)
    ·
      refine ⟨704998514677321539641393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 469999009784881026427595 704998514677321539641393)
      ·
        refine ⟨528748886007991154731045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 704998514677321539641393 528748886007991154731045)
        ·
          refine ⟨99140416126498341512071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 528748886007991154731045 99140416126498341512071)
          ·
            refine ⟨148710624189747512268107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99140416126498341512071 148710624189747512268107)
            ·
              refine ⟨223065936284621268402161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148710624189747512268107 223065936284621268402161)
              ·
                refine ⟨167299452213465951301621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223065936284621268402161 167299452213465951301621)
                ·
                  refine ⟨15684323645012432934527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167299452213465951301621 15684323645012432934527)
                  ·
                    rfl

theorem cell22_137453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_137453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137453 prefixEnd_137453 := by exact prefixLift 137453
  have htrace : WordTrace (prefixWord ++ tailWord_137453) baseStart_137453 baseEnd_137453 := by
    simpa [prefixWord, tailWord_137453, baseEnd_137453] using wordTrace_append hprefix tailTrace_137453
  have hstable : (prefixWord ++ tailWord_137453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137453).length < 2 ^ (prefixWord ++ tailWord_137453).sum := by decide
  have hdescent : baseEnd_137453 < baseStart_137453 := by decide
  rcases family_descends (prefixWord ++ tailWord_137453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137477 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_137477 : Nat := 118140960795 + 137477 * 2 ^ 59
def prefixEnd_137477 : Nat := 4983230072969 + 3 ^ 40 * 137477 * 2
def baseEnd_137477 : Nat := 47061186625509236203507

theorem tailTrace_137477 : CollatzResearch.WordTrace tailWord_137477 prefixEnd_137477 47061186625509236203507 := by
  unfold tailWord_137477
  simp only [CollatzResearch.WordTrace]
  refine ⟨5014198122951783047434685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3342798748634522031623123 5014198122951783047434685)
  ·
    refine ⟨1880324296106918642788007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5014198122951783047434685 1880324296106918642788007)
    ·
      refine ⟨2820486444160377964182011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1880324296106918642788007 2820486444160377964182011)
      ·
        refine ⟨4230729666240566946273017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820486444160377964182011 4230729666240566946273017)
        ·
          refine ⟨3173047249680425209704763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4230729666240566946273017 3173047249680425209704763)
          ·
            refine ⟨4759570874520637814557145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173047249680425209704763 4759570874520637814557145)
            ·
              refine ⟨3569678155890478360917859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4759570874520637814557145 3569678155890478360917859)
              ·
                refine ⟨5354517233835717541376789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3569678155890478360917859 5354517233835717541376789)
                ·
                  refine ⟨250992995336049259752037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5354517233835717541376789 250992995336049259752037)
                  ·
                    refine ⟨47061186625509236203507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 250992995336049259752037 47061186625509236203507)
                    ·
                      rfl

theorem cell22_137477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_137477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137477 prefixEnd_137477 := by exact prefixLift 137477
  have htrace : WordTrace (prefixWord ++ tailWord_137477) baseStart_137477 baseEnd_137477 := by
    simpa [prefixWord, tailWord_137477, baseEnd_137477] using wordTrace_append hprefix tailTrace_137477
  have hstable : (prefixWord ++ tailWord_137477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137477).length < 2 ^ (prefixWord ++ tailWord_137477).sum := by decide
  have hdescent : baseEnd_137477 < baseStart_137477 := by decide
  rcases family_descends (prefixWord ++ tailWord_137477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137498 : List Nat := [3, 1, 1, 3, 4, 2, 1, 3, 4]
def baseStart_137498 : Nat := 118140960795 + 137498 * 2 ^ 59
def prefixEnd_137498 : Nat := 4983230072969 + 3 ^ 40 * 137498 * 2
def baseEnd_137498 : Nat := 15689458451557393809481

theorem tailTrace_137498 : CollatzResearch.WordTrace tailWord_137498 prefixEnd_137498 15689458451557393809481 := by
  unfold tailWord_137498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253741013968925908487287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3343309370583802422632765 1253741013968925908487287)
  ·
    refine ⟨1880611520953388862730931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1253741013968925908487287 1880611520953388862730931)
    ·
      refine ⟨2820917281430083294096397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1880611520953388862730931 2820917281430083294096397)
      ·
        refine ⟨1057843980536281235286149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2820917281430083294096397 1057843980536281235286149)
        ·
          refine ⟨198345746350552731616153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1057843980536281235286149 198345746350552731616153)
          ·
            refine ⟨148759309762914548712115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198345746350552731616153 148759309762914548712115)
            ·
              refine ⟨223138964644371823068173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148759309762914548712115 223138964644371823068173)
              ·
                refine ⟨83677111741639433650565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223138964644371823068173 83677111741639433650565)
                ·
                  refine ⟨15689458451557393809481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83677111741639433650565 15689458451557393809481)
                  ·
                    rfl

theorem cell22_137498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_137498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137498 prefixEnd_137498 := by exact prefixLift 137498
  have htrace : WordTrace (prefixWord ++ tailWord_137498) baseStart_137498 baseEnd_137498 := by
    simpa [prefixWord, tailWord_137498, baseEnd_137498] using wordTrace_append hprefix tailTrace_137498
  have hstable : (prefixWord ++ tailWord_137498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137498).length < 2 ^ (prefixWord ++ tailWord_137498).sum := by decide
  have hdescent : baseEnd_137498 < baseStart_137498 := by decide
  rcases family_descends (prefixWord ++ tailWord_137498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137509 : List Nat := [1, 3, 1, 2, 5, 2, 8]
def baseStart_137509 : Nat := 118140960795 + 137509 * 2 ^ 59
def prefixEnd_137509 : Nat := 4983230072969 + 3 ^ 40 * 137509 * 2
def baseEnd_137509 : Nat := 1743412625165622940867

theorem tailTrace_137509 : CollatzResearch.WordTrace tailWord_137509 prefixEnd_137509 1743412625165622940867 := by
  unfold tailWord_137509
  simp only [CollatzResearch.WordTrace]
  refine ⟨5015365258835852512599581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3343576839223901675066387 5015365258835852512599581)
  ·
    refine ⟨1880761972063444692224843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5015365258835852512599581 1880761972063444692224843)
    ·
      refine ⟨2821142958095167038337265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1880761972063444692224843 2821142958095167038337265)
      ·
        refine ⟨2115857218571375278752949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2821142958095167038337265 2115857218571375278752949)
        ·
          refine ⟨198361614241066432383089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2115857218571375278752949 198361614241066432383089)
          ·
            refine ⟨148771210680799824287317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198361614241066432383089 148771210680799824287317)
            ·
              refine ⟨1743412625165622940867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 148771210680799824287317 1743412625165622940867)
              ·
                rfl

theorem cell22_137509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 8].length) (baseStart_137509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137509 prefixEnd_137509 := by exact prefixLift 137509
  have htrace : WordTrace (prefixWord ++ tailWord_137509) baseStart_137509 baseEnd_137509 := by
    simpa [prefixWord, tailWord_137509, baseEnd_137509] using wordTrace_append hprefix tailTrace_137509
  have hstable : (prefixWord ++ tailWord_137509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137509).length < 2 ^ (prefixWord ++ tailWord_137509).sum := by decide
  have hdescent : baseEnd_137509 < baseStart_137509 := by decide
  rcases family_descends (prefixWord ++ tailWord_137509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137566 : List Nat := [4, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_137566 : Nat := 118140960795 + 137566 * 2 ^ 59
def prefixEnd_137566 : Nat := 4983230072969 + 3 ^ 40 * 137566 * 2
def baseEnd_137566 : Nat := 15697217714780890242745

theorem tailTrace_137566 : CollatzResearch.WordTrace tailWord_137566 prefixEnd_137566 15697217714780890242745 := by
  unfold tailWord_137566
  simp only [CollatzResearch.WordTrace]
  refine ⟨627180527453668905928069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3344962813086234164949701 627180527453668905928069)
  ·
    refine ⟨117596348897562919861513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 627180527453668905928069 117596348897562919861513)
    ·
      refine ⟨88197261673172189896135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117596348897562919861513 88197261673172189896135)
      ·
        refine ⟨132295892509758284844203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88197261673172189896135 132295892509758284844203)
        ·
          refine ⟨198443838764637427266305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132295892509758284844203 198443838764637427266305)
          ·
            refine ⟨148832879073478070449729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198443838764637427266305 148832879073478070449729)
            ·
              refine ⟨111624659305108552837297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148832879073478070449729 111624659305108552837297)
              ·
                refine ⟨83718494478831414627973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111624659305108552837297 83718494478831414627973)
                ·
                  refine ⟨15697217714780890242745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83718494478831414627973 15697217714780890242745)
                  ·
                    rfl

theorem cell22_137566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_137566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137566 prefixEnd_137566 := by exact prefixLift 137566
  have htrace : WordTrace (prefixWord ++ tailWord_137566) baseStart_137566 baseEnd_137566 := by
    simpa [prefixWord, tailWord_137566, baseEnd_137566] using wordTrace_append hprefix tailTrace_137566
  have hstable : (prefixWord ++ tailWord_137566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137566).length < 2 ^ (prefixWord ++ tailWord_137566).sum := by decide
  have hdescent : baseEnd_137566 < baseStart_137566 := by decide
  rcases family_descends (prefixWord ++ tailWord_137566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137575 : List Nat := [1, 1, 5, 1, 3, 1, 4, 2, 1, 3]
def baseStart_137575 : Nat := 118140960795 + 137575 * 2 ^ 59
def prefixEnd_137575 : Nat := 4983230072969 + 3 ^ 40 * 137575 * 2
def baseEnd_137575 : Nat := 47094734028269647253207

theorem tailTrace_137575 : CollatzResearch.WordTrace tailWord_137575 prefixEnd_137575 47094734028269647253207 := by
  unfold tailWord_137575
  simp only [CollatzResearch.WordTrace]
  refine ⟨5017772476596745784502179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3345181651064497189668119 5017772476596745784502179)
  ·
    refine ⟨7526658714895118676753269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5017772476596745784502179 7526658714895118676753269)
    ·
      refine ⟨705624254521417375945619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7526658714895118676753269 705624254521417375945619)
      ·
        refine ⟨1058436381782126063918429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705624254521417375945619 1058436381782126063918429)
        ·
          refine ⟨396913643168297273969411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1058436381782126063918429 396913643168297273969411)
          ·
            refine ⟨595370464752445910954117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396913643168297273969411 595370464752445910954117)
            ·
              refine ⟨111631962141083608303897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 595370464752445910954117 111631962141083608303897)
              ·
                refine ⟨83723971605812706227923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111631962141083608303897 83723971605812706227923)
                ·
                  refine ⟨125585957408719059341885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83723971605812706227923 125585957408719059341885)
                  ·
                    refine ⟨47094734028269647253207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125585957408719059341885 47094734028269647253207)
                    ·
                      rfl

theorem cell22_137575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_137575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137575 prefixEnd_137575 := by exact prefixLift 137575
  have htrace : WordTrace (prefixWord ++ tailWord_137575) baseStart_137575 baseEnd_137575 := by
    simpa [prefixWord, tailWord_137575, baseEnd_137575] using wordTrace_append hprefix tailTrace_137575
  have hstable : (prefixWord ++ tailWord_137575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137575).length < 2 ^ (prefixWord ++ tailWord_137575).sum := by decide
  have hdescent : baseEnd_137575 < baseStart_137575 := by decide
  rcases family_descends (prefixWord ++ tailWord_137575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137584 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 3, 4]
def baseStart_137584 : Nat := 118140960795 + 137584 * 2 ^ 59
def prefixEnd_137584 : Nat := 4983230072969 + 3 ^ 40 * 137584 * 2
def baseEnd_137584 : Nat := 47097814912196623778179

theorem tailTrace_137584 : CollatzResearch.WordTrace tailWord_137584 prefixEnd_137584 47097814912196623778179 := by
  unfold tailWord_137584
  simp only [CollatzResearch.WordTrace]
  refine ⟨2509050366782070160789903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3345400489042760214386537 2509050366782070160789903)
  ·
    refine ⟨3763575550173105241184855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2509050366782070160789903 3763575550173105241184855)
    ·
      refine ⟨5645363325259657861777283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3763575550173105241184855 5645363325259657861777283)
      ·
        refine ⟨8468044987889486792665925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5645363325259657861777283 8468044987889486792665925)
        ·
          refine ⟨1587758435229278773624861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8468044987889486792665925 1587758435229278773624861)
          ·
            refine ⟨595409413210979540109323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1587758435229278773624861 595409413210979540109323)
            ·
              refine ⟨893114119816469310163985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595409413210979540109323 893114119816469310163985)
              ·
                refine ⟨669835589862351982622989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893114119816469310163985 669835589862351982622989)
                ·
                  refine ⟨251188346198381993483621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 669835589862351982622989 251188346198381993483621)
                  ·
                    refine ⟨47097814912196623778179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 251188346198381993483621 47097814912196623778179)
                    ·
                      rfl

theorem cell22_137584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_137584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137584 prefixEnd_137584 := by exact prefixLift 137584
  have htrace : WordTrace (prefixWord ++ tailWord_137584) baseStart_137584 baseEnd_137584 := by
    simpa [prefixWord, tailWord_137584, baseEnd_137584] using wordTrace_append hprefix tailTrace_137584
  have hstable : (prefixWord ++ tailWord_137584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137584).length < 2 ^ (prefixWord ++ tailWord_137584).sum := by decide
  have hdescent : baseEnd_137584 < baseStart_137584 := by decide
  rcases family_descends (prefixWord ++ tailWord_137584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137601 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 3, 4]
def baseStart_137601 : Nat := 118140960795 + 137601 * 2 ^ 59
def prefixEnd_137601 : Nat := 4983230072969 + 3 ^ 40 * 137601 * 2
def baseEnd_137601 : Nat := 47103634359614246103127

theorem tailTrace_137601 : CollatzResearch.WordTrace tailWord_137601 prefixEnd_137601 47103634359614246103127 := by
  unfold tailWord_137601
  simp only [CollatzResearch.WordTrace]
  refine ⟨5018720774502552224948657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3345813849668368149965771 5018720774502552224948657)
  ·
    refine ⟨3764040580876914168711493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5018720774502552224948657 3764040580876914168711493)
    ·
      refine ⟨705757608914421406633405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3764040580876914168711493 705757608914421406633405)
      ·
        refine ⟨264659103342908027487527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 705757608914421406633405 264659103342908027487527)
        ·
          refine ⟨396988655014362041231291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264659103342908027487527 396988655014362041231291)
          ·
            refine ⟨595482982521543061846937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396988655014362041231291 595482982521543061846937)
            ·
              refine ⟨446612236891157296385203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595482982521543061846937 446612236891157296385203)
              ·
                refine ⟨669918355336735944577805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446612236891157296385203 669918355336735944577805)
                ·
                  refine ⟨251219383251275979216677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 669918355336735944577805 251219383251275979216677)
                  ·
                    refine ⟨47103634359614246103127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 251219383251275979216677 47103634359614246103127)
                    ·
                      rfl

theorem cell22_137601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_137601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137601 prefixEnd_137601 := by exact prefixLift 137601
  have htrace : WordTrace (prefixWord ++ tailWord_137601) baseStart_137601 baseEnd_137601 := by
    simpa [prefixWord, tailWord_137601, baseEnd_137601] using wordTrace_append hprefix tailTrace_137601
  have hstable : (prefixWord ++ tailWord_137601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137601).length < 2 ^ (prefixWord ++ tailWord_137601).sum := by decide
  have hdescent : baseEnd_137601 < baseStart_137601 := by decide
  rcases family_descends (prefixWord ++ tailWord_137601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137631 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 4, 3]
def baseStart_137631 : Nat := 118140960795 + 137631 * 2 ^ 59
def prefixEnd_137631 : Nat := 4983230072969 + 3 ^ 40 * 137631 * 2
def baseEnd_137631 : Nat := 47113903972704167853035

theorem tailTrace_137631 : CollatzResearch.WordTrace tailWord_137631 prefixEnd_137631 47113903972704167853035 := by
  unfold tailWord_137631
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019814964393867348540747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3346543309595911565693831 5019814964393867348540747)
  ·
    refine ⟨7529722446590801022811121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5019814964393867348540747 7529722446590801022811121)
    ·
      refine ⟨5647291834943100767108341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7529722446590801022811121 5647291834943100767108341)
      ·
        refine ⟨529433609525915696916407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5647291834943100767108341 529433609525915696916407)
        ·
          refine ⟨794150414288873545374611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529433609525915696916407 794150414288873545374611)
          ·
            refine ⟨1191225621433310318061917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794150414288873545374611 1191225621433310318061917)
            ·
              refine ⟨446709608037491369273219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1191225621433310318061917 446709608037491369273219)
              ·
                refine ⟨670064412056237053909829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446709608037491369273219 670064412056237053909829)
                ·
                  refine ⟨125637077260544447608093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 670064412056237053909829 125637077260544447608093)
                  ·
                    refine ⟨47113903972704167853035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125637077260544447608093 47113903972704167853035)
                    ·
                      rfl

theorem cell22_137631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 3].length) (baseStart_137631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137631 prefixEnd_137631 := by exact prefixLift 137631
  have htrace : WordTrace (prefixWord ++ tailWord_137631) baseStart_137631 baseEnd_137631 := by
    simpa [prefixWord, tailWord_137631, baseEnd_137631] using wordTrace_append hprefix tailTrace_137631
  have hstable : (prefixWord ++ tailWord_137631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137631).length < 2 ^ (prefixWord ++ tailWord_137631).sum := by decide
  have hdescent : baseEnd_137631 < baseStart_137631 := by decide
  rcases family_descends (prefixWord ++ tailWord_137631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137633 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 6]
def baseStart_137633 : Nat := 118140960795 + 137633 * 2 ^ 59
def prefixEnd_137633 : Nat := 4983230072969 + 3 ^ 40 * 137633 * 2
def baseEnd_137633 : Nat := 15704862871192276434343

theorem tailTrace_137633 : CollatzResearch.WordTrace tailWord_137633 prefixEnd_137633 15704862871192276434343 := by
  unfold tailWord_137633
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019887910386621690113553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3346591940257747793409035 5019887910386621690113553)
  ·
    refine ⟨3764915932789966267585165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5019887910386621690113553 3764915932789966267585165)
    ·
      refine ⟨1411843474796237350344437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3764915932789966267585165 1411843474796237350344437)
      ·
        refine ⟨132360325762147251594791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1411843474796237350344437 132360325762147251594791)
        ·
          refine ⟨198540488643220877392187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132360325762147251594791 198540488643220877392187)
          ·
            refine ⟨297810732964831316088281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198540488643220877392187 297810732964831316088281)
            ·
              refine ⟨223358049723623487066211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297810732964831316088281 223358049723623487066211)
              ·
                refine ⟨335037074585435230599317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223358049723623487066211 335037074585435230599317)
                ·
                  refine ⟨15704862871192276434343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 335037074585435230599317 15704862871192276434343)
                  ·
                    rfl

theorem cell22_137633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 6].length) (baseStart_137633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137633 prefixEnd_137633 := by exact prefixLift 137633
  have htrace : WordTrace (prefixWord ++ tailWord_137633) baseStart_137633 baseEnd_137633 := by
    simpa [prefixWord, tailWord_137633, baseEnd_137633] using wordTrace_append hprefix tailTrace_137633
  have hstable : (prefixWord ++ tailWord_137633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137633).length < 2 ^ (prefixWord ++ tailWord_137633).sum := by decide
  have hdescent : baseEnd_137633 < baseStart_137633 := by decide
  rcases family_descends (prefixWord ++ tailWord_137633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137652 : List Nat := [2, 5, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_137652 : Nat := 118140960795 + 137652 * 2 ^ 59
def prefixEnd_137652 : Nat := 4983230072969 + 3 ^ 40 * 137652 * 2
def baseEnd_137652 : Nat := 47121092701867113077971

theorem tailTrace_137652 : CollatzResearch.WordTrace tailWord_137652 prefixEnd_137652 47121092701867113077971 := by
  unfold tailWord_137652
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510290448658893967527605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3347053931545191956703473 2510290448658893967527605)
  ·
    refine ⟨235339729561771309455713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2510290448658893967527605 235339729561771309455713)
    ·
      refine ⟨176504797171328482091785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235339729561771309455713 176504797171328482091785)
      ·
        refine ⟨132378597878496361568839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176504797171328482091785 132378597878496361568839)
        ·
          refine ⟨198567896817744542353259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132378597878496361568839 198567896817744542353259)
          ·
            refine ⟨297851845226616813529889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198567896817744542353259 297851845226616813529889)
            ·
              refine ⟨223388883919962610147417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297851845226616813529889 223388883919962610147417)
              ·
                refine ⟨167541662939971957610563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223388883919962610147417 167541662939971957610563)
                ·
                  refine ⟨251312494409957936415845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167541662939971957610563 251312494409957936415845)
                  ·
                    refine ⟨47121092701867113077971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 251312494409957936415845 47121092701867113077971)
                    ·
                      rfl

theorem cell22_137652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_137652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137652 prefixEnd_137652 := by exact prefixLift 137652
  have htrace : WordTrace (prefixWord ++ tailWord_137652) baseStart_137652 baseEnd_137652 := by
    simpa [prefixWord, tailWord_137652, baseEnd_137652] using wordTrace_append hprefix tailTrace_137652
  have hstable : (prefixWord ++ tailWord_137652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137652).length < 2 ^ (prefixWord ++ tailWord_137652).sum := by decide
  have hdescent : baseEnd_137652 < baseStart_137652 := by decide
  rcases family_descends (prefixWord ++ tailWord_137652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137661 : List Nat := [1, 4, 1, 2, 2, 2, 4, 6]
def baseStart_137661 : Nat := 118140960795 + 137661 * 2 ^ 59
def prefixEnd_137661 : Nat := 4983230072969 + 3 ^ 40 * 137661 * 2
def baseEnd_137661 : Nat := 5236019287310454400327

theorem tailTrace_137661 : CollatzResearch.WordTrace tailWord_137661 prefixEnd_137661 5236019287310454400327 := by
  unfold tailWord_137661
  simp only [CollatzResearch.WordTrace]
  refine ⟨5020909154285182472132837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3347272769523454981421891 5020909154285182472132837)
  ·
    refine ⟨941420466428471713524907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5020909154285182472132837 941420466428471713524907)
    ·
      refine ⟨1412130699642707570287361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 941420466428471713524907 1412130699642707570287361)
      ·
        refine ⟨1059098024732030677715521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1412130699642707570287361 1059098024732030677715521)
        ·
          refine ⟨794323518549023008286641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1059098024732030677715521 794323518549023008286641)
          ·
            refine ⟨595742638911767256214981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794323518549023008286641 595742638911767256214981)
            ·
              refine ⟨111701744795956360540309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 595742638911767256214981 111701744795956360540309)
              ·
                refine ⟨5236019287310454400327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111701744795956360540309 5236019287310454400327)
                ·
                  rfl

theorem cell22_137661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 6].length) (baseStart_137661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137661 prefixEnd_137661 := by exact prefixLift 137661
  have htrace : WordTrace (prefixWord ++ tailWord_137661) baseStart_137661 baseEnd_137661 := by
    simpa [prefixWord, tailWord_137661, baseEnd_137661] using wordTrace_append hprefix tailTrace_137661
  have hstable : (prefixWord ++ tailWord_137661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137661).length < 2 ^ (prefixWord ++ tailWord_137661).sum := by decide
  have hdescent : baseEnd_137661 < baseStart_137661 := by decide
  rcases family_descends (prefixWord ++ tailWord_137661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137689 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 7]
def baseStart_137689 : Nat := 118140960795 + 137689 * 2 ^ 59
def prefixEnd_137689 : Nat := 4983230072969 + 3 ^ 40 * 137689 * 2
def baseEnd_137689 : Nat := 15711252852670449967619

theorem tailTrace_137689 : CollatzResearch.WordTrace tailWord_137689 prefixEnd_137689 15711252852670449967619 := by
  unfold tailWord_137689
  simp only [CollatzResearch.WordTrace]
  refine ⟨5021930398183743254152121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3347953598789162169434747 5021930398183743254152121)
  ·
    refine ⟨3766447798637807440614091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5021930398183743254152121 3766447798637807440614091)
    ·
      refine ⟨5649671697956711160921137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3766447798637807440614091 5649671697956711160921137)
      ·
        refine ⟨4237253773467533370690853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5649671697956711160921137 4237253773467533370690853)
        ·
          refine ⟨794485082525162507004535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4237253773467533370690853 794485082525162507004535)
          ·
            refine ⟨1191727623787743760506803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794485082525162507004535 1191727623787743760506803)
            ·
              refine ⟨1787591435681615640760205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191727623787743760506803 1787591435681615640760205)
              ·
                refine ⟨670346788380605865285077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1787591435681615640760205 670346788380605865285077)
                ·
                  refine ⟨15711252852670449967619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 670346788380605865285077 15711252852670449967619)
                  ·
                    rfl

theorem cell22_137689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_137689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137689 prefixEnd_137689 := by exact prefixLift 137689
  have htrace : WordTrace (prefixWord ++ tailWord_137689) baseStart_137689 baseEnd_137689 := by
    simpa [prefixWord, tailWord_137689, baseEnd_137689] using wordTrace_append hprefix tailTrace_137689
  have hstable : (prefixWord ++ tailWord_137689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137689).length < 2 ^ (prefixWord ++ tailWord_137689).sum := by decide
  have hdescent : baseEnd_137689 < baseStart_137689 := by decide
  rcases family_descends (prefixWord ++ tailWord_137689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137768 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 6]
def baseStart_137768 : Nat := 118140960795 + 137768 * 2 ^ 59
def prefixEnd_137768 : Nat := 4983230072969 + 3 ^ 40 * 137768 * 2
def baseEnd_137768 : Nat := 15720267290827159059205

theorem tailTrace_137768 : CollatzResearch.WordTrace tailWord_137768 prefixEnd_137768 15720267290827159059205 := by
  unfold tailWord_137768
  simp only [CollatzResearch.WordTrace]
  refine ⟨2512405882448769873138979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3349874509931693164185305 2512405882448769873138979)
  ·
    refine ⟨3768608823673154809708469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2512405882448769873138979 3768608823673154809708469)
    ·
      refine ⟨353307077219358263410169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3768608823673154809708469 353307077219358263410169)
      ·
        refine ⟨264980307914518697557627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353307077219358263410169 264980307914518697557627)
        ·
          refine ⟨397470461871778046336441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264980307914518697557627 397470461871778046336441)
          ·
            refine ⟨298102846403833534752331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 397470461871778046336441 298102846403833534752331)
            ·
              refine ⟨447154269605750302128497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298102846403833534752331 447154269605750302128497)
              ·
                refine ⟨335365702204312726596373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447154269605750302128497 335365702204312726596373)
                ·
                  refine ⟨15720267290827159059205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 335365702204312726596373 15720267290827159059205)
                  ·
                    rfl

theorem cell22_137768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_137768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137768 prefixEnd_137768 := by exact prefixLift 137768
  have htrace : WordTrace (prefixWord ++ tailWord_137768) baseStart_137768 baseEnd_137768 := by
    simpa [prefixWord, tailWord_137768, baseEnd_137768] using wordTrace_append hprefix tailTrace_137768
  have hstable : (prefixWord ++ tailWord_137768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137768).length < 2 ^ (prefixWord ++ tailWord_137768).sum := by decide
  have hdescent : baseEnd_137768 < baseStart_137768 := by decide
  rcases family_descends (prefixWord ++ tailWord_137768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137781 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_137781 : Nat := 118140960795 + 137781 * 2 ^ 59
def prefixEnd_137781 : Nat := 4983230072969 + 3 ^ 40 * 137781 * 2
def baseEnd_137781 : Nat := 47165252038153776602575

theorem tailTrace_137781 : CollatzResearch.WordTrace tailWord_137781 prefixEnd_137781 47165252038153776602575 := by
  unfold tailWord_137781
  simp only [CollatzResearch.WordTrace]
  refine ⟨5025285913850442966501197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3350190609233628644334131 5025285913850442966501197)
  ·
    refine ⟨1884482217693916112437949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5025285913850442966501197 1884482217693916112437949)
    ·
      refine ⟨706680831635218542164231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1884482217693916112437949 706680831635218542164231)
      ·
        refine ⟨1060021247452827813246347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 706680831635218542164231 1060021247452827813246347)
        ·
          refine ⟨1590031871179241719869521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060021247452827813246347 1590031871179241719869521)
          ·
            refine ⟨1192523903384431289902141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1590031871179241719869521 1192523903384431289902141)
            ·
              refine ⟨447196463769161733713303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1192523903384431289902141 447196463769161733713303)
              ·
                refine ⟨670794695653742600569955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447196463769161733713303 670794695653742600569955)
                ·
                  refine ⟨1006192043480613900854933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670794695653742600569955 1006192043480613900854933)
                  ·
                    refine ⟨47165252038153776602575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1006192043480613900854933 47165252038153776602575)
                    ·
                      rfl

theorem cell22_137781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_137781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137781 prefixEnd_137781 := by exact prefixLift 137781
  have htrace : WordTrace (prefixWord ++ tailWord_137781) baseStart_137781 baseEnd_137781 := by
    simpa [prefixWord, tailWord_137781, baseEnd_137781] using wordTrace_append hprefix tailTrace_137781
  have hstable : (prefixWord ++ tailWord_137781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137781).length < 2 ^ (prefixWord ++ tailWord_137781).sum := by decide
  have hdescent : baseEnd_137781 < baseStart_137781 := by decide
  rcases family_descends (prefixWord ++ tailWord_137781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137828 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_137828 : Nat := 118140960795 + 137828 * 2 ^ 59
def prefixEnd_137828 : Nat := 4983230072969 + 3 ^ 40 * 137828 * 2
def baseEnd_137828 : Nat := 47181341098661320677431

theorem tailTrace_137828 : CollatzResearch.WordTrace tailWord_137828 prefixEnd_137828 47181341098661320677431 := by
  unfold tailWord_137828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2513500072340084996731069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3351333429786779995641425 2513500072340084996731069)
  ·
    refine ⟨942562527127531873774151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2513500072340084996731069 942562527127531873774151)
    ·
      refine ⟨1413843790691297810661227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 942562527127531873774151 1413843790691297810661227)
      ·
        refine ⟨2120765686036946715991841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413843790691297810661227 2120765686036946715991841)
        ·
          refine ⟨1590574264527710036993881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2120765686036946715991841 1590574264527710036993881)
          ·
            refine ⟨1192930698395782527745411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1590574264527710036993881 1192930698395782527745411)
            ·
              refine ⟨1789396047593673791618117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192930698395782527745411 1789396047593673791618117)
              ·
                refine ⟨335511758923813835928397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1789396047593673791618117 335511758923813835928397)
                ·
                  refine ⟨125816909596430188473149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335511758923813835928397 125816909596430188473149)
                  ·
                    refine ⟨47181341098661320677431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125816909596430188473149 47181341098661320677431)
                    ·
                      rfl

theorem cell22_137828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_137828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137828 prefixEnd_137828 := by exact prefixLift 137828
  have htrace : WordTrace (prefixWord ++ tailWord_137828) baseStart_137828 baseEnd_137828 := by
    simpa [prefixWord, tailWord_137828, baseEnd_137828] using wordTrace_append hprefix tailTrace_137828
  have hstable : (prefixWord ++ tailWord_137828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137828).length < 2 ^ (prefixWord ++ tailWord_137828).sum := by decide
  have hdescent : baseEnd_137828 < baseStart_137828 := by decide
  rcases family_descends (prefixWord ++ tailWord_137828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137871 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 5, 4]
def baseStart_137871 : Nat := 118140960795 + 137871 * 2 ^ 59
def prefixEnd_137871 : Nat := 4983230072969 + 3 ^ 40 * 137871 * 2
def baseEnd_137871 : Nat := 47196060877423541852299

theorem tailTrace_137871 : CollatzResearch.WordTrace tailWord_137871 prefixEnd_137871 47196060877423541852299 := by
  unfold tailWord_137871
  simp only [CollatzResearch.WordTrace]
  refine ⟨5028568483524388337277467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3352378989016258891518311 5028568483524388337277467)
  ·
    refine ⟨7542852725286582505916201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5028568483524388337277467 7542852725286582505916201)
    ·
      refine ⟨5657139543964936879437151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7542852725286582505916201 5657139543964936879437151)
      ·
        refine ⟨8485709315947405319155727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5657139543964936879437151 8485709315947405319155727)
        ·
          refine ⟨12728563973921107978733591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8485709315947405319155727 12728563973921107978733591)
          ·
            refine ⟨19092845960881661968100387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12728563973921107978733591 19092845960881661968100387)
            ·
              refine ⟨28639268941322492952150581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19092845960881661968100387 28639268941322492952150581)
              ·
                refine ⟨2684931463248983714264117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28639268941322492952150581 2684931463248983714264117)
                ·
                  refine ⟨251712324679592223212261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2684931463248983714264117 251712324679592223212261)
                  ·
                    refine ⟨47196060877423541852299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 251712324679592223212261 47196060877423541852299)
                    ·
                      rfl

theorem cell22_137871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_137871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137871 prefixEnd_137871 := by exact prefixLift 137871
  have htrace : WordTrace (prefixWord ++ tailWord_137871) baseStart_137871 baseEnd_137871 := by
    simpa [prefixWord, tailWord_137871, baseEnd_137871] using wordTrace_append hprefix tailTrace_137871
  have hstable : (prefixWord ++ tailWord_137871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137871).length < 2 ^ (prefixWord ++ tailWord_137871).sum := by decide
  have hdescent : baseEnd_137871 < baseStart_137871 := by decide
  rcases family_descends (prefixWord ++ tailWord_137871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137918 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_137918 : Nat := 118140960795 + 137918 * 2 ^ 59
def prefixEnd_137918 : Nat := 4983230072969 + 3 ^ 40 * 137918 * 2
def baseEnd_137918 : Nat := 47212149937931085927155

theorem tailTrace_137918 : CollatzResearch.WordTrace tailWord_137918 prefixEnd_137918 47212149937931085927155 := by
  unfold tailWord_137918
  simp only [CollatzResearch.WordTrace]
  refine ⟨628785339294264420529801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3353521809569410242825605 628785339294264420529801)
  ·
    refine ⟨471589004470698315397351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 628785339294264420529801 471589004470698315397351)
    ·
      refine ⟨707383506706047473096027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 471589004470698315397351 707383506706047473096027)
      ·
        refine ⟨1061075260059071209644041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 707383506706047473096027 1061075260059071209644041)
        ·
          refine ⟨795806445044303407233031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1061075260059071209644041 795806445044303407233031)
          ·
            refine ⟨1193709667566455110849547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795806445044303407233031 1193709667566455110849547)
            ·
              refine ⟨1790564501349682666274321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193709667566455110849547 1790564501349682666274321)
              ·
                refine ⟨1342923376012261999705741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790564501349682666274321 1342923376012261999705741)
                ·
                  refine ⟨503596266004598249889653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1342923376012261999705741 503596266004598249889653)
                  ·
                    refine ⟨47212149937931085927155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 503596266004598249889653 47212149937931085927155)
                    ·
                      rfl

theorem cell22_137918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_137918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137918 prefixEnd_137918 := by exact prefixLift 137918
  have htrace : WordTrace (prefixWord ++ tailWord_137918) baseStart_137918 baseEnd_137918 := by
    simpa [prefixWord, tailWord_137918, baseEnd_137918] using wordTrace_append hprefix tailTrace_137918
  have hstable : (prefixWord ++ tailWord_137918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137918).length < 2 ^ (prefixWord ++ tailWord_137918).sum := by decide
  have hdescent : baseEnd_137918 < baseStart_137918 := by decide
  rcases family_descends (prefixWord ++ tailWord_137918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137920 : List Nat := [2, 1, 1, 2, 4, 3, 1, 4, 4]
def baseStart_137920 : Nat := 118140960795 + 137920 * 2 ^ 59
def prefixEnd_137920 : Nat := 4983230072969 + 3 ^ 40 * 137920 * 2
def baseEnd_137920 : Nat := 15737611526267915792383

theorem tailTrace_137920 : CollatzResearch.WordTrace tailWord_137920 prefixEnd_137920 15737611526267915792383 := by
  unfold tailWord_137920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2515177830173434852905607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3353570440231246470540809 2515177830173434852905607)
  ·
    refine ⟨3772766745260152279358411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2515177830173434852905607 3772766745260152279358411)
    ·
      refine ⟨5659150117890228419037617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3772766745260152279358411 5659150117890228419037617)
      ·
        refine ⟨4244362588417671314278213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5659150117890228419037617 4244362588417671314278213)
        ·
          refine ⟨795817985328313371427165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4244362588417671314278213 795817985328313371427165)
          ·
            refine ⟨298431744498117514285187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 795817985328313371427165 298431744498117514285187)
            ·
              refine ⟨447647616747176271427781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298431744498117514285187 447647616747176271427781)
              ·
                refine ⟨83933928140095550892709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 447647616747176271427781 83933928140095550892709)
                ·
                  refine ⟨15737611526267915792383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83933928140095550892709 15737611526267915792383)
                  ·
                    rfl

theorem cell22_137920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 4].length) (baseStart_137920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137920 prefixEnd_137920 := by exact prefixLift 137920
  have htrace : WordTrace (prefixWord ++ tailWord_137920) baseStart_137920 baseEnd_137920 := by
    simpa [prefixWord, tailWord_137920, baseEnd_137920] using wordTrace_append hprefix tailTrace_137920
  have hstable : (prefixWord ++ tailWord_137920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137920).length < 2 ^ (prefixWord ++ tailWord_137920).sum := by decide
  have hdescent : baseEnd_137920 < baseStart_137920 := by decide
  rcases family_descends (prefixWord ++ tailWord_137920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137963 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 7, 3]
def baseStart_137963 : Nat := 118140960795 + 137963 * 2 ^ 59
def prefixEnd_137963 : Nat := 4983230072969 + 3 ^ 40 * 137963 * 2
def baseEnd_137963 : Nat := 47227554357565968552017

theorem tailTrace_137963 : CollatzResearch.WordTrace tailWord_137963 prefixEnd_137963 47227554357565968552017 := by
  unfold tailWord_137963
  simp only [CollatzResearch.WordTrace]
  refine ⟨5031923999191088049626543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3354615999460725366417695 5031923999191088049626543)
  ·
    refine ⟨7547885998786632074439815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5031923999191088049626543 7547885998786632074439815)
    ·
      refine ⟨11321828998179948111659723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7547885998786632074439815 11321828998179948111659723)
      ·
        refine ⟨16982743497269922167489585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11321828998179948111659723 16982743497269922167489585)
        ·
          refine ⟨12737057622952441625617189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16982743497269922167489585 12737057622952441625617189)
          ·
            refine ⟨2388198304303582804803223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12737057622952441625617189 2388198304303582804803223)
            ·
              refine ⟨3582297456455374207204835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2388198304303582804803223 3582297456455374207204835)
              ·
                refine ⟨5373446184683061310807253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582297456455374207204835 5373446184683061310807253)
                ·
                  refine ⟨125940144953509249472045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5373446184683061310807253 125940144953509249472045)
                  ·
                    refine ⟨47227554357565968552017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125940144953509249472045 47227554357565968552017)
                    ·
                      rfl

theorem cell22_137963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 3].length) (baseStart_137963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137963 prefixEnd_137963 := by exact prefixLift 137963
  have htrace : WordTrace (prefixWord ++ tailWord_137963) baseStart_137963 baseEnd_137963 := by
    simpa [prefixWord, tailWord_137963, baseEnd_137963] using wordTrace_append hprefix tailTrace_137963
  have hstable : (prefixWord ++ tailWord_137963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137963).length < 2 ^ (prefixWord ++ tailWord_137963).sum := by decide
  have hdescent : baseEnd_137963 < baseStart_137963 := by decide
  rcases family_descends (prefixWord ++ tailWord_137963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137980 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 3, 3]
def baseStart_137980 : Nat := 118140960795 + 137980 * 2 ^ 59
def prefixEnd_137980 : Nat := 4983230072969 + 3 ^ 40 * 137980 * 2
def baseEnd_137980 : Nat := 47233373804983590876965

theorem tailTrace_137980 : CollatzResearch.WordTrace tailWord_137980 prefixEnd_137980 47233373804983590876965 := by
  unfold tailWord_137980
  simp only [CollatzResearch.WordTrace]
  refine ⟨2516272020064749976497697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3355029360086333301996929 2516272020064749976497697)
  ·
    refine ⟨1887204015048562482373273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2516272020064749976497697 1887204015048562482373273)
    ·
      refine ⟨1415403011286421861779955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1887204015048562482373273 1415403011286421861779955)
      ·
        refine ⟨2123104516929632792669933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1415403011286421861779955 2123104516929632792669933)
        ·
          refine ⟨796164193848612297251225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2123104516929632792669933 796164193848612297251225)
          ·
            refine ⟨597123145386459222938419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 796164193848612297251225 597123145386459222938419)
            ·
              refine ⟨895684718079688834407629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597123145386459222938419 895684718079688834407629)
              ·
                refine ⟨335881769279883312902861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 895684718079688834407629 335881769279883312902861)
                ·
                  refine ⟨125955663479956242338573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335881769279883312902861 125955663479956242338573)
                  ·
                    refine ⟨47233373804983590876965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125955663479956242338573 47233373804983590876965)
                    ·
                      rfl

theorem cell22_137980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_137980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137980 prefixEnd_137980 := by exact prefixLift 137980
  have htrace : WordTrace (prefixWord ++ tailWord_137980) baseStart_137980 baseEnd_137980 := by
    simpa [prefixWord, tailWord_137980, baseEnd_137980] using wordTrace_append hprefix tailTrace_137980
  have hstable : (prefixWord ++ tailWord_137980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137980).length < 2 ^ (prefixWord ++ tailWord_137980).sum := by decide
  have hdescent : baseEnd_137980 < baseStart_137980 := by decide
  rcases family_descends (prefixWord ++ tailWord_137980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137993 : List Nat := [1, 2, 1, 1, 3, 2, 2, 5, 5]
def baseStart_137993 : Nat := 118140960795 + 137993 * 2 ^ 59
def prefixEnd_137993 : Nat := 4983230072969 + 3 ^ 40 * 137993 * 2
def baseEnd_137993 : Nat := 15745941323551963433975

theorem tailTrace_137993 : CollatzResearch.WordTrace tailWord_137993 prefixEnd_137993 15745941323551963433975 := by
  unfold tailWord_137993
  simp only [CollatzResearch.WordTrace]
  refine ⟨5033018189082403173218633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3355345459388268782145755 5033018189082403173218633)
  ·
    refine ⟨3774763641811802379913975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5033018189082403173218633 3774763641811802379913975)
    ·
      refine ⟨5662145462717703569870963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3774763641811802379913975 5662145462717703569870963)
      ·
        refine ⟨8493218194076555354806445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5662145462717703569870963 8493218194076555354806445)
        ·
          refine ⟨3184956822778708258052417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8493218194076555354806445 3184956822778708258052417)
          ·
            refine ⟨2388717617084031193539313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3184956822778708258052417 2388717617084031193539313)
            ·
              refine ⟨1791538212813023395154485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388717617084031193539313 1791538212813023395154485)
              ·
                refine ⟨167956707451220943295733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1791538212813023395154485 167956707451220943295733)
                ·
                  refine ⟨15745941323551963433975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167956707451220943295733 15745941323551963433975)
                  ·
                    rfl

theorem cell22_137993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_137993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_137993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_137993 prefixEnd_137993 := by exact prefixLift 137993
  have htrace : WordTrace (prefixWord ++ tailWord_137993) baseStart_137993 baseEnd_137993 := by
    simpa [prefixWord, tailWord_137993, baseEnd_137993] using wordTrace_append hprefix tailTrace_137993
  have hstable : (prefixWord ++ tailWord_137993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137993).length < 2 ^ (prefixWord ++ tailWord_137993).sum := by decide
  have hdescent : baseEnd_137993 < baseStart_137993 := by decide
  rcases family_descends (prefixWord ++ tailWord_137993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138057 : List Nat := [1, 2, 1, 1, 2, 7, 1, 2, 1, 4]
def baseStart_138057 : Nat := 118140960795 + 138057 * 2 ^ 59
def prefixEnd_138057 : Nat := 4983230072969 + 3 ^ 40 * 138057 * 2
def baseEnd_138057 : Nat := 47259732478581056701729

theorem tailTrace_138057 : CollatzResearch.WordTrace tailWord_138057 prefixEnd_138057 47259732478581056701729 := by
  unfold tailWord_138057
  simp only [CollatzResearch.WordTrace]
  refine ⟨5035352460850542103548425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3356901640567028069032283 5035352460850542103548425)
  ·
    refine ⟨3776514345637906577661319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5035352460850542103548425 3776514345637906577661319)
    ·
      refine ⟨5664771518456859866491979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3776514345637906577661319 5664771518456859866491979)
      ·
        refine ⟨8497157277685289799737969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5664771518456859866491979 8497157277685289799737969)
        ·
          refine ⟨6372867958263967349803477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8497157277685289799737969 6372867958263967349803477)
          ·
            refine ⟨149364092771811734761019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 6372867958263967349803477 149364092771811734761019)
            ·
              refine ⟨224046139157717602141529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149364092771811734761019 224046139157717602141529)
              ·
                refine ⟨168034604368288201606147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224046139157717602141529 168034604368288201606147)
                ·
                  refine ⟨252051906552432302409221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168034604368288201606147 252051906552432302409221)
                  ·
                    refine ⟨47259732478581056701729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 252051906552432302409221 47259732478581056701729)
                    ·
                      rfl

theorem cell22_138057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 4].length) (baseStart_138057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138057 prefixEnd_138057 := by exact prefixLift 138057
  have htrace : WordTrace (prefixWord ++ tailWord_138057) baseStart_138057 baseEnd_138057 := by
    simpa [prefixWord, tailWord_138057, baseEnd_138057] using wordTrace_append hprefix tailTrace_138057
  have hstable : (prefixWord ++ tailWord_138057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138057).length < 2 ^ (prefixWord ++ tailWord_138057).sum := by decide
  have hdescent : baseEnd_138057 < baseStart_138057 := by decide
  rcases family_descends (prefixWord ++ tailWord_138057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138083 : List Nat := [1, 1, 1, 5, 3, 11]
def baseStart_138083 : Nat := 118140960795 + 138083 * 2 ^ 59
def prefixEnd_138083 : Nat := 4983230072969 + 3 ^ 40 * 138083 * 2
def baseEnd_138083 : Nat := 583563368023773525329

theorem tailTrace_138083 : CollatzResearch.WordTrace tailWord_138083 prefixEnd_138083 583563368023773525329 := by
  unfold tailWord_138083
  simp only [CollatzResearch.WordTrace]
  refine ⟨5036300758756348543994903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3357533839170899029329935 5036300758756348543994903)
  ·
    refine ⟨7554451138134522815992355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5036300758756348543994903 7554451138134522815992355)
    ·
      refine ⟨11331676707201784223988533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7554451138134522815992355 11331676707201784223988533)
      ·
        refine ⟨1062344691300167270998925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11331676707201784223988533 1062344691300167270998925)
        ·
          refine ⟨398379259237562726624597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1062344691300167270998925 398379259237562726624597)
          ·
            refine ⟨583563368023773525329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 398379259237562726624597 583563368023773525329)
            ·
              rfl

theorem cell22_138083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 11].length) (baseStart_138083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138083 prefixEnd_138083 := by exact prefixLift 138083
  have htrace : WordTrace (prefixWord ++ tailWord_138083) baseStart_138083 baseEnd_138083 := by
    simpa [prefixWord, tailWord_138083, baseEnd_138083] using wordTrace_append hprefix tailTrace_138083
  have hstable : (prefixWord ++ tailWord_138083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138083).length < 2 ^ (prefixWord ++ tailWord_138083).sum := by decide
  have hdescent : baseEnd_138083 < baseStart_138083 := by decide
  rcases family_descends (prefixWord ++ tailWord_138083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138085 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_138085 : Nat := 118140960795 + 138085 * 2 ^ 59
def prefixEnd_138085 : Nat := 4983230072969 + 3 ^ 40 * 138085 * 2
def baseEnd_138085 : Nat := 47269317450798317001643

theorem tailTrace_138085 : CollatzResearch.WordTrace tailWord_138085 prefixEnd_138085 47269317450798317001643 := by
  unfold tailWord_138085
  simp only [CollatzResearch.WordTrace]
  refine ⟨5036373704749102885567709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3357582469832735257045139 5036373704749102885567709)
  ·
    refine ⟨1888640139280913582087891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5036373704749102885567709 1888640139280913582087891)
    ·
      refine ⟨2832960208921370373131837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1888640139280913582087891 2832960208921370373131837)
      ·
        refine ⟨1062360078345513889924439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2832960208921370373131837 1062360078345513889924439)
        ·
          refine ⟨1593540117518270834886659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062360078345513889924439 1593540117518270834886659)
          ·
            refine ⟨2390310176277406252329989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593540117518270834886659 2390310176277406252329989)
            ·
              refine ⟨448183158052013672311873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2390310176277406252329989 448183158052013672311873)
              ·
                refine ⟨336137368539010254233905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448183158052013672311873 336137368539010254233905)
                ·
                  refine ⟨252103026404257690675429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336137368539010254233905 252103026404257690675429)
                  ·
                    refine ⟨47269317450798317001643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 252103026404257690675429 47269317450798317001643)
                    ·
                      rfl

theorem cell22_138085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_138085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138085 prefixEnd_138085 := by exact prefixLift 138085
  have htrace : WordTrace (prefixWord ++ tailWord_138085) baseStart_138085 baseEnd_138085 := by
    simpa [prefixWord, tailWord_138085, baseEnd_138085] using wordTrace_append hprefix tailTrace_138085
  have hstable : (prefixWord ++ tailWord_138085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138085).length < 2 ^ (prefixWord ++ tailWord_138085).sum := by decide
  have hdescent : baseEnd_138085 < baseStart_138085 := by decide
  rcases family_descends (prefixWord ++ tailWord_138085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138087 : List Nat := [1, 1, 5, 1, 2, 2, 1, 4, 2, 3]
def baseStart_138087 : Nat := 118140960795 + 138087 * 2 ^ 59
def prefixEnd_138087 : Nat := 4983230072969 + 3 ^ 40 * 138087 * 2
def baseEnd_138087 : Nat := 47270002091670978451637

theorem tailTrace_138087 : CollatzResearch.WordTrace tailWord_138087 prefixEnd_138087 47270002091670978451637 := by
  unfold tailWord_138087
  simp only [CollatzResearch.WordTrace]
  refine ⟨5036446650741857227140515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3357631100494571484760343 5036446650741857227140515)
  ·
    refine ⟨7554669976112785840710773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5036446650741857227140515 7554669976112785840710773)
    ·
      refine ⟨708250310260573672566635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7554669976112785840710773 708250310260573672566635)
      ·
        refine ⟨1062375465390860508849953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708250310260573672566635 1062375465390860508849953)
        ·
          refine ⟨796781599043145381637465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1062375465390860508849953 796781599043145381637465)
          ·
            refine ⟨597586199282359036228099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 796781599043145381637465 597586199282359036228099)
            ·
              refine ⟨896379298923538554342149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597586199282359036228099 896379298923538554342149)
              ·
                refine ⟨168071118548163478939153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 896379298923538554342149 168071118548163478939153)
                ·
                  refine ⟨126053338911122609204365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168071118548163478939153 126053338911122609204365)
                  ·
                    refine ⟨47270002091670978451637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126053338911122609204365 47270002091670978451637)
                    ·
                      rfl

theorem cell22_138087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_138087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138087 prefixEnd_138087 := by exact prefixLift 138087
  have htrace : WordTrace (prefixWord ++ tailWord_138087) baseStart_138087 baseEnd_138087 := by
    simpa [prefixWord, tailWord_138087, baseEnd_138087] using wordTrace_append hprefix tailTrace_138087
  have hstable : (prefixWord ++ tailWord_138087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138087).length < 2 ^ (prefixWord ++ tailWord_138087).sum := by decide
  have hdescent : baseEnd_138087 < baseStart_138087 := by decide
  rcases family_descends (prefixWord ++ tailWord_138087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138132 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_138132 : Nat := 118140960795 + 138132 * 2 ^ 59
def prefixEnd_138132 : Nat := 4983230072969 + 3 ^ 40 * 138132 * 2
def baseEnd_138132 : Nat := 47285406511305861076499

theorem tailTrace_138132 : CollatzResearch.WordTrace tailWord_138132 prefixEnd_138132 47285406511305861076499 := by
  unfold tailWord_138132
  simp only [CollatzResearch.WordTrace]
  refine ⟨2519043967789414956264325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3358725290385886608352433 2519043967789414956264325)
  ·
    refine ⟨472320743960515304299561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2519043967789414956264325 472320743960515304299561)
    ·
      refine ⟨354240557970386478224671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 472320743960515304299561 354240557970386478224671)
      ·
        refine ⟨531360836955579717337007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354240557970386478224671 531360836955579717337007)
        ·
          refine ⟨797041255433369576005511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531360836955579717337007 797041255433369576005511)
          ·
            refine ⟨1195561883150054364008267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797041255433369576005511 1195561883150054364008267)
            ·
              refine ⟨1793342824725081546012401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195561883150054364008267 1793342824725081546012401)
              ·
                refine ⟨1345007118543811159509301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1793342824725081546012401 1345007118543811159509301)
                ·
                  refine ⟨126094417363482296203997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1345007118543811159509301 126094417363482296203997)
                  ·
                    refine ⟨47285406511305861076499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126094417363482296203997 47285406511305861076499)
                    ·
                      rfl

theorem cell22_138132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_138132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138132 prefixEnd_138132 := by exact prefixLift 138132
  have htrace : WordTrace (prefixWord ++ tailWord_138132) baseStart_138132 baseEnd_138132 := by
    simpa [prefixWord, tailWord_138132, baseEnd_138132] using wordTrace_append hprefix tailTrace_138132
  have hstable : (prefixWord ++ tailWord_138132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138132).length < 2 ^ (prefixWord ++ tailWord_138132).sum := by decide
  have hdescent : baseEnd_138132 < baseStart_138132 := by decide
  rcases family_descends (prefixWord ++ tailWord_138132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138134 : List Nat := [5, 3, 1, 1, 1, 2, 9]
def baseStart_138134 : Nat := 118140960795 + 138134 * 2 ^ 59
def prefixEnd_138134 : Nat := 4983230072969 + 3 ^ 40 * 138134 * 2
def baseEnd_138134 : Nat := 1751336709339945278759

theorem tailTrace_138134 : CollatzResearch.WordTrace tailWord_138134 prefixEnd_138134 1751336709339945278759 := by
  unfold tailWord_138134
  simp only [CollatzResearch.WordTrace]
  refine ⟨314885055098224015881341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3358773921047722836067637 314885055098224015881341)
  ·
    refine ⟨118081895661834005955503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 314885055098224015881341 118081895661834005955503)
    ·
      refine ⟨177122843492751008933255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118081895661834005955503 177122843492751008933255)
      ·
        refine ⟨265684265239126513399883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177122843492751008933255 265684265239126513399883)
        ·
          refine ⟨398526397858689770099825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265684265239126513399883 398526397858689770099825)
          ·
            refine ⟨298894798394017327574869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398526397858689770099825 298894798394017327574869)
            ·
              refine ⟨1751336709339945278759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 298894798394017327574869 1751336709339945278759)
              ·
                rfl

theorem cell22_138134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 9].length) (baseStart_138134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138134 prefixEnd_138134 := by exact prefixLift 138134
  have htrace : WordTrace (prefixWord ++ tailWord_138134) baseStart_138134 baseEnd_138134 := by
    simpa [prefixWord, tailWord_138134, baseEnd_138134] using wordTrace_append hprefix tailTrace_138134
  have hstable : (prefixWord ++ tailWord_138134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138134).length < 2 ^ (prefixWord ++ tailWord_138134).sum := by decide
  have hdescent : baseEnd_138134 < baseStart_138134 := by decide
  rcases family_descends (prefixWord ++ tailWord_138134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138213 : List Nat := [1, 3, 1, 6, 2, 1, 2, 1, 5]
def baseStart_138213 : Nat := 118140960795 + 138213 * 2 ^ 59
def prefixEnd_138213 : Nat := 4983230072969 + 3 ^ 40 * 138213 * 2
def baseEnd_138213 : Nat := 15771044822216216600417

theorem tailTrace_138213 : CollatzResearch.WordTrace tailWord_138213 prefixEnd_138213 15771044822216216600417 := by
  unfold tailWord_138213
  simp only [CollatzResearch.WordTrace]
  refine ⟨5041042248285380746227293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3360694832190253830818195 5041042248285380746227293)
  ·
    refine ⟨1890390843107017779835235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5041042248285380746227293 1890390843107017779835235)
    ·
      refine ⟨2835586264660526669752853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890390843107017779835235 2835586264660526669752853)
      ·
        refine ⟨132918106155962187644665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2835586264660526669752853 132918106155962187644665)
        ·
          refine ⟨99688579616971640733499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132918106155962187644665 99688579616971640733499)
          ·
            refine ⟨149532869425457461100249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99688579616971640733499 149532869425457461100249)
            ·
              refine ⟨112149652069093095825187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149532869425457461100249 112149652069093095825187)
              ·
                refine ⟨168224478103639643737781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112149652069093095825187 168224478103639643737781)
                ·
                  refine ⟨15771044822216216600417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 168224478103639643737781 15771044822216216600417)
                  ·
                    rfl

theorem cell22_138213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_138213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138213 prefixEnd_138213 := by exact prefixLift 138213
  have htrace : WordTrace (prefixWord ++ tailWord_138213) baseStart_138213 baseEnd_138213 := by
    simpa [prefixWord, tailWord_138213, baseEnd_138213] using wordTrace_append hprefix tailTrace_138213
  have hstable : (prefixWord ++ tailWord_138213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138213).length < 2 ^ (prefixWord ++ tailWord_138213).sum := by decide
  have hdescent : baseEnd_138213 < baseStart_138213 := by decide
  rcases family_descends (prefixWord ++ tailWord_138213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138265 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 2, 6]
def baseStart_138265 : Nat := 118140960795 + 138265 * 2 ^ 59
def prefixEnd_138265 : Nat := 4983230072969 + 3 ^ 40 * 138265 * 2
def baseEnd_138265 : Nat := 47330935129337847501091

theorem tailTrace_138265 : CollatzResearch.WordTrace tailWord_138265 prefixEnd_138265 47330935129337847501091 := by
  unfold tailWord_138265
  simp only [CollatzResearch.WordTrace]
  refine ⟨5042938844096993627120249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3361959229397995751413499 5042938844096993627120249)
  ·
    refine ⟨3782204133072745220340187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5042938844096993627120249 3782204133072745220340187)
    ·
      refine ⟨5673306199609117830510281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3782204133072745220340187 5673306199609117830510281)
      ·
        refine ⟨4254979649706838372882711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5673306199609117830510281 4254979649706838372882711)
        ·
          refine ⟨6382469474560257559324067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4254979649706838372882711 6382469474560257559324067)
          ·
            refine ⟨9573704211840386338986101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6382469474560257559324067 9573704211840386338986101)
            ·
              refine ⟨897534769860036219279947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9573704211840386338986101 897534769860036219279947)
              ·
                refine ⟨1346302154790054328919921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 897534769860036219279947 1346302154790054328919921)
                ·
                  refine ⟨1009726616092540746689941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1346302154790054328919921 1009726616092540746689941)
                  ·
                    refine ⟨47330935129337847501091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1009726616092540746689941 47330935129337847501091)
                    ·
                      rfl

theorem cell22_138265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_138265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138265 prefixEnd_138265 := by exact prefixLift 138265
  have htrace : WordTrace (prefixWord ++ tailWord_138265) baseStart_138265 baseEnd_138265 := by
    simpa [prefixWord, tailWord_138265, baseEnd_138265] using wordTrace_append hprefix tailTrace_138265
  have hstable : (prefixWord ++ tailWord_138265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138265).length < 2 ^ (prefixWord ++ tailWord_138265).sum := by decide
  have hdescent : baseEnd_138265 < baseStart_138265 := by decide
  rcases family_descends (prefixWord ++ tailWord_138265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138269 : List Nat := [1, 4, 2, 2, 3, 2, 1, 7]
def baseStart_138269 : Nat := 118140960795 + 138269 * 2 ^ 59
def prefixEnd_138269 : Nat := 4983230072969 + 3 ^ 40 * 138269 * 2
def baseEnd_138269 : Nat := 5259144934564796711231

theorem tailTrace_138269 : CollatzResearch.WordTrace tailWord_138269 prefixEnd_138269 5259144934564796711231 := by
  unfold tailWord_138269
  simp only [CollatzResearch.WordTrace]
  refine ⟨5043084736082502310265861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3362056490721668206843907 5043084736082502310265861)
  ·
    refine ⟨945578388015469183174849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5043084736082502310265861 945578388015469183174849)
    ·
      refine ⟨709183791011601887381137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 945578388015469183174849 709183791011601887381137)
      ·
        refine ⟨531887843258701415535853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 709183791011601887381137 531887843258701415535853)
        ·
          refine ⟨199457941222013030825945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 531887843258701415535853 199457941222013030825945)
          ·
            refine ⟨149593455916509773119459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199457941222013030825945 149593455916509773119459)
            ·
              refine ⟨224390183874764659679189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149593455916509773119459 224390183874764659679189)
              ·
                refine ⟨5259144934564796711231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 224390183874764659679189 5259144934564796711231)
                ·
                  rfl

theorem cell22_138269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 7].length) (baseStart_138269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138269 prefixEnd_138269 := by exact prefixLift 138269
  have htrace : WordTrace (prefixWord ++ tailWord_138269) baseStart_138269 baseEnd_138269 := by
    simpa [prefixWord, tailWord_138269, baseEnd_138269] using wordTrace_append hprefix tailTrace_138269
  have hstable : (prefixWord ++ tailWord_138269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138269).length < 2 ^ (prefixWord ++ tailWord_138269).sum := by decide
  have hdescent : baseEnd_138269 < baseStart_138269 := by decide
  rcases family_descends (prefixWord ++ tailWord_138269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138295 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 3, 7]
def baseStart_138295 : Nat := 118140960795 + 138295 * 2 ^ 59
def prefixEnd_138295 : Nat := 4983230072969 + 3 ^ 40 * 138295 * 2
def baseEnd_138295 : Nat := 47341204742427769250999

theorem tailTrace_138295 : CollatzResearch.WordTrace tailWord_138295 prefixEnd_138295 47341204742427769250999 := by
  unfold tailWord_138295
  simp only [CollatzResearch.WordTrace]
  refine ⟨5044033033988308750712339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3362688689325539167141559 5044033033988308750712339)
  ·
    refine ⟨7566049550982463126068509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5044033033988308750712339 7566049550982463126068509)
    ·
      refine ⟨2837268581618423672275691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7566049550982463126068509 2837268581618423672275691)
      ·
        refine ⟨4255902872427635508413537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2837268581618423672275691 4255902872427635508413537)
        ·
          refine ⟨3191927154320726631310153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4255902872427635508413537 3191927154320726631310153)
          ·
            refine ⟨2393945365740544973482615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3191927154320726631310153 2393945365740544973482615)
            ·
              refine ⟨3590918048610817460223923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2393945365740544973482615 3590918048610817460223923)
              ·
                refine ⟨5386377072916226190335885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3590918048610817460223923 5386377072916226190335885)
                ·
                  refine ⟨2019891402343584821375957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5386377072916226190335885 2019891402343584821375957)
                  ·
                    refine ⟨47341204742427769250999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2019891402343584821375957 47341204742427769250999)
                    ·
                      rfl

theorem cell22_138295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_138295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138295 prefixEnd_138295 := by exact prefixLift 138295
  have htrace : WordTrace (prefixWord ++ tailWord_138295) baseStart_138295 baseEnd_138295 := by
    simpa [prefixWord, tailWord_138295, baseEnd_138295] using wordTrace_append hprefix tailTrace_138295
  have hstable : (prefixWord ++ tailWord_138295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138295).length < 2 ^ (prefixWord ++ tailWord_138295).sum := by decide
  have hdescent : baseEnd_138295 < baseStart_138295 := by decide
  rcases family_descends (prefixWord ++ tailWord_138295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138301 : List Nat := [1, 4, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_138301 : Nat := 118140960795 + 138301 * 2 ^ 59
def prefixEnd_138301 : Nat := 4983230072969 + 3 ^ 40 * 138301 * 2
def baseEnd_138301 : Nat := 47343258665045753600981

theorem tailTrace_138301 : CollatzResearch.WordTrace tailWord_138301 prefixEnd_138301 47343258665045753600981 := by
  unfold tailWord_138301
  simp only [CollatzResearch.WordTrace]
  refine ⟨5044251871966571775430757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3362834581311047850287171 5044251871966571775430757)
  ·
    refine ⟨945797225993732207893267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5044251871966571775430757 945797225993732207893267)
    ·
      refine ⟨1418695838990598311839901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 945797225993732207893267 1418695838990598311839901)
      ·
        refine ⟨532010939621474366939963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1418695838990598311839901 532010939621474366939963)
        ·
          refine ⟨798016409432211550409945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532010939621474366939963 798016409432211550409945)
          ·
            refine ⟨598512307074158662807459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 798016409432211550409945 598512307074158662807459)
            ·
              refine ⟨897768460611237994211189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598512307074158662807459 897768460611237994211189)
              ·
                refine ⟨84165793182303561957299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 897768460611237994211189 84165793182303561957299)
                ·
                  refine ⟨126248689773455342935949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84165793182303561957299 126248689773455342935949)
                  ·
                    refine ⟨47343258665045753600981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126248689773455342935949 47343258665045753600981)
                    ·
                      rfl

theorem cell22_138301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_138301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138301 prefixEnd_138301 := by exact prefixLift 138301
  have htrace : WordTrace (prefixWord ++ tailWord_138301) baseStart_138301 baseEnd_138301 := by
    simpa [prefixWord, tailWord_138301, baseEnd_138301] using wordTrace_append hprefix tailTrace_138301
  have hstable : (prefixWord ++ tailWord_138301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138301).length < 2 ^ (prefixWord ++ tailWord_138301).sum := by decide
  have hdescent : baseEnd_138301 < baseStart_138301 := by decide
  rcases family_descends (prefixWord ++ tailWord_138301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138376 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 6]
def baseStart_138376 : Nat := 118140960795 + 138376 * 2 ^ 59
def prefixEnd_138376 : Nat := 4983230072969 + 3 ^ 40 * 138376 * 2
def baseEnd_138376 : Nat := 15789644232590185991917

theorem tailTrace_138376 : CollatzResearch.WordTrace tailWord_138376 prefixEnd_138376 15789644232590185991917 := by
  unfold tailWord_138376
  simp only [CollatzResearch.WordTrace]
  refine ⟨2523493673347429792205491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3364658231129906389607321 2523493673347429792205491)
  ·
    refine ⟨3785240510021144688308237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2523493673347429792205491 3785240510021144688308237)
    ·
      refine ⟨1419465191257929258115589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3785240510021144688308237 1419465191257929258115589)
      ·
        refine ⟨266149723360861735896673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1419465191257929258115589 266149723360861735896673)
        ·
          refine ⟨199612292520646301922505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266149723360861735896673 199612292520646301922505)
          ·
            refine ⟨149709219390484726441879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199612292520646301922505 149709219390484726441879)
            ·
              refine ⟨224563829085727089662819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149709219390484726441879 224563829085727089662819)
              ·
                refine ⟨336845743628590634494229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224563829085727089662819 336845743628590634494229)
                ·
                  refine ⟨15789644232590185991917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 336845743628590634494229 15789644232590185991917)
                  ·
                    rfl

theorem cell22_138376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 6].length) (baseStart_138376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138376 prefixEnd_138376 := by exact prefixLift 138376
  have htrace : WordTrace (prefixWord ++ tailWord_138376) baseStart_138376 baseEnd_138376 := by
    simpa [prefixWord, tailWord_138376, baseEnd_138376] using wordTrace_append hprefix tailTrace_138376
  have hstable : (prefixWord ++ tailWord_138376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138376).length < 2 ^ (prefixWord ++ tailWord_138376).sum := by decide
  have hdescent : baseEnd_138376 < baseStart_138376 := by decide
  rcases family_descends (prefixWord ++ tailWord_138376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138391 : List Nat := [1, 1, 3, 3, 3, 2, 1, 3, 2, 3]
def baseStart_138391 : Nat := 118140960795 + 138391 * 2 ^ 59
def prefixEnd_138391 : Nat := 4983230072969 + 3 ^ 40 * 138391 * 2
def baseEnd_138391 : Nat := 47374067504315518850705

theorem tailTrace_138391 : CollatzResearch.WordTrace tailWord_138391 prefixEnd_138391 47374067504315518850705 := by
  unfold tailWord_138391
  simp only [CollatzResearch.WordTrace]
  refine ⟨5047534441640517146207027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3365022961093678097471351 5047534441640517146207027)
  ·
    refine ⟨7571301662460775719310541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5047534441640517146207027 7571301662460775719310541)
    ·
      refine ⟨2839238123422790894741453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7571301662460775719310541 2839238123422790894741453)
      ·
        refine ⟨1064714296283546585528045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2839238123422790894741453 1064714296283546585528045)
        ·
          refine ⟨399267861106329969573017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1064714296283546585528045 399267861106329969573017)
          ·
            refine ⟨299450895829747477179763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399267861106329969573017 299450895829747477179763)
            ·
              refine ⟨449176343744621215769645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299450895829747477179763 449176343744621215769645)
              ·
                refine ⟨168441128904232955913617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 449176343744621215769645 168441128904232955913617)
                ·
                  refine ⟨126330846678174716935213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168441128904232955913617 126330846678174716935213)
                  ·
                    refine ⟨47374067504315518850705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126330846678174716935213 47374067504315518850705)
                    ·
                      rfl

theorem cell22_138391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_138391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138391 prefixEnd_138391 := by exact prefixLift 138391
  have htrace : WordTrace (prefixWord ++ tailWord_138391) baseStart_138391 baseEnd_138391 := by
    simpa [prefixWord, tailWord_138391, baseEnd_138391] using wordTrace_append hprefix tailTrace_138391
  have hstable : (prefixWord ++ tailWord_138391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138391).length < 2 ^ (prefixWord ++ tailWord_138391).sum := by decide
  have hdescent : baseEnd_138391 < baseStart_138391 := by decide
  rcases family_descends (prefixWord ++ tailWord_138391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138524 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_138524 : Nat := 118140960795 + 138524 * 2 ^ 59
def prefixEnd_138524 : Nat := 4983230072969 + 3 ^ 40 * 138524 * 2
def baseEnd_138524 : Nat := 47419596122347505275297

theorem tailTrace_138524 : CollatzResearch.WordTrace tailWord_138524 prefixEnd_138524 47419596122347505275297 := by
  unfold tailWord_138524
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526192675079340430399313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3368256900105787240532417 2526192675079340430399313)
  ·
    refine ⟨1894644506309505322799485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2526192675079340430399313 1894644506309505322799485)
    ·
      refine ⟨710491689866064496049807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1894644506309505322799485 710491689866064496049807)
      ·
        refine ⟨1065737534799096744074711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710491689866064496049807 1065737534799096744074711)
        ·
          refine ⟨1598606302198645116112067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065737534799096744074711 1598606302198645116112067)
          ·
            refine ⟨2397909453297967674168101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598606302198645116112067 2397909453297967674168101)
            ·
              refine ⟨449608022493368938906519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2397909453297967674168101 449608022493368938906519)
              ·
                refine ⟨674412033740053408359779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449608022493368938906519 674412033740053408359779)
                ·
                  refine ⟨1011618050610080112539669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674412033740053408359779 1011618050610080112539669)
                  ·
                    refine ⟨47419596122347505275297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1011618050610080112539669 47419596122347505275297)
                    ·
                      rfl

theorem cell22_138524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_138524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138524 prefixEnd_138524 := by exact prefixLift 138524
  have htrace : WordTrace (prefixWord ++ tailWord_138524) baseStart_138524 baseEnd_138524 := by
    simpa [prefixWord, tailWord_138524, baseEnd_138524] using wordTrace_append hprefix tailTrace_138524
  have hstable : (prefixWord ++ tailWord_138524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138524).length < 2 ^ (prefixWord ++ tailWord_138524).sum := by decide
  have hdescent : baseEnd_138524 < baseStart_138524 := by decide
  rcases family_descends (prefixWord ++ tailWord_138524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138605 : List Nat := [1, 5, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_138605 : Nat := 118140960795 + 138605 * 2 ^ 59
def prefixEnd_138605 : Nat := 4983230072969 + 3 ^ 40 * 138605 * 2
def baseEnd_138605 : Nat := 47447324077690294000049

theorem tailTrace_138605 : CollatzResearch.WordTrace tailWord_138605 prefixEnd_138605 47447324077690294000049 := by
  unfold tailWord_138605
  simp only [CollatzResearch.WordTrace]
  refine ⟨5055339662865231694497269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3370226441910154462998179 5055339662865231694497269)
  ·
    refine ⟨473938093393615471359119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5055339662865231694497269 473938093393615471359119)
    ·
      refine ⟨710907140090423207038679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 473938093393615471359119 710907140090423207038679)
      ·
        refine ⟨1066360710135634810558019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710907140090423207038679 1066360710135634810558019)
        ·
          refine ⟨1599541065203452215837029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066360710135634810558019 1599541065203452215837029)
          ·
            refine ⟨299913949725647290469443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1599541065203452215837029 299913949725647290469443)
            ·
              refine ⟨449870924588470935704165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299913949725647290469443 449870924588470935704165)
              ·
                refine ⟨84350798360338300444531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 449870924588470935704165 84350798360338300444531)
                ·
                  refine ⟨126526197540507450666797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84350798360338300444531 126526197540507450666797)
                  ·
                    refine ⟨47447324077690294000049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126526197540507450666797 47447324077690294000049)
                    ·
                      rfl

theorem cell22_138605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_138605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138605 prefixEnd_138605 := by exact prefixLift 138605
  have htrace : WordTrace (prefixWord ++ tailWord_138605) baseStart_138605 baseEnd_138605 := by
    simpa [prefixWord, tailWord_138605, baseEnd_138605] using wordTrace_append hprefix tailTrace_138605
  have hstable : (prefixWord ++ tailWord_138605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138605).length < 2 ^ (prefixWord ++ tailWord_138605).sum := by decide
  have hdescent : baseEnd_138605 < baseStart_138605 := by decide
  rcases family_descends (prefixWord ++ tailWord_138605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138622 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_138622 : Nat := 118140960795 + 138622 * 2 ^ 59
def prefixEnd_138622 : Nat := 4983230072969 + 3 ^ 40 * 138622 * 2
def baseEnd_138622 : Nat := 47453143525107916324997

theorem tailTrace_138622 : CollatzResearch.WordTrace tailWord_138622 prefixEnd_138622 47453143525107916324997 := by
  unfold tailWord_138622
  simp only [CollatzResearch.WordTrace]
  refine ⟨631994962975455449733265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3370639802535762398577413 631994962975455449733265)
  ·
    refine ⟨473996222231591587299949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 631994962975455449733265 473996222231591587299949)
    ·
      refine ⟨177748583336846845237481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 473996222231591587299949 177748583336846845237481)
      ·
        refine ⟨133311437502635133928111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177748583336846845237481 133311437502635133928111)
        ·
          refine ⟨199967156253952700892167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133311437502635133928111 199967156253952700892167)
          ·
            refine ⟨299950734380929051338251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199967156253952700892167 299950734380929051338251)
            ·
              refine ⟨449926101571393577007377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299950734380929051338251 449926101571393577007377)
              ·
                refine ⟨337444576178545182755533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449926101571393577007377 337444576178545182755533)
                ·
                  refine ⟨126541716066954443533325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 337444576178545182755533 126541716066954443533325)
                  ·
                    refine ⟨47453143525107916324997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126541716066954443533325 47453143525107916324997)
                    ·
                      rfl

theorem cell22_138622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_138622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138622 prefixEnd_138622 := by exact prefixLift 138622
  have htrace : WordTrace (prefixWord ++ tailWord_138622) baseStart_138622 baseEnd_138622 := by
    simpa [prefixWord, tailWord_138622, baseEnd_138622] using wordTrace_append hprefix tailTrace_138622
  have hstable : (prefixWord ++ tailWord_138622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138622).length < 2 ^ (prefixWord ++ tailWord_138622).sum := by decide
  have hdescent : baseEnd_138622 < baseStart_138622 := by decide
  rcases family_descends (prefixWord ++ tailWord_138622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138629 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 8]
def baseStart_138629 : Nat := 118140960795 + 138629 * 2 ^ 59
def prefixEnd_138629 : Nat := 4983230072969 + 3 ^ 40 * 138629 * 2
def baseEnd_138629 : Nat := 15818513256054077133325

theorem tailTrace_138629 : CollatzResearch.WordTrace tailWord_138629 prefixEnd_138629 15818513256054077133325 := by
  unfold tailWord_138629
  simp only [CollatzResearch.WordTrace]
  refine ⟨5056215014778283793370941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3370810009852189195580627 5056215014778283793370941)
  ·
    refine ⟨1896080630541856422514103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5056215014778283793370941 1896080630541856422514103)
    ·
      refine ⟨2844120945812784633771155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1896080630541856422514103 2844120945812784633771155)
      ·
        refine ⟨4266181418719176950656733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2844120945812784633771155 4266181418719176950656733)
        ·
          refine ⟨1599818032019691356496275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4266181418719176950656733 1599818032019691356496275)
          ·
            refine ⟨2399727048029537034744413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599818032019691356496275 2399727048029537034744413)
            ·
              refine ⟨899897643011076388029155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2399727048029537034744413 899897643011076388029155)
              ·
                refine ⟨1349846464516614582043733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899897643011076388029155 1349846464516614582043733)
                ·
                  refine ⟨15818513256054077133325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1349846464516614582043733 15818513256054077133325)
                  ·
                    rfl

theorem cell22_138629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_138629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138629 prefixEnd_138629 := by exact prefixLift 138629
  have htrace : WordTrace (prefixWord ++ tailWord_138629) baseStart_138629 baseEnd_138629 := by
    simpa [prefixWord, tailWord_138629, baseEnd_138629] using wordTrace_append hprefix tailTrace_138629
  have hstable : (prefixWord ++ tailWord_138629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138629).length < 2 ^ (prefixWord ++ tailWord_138629).sum := by decide
  have hdescent : baseEnd_138629 < baseStart_138629 := by decide
  rcases family_descends (prefixWord ++ tailWord_138629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138631 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 3, 4]
def baseStart_138631 : Nat := 118140960795 + 138631 * 2 ^ 59
def prefixEnd_138631 : Nat := 4983230072969 + 3 ^ 40 * 138631 * 2
def baseEnd_138631 : Nat := 47456224409034892849969

theorem tailTrace_138631 : CollatzResearch.WordTrace tailWord_138631 prefixEnd_138631 47456224409034892849969 := by
  unfold tailWord_138631
  simp only [CollatzResearch.WordTrace]
  refine ⟨5056287960771038134943747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3370858640514025423295831 5056287960771038134943747)
  ·
    refine ⟨7584431941156557202415621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5056287960771038134943747 7584431941156557202415621)
    ·
      refine ⟨1422080988966854475452929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7584431941156557202415621 1422080988966854475452929)
      ·
        refine ⟨1066560741725140856589697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1422080988966854475452929 1066560741725140856589697)
        ·
          refine ⟨799920556293855642442273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1066560741725140856589697 799920556293855642442273)
          ·
            refine ⟨599940417220391731831705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 799920556293855642442273 599940417220391731831705)
            ·
              refine ⟨449955312915293798873779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 599940417220391731831705 449955312915293798873779)
              ·
                refine ⟨674932969372940698310669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449955312915293798873779 674932969372940698310669)
                ·
                  refine ⟨253099863514852761866501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674932969372940698310669 253099863514852761866501)
                  ·
                    refine ⟨47456224409034892849969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 253099863514852761866501 47456224409034892849969)
                    ·
                      rfl

theorem cell22_138631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_138631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138631 prefixEnd_138631 := by exact prefixLift 138631
  have htrace : WordTrace (prefixWord ++ tailWord_138631) baseStart_138631 baseEnd_138631 := by
    simpa [prefixWord, tailWord_138631, baseEnd_138631] using wordTrace_append hprefix tailTrace_138631
  have hstable : (prefixWord ++ tailWord_138631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138631).length < 2 ^ (prefixWord ++ tailWord_138631).sum := by decide
  have hdescent : baseEnd_138631 < baseStart_138631 := by decide
  rcases family_descends (prefixWord ++ tailWord_138631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138652 : List Nat := [2, 2, 3, 4, 2, 1, 1, 2, 5]
def baseStart_138652 : Nat := 118140960795 + 138652 * 2 ^ 59
def prefixEnd_138652 : Nat := 4983230072969 + 3 ^ 40 * 138652 * 2
def baseEnd_138652 : Nat := 15821137712732612691635

theorem tailTrace_138652 : CollatzResearch.WordTrace tailWord_138652 prefixEnd_138652 15821137712732612691635 := by
  unfold tailWord_138652
  simp only [CollatzResearch.WordTrace]
  refine ⟨2528526946847479360729105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3371369262463305814305473 2528526946847479360729105)
  ·
    refine ⟨1896395210135609520546829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2528526946847479360729105 1896395210135609520546829)
    ·
      refine ⟨711148203800853570205061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1896395210135609520546829 711148203800853570205061)
      ·
        refine ⟨133340288212660044413449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 711148203800853570205061 133340288212660044413449)
        ·
          refine ⟨100005216159495033310087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133340288212660044413449 100005216159495033310087)
          ·
            refine ⟨150007824239242549965131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100005216159495033310087 150007824239242549965131)
            ·
              refine ⟨225011736358863824947697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150007824239242549965131 225011736358863824947697)
              ·
                refine ⟨168758802269147868710773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225011736358863824947697 168758802269147868710773)
                ·
                  refine ⟨15821137712732612691635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 168758802269147868710773 15821137712732612691635)
                  ·
                    rfl

theorem cell22_138652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_138652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138652 prefixEnd_138652 := by exact prefixLift 138652
  have htrace : WordTrace (prefixWord ++ tailWord_138652) baseStart_138652 baseEnd_138652 := by
    simpa [prefixWord, tailWord_138652, baseEnd_138652] using wordTrace_append hprefix tailTrace_138652
  have hstable : (prefixWord ++ tailWord_138652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138652).length < 2 ^ (prefixWord ++ tailWord_138652).sum := by decide
  have hdescent : baseEnd_138652 < baseStart_138652 := by decide
  rcases family_descends (prefixWord ++ tailWord_138652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138663 : List Nat := [1, 1, 6, 1, 1, 1, 1, 6, 4]
def baseStart_138663 : Nat := 118140960795 + 138663 * 2 ^ 59
def prefixEnd_138663 : Nat := 4983230072969 + 3 ^ 40 * 138663 * 2
def baseEnd_138663 : Nat := 15822392887665825349957

theorem tailTrace_138663 : CollatzResearch.WordTrace tailWord_138663 prefixEnd_138663 15822392887665825349957 := by
  unfold tailWord_138663
  simp only [CollatzResearch.WordTrace]
  refine ⟨5057455096655107600108643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3371636731103405066739095 5057455096655107600108643)
  ·
    refine ⟨7586182644982661400162965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5057455096655107600108643 7586182644982661400162965)
    ·
      refine ⟨355602311483562253132639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7586182644982661400162965 355602311483562253132639)
      ·
        refine ⟨533403467225343379698959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355602311483562253132639 533403467225343379698959)
        ·
          refine ⟨800105200838015069548439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533403467225343379698959 800105200838015069548439)
          ·
            refine ⟨1200157801257022604322659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800105200838015069548439 1200157801257022604322659)
            ·
              refine ⟨1800236701885533906483989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200157801257022604322659 1800236701885533906483989)
              ·
                refine ⟨84386095400884401866437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1800236701885533906483989 84386095400884401866437)
                ·
                  refine ⟨15822392887665825349957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84386095400884401866437 15822392887665825349957)
                  ·
                    rfl

theorem cell22_138663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 4].length) (baseStart_138663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138663 prefixEnd_138663 := by exact prefixLift 138663
  have htrace : WordTrace (prefixWord ++ tailWord_138663) baseStart_138663 baseEnd_138663 := by
    simpa [prefixWord, tailWord_138663, baseEnd_138663] using wordTrace_append hprefix tailTrace_138663
  have hstable : (prefixWord ++ tailWord_138663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138663).length < 2 ^ (prefixWord ++ tailWord_138663).sum := by decide
  have hdescent : baseEnd_138663 < baseStart_138663 := by decide
  rcases family_descends (prefixWord ++ tailWord_138663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138690 : List Nat := [3, 5, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_138690 : Nat := 118140960795 + 138690 * 2 ^ 59
def prefixEnd_138690 : Nat := 4983230072969 + 3 ^ 40 * 138690 * 2
def baseEnd_138690 : Nat := 47476421314778405624789

theorem tailTrace_138690 : CollatzResearch.WordTrace tailWord_138690 prefixEnd_138690 47476421314778405624789 := by
  unfold tailWord_138690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264609966889322802835381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3372293245038194140894349 1264609966889322802835381)
  ·
    refine ⟨118557184395874012765817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1264609966889322802835381 118557184395874012765817)
    ·
      refine ⟨88917888296905509574363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118557184395874012765817 88917888296905509574363)
      ·
        refine ⟨133376832445358264361545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88917888296905509574363 133376832445358264361545)
        ·
          refine ⟨100032624334018698271159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133376832445358264361545 100032624334018698271159)
          ·
            refine ⟨150048936501028047406739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100032624334018698271159 150048936501028047406739)
            ·
              refine ⟨225073404751542071110109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150048936501028047406739 225073404751542071110109)
              ·
                refine ⟨84402526781828276666291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225073404751542071110109 84402526781828276666291)
                ·
                  refine ⟨126603790172742414999437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84402526781828276666291 126603790172742414999437)
                  ·
                    refine ⟨47476421314778405624789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126603790172742414999437 47476421314778405624789)
                    ·
                      rfl

theorem cell22_138690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_138690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138690 prefixEnd_138690 := by exact prefixLift 138690
  have htrace : WordTrace (prefixWord ++ tailWord_138690) baseStart_138690 baseEnd_138690 := by
    simpa [prefixWord, tailWord_138690, baseEnd_138690] using wordTrace_append hprefix tailTrace_138690
  have hstable : (prefixWord ++ tailWord_138690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138690).length < 2 ^ (prefixWord ++ tailWord_138690).sum := by decide
  have hdescent : baseEnd_138690 < baseStart_138690 := by decide
  rcases family_descends (prefixWord ++ tailWord_138690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138691 : List Nat := [1, 1, 1, 3, 1, 1, 8, 6]
def baseStart_138691 : Nat := 118140960795 + 138691 * 2 ^ 59
def prefixEnd_138691 : Nat := 4983230072969 + 3 ^ 40 * 138691 * 2
def baseEnd_138691 : Nat := 5275195959468304038865

theorem tailTrace_138691 : CollatzResearch.WordTrace tailWord_138691 prefixEnd_138691 5275195959468304038865 := by
  unfold tailWord_138691
  simp only [CollatzResearch.WordTrace]
  refine ⟨5058476340553668382127927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3372317560369112254751951 5058476340553668382127927)
  ·
    refine ⟨7587714510830502573191891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5058476340553668382127927 7587714510830502573191891)
    ·
      refine ⟨11381571766245753859787837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7587714510830502573191891 11381571766245753859787837)
      ·
        refine ⟨4268089412342157697420439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11381571766245753859787837 4268089412342157697420439)
        ·
          refine ⟨6402134118513236546130659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4268089412342157697420439 6402134118513236546130659)
          ·
            refine ⟨9603201177769854819195989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6402134118513236546130659 9603201177769854819195989)
            ·
              refine ⟨112537513801990486162453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 9603201177769854819195989 112537513801990486162453)
              ·
                refine ⟨5275195959468304038865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112537513801990486162453 5275195959468304038865)
                ·
                  rfl

theorem cell22_138691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 6].length) (baseStart_138691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138691 prefixEnd_138691 := by exact prefixLift 138691
  have htrace : WordTrace (prefixWord ++ tailWord_138691) baseStart_138691 baseEnd_138691 := by
    simpa [prefixWord, tailWord_138691, baseEnd_138691] using wordTrace_append hprefix tailTrace_138691
  have hstable : (prefixWord ++ tailWord_138691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138691).length < 2 ^ (prefixWord ++ tailWord_138691).sum := by decide
  have hdescent : baseEnd_138691 < baseStart_138691 := by decide
  rcases family_descends (prefixWord ++ tailWord_138691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138708 : List Nat := [2, 4, 1, 2, 3, 2, 8]
def baseStart_138708 : Nat := 118140960795 + 138708 * 2 ^ 59
def prefixEnd_138708 : Nat := 4983230072969 + 3 ^ 40 * 138708 * 2
def baseEnd_138708 : Nat := 1758614188245642913879

theorem tailTrace_138708 : CollatzResearch.WordTrace tailWord_138708 prefixEnd_138708 1758614188245642913879 := by
  unfold tailWord_138708
  simp only [CollatzResearch.WordTrace]
  refine ⟨2529548190746040142748389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3372730920994720190331185 2529548190746040142748389)
  ·
    refine ⟨474290285764882526765323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2529548190746040142748389 474290285764882526765323)
    ·
      refine ⟨711435428647323790147985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474290285764882526765323 711435428647323790147985)
      ·
        refine ⟨533576571485492842610989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 711435428647323790147985 533576571485492842610989)
        ·
          refine ⟨200091214307059815979121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 533576571485492842610989 200091214307059815979121)
          ·
            refine ⟨150068410730294861984341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200091214307059815979121 150068410730294861984341)
            ·
              refine ⟨1758614188245642913879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 150068410730294861984341 1758614188245642913879)
              ·
                rfl

theorem cell22_138708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 8].length) (baseStart_138708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138708 prefixEnd_138708 := by exact prefixLift 138708
  have htrace : WordTrace (prefixWord ++ tailWord_138708) baseStart_138708 baseEnd_138708 := by
    simpa [prefixWord, tailWord_138708, baseEnd_138708] using wordTrace_append hprefix tailTrace_138708
  have hstable : (prefixWord ++ tailWord_138708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138708).length < 2 ^ (prefixWord ++ tailWord_138708).sum := by decide
  have hdescent : baseEnd_138708 < baseStart_138708 := by decide
  rcases family_descends (prefixWord ++ tailWord_138708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138710 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_138710 : Nat := 118140960795 + 138710 * 2 ^ 59
def prefixEnd_138710 : Nat := 4983230072969 + 3 ^ 40 * 138710 * 2
def baseEnd_138710 : Nat := 47483267723505020124727

theorem tailTrace_138710 : CollatzResearch.WordTrace tailWord_138710 prefixEnd_138710 47483267723505020124727 := by
  unfold tailWord_138710
  simp only [CollatzResearch.WordTrace]
  refine ⟨316198082967802164191849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3372779551656556418046389 316198082967802164191849)
  ·
    refine ⟨237148562225851623143887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 316198082967802164191849 237148562225851623143887)
    ·
      refine ⟨355722843338777434715831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237148562225851623143887 355722843338777434715831)
      ·
        refine ⟨533584265008166152073747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355722843338777434715831 533584265008166152073747)
        ·
          refine ⟨800376397512249228110621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533584265008166152073747 800376397512249228110621)
          ·
            refine ⟨300141149067093460541483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 800376397512249228110621 300141149067093460541483)
            ·
              refine ⟨450211723600640190812225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300141149067093460541483 450211723600640190812225)
              ·
                refine ⟨337658792700480143109169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450211723600640190812225 337658792700480143109169)
                ·
                  refine ⟨253244094525360107331877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337658792700480143109169 253244094525360107331877)
                  ·
                    refine ⟨47483267723505020124727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 253244094525360107331877 47483267723505020124727)
                    ·
                      rfl

theorem cell22_138710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_138710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138710 prefixEnd_138710 := by exact prefixLift 138710
  have htrace : WordTrace (prefixWord ++ tailWord_138710) baseStart_138710 baseEnd_138710 := by
    simpa [prefixWord, tailWord_138710, baseEnd_138710] using wordTrace_append hprefix tailTrace_138710
  have hstable : (prefixWord ++ tailWord_138710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138710).length < 2 ^ (prefixWord ++ tailWord_138710).sum := by decide
  have hdescent : baseEnd_138710 < baseStart_138710 := by decide
  rcases family_descends (prefixWord ++ tailWord_138710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138798 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_138798 : Nat := 118140960795 + 138798 * 2 ^ 59
def prefixEnd_138798 : Nat := 4983230072969 + 3 ^ 40 * 138798 * 2
def baseEnd_138798 : Nat := 15837797307300707974819

theorem tailTrace_138798 : CollatzResearch.WordTrace tailWord_138798 prefixEnd_138798 15837797307300707974819 := by
  unfold tailWord_138798
  simp only [CollatzResearch.WordTrace]
  refine ⟨632797368895753207034131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3374919300777350437515365 632797368895753207034131)
  ·
    refine ⟨949196053343629810551197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 632797368895753207034131 949196053343629810551197)
    ·
      refine ⟨355948520003861178956699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 949196053343629810551197 355948520003861178956699)
      ·
        refine ⟨533922780005791768435049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355948520003861178956699 533922780005791768435049)
        ·
          refine ⟨400442085004343826326287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533922780005791768435049 400442085004343826326287)
          ·
            refine ⟨600663127506515739489431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400442085004343826326287 600663127506515739489431)
            ·
              refine ⟨900994691259773609234147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600663127506515739489431 900994691259773609234147)
              ·
                refine ⟨1351492036889660413851221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900994691259773609234147 1351492036889660413851221)
                ·
                  refine ⟨15837797307300707974819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1351492036889660413851221 15837797307300707974819)
                  ·
                    rfl

theorem cell22_138798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_138798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138798 prefixEnd_138798 := by exact prefixLift 138798
  have htrace : WordTrace (prefixWord ++ tailWord_138798) baseStart_138798 baseEnd_138798 := by
    simpa [prefixWord, tailWord_138798, baseEnd_138798] using wordTrace_append hprefix tailTrace_138798
  have hstable : (prefixWord ++ tailWord_138798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138798).length < 2 ^ (prefixWord ++ tailWord_138798).sum := by decide
  have hdescent : baseEnd_138798 < baseStart_138798 := by decide
  rcases family_descends (prefixWord ++ tailWord_138798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138815 : List Nat := [1, 1, 2, 2, 3, 4, 2, 3, 4]
def baseStart_138815 : Nat := 118140960795 + 138815 * 2 ^ 59
def prefixEnd_138815 : Nat := 4983230072969 + 3 ^ 40 * 138815 * 2
def baseEnd_138815 : Nat := 15839737123106582083135

theorem tailTrace_138815 : CollatzResearch.WordTrace tailWord_138815 prefixEnd_138815 15839737123106582083135 := by
  unfold tailWord_138815
  simp only [CollatzResearch.WordTrace]
  refine ⟨5062998992104437559641899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3375332661402958373094599 5062998992104437559641899)
  ·
    refine ⟨7594498488156656339462849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5062998992104437559641899 7594498488156656339462849)
    ·
      refine ⟨5695873866117492254597137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7594498488156656339462849 5695873866117492254597137)
      ·
        refine ⟨4271905399588119190947853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5695873866117492254597137 4271905399588119190947853)
        ·
          refine ⟨1601964524845544696605445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4271905399588119190947853 1601964524845544696605445)
          ·
            refine ⟨300368348408539630613521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1601964524845544696605445 300368348408539630613521)
            ·
              refine ⟨225276261306404722960141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300368348408539630613521 225276261306404722960141)
              ·
                refine ⟨84478597989901771110053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225276261306404722960141 84478597989901771110053)
                ·
                  refine ⟨15839737123106582083135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84478597989901771110053 15839737123106582083135)
                  ·
                    rfl

theorem cell22_138815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 4].length) (baseStart_138815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138815 prefixEnd_138815 := by exact prefixLift 138815
  have htrace : WordTrace (prefixWord ++ tailWord_138815) baseStart_138815 baseEnd_138815 := by
    simpa [prefixWord, tailWord_138815, baseEnd_138815] using wordTrace_append hprefix tailTrace_138815
  have hstable : (prefixWord ++ tailWord_138815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138815).length < 2 ^ (prefixWord ++ tailWord_138815).sum := by decide
  have hdescent : baseEnd_138815 < baseStart_138815 := by decide
  rcases family_descends (prefixWord ++ tailWord_138815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138826 : List Nat := [3, 1, 2, 1, 1, 3, 11]
def baseStart_138826 : Nat := 118140960795 + 138826 * 2 ^ 59
def prefixEnd_138826 : Nat := 4983230072969 + 3 ^ 40 * 138826 * 2
def baseEnd_138826 : Nat := 1760110255337754971273

theorem tailTrace_138826 : CollatzResearch.WordTrace tailWord_138826 prefixEnd_138826 1760110255337754971273 := by
  unfold tailWord_138826
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265850048766146609573083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3375600130043057625528221 1265850048766146609573083)
  ·
    refine ⟨1898775073149219914359625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1265850048766146609573083 1898775073149219914359625)
    ·
      refine ⟨1424081304861914935769719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1898775073149219914359625 1424081304861914935769719)
      ·
        refine ⟨2136121957292872403654579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1424081304861914935769719 2136121957292872403654579)
        ·
          refine ⟨3204182935939308605481869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2136121957292872403654579 3204182935939308605481869)
          ·
            refine ⟨1201568600977240727055701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3204182935939308605481869 1201568600977240727055701)
            ·
              refine ⟨1760110255337754971273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1201568600977240727055701 1760110255337754971273)
              ·
                rfl

theorem cell22_138826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 11].length) (baseStart_138826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_138826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_138826 prefixEnd_138826 := by exact prefixLift 138826
  have htrace : WordTrace (prefixWord ++ tailWord_138826) baseStart_138826 baseEnd_138826 := by
    simpa [prefixWord, tailWord_138826, baseEnd_138826] using wordTrace_append hprefix tailTrace_138826
  have hstable : (prefixWord ++ tailWord_138826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138826).length < 2 ^ (prefixWord ++ tailWord_138826).sum := by decide
  have hdescent : baseEnd_138826 < baseStart_138826 := by decide
  rcases family_descends (prefixWord ++ tailWord_138826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139061 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 3, 3]
def baseStart_139061 : Nat := 118140960795 + 139061 * 2 ^ 59
def prefixEnd_139061 : Nat := 4983230072969 + 3 ^ 40 * 139061 * 2
def baseEnd_139061 : Nat := 47603422196657104598651

theorem tailTrace_139061 : CollatzResearch.WordTrace tailWord_139061 prefixEnd_139061 47603422196657104598651 := by
  unfold tailWord_139061
  simp only [CollatzResearch.WordTrace]
  refine ⟨5071971349213221573097037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3381314232808814382064691 5071971349213221573097037)
  ·
    refine ⟨1901989255954958089911389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5071971349213221573097037 1901989255954958089911389)
    ·
      refine ⟨713245970983109283716771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1901989255954958089911389 713245970983109283716771)
      ·
        refine ⟨1069868956474663925575157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713245970983109283716771 1069868956474663925575157)
        ·
          refine ⟨100300214669499743022671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1069868956474663925575157 100300214669499743022671)
          ·
            refine ⟨150450322004249614534007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100300214669499743022671 150450322004249614534007)
            ·
              refine ⟨225675483006374421801011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150450322004249614534007 225675483006374421801011)
              ·
                refine ⟨338513224509561632701517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225675483006374421801011 338513224509561632701517)
                ·
                  refine ⟨126942459191085612263069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338513224509561632701517 126942459191085612263069)
                  ·
                    refine ⟨47603422196657104598651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126942459191085612263069 47603422196657104598651)
                    ·
                      rfl

theorem cell22_139061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_139061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139061 prefixEnd_139061 := by exact prefixLift 139061
  have htrace : WordTrace (prefixWord ++ tailWord_139061) baseStart_139061 baseEnd_139061 := by
    simpa [prefixWord, tailWord_139061, baseEnd_139061] using wordTrace_append hprefix tailTrace_139061
  have hstable : (prefixWord ++ tailWord_139061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139061).length < 2 ^ (prefixWord ++ tailWord_139061).sum := by decide
  have hdescent : baseEnd_139061 < baseStart_139061 := by decide
  rcases family_descends (prefixWord ++ tailWord_139061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139104 : List Nat := [2, 1, 1, 3, 3, 3, 3, 1, 1, 4]
def baseStart_139104 : Nat := 118140960795 + 139104 * 2 ^ 59
def prefixEnd_139104 : Nat := 4983230072969 + 3 ^ 40 * 139104 * 2
def baseEnd_139104 : Nat := 47618141975419325773519

theorem tailTrace_139104 : CollatzResearch.WordTrace tailWord_139104 prefixEnd_139104 47618141975419325773519 := by
  unfold tailWord_139104
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536769844028719958456183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3382359792038293277941577 2536769844028719958456183)
  ·
    refine ⟨3805154766043079937684275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2536769844028719958456183 3805154766043079937684275)
    ·
      refine ⟨5707732149064619906526413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3805154766043079937684275 5707732149064619906526413)
      ·
        refine ⟨2140399555899232464947405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5707732149064619906526413 2140399555899232464947405)
        ·
          refine ⟨802649833462212174355277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2140399555899232464947405 802649833462212174355277)
          ·
            refine ⟨300993687548329565383229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 802649833462212174355277 300993687548329565383229)
            ·
              refine ⟨112872632830623587018711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 300993687548329565383229 112872632830623587018711)
              ·
                refine ⟨169308949245935380528067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112872632830623587018711 169308949245935380528067)
                ·
                  refine ⟨253963423868903070792101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169308949245935380528067 253963423868903070792101)
                  ·
                    refine ⟨47618141975419325773519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 253963423868903070792101 47618141975419325773519)
                    ·
                      rfl

theorem cell22_139104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 4].length) (baseStart_139104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139104 prefixEnd_139104 := by exact prefixLift 139104
  have htrace : WordTrace (prefixWord ++ tailWord_139104) baseStart_139104 baseEnd_139104 := by
    simpa [prefixWord, tailWord_139104, baseEnd_139104] using wordTrace_append hprefix tailTrace_139104
  have hstable : (prefixWord ++ tailWord_139104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139104).length < 2 ^ (prefixWord ++ tailWord_139104).sum := by decide
  have hdescent : baseEnd_139104 < baseStart_139104 := by decide
  rcases family_descends (prefixWord ++ tailWord_139104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139117 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_139117 : Nat := 118140960795 + 139117 * 2 ^ 59
def prefixEnd_139117 : Nat := 4983230072969 + 3 ^ 40 * 139117 * 2
def baseEnd_139117 : Nat := 47622592141091625198479

theorem tailTrace_139117 : CollatzResearch.WordTrace tailWord_139117 prefixEnd_139117 47622592141091625198479 := by
  unfold tailWord_139117
  simp only [CollatzResearch.WordTrace]
  refine ⟨5074013837010343137135605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3382675891340228758090403 5074013837010343137135605)
  ·
    refine ⟨475688797219719669106463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5074013837010343137135605 475688797219719669106463)
    ·
      refine ⟨713533195829579503659695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 475688797219719669106463 713533195829579503659695)
      ·
        refine ⟨1070299793744369255489543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713533195829579503659695 1070299793744369255489543)
        ·
          refine ⟨1605449690616553883234315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070299793744369255489543 1605449690616553883234315)
          ·
            refine ⟨2408174535924830824851473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605449690616553883234315 2408174535924830824851473)
            ·
              refine ⟨1806130901943623118638605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2408174535924830824851473 1806130901943623118638605)
              ·
                refine ⟨677299088228858669489477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1806130901943623118638605 677299088228858669489477)
                ·
                  refine ⟨126993579042911000529277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 677299088228858669489477 126993579042911000529277)
                  ·
                    refine ⟨47622592141091625198479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126993579042911000529277 47622592141091625198479)
                    ·
                      rfl

theorem cell22_139117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_139117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139117 prefixEnd_139117 := by exact prefixLift 139117
  have htrace : WordTrace (prefixWord ++ tailWord_139117) baseStart_139117 baseEnd_139117 := by
    simpa [prefixWord, tailWord_139117, baseEnd_139117] using wordTrace_append hprefix tailTrace_139117
  have hstable : (prefixWord ++ tailWord_139117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139117).length < 2 ^ (prefixWord ++ tailWord_139117).sum := by decide
  have hdescent : baseEnd_139117 < baseStart_139117 := by decide
  rcases family_descends (prefixWord ++ tailWord_139117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139130 : List Nat := [3, 1, 1, 1, 1, 1, 7, 7]
def baseStart_139130 : Nat := 118140960795 + 139130 * 2 ^ 59
def prefixEnd_139130 : Nat := 4983230072969 + 3 ^ 40 * 139130 * 2
def baseEnd_139130 : Nat := 5291893589640436069271

theorem tailTrace_139130 : CollatzResearch.WordTrace tailWord_139130 prefixEnd_139130 5291893589640436069271 := by
  unfold tailWord_139130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268621996490811589339711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3382991990642164238239229 1268621996490811589339711)
  ·
    refine ⟨1902932994736217384009567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1268621996490811589339711 1902932994736217384009567)
    ·
      refine ⟨2854399492104326076014351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902932994736217384009567 2854399492104326076014351)
      ·
        refine ⟨4281599238156489114021527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2854399492104326076014351 4281599238156489114021527)
        ·
          refine ⟨6422398857234733671032291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4281599238156489114021527 6422398857234733671032291)
          ·
            refine ⟨9633598285852100506548437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6422398857234733671032291 9633598285852100506548437)
            ·
              refine ⟨225787459824658605622229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9633598285852100506548437 225787459824658605622229)
              ·
                refine ⟨5291893589640436069271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 225787459824658605622229 5291893589640436069271)
                ·
                  rfl

theorem cell22_139130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_139130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139130 prefixEnd_139130 := by exact prefixLift 139130
  have htrace : WordTrace (prefixWord ++ tailWord_139130) baseStart_139130 baseEnd_139130 := by
    simpa [prefixWord, tailWord_139130, baseEnd_139130] using wordTrace_append hprefix tailTrace_139130
  have hstable : (prefixWord ++ tailWord_139130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139130).length < 2 ^ (prefixWord ++ tailWord_139130).sum := by decide
  have hdescent : baseEnd_139130 < baseStart_139130 := by decide
  rcases family_descends (prefixWord ++ tailWord_139130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139134 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_139134 : Nat := 118140960795 + 139134 * 2 ^ 59
def prefixEnd_139134 : Nat := 4983230072969 + 3 ^ 40 * 139134 * 2
def baseEnd_139134 : Nat := 47628411588509247523427

theorem tailTrace_139134 : CollatzResearch.WordTrace tailWord_139134 prefixEnd_139134 47628411588509247523427 := by
  unfold tailWord_139134
  simp only [CollatzResearch.WordTrace]
  refine ⟨634329234743594380063057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3383089251965836693669637 634329234743594380063057)
  ·
    refine ⟨475746926057695785047293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 634329234743594380063057 475746926057695785047293)
    ·
      refine ⟨178405097271635919392735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 475746926057695785047293 178405097271635919392735)
      ·
        refine ⟨267607645907453879089103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178405097271635919392735 267607645907453879089103)
        ·
          refine ⟨401411468861180818633655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267607645907453879089103 401411468861180818633655)
          ·
            refine ⟨602117203291771227950483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401411468861180818633655 602117203291771227950483)
            ·
              refine ⟨903175804937656841925725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602117203291771227950483 903175804937656841925725)
              ·
                refine ⟨338690926851621315722147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 903175804937656841925725 338690926851621315722147)
                ·
                  refine ⟨508036390277431973583221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338690926851621315722147 508036390277431973583221)
                  ·
                    refine ⟨47628411588509247523427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 508036390277431973583221 47628411588509247523427)
                    ·
                      rfl

theorem cell22_139134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_139134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139134 prefixEnd_139134 := by exact prefixLift 139134
  have htrace : WordTrace (prefixWord ++ tailWord_139134) baseStart_139134 baseEnd_139134 := by
    simpa [prefixWord, tailWord_139134, baseEnd_139134] using wordTrace_append hprefix tailTrace_139134
  have hstable : (prefixWord ++ tailWord_139134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139134).length < 2 ^ (prefixWord ++ tailWord_139134).sum := by decide
  have hdescent : baseEnd_139134 < baseStart_139134 := by decide
  rcases family_descends (prefixWord ++ tailWord_139134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139314 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_139314 : Nat := 118140960795 + 139314 * 2 ^ 59
def prefixEnd_139314 : Nat := 4983230072969 + 3 ^ 40 * 139314 * 2
def baseEnd_139314 : Nat := 47690029267048778022875

theorem tailTrace_139314 : CollatzResearch.WordTrace tailWord_139314 prefixEnd_139314 47690029267048778022875 := by
  unfold tailWord_139314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270299754324161445514249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3387466011531097188037997 1270299754324161445514249)
  ·
    refine ⟨952724815743121084135687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1270299754324161445514249 952724815743121084135687)
    ·
      refine ⟨1429087223614681626203531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952724815743121084135687 1429087223614681626203531)
      ·
        refine ⟨2143630835422022439305297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429087223614681626203531 2143630835422022439305297)
        ·
          refine ⟨1607723126566516829478973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2143630835422022439305297 1607723126566516829478973)
          ·
            refine ⟨602896172462443811054615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1607723126566516829478973 602896172462443811054615)
            ·
              refine ⟨904344258693665716581923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602896172462443811054615 904344258693665716581923)
              ·
                refine ⟨1356516388040498574872885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904344258693665716581923 1356516388040498574872885)
                ·
                  refine ⟨127173411378796741394333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1356516388040498574872885 127173411378796741394333)
                  ·
                    refine ⟨47690029267048778022875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127173411378796741394333 47690029267048778022875)
                    ·
                      rfl

theorem cell22_139314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_139314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139314 prefixEnd_139314 := by exact prefixLift 139314
  have htrace : WordTrace (prefixWord ++ tailWord_139314) baseStart_139314 baseEnd_139314 := by
    simpa [prefixWord, tailWord_139314, baseEnd_139314] using wordTrace_append hprefix tailTrace_139314
  have hstable : (prefixWord ++ tailWord_139314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139314).length < 2 ^ (prefixWord ++ tailWord_139314).sum := by decide
  have hdescent : baseEnd_139314 < baseStart_139314 := by decide
  rcases family_descends (prefixWord ++ tailWord_139314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139412 : List Nat := [2, 4, 2, 3, 2, 1, 2, 1, 5]
def baseStart_139412 : Nat := 118140960795 + 139412 * 2 ^ 59
def prefixEnd_139412 : Nat := 4983230072969 + 3 ^ 40 * 139412 * 2
def baseEnd_139412 : Nat := 15907858889936396357525

theorem tailTrace_139412 : CollatzResearch.WordTrace tailWord_139412 prefixEnd_139412 15907858889936396357525 := by
  unfold tailWord_139412
  simp only [CollatzResearch.WordTrace]
  refine ⟨2542386685470804259562245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3389848913961072346082993 2542386685470804259562245)
  ·
    refine ⟨476697503525775798667921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2542386685470804259562245 476697503525775798667921)
    ·
      refine ⟨357523127644331849000941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 476697503525775798667921 357523127644331849000941)
      ·
        refine ⟨134071172866624443375353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 357523127644331849000941 134071172866624443375353)
        ·
          refine ⟨100553379649968332531515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134071172866624443375353 100553379649968332531515)
          ·
            refine ⟨150830069474952498797273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100553379649968332531515 150830069474952498797273)
            ·
              refine ⟨113122552106214374097955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150830069474952498797273 113122552106214374097955)
              ·
                refine ⟨169683828159321561146933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113122552106214374097955 169683828159321561146933)
                ·
                  refine ⟨15907858889936396357525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169683828159321561146933 15907858889936396357525)
                  ·
                    rfl

theorem cell22_139412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_139412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139412 prefixEnd_139412 := by exact prefixLift 139412
  have htrace : WordTrace (prefixWord ++ tailWord_139412) baseStart_139412 baseEnd_139412 := by
    simpa [prefixWord, tailWord_139412, baseEnd_139412] using wordTrace_append hprefix tailTrace_139412
  have hstable : (prefixWord ++ tailWord_139412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139412).length < 2 ^ (prefixWord ++ tailWord_139412).sum := by decide
  have hdescent : baseEnd_139412 < baseStart_139412 := by decide
  rcases family_descends (prefixWord ++ tailWord_139412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139457 : List Nat := [1, 2, 6, 1, 2, 2, 2, 2, 4]
def baseStart_139457 : Nat := 118140960795 + 139457 * 2 ^ 59
def prefixEnd_139457 : Nat := 4983230072969 + 3 ^ 40 * 139457 * 2
def baseEnd_139457 : Nat := 15912993696481357232479

theorem tailTrace_139457 : CollatzResearch.WordTrace tailWord_139457 prefixEnd_139457 15912993696481357232479 := by
  unfold tailWord_139457
  simp only [CollatzResearch.WordTrace]
  refine ⟨5086414655778581204512625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3390943103852387469675083 5086414655778581204512625)
  ·
    refine ⟨3814810991833935903384469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5086414655778581204512625 3814810991833935903384469)
    ·
      refine ⟨178819265242215745471147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3814810991833935903384469 178819265242215745471147)
      ·
        refine ⟨268228897863323618206721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178819265242215745471147 268228897863323618206721)
        ·
          refine ⟨201171673397492713655041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268228897863323618206721 201171673397492713655041)
          ·
            refine ⟨150878755048119535241281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201171673397492713655041 150878755048119535241281)
            ·
              refine ⟨113159066286089651430961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150878755048119535241281 113159066286089651430961)
              ·
                refine ⟨84869299714567238573221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113159066286089651430961 84869299714567238573221)
                ·
                  refine ⟨15912993696481357232479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84869299714567238573221 15912993696481357232479)
                  ·
                    rfl

theorem cell22_139457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 4].length) (baseStart_139457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139457 prefixEnd_139457 := by exact prefixLift 139457
  have htrace : WordTrace (prefixWord ++ tailWord_139457) baseStart_139457 baseEnd_139457 := by
    simpa [prefixWord, tailWord_139457, baseEnd_139457] using wordTrace_append hprefix tailTrace_139457
  have hstable : (prefixWord ++ tailWord_139457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139457).length < 2 ^ (prefixWord ++ tailWord_139457).sum := by decide
  have hdescent : baseEnd_139457 < baseStart_139457 := by decide
  rcases family_descends (prefixWord ++ tailWord_139457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139466 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 3, 3]
def baseStart_139466 : Nat := 118140960795 + 139466 * 2 ^ 59
def prefixEnd_139466 : Nat := 4983230072969 + 3 ^ 40 * 139466 * 2
def baseEnd_139466 : Nat := 47742061973371048222409

theorem tailTrace_139466 : CollatzResearch.WordTrace tailWord_139466 prefixEnd_139466 47742061973371048222409 := by
  unfold tailWord_139466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1271685728186493935397563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3391161941830650494393501 1271685728186493935397563)
  ·
    refine ⟨1907528592279740903096345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1271685728186493935397563 1907528592279740903096345)
    ·
      refine ⟨1430646444209805677322259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1907528592279740903096345 1430646444209805677322259)
      ·
        refine ⟨2145969666314708515983389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430646444209805677322259 2145969666314708515983389)
        ·
          refine ⟨804738624868015693493771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2145969666314708515983389 804738624868015693493771)
          ·
            refine ⟨1207107937302023540240657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804738624868015693493771 1207107937302023540240657)
            ·
              refine ⟨905330952976517655180493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1207107937302023540240657 905330952976517655180493)
              ·
                refine ⟨339499107366194120692685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 905330952976517655180493 339499107366194120692685)
                ·
                  refine ⟨127312165262322795259757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339499107366194120692685 127312165262322795259757)
                  ·
                    refine ⟨47742061973371048222409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127312165262322795259757 47742061973371048222409)
                    ·
                      rfl

theorem cell22_139466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_139466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139466 prefixEnd_139466 := by exact prefixLift 139466
  have htrace : WordTrace (prefixWord ++ tailWord_139466) baseStart_139466 baseEnd_139466 := by
    simpa [prefixWord, tailWord_139466, baseEnd_139466] using wordTrace_append hprefix tailTrace_139466
  have hstable : (prefixWord ++ tailWord_139466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139466).length < 2 ^ (prefixWord ++ tailWord_139466).sum := by decide
  have hdescent : baseEnd_139466 < baseStart_139466 := by decide
  rcases family_descends (prefixWord ++ tailWord_139466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139468 : List Nat := [2, 2, 1, 6, 1, 2, 1, 7]
def baseStart_139468 : Nat := 118140960795 + 139468 * 2 ^ 59
def prefixEnd_139468 : Nat := 4983230072969 + 3 ^ 40 * 139468 * 2
def baseEnd_139468 : Nat := 5304749623804856630267

theorem tailTrace_139468 : CollatzResearch.WordTrace tailWord_139468 prefixEnd_139468 5304749623804856630267 := by
  unfold tailWord_139468
  simp only [CollatzResearch.WordTrace]
  refine ⟨2543407929369365041581529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3391210572492486722108705 2543407929369365041581529)
  ·
    refine ⟨1907555947027023781186147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2543407929369365041581529 1907555947027023781186147)
    ·
      refine ⟨2861333920540535671779221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907555947027023781186147 2861333920540535671779221)
      ·
        refine ⟨134125027525337609614651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2861333920540535671779221 134125027525337609614651)
        ·
          refine ⟨201187541288006414421977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134125027525337609614651 201187541288006414421977)
          ·
            refine ⟨150890655966004810816483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201187541288006414421977 150890655966004810816483)
            ·
              refine ⟨226335983949007216224725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150890655966004810816483 226335983949007216224725)
              ·
                refine ⟨5304749623804856630267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 226335983949007216224725 5304749623804856630267)
                ·
                  rfl

theorem cell22_139468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 7].length) (baseStart_139468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139468 prefixEnd_139468 := by exact prefixLift 139468
  have htrace : WordTrace (prefixWord ++ tailWord_139468) baseStart_139468 baseEnd_139468 := by
    simpa [prefixWord, tailWord_139468, baseEnd_139468] using wordTrace_append hprefix tailTrace_139468
  have hstable : (prefixWord ++ tailWord_139468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139468).length < 2 ^ (prefixWord ++ tailWord_139468).sum := by decide
  have hdescent : baseEnd_139468 < baseStart_139468 := by decide
  rcases family_descends (prefixWord ++ tailWord_139468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139543 : List Nat := [1, 1, 3, 4, 1, 3, 2, 2, 1, 4]
def baseStart_139543 : Nat := 118140960795 + 139543 * 2 ^ 59
def prefixEnd_139543 : Nat := 4983230072969 + 3 ^ 40 * 139543 * 2
def baseEnd_139543 : Nat := 47768420646968514047173

theorem tailTrace_139543 : CollatzResearch.WordTrace tailWord_139543 prefixEnd_139543 47768420646968514047173 := by
  unfold tailWord_139543
  simp only [CollatzResearch.WordTrace]
  refine ⟨5089551333467017892143283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3393034222311345261428855 5089551333467017892143283)
  ·
    refine ⟨7634327000200526838214925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5089551333467017892143283 7634327000200526838214925)
    ·
      refine ⟨2862872625075197564330597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7634327000200526838214925 2862872625075197564330597)
      ·
        refine ⟨536788617201599543311987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2862872625075197564330597 536788617201599543311987)
        ·
          refine ⟨805182925802399314967981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536788617201599543311987 805182925802399314967981)
          ·
            refine ⟨301943597175899743112993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 805182925802399314967981 301943597175899743112993)
            ·
              refine ⟨226457697881924807334745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301943597175899743112993 226457697881924807334745)
              ·
                refine ⟨169843273411443605501059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226457697881924807334745 169843273411443605501059)
                ·
                  refine ⟨254764910117165408251589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169843273411443605501059 254764910117165408251589)
                  ·
                    refine ⟨47768420646968514047173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 254764910117165408251589 47768420646968514047173)
                    ·
                      rfl

theorem cell22_139543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_139543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139543 prefixEnd_139543 := by exact prefixLift 139543
  have htrace : WordTrace (prefixWord ++ tailWord_139543) baseStart_139543 baseEnd_139543 := by
    simpa [prefixWord, tailWord_139543, baseEnd_139543] using wordTrace_append hprefix tailTrace_139543
  have hstable : (prefixWord ++ tailWord_139543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139543).length < 2 ^ (prefixWord ++ tailWord_139543).sum := by decide
  have hdescent : baseEnd_139543 < baseStart_139543 := by decide
  rcases family_descends (prefixWord ++ tailWord_139543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139571 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 2, 4]
def baseStart_139571 : Nat := 118140960795 + 139571 * 2 ^ 59
def prefixEnd_139571 : Nat := 4983230072969 + 3 ^ 40 * 139571 * 2
def baseEnd_139571 : Nat := 47778005619185774347087

theorem tailTrace_139571 : CollatzResearch.WordTrace tailWord_139571 prefixEnd_139571 47778005619185774347087 := by
  unfold tailWord_139571
  simp only [CollatzResearch.WordTrace]
  refine ⟨5090572577365578674162567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3393715051577052449441711 5090572577365578674162567)
  ·
    refine ⟨7635858866048368011243851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5090572577365578674162567 7635858866048368011243851)
    ·
      refine ⟨11453788299072552016865777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7635858866048368011243851 11453788299072552016865777)
      ·
        refine ⟨8590341224304414012649333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11453788299072552016865777 8590341224304414012649333)
        ·
          refine ⟨805344489778538813685875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8590341224304414012649333 805344489778538813685875)
          ·
            refine ⟨1208016734667808220528813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805344489778538813685875 1208016734667808220528813)
            ·
              refine ⟨453006275500428082698305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1208016734667808220528813 453006275500428082698305)
              ·
                refine ⟨339754706625321062023729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453006275500428082698305 339754706625321062023729)
                ·
                  refine ⟨254816029968990796517797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339754706625321062023729 254816029968990796517797)
                  ·
                    refine ⟨47778005619185774347087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 254816029968990796517797 47778005619185774347087)
                    ·
                      rfl

theorem cell22_139571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 4].length) (baseStart_139571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139571 prefixEnd_139571 := by exact prefixLift 139571
  have htrace : WordTrace (prefixWord ++ tailWord_139571) baseStart_139571 baseEnd_139571 := by
    simpa [prefixWord, tailWord_139571, baseEnd_139571] using wordTrace_append hprefix tailTrace_139571
  have hstable : (prefixWord ++ tailWord_139571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139571).length < 2 ^ (prefixWord ++ tailWord_139571).sum := by decide
  have hdescent : baseEnd_139571 < baseStart_139571 := by decide
  rcases family_descends (prefixWord ++ tailWord_139571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139573 : List Nat := [1, 3, 3, 1, 2, 1, 2, 4, 2, 3]
def baseStart_139573 : Nat := 118140960795 + 139573 * 2 ^ 59
def prefixEnd_139573 : Nat := 4983230072969 + 3 ^ 40 * 139573 * 2
def baseEnd_139573 : Nat := 47778690260058435797081

theorem tailTrace_139573 : CollatzResearch.WordTrace tailWord_139573 prefixEnd_139573 47778690260058435797081 := by
  unfold tailWord_139573
  simp only [CollatzResearch.WordTrace]
  refine ⟨5090645523358333015735373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3393763682238888677156915 5090645523358333015735373)
  ·
    refine ⟨1908992071259374880900765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5090645523358333015735373 1908992071259374880900765)
    ·
      refine ⟨715872026722265580337787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1908992071259374880900765 715872026722265580337787)
      ·
        refine ⟨1073808040083398370506681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715872026722265580337787 1073808040083398370506681)
        ·
          refine ⟨805356030062548777880011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1073808040083398370506681 805356030062548777880011)
          ·
            refine ⟨1208034045093823166820017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805356030062548777880011 1208034045093823166820017)
            ·
              refine ⟨906025533820367375115013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1208034045093823166820017 906025533820367375115013)
              ·
                refine ⟨169879787591318882834065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 906025533820367375115013 169879787591318882834065)
                ·
                  refine ⟨127409840693489162125549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169879787591318882834065 127409840693489162125549)
                  ·
                    refine ⟨47778690260058435797081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127409840693489162125549 47778690260058435797081)
                    ·
                      rfl

theorem cell22_139573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_139573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139573 prefixEnd_139573 := by exact prefixLift 139573
  have htrace : WordTrace (prefixWord ++ tailWord_139573) baseStart_139573 baseEnd_139573 := by
    simpa [prefixWord, tailWord_139573, baseEnd_139573] using wordTrace_append hprefix tailTrace_139573
  have hstable : (prefixWord ++ tailWord_139573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139573).length < 2 ^ (prefixWord ++ tailWord_139573).sum := by decide
  have hdescent : baseEnd_139573 < baseStart_139573 := by decide
  rcases family_descends (prefixWord ++ tailWord_139573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139584 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 2, 7]
def baseStart_139584 : Nat := 118140960795 + 139584 * 2 ^ 59
def prefixEnd_139584 : Nat := 4983230072969 + 3 ^ 40 * 139584 * 2
def baseEnd_139584 : Nat := 47782455784858073772047

theorem tailTrace_139584 : CollatzResearch.WordTrace tailWord_139584 prefixEnd_139584 47782455784858073772047 := by
  unfold tailWord_139584
  simp only [CollatzResearch.WordTrace]
  refine ⟨2545523363159240947192903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3394031150878987929590537 2545523363159240947192903)
  ·
    refine ⟨3818285044738861420789355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2545523363159240947192903 3818285044738861420789355)
    ·
      refine ⟨5727427567108292131184033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3818285044738861420789355 5727427567108292131184033)
      ·
        refine ⟨4295570675331219098388025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5727427567108292131184033 4295570675331219098388025)
        ·
          refine ⟨3221678006498414323791019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4295570675331219098388025 3221678006498414323791019)
          ·
            refine ⟨4832517009747621485686529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221678006498414323791019 4832517009747621485686529)
            ·
              refine ⟨3624387757310716114264897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4832517009747621485686529 3624387757310716114264897)
              ·
                refine ⟨2718290817983037085698673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3624387757310716114264897 2718290817983037085698673)
                ·
                  refine ⟨2038718113487277814274005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2718290817983037085698673 2038718113487277814274005)
                  ·
                    refine ⟨47782455784858073772047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2038718113487277814274005 47782455784858073772047)
                    ·
                      rfl

theorem cell22_139584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_139584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139584 prefixEnd_139584 := by exact prefixLift 139584
  have htrace : WordTrace (prefixWord ++ tailWord_139584) baseStart_139584 baseEnd_139584 := by
    simpa [prefixWord, tailWord_139584, baseEnd_139584] using wordTrace_append hprefix tailTrace_139584
  have hstable : (prefixWord ++ tailWord_139584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139584).length < 2 ^ (prefixWord ++ tailWord_139584).sum := by decide
  have hdescent : baseEnd_139584 < baseStart_139584 := by decide
  rcases family_descends (prefixWord ++ tailWord_139584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139599 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 4, 6]
def baseStart_139599 : Nat := 118140960795 + 139599 * 2 ^ 59
def prefixEnd_139599 : Nat := 4983230072969 + 3 ^ 40 * 139599 * 2
def baseEnd_139599 : Nat := 47787590591403034647001

theorem tailTrace_139599 : CollatzResearch.WordTrace tailWord_139599 prefixEnd_139599 47787590591403034647001 := by
  unfold tailWord_139599
  simp only [CollatzResearch.WordTrace]
  refine ⟨5091593821264139456181851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3394395880842759637454567 5091593821264139456181851)
  ·
    refine ⟨7637390731896209184272777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5091593821264139456181851 7637390731896209184272777)
    ·
      refine ⟨5728043048922156888204583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7637390731896209184272777 5728043048922156888204583)
      ·
        refine ⟨8592064573383235332306875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5728043048922156888204583 8592064573383235332306875)
        ·
          refine ⟨12888096860074852998460313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8592064573383235332306875 12888096860074852998460313)
          ·
            refine ⟨9666072645056139748845235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12888096860074852998460313 9666072645056139748845235)
            ·
              refine ⟨14499108967584209623267853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9666072645056139748845235 14499108967584209623267853)
              ·
                refine ⟨5437165862844078608725445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14499108967584209623267853 5437165862844078608725445)
                ·
                  refine ⟨1019468599283264739136021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5437165862844078608725445 1019468599283264739136021)
                  ·
                    refine ⟨47787590591403034647001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1019468599283264739136021 47787590591403034647001)
                    ·
                      rfl

theorem cell22_139599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_139599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139599 prefixEnd_139599 := by exact prefixLift 139599
  have htrace : WordTrace (prefixWord ++ tailWord_139599) baseStart_139599 baseEnd_139599 := by
    simpa [prefixWord, tailWord_139599, baseEnd_139599] using wordTrace_append hprefix tailTrace_139599
  have hstable : (prefixWord ++ tailWord_139599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139599).length < 2 ^ (prefixWord ++ tailWord_139599).sum := by decide
  have hdescent : baseEnd_139599 < baseStart_139599 := by decide
  rcases family_descends (prefixWord ++ tailWord_139599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139753 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 3, 3]
def baseStart_139753 : Nat := 118140960795 + 139753 * 2 ^ 59
def prefixEnd_139753 : Nat := 4983230072969 + 3 ^ 40 * 139753 * 2
def baseEnd_139753 : Nat := 47840307938597966296529

theorem tailTrace_139753 : CollatzResearch.WordTrace tailWord_139753 prefixEnd_139753 47840307938597966296529 := by
  unfold tailWord_139753
  simp only [CollatzResearch.WordTrace]
  refine ⟨5097210662706223757287913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3398140441804149171525275 5097210662706223757287913)
  ·
    refine ⟨3822907997029667817965935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5097210662706223757287913 3822907997029667817965935)
    ·
      refine ⟨5734361995544501726948903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3822907997029667817965935 5734361995544501726948903)
      ·
        refine ⟨8601542993316752590423355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5734361995544501726948903 8601542993316752590423355)
        ·
          refine ⟨12902314489975128885635033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8601542993316752590423355 12902314489975128885635033)
          ·
            refine ⟨9676735867481346664226275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12902314489975128885635033 9676735867481346664226275)
            ·
              refine ⟨14515103801222019996339413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9676735867481346664226275 14515103801222019996339413)
              ·
                refine ⟨340197745341141093664205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14515103801222019996339413 340197745341141093664205)
                ·
                  refine ⟨127574154502927910124077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340197745341141093664205 127574154502927910124077)
                  ·
                    refine ⟨47840307938597966296529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127574154502927910124077 47840307938597966296529)
                    ·
                      rfl

theorem cell22_139753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 3].length) (baseStart_139753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139753 prefixEnd_139753 := by exact prefixLift 139753
  have htrace : WordTrace (prefixWord ++ tailWord_139753) baseStart_139753 baseEnd_139753 := by
    simpa [prefixWord, tailWord_139753, baseEnd_139753] using wordTrace_append hprefix tailTrace_139753
  have hstable : (prefixWord ++ tailWord_139753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139753).length < 2 ^ (prefixWord ++ tailWord_139753).sum := by decide
  have hdescent : baseEnd_139753 < baseStart_139753 := by decide
  rcases family_descends (prefixWord ++ tailWord_139753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139800 : List Nat := [2, 1, 2, 3, 3, 2, 2, 2, 5]
def baseStart_139800 : Nat := 118140960795 + 139800 * 2 ^ 59
def prefixEnd_139800 : Nat := 4983230072969 + 3 ^ 40 * 139800 * 2
def baseEnd_139800 : Nat := 15952132333035170123795

theorem tailTrace_139800 : CollatzResearch.WordTrace tailWord_139800 prefixEnd_139800 15952132333035170123795 := by
  unfold tailWord_139800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549462446767975392124427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3399283262357300522832569 2549462446767975392124427)
  ·
    refine ⟨3824193670151963088186641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2549462446767975392124427 3824193670151963088186641)
    ·
      refine ⟨2868145252613972316139981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3824193670151963088186641 2868145252613972316139981)
      ·
        refine ⟨1075554469730239618552493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2868145252613972316139981 1075554469730239618552493)
        ·
          refine ⟨403332926148839856957185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1075554469730239618552493 403332926148839856957185)
          ·
            refine ⟨302499694611629892717889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403332926148839856957185 302499694611629892717889)
            ·
              refine ⟨226874770958722419538417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302499694611629892717889 226874770958722419538417)
              ·
                refine ⟨170156078219041814653813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226874770958722419538417 170156078219041814653813)
                ·
                  refine ⟨15952132333035170123795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 170156078219041814653813 15952132333035170123795)
                  ·
                    rfl

theorem cell22_139800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_139800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139800 prefixEnd_139800 := by exact prefixLift 139800
  have htrace : WordTrace (prefixWord ++ tailWord_139800) baseStart_139800 baseEnd_139800 := by
    simpa [prefixWord, tailWord_139800, baseEnd_139800] using wordTrace_append hprefix tailTrace_139800
  have hstable : (prefixWord ++ tailWord_139800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139800).length < 2 ^ (prefixWord ++ tailWord_139800).sum := by decide
  have hdescent : baseEnd_139800 < baseStart_139800 := by decide
  rcases family_descends (prefixWord ++ tailWord_139800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139804 : List Nat := [2, 2, 3, 1, 2, 2, 4, 2, 1, 3]
def baseStart_139804 : Nat := 118140960795 + 139804 * 2 ^ 59
def prefixEnd_139804 : Nat := 4983230072969 + 3 ^ 40 * 139804 * 2
def baseEnd_139804 : Nat := 47857766280850833271373

theorem tailTrace_139804 : CollatzResearch.WordTrace tailWord_139804 prefixEnd_139804 47857766280850833271373 := by
  unfold tailWord_139804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549535392760729733697233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3399380523680972978262977 2549535392760729733697233)
  ·
    refine ⟨1912151544570547300272925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2549535392760729733697233 1912151544570547300272925)
    ·
      refine ⟨717056829213955237602347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1912151544570547300272925 717056829213955237602347)
      ·
        refine ⟨1075585243820932856403521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717056829213955237602347 1075585243820932856403521)
        ·
          refine ⟨806688932865699642302641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1075585243820932856403521 806688932865699642302641)
          ·
            refine ⟨605016699649274731726981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806688932865699642302641 605016699649274731726981)
            ·
              refine ⟨113440631184239012198809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 605016699649274731726981 113440631184239012198809)
              ·
                refine ⟨85080473388179259149107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113440631184239012198809 85080473388179259149107)
                ·
                  refine ⟨127620710082268888723661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85080473388179259149107 127620710082268888723661)
                  ·
                    refine ⟨47857766280850833271373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127620710082268888723661 47857766280850833271373)
                    ·
                      rfl

theorem cell22_139804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_139804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139804 prefixEnd_139804 := by exact prefixLift 139804
  have htrace : WordTrace (prefixWord ++ tailWord_139804) baseStart_139804 baseEnd_139804 := by
    simpa [prefixWord, tailWord_139804, baseEnd_139804] using wordTrace_append hprefix tailTrace_139804
  have hstable : (prefixWord ++ tailWord_139804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139804).length < 2 ^ (prefixWord ++ tailWord_139804).sum := by decide
  have hdescent : baseEnd_139804 < baseStart_139804 := by decide
  rcases family_descends (prefixWord ++ tailWord_139804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139813 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_139813 : Nat := 118140960795 + 139813 * 2 ^ 59
def prefixEnd_139813 : Nat := 4983230072969 + 3 ^ 40 * 139813 * 2
def baseEnd_139813 : Nat := 47860847164777809796345

theorem tailTrace_139813 : CollatzResearch.WordTrace tailWord_139813 prefixEnd_139813 47860847164777809796345 := by
  unfold tailWord_139813
  simp only [CollatzResearch.WordTrace]
  refine ⟨5099399042488854004472093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3399599361659236002981395 5099399042488854004472093)
  ·
    refine ⟨1912274640933320251677035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5099399042488854004472093 1912274640933320251677035)
    ·
      refine ⟨2868411961399980377515553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1912274640933320251677035 2868411961399980377515553)
      ·
        refine ⟨2151308971049985283136665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2868411961399980377515553 2151308971049985283136665)
        ·
          refine ⟨1613481728287488962352499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2151308971049985283136665 1613481728287488962352499)
          ·
            refine ⟨2420222592431233443528749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613481728287488962352499 2420222592431233443528749)
            ·
              refine ⟨907583472161712541323281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2420222592431233443528749 907583472161712541323281)
              ·
                refine ⟨680687604121284405992461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 907583472161712541323281 680687604121284405992461)
                ·
                  refine ⟨255257851545481652247173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680687604121284405992461 255257851545481652247173)
                  ·
                    refine ⟨47860847164777809796345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 255257851545481652247173 47860847164777809796345)
                    ·
                      rfl

theorem cell22_139813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_139813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139813 prefixEnd_139813 := by exact prefixLift 139813
  have htrace : WordTrace (prefixWord ++ tailWord_139813) baseStart_139813 baseEnd_139813 := by
    simpa [prefixWord, tailWord_139813, baseEnd_139813] using wordTrace_append hprefix tailTrace_139813
  have hstable : (prefixWord ++ tailWord_139813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139813).length < 2 ^ (prefixWord ++ tailWord_139813).sum := by decide
  have hdescent : baseEnd_139813 < baseStart_139813 := by decide
  rcases family_descends (prefixWord ++ tailWord_139813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139821 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_139821 : Nat := 118140960795 + 139821 * 2 ^ 59
def prefixEnd_139821 : Nat := 4983230072969 + 3 ^ 40 * 139821 * 2
def baseEnd_139821 : Nat := 47863585728268455596321

theorem tailTrace_139821 : CollatzResearch.WordTrace tailWord_139821 prefixEnd_139821 47863585728268455596321 := by
  unfold tailWord_139821
  simp only [CollatzResearch.WordTrace]
  refine ⟨5099690826459871370763317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3399793884306580913842211 5099690826459871370763317)
  ·
    refine ⟨478096014980612941009061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5099690826459871370763317 478096014980612941009061)
    ·
      refine ⟨89643002808864926439199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 478096014980612941009061 89643002808864926439199)
      ·
        refine ⟨134464504213297389658799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89643002808864926439199 134464504213297389658799)
        ·
          refine ⟨201696756319946084488199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134464504213297389658799 201696756319946084488199)
          ·
            refine ⟨302545134479919126732299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201696756319946084488199 302545134479919126732299)
            ·
              refine ⟨453817701719878690098449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302545134479919126732299 453817701719878690098449)
              ·
                refine ⟨340363276289909017573837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453817701719878690098449 340363276289909017573837)
                ·
                  refine ⟨127636228608715881590189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340363276289909017573837 127636228608715881590189)
                  ·
                    refine ⟨47863585728268455596321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127636228608715881590189 47863585728268455596321)
                    ·
                      rfl

theorem cell22_139821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_139821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139821 prefixEnd_139821 := by exact prefixLift 139821
  have htrace : WordTrace (prefixWord ++ tailWord_139821) baseStart_139821 baseEnd_139821 := by
    simpa [prefixWord, tailWord_139821, baseEnd_139821] using wordTrace_append hprefix tailTrace_139821
  have hstable : (prefixWord ++ tailWord_139821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139821).length < 2 ^ (prefixWord ++ tailWord_139821).sum := by decide
  have hdescent : baseEnd_139821 < baseStart_139821 := by decide
  rcases family_descends (prefixWord ++ tailWord_139821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139845 : List Nat := [1, 3, 1, 1, 1, 5, 1, 5, 4]
def baseStart_139845 : Nat := 118140960795 + 139845 * 2 ^ 59
def prefixEnd_139845 : Nat := 4983230072969 + 3 ^ 40 * 139845 * 2
def baseEnd_139845 : Nat := 15957267139580130998749

theorem tailTrace_139845 : CollatzResearch.WordTrace tailWord_139845 prefixEnd_139845 15957267139580130998749 := by
  unfold tailWord_139845
  simp only [CollatzResearch.WordTrace]
  refine ⟨5100566178372923469636989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3400377452248615646424659 5100566178372923469636989)
  ·
    refine ⟨1912712316889846301113871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5100566178372923469636989 1912712316889846301113871)
    ·
      refine ⟨2869068475334769451670807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1912712316889846301113871 2869068475334769451670807)
      ·
        refine ⟨4303602713002154177506211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869068475334769451670807 4303602713002154177506211)
        ·
          refine ⟨6455404069503231266259317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4303602713002154177506211 6455404069503231266259317)
          ·
            refine ⟨605194131515927931211811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6455404069503231266259317 605194131515927931211811)
            ·
              refine ⟨907791197273891896817717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605194131515927931211811 907791197273891896817717)
              ·
                refine ⟨85105424744427365326661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 907791197273891896817717 85105424744427365326661)
                ·
                  refine ⟨15957267139580130998749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85105424744427365326661 15957267139580130998749)
                  ·
                    rfl

theorem cell22_139845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_139845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139845 prefixEnd_139845 := by exact prefixLift 139845
  have htrace : WordTrace (prefixWord ++ tailWord_139845) baseStart_139845 baseEnd_139845 := by
    simpa [prefixWord, tailWord_139845, baseEnd_139845] using wordTrace_append hprefix tailTrace_139845
  have hstable : (prefixWord ++ tailWord_139845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139845).length < 2 ^ (prefixWord ++ tailWord_139845).sum := by decide
  have hdescent : baseEnd_139845 < baseStart_139845 := by decide
  rcases family_descends (prefixWord ++ tailWord_139845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139847 : List Nat := [1, 1, 4, 1, 4, 1, 4, 1, 1, 4]
def baseStart_139847 : Nat := 118140960795 + 139847 * 2 ^ 59
def prefixEnd_139847 : Nat := 4983230072969 + 3 ^ 40 * 139847 * 2
def baseEnd_139847 : Nat := 47872486059613054446241

theorem tailTrace_139847 : CollatzResearch.WordTrace tailWord_139847 prefixEnd_139847 47872486059613054446241 := by
  unfold tailWord_139847
  simp only [CollatzResearch.WordTrace]
  refine ⟨5100639124365677811209795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3400426082910451874139863 5100639124365677811209795)
  ·
    refine ⟨7650958686548516716814693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5100639124365677811209795 7650958686548516716814693)
    ·
      refine ⟨1434554753727846884402755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7650958686548516716814693 1434554753727846884402755)
      ·
        refine ⟨2151832130591770326604133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1434554753727846884402755 2151832130591770326604133)
        ·
          refine ⟨403468524485956936238275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2151832130591770326604133 403468524485956936238275)
          ·
            refine ⟨605202786728935404357413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403468524485956936238275 605202786728935404357413)
            ·
              refine ⟨113475522511675388317015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 605202786728935404357413 113475522511675388317015)
              ·
                refine ⟨170213283767513082475523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113475522511675388317015 170213283767513082475523)
                ·
                  refine ⟨255319925651269623713285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170213283767513082475523 255319925651269623713285)
                  ·
                    refine ⟨47872486059613054446241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 255319925651269623713285 47872486059613054446241)
                    ·
                      rfl

theorem cell22_139847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_139847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139847 prefixEnd_139847 := by exact prefixLift 139847
  have htrace : WordTrace (prefixWord ++ tailWord_139847) baseStart_139847 baseEnd_139847 := by
    simpa [prefixWord, tailWord_139847, baseEnd_139847] using wordTrace_append hprefix tailTrace_139847
  have hstable : (prefixWord ++ tailWord_139847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139847).length < 2 ^ (prefixWord ++ tailWord_139847).sum := by decide
  have hdescent : baseEnd_139847 < baseStart_139847 := by decide
  rcases family_descends (prefixWord ++ tailWord_139847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139877 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 1, 5]
def baseStart_139877 : Nat := 118140960795 + 139877 * 2 ^ 59
def prefixEnd_139877 : Nat := 4983230072969 + 3 ^ 40 * 139877 * 2
def baseEnd_139877 : Nat := 47882755672702976196149

theorem tailTrace_139877 : CollatzResearch.WordTrace tailWord_139877 prefixEnd_139877 47882755672702976196149 := by
  unfold tailWord_139877
  simp only [CollatzResearch.WordTrace]
  refine ⟨5101733314256992934801885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3401155542837995289867923 5101733314256992934801885)
  ·
    refine ⟨1913149992846372350550707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5101733314256992934801885 1913149992846372350550707)
    ·
      refine ⟨2869724989269558525826061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1913149992846372350550707 2869724989269558525826061)
      ·
        refine ⟨1076146870976084447184773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2869724989269558525826061 1076146870976084447184773)
        ·
          refine ⟨201777538308015833847145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1076146870976084447184773 201777538308015833847145)
          ·
            refine ⟨151333153731011875385359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201777538308015833847145 151333153731011875385359)
            ·
              refine ⟨226999730596517813078039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151333153731011875385359 226999730596517813078039)
              ·
                refine ⟨340499595894776719617059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226999730596517813078039 340499595894776719617059)
                ·
                  refine ⟨510749393842165079425589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340499595894776719617059 510749393842165079425589)
                  ·
                    refine ⟨47882755672702976196149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 510749393842165079425589 47882755672702976196149)
                    ·
                      rfl

theorem cell22_139877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_139877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139877 prefixEnd_139877 := by exact prefixLift 139877
  have htrace : WordTrace (prefixWord ++ tailWord_139877) baseStart_139877 baseEnd_139877 := by
    simpa [prefixWord, tailWord_139877, baseEnd_139877] using wordTrace_append hprefix tailTrace_139877
  have hstable : (prefixWord ++ tailWord_139877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139877).length < 2 ^ (prefixWord ++ tailWord_139877).sum := by decide
  have hdescent : baseEnd_139877 < baseStart_139877 := by decide
  rcases family_descends (prefixWord ++ tailWord_139877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139890 : List Nat := [3, 2, 1, 2, 4, 1, 1, 8]
def baseStart_139890 : Nat := 118140960795 + 139890 * 2 ^ 59
def prefixEnd_139890 : Nat := 4983230072969 + 3 ^ 40 * 139890 * 2
def baseEnd_139890 : Nat := 5320800648708363957901

theorem tailTrace_139890 : CollatzResearch.WordTrace tailWord_139890 prefixEnd_139890 5320800648708363957901 := by
  unfold tailWord_139890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1275551865802474038756281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3401471642139930770016749 1275551865802474038756281)
  ·
    refine ⟨956663899351855529067211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1275551865802474038756281 956663899351855529067211)
    ·
      refine ⟨1434995849027783293600817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 956663899351855529067211 1434995849027783293600817)
      ·
        refine ⟨1076246886770837470200613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1434995849027783293600817 1076246886770837470200613)
        ·
          refine ⟨201796291269532025662615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1076246886770837470200613 201796291269532025662615)
          ·
            refine ⟨302694436904298038493923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201796291269532025662615 302694436904298038493923)
            ·
              refine ⟨454041655356447057740885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302694436904298038493923 454041655356447057740885)
              ·
                refine ⟨5320800648708363957901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 454041655356447057740885 5320800648708363957901)
                ·
                  rfl

theorem cell22_139890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_139890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_139890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_139890 prefixEnd_139890 := by exact prefixLift 139890
  have htrace : WordTrace (prefixWord ++ tailWord_139890) baseStart_139890 baseEnd_139890 := by
    simpa [prefixWord, tailWord_139890, baseEnd_139890] using wordTrace_append hprefix tailTrace_139890
  have hstable : (prefixWord ++ tailWord_139890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139890).length < 2 ^ (prefixWord ++ tailWord_139890).sum := by decide
  have hdescent : baseEnd_139890 < baseStart_139890 := by decide
  rcases family_descends (prefixWord ++ tailWord_139890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140014 : List Nat := [4, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_140014 : Nat := 118140960795 + 140014 * 2 ^ 59
def prefixEnd_140014 : Nat := 4983230072969 + 3 ^ 40 * 140014 * 2
def baseEnd_140014 : Nat := 15976551190826761840243

theorem tailTrace_140014 : CollatzResearch.WordTrace tailWord_140014 prefixEnd_140014 15976551190826761840243 := by
  unfold tailWord_140014
  simp only [CollatzResearch.WordTrace]
  refine ⟨638341264345083166567387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3404486743173776888359397 638341264345083166567387)
  ·
    refine ⟨957511896517624749851081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 638341264345083166567387 957511896517624749851081)
    ·
      refine ⟨718133922388218562388311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 957511896517624749851081 718133922388218562388311)
      ·
        refine ⟨1077200883582327843582467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718133922388218562388311 1077200883582327843582467)
        ·
          refine ⟨1615801325373491765373701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077200883582327843582467 1615801325373491765373701)
          ·
            refine ⟨302962748507529706007569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1615801325373491765373701 302962748507529706007569)
            ·
              refine ⟨227222061380647279505677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302962748507529706007569 227222061380647279505677)
              ·
                refine ⟨85208273017742729814629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227222061380647279505677 85208273017742729814629)
                ·
                  refine ⟨15976551190826761840243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85208273017742729814629 15976551190826761840243)
                  ·
                    rfl

theorem cell22_140014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_140014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140014 prefixEnd_140014 := by exact prefixLift 140014
  have htrace : WordTrace (prefixWord ++ tailWord_140014) baseStart_140014 baseEnd_140014 := by
    simpa [prefixWord, tailWord_140014, baseEnd_140014] using wordTrace_append hprefix tailTrace_140014
  have hstable : (prefixWord ++ tailWord_140014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140014).length < 2 ^ (prefixWord ++ tailWord_140014).sum := by decide
  have hdescent : baseEnd_140014 < baseStart_140014 := by decide
  rcases family_descends (prefixWord ++ tailWord_140014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140115 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 6]
def baseStart_140115 : Nat := 118140960795 + 140115 * 2 ^ 59
def prefixEnd_140115 : Nat := 4983230072969 + 3 ^ 40 * 140115 * 2
def baseEnd_140115 : Nat := 15988075978849896248473

theorem tailTrace_140115 : CollatzResearch.WordTrace tailWord_140115 prefixEnd_140115 15988075978849896248473 := by
  unfold tailWord_140115
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110413887394759581965799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3406942591596506387977199 5110413887394759581965799)
  ·
    refine ⟨7665620831092139372948699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5110413887394759581965799 7665620831092139372948699)
    ·
      refine ⟨11498431246638209059423049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7665620831092139372948699 11498431246638209059423049)
      ·
        refine ⟨8623823434978656794567287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11498431246638209059423049 8623823434978656794567287)
        ·
          refine ⟨12935735152467985191850931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8623823434978656794567287 12935735152467985191850931)
          ·
            refine ⟨19403602728701977787776397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12935735152467985191850931 19403602728701977787776397)
            ·
              refine ⟨7276351023263241670416149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19403602728701977787776397 7276351023263241670416149)
              ·
                refine ⟨341078954215464453300757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7276351023263241670416149 341078954215464453300757)
                ·
                  refine ⟨15988075978849896248473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 341078954215464453300757 15988075978849896248473)
                  ·
                    rfl

theorem cell22_140115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 6].length) (baseStart_140115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140115 prefixEnd_140115 := by exact prefixLift 140115
  have htrace : WordTrace (prefixWord ++ tailWord_140115) baseStart_140115 baseEnd_140115 := by
    simpa [prefixWord, tailWord_140115, baseEnd_140115] using wordTrace_append hprefix tailTrace_140115
  have hstable : (prefixWord ++ tailWord_140115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140115).length < 2 ^ (prefixWord ++ tailWord_140115).sum := by decide
  have hdescent : baseEnd_140115 < baseStart_140115 := by decide
  rcases family_descends (prefixWord ++ tailWord_140115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140117 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_140117 : Nat := 118140960795 + 140117 * 2 ^ 59
def prefixEnd_140117 : Nat := 4983230072969 + 3 ^ 40 * 140117 * 2
def baseEnd_140117 : Nat := 47964912577422350195413

theorem tailTrace_140117 : CollatzResearch.WordTrace tailWord_140117 prefixEnd_140117 47964912577422350195413 := by
  unfold tailWord_140117
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110486833387513923538605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3406991222258342615692403 5110486833387513923538605)
  ·
    refine ⟨1916432562520317721326977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5110486833387513923538605 1916432562520317721326977)
    ·
      refine ⟨1437324421890238290995233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1916432562520317721326977 1437324421890238290995233)
      ·
        refine ⟨1077993316417678718246425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1437324421890238290995233 1077993316417678718246425)
        ·
          refine ⟨808494987313259038684819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1077993316417678718246425 808494987313259038684819)
          ·
            refine ⟨1212742480969888558027229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808494987313259038684819 1212742480969888558027229)
            ·
              refine ⟨454778430363708209260211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1212742480969888558027229 454778430363708209260211)
              ·
                refine ⟨682167645545562313890317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454778430363708209260211 682167645545562313890317)
                ·
                  refine ⟨255812867079585867708869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682167645545562313890317 255812867079585867708869)
                  ·
                    refine ⟨47964912577422350195413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 255812867079585867708869 47964912577422350195413)
                    ·
                      rfl

theorem cell22_140117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_140117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140117 prefixEnd_140117 := by exact prefixLift 140117
  have htrace : WordTrace (prefixWord ++ tailWord_140117) baseStart_140117 baseEnd_140117 := by
    simpa [prefixWord, tailWord_140117, baseEnd_140117] using wordTrace_append hprefix tailTrace_140117
  have hstable : (prefixWord ++ tailWord_140117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140117).length < 2 ^ (prefixWord ++ tailWord_140117).sum := by decide
  have hdescent : baseEnd_140117 < baseStart_140117 := by decide
  rcases family_descends (prefixWord ++ tailWord_140117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140142 : List Nat := [4, 1, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_140142 : Nat := 118140960795 + 140142 * 2 ^ 59
def prefixEnd_140142 : Nat := 4983230072969 + 3 ^ 40 * 140142 * 2
def baseEnd_140142 : Nat := 47973470588330618320337

theorem tailTrace_140142 : CollatzResearch.WordTrace tailWord_140142 prefixEnd_140142 47973470588330618320337 := by
  unfold tailWord_140142
  simp only [CollatzResearch.WordTrace]
  refine ⟨638924832287117899149835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3407599105531295462132453 638924832287117899149835)
  ·
    refine ⟨958387248430676848724753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 638924832287117899149835 958387248430676848724753)
    ·
      refine ⟨718790436323007636543565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 958387248430676848724753 718790436323007636543565)
      ·
        refine ⟨269546413621127863703837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 718790436323007636543565 269546413621127863703837)
        ·
          refine ⟨101079905107922948888939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269546413621127863703837 101079905107922948888939)
          ·
            refine ⟨151619857661884423333409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101079905107922948888939 151619857661884423333409)
            ·
              refine ⟨113714893246413317500057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151619857661884423333409 113714893246413317500057)
              ·
                refine ⟨85286169934809988125043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113714893246413317500057 85286169934809988125043)
                ·
                  refine ⟨127929254902214982187565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85286169934809988125043 127929254902214982187565)
                  ·
                    refine ⟨47973470588330618320337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127929254902214982187565 47973470588330618320337)
                    ·
                      rfl

theorem cell22_140142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_140142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140142 prefixEnd_140142 := by exact prefixLift 140142
  have htrace : WordTrace (prefixWord ++ tailWord_140142) baseStart_140142 baseEnd_140142 := by
    simpa [prefixWord, tailWord_140142, baseEnd_140142] using wordTrace_append hprefix tailTrace_140142
  have hstable : (prefixWord ++ tailWord_140142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140142).length < 2 ^ (prefixWord ++ tailWord_140142).sum := by decide
  have hdescent : baseEnd_140142 < baseStart_140142 := by decide
  rcases family_descends (prefixWord ++ tailWord_140142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140147 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 4, 3]
def baseStart_140147 : Nat := 118140960795 + 140147 * 2 ^ 59
def prefixEnd_140147 : Nat := 4983230072969 + 3 ^ 40 * 140147 * 2
def baseEnd_140147 : Nat := 47975182190512271945321

theorem tailTrace_140147 : CollatzResearch.WordTrace tailWord_140147 prefixEnd_140147 47975182190512271945321 := by
  unfold tailWord_140147
  simp only [CollatzResearch.WordTrace]
  refine ⟨5111581023278829047130695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3407720682185886031420463 5111581023278829047130695)
  ·
    refine ⟨7667371534918243570696043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5111581023278829047130695 7667371534918243570696043)
    ·
      refine ⟨11501057302377365356044065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7667371534918243570696043 11501057302377365356044065)
      ·
        refine ⟨8625792976783024017033049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11501057302377365356044065 8625792976783024017033049)
        ·
          refine ⟨6469344732587268012774787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8625792976783024017033049 6469344732587268012774787)
          ·
            refine ⟨9704017098880902019162181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6469344732587268012774787 9704017098880902019162181)
            ·
              refine ⟨1819503206040169128592909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9704017098880902019162181 1819503206040169128592909)
              ·
                refine ⟨682313702265063423222341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1819503206040169128592909 682313702265063423222341)
                ·
                  refine ⟨127933819174699391854189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 682313702265063423222341 127933819174699391854189)
                  ·
                    refine ⟨47975182190512271945321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127933819174699391854189 47975182190512271945321)
                    ·
                      rfl

theorem cell22_140147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 3].length) (baseStart_140147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140147 prefixEnd_140147 := by exact prefixLift 140147
  have htrace : WordTrace (prefixWord ++ tailWord_140147) baseStart_140147 baseEnd_140147 := by
    simpa [prefixWord, tailWord_140147, baseEnd_140147] using wordTrace_append hprefix tailTrace_140147
  have hstable : (prefixWord ++ tailWord_140147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140147).length < 2 ^ (prefixWord ++ tailWord_140147).sum := by decide
  have hdescent : baseEnd_140147 < baseStart_140147 := by decide
  rcases family_descends (prefixWord ++ tailWord_140147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140160 : List Nat := [2, 1, 1, 2, 1, 2, 2, 11]
def baseStart_140160 : Nat := 118140960795 + 140160 * 2 ^ 59
def prefixEnd_140160 : Nat := 4983230072969 + 3 ^ 40 * 140160 * 2
def baseEnd_140160 : Nat := 5331070261798285707809

theorem tailTrace_140160 : CollatzResearch.WordTrace tailWord_140160 prefixEnd_140160 5331070261798285707809 := by
  unfold tailWord_140160
  simp only [CollatzResearch.WordTrace]
  refine ⟨2556027586115866133676967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3408036781487821511569289 2556027586115866133676967)
  ·
    refine ⟨3834041379173799200515451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2556027586115866133676967 3834041379173799200515451)
    ·
      refine ⟨5751062068760698800773177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3834041379173799200515451 5751062068760698800773177)
      ·
        refine ⟨4313296551570524100579883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5751062068760698800773177 4313296551570524100579883)
        ·
          refine ⟨6469944827355786150869825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4313296551570524100579883 6469944827355786150869825)
          ·
            refine ⟨4852458620516839613152369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6469944827355786150869825 4852458620516839613152369)
            ·
              refine ⟨3639343965387629709864277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4852458620516839613152369 3639343965387629709864277)
              ·
                refine ⟨5331070261798285707809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 3639343965387629709864277 5331070261798285707809)
                ·
                  rfl

theorem cell22_140160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 11].length) (baseStart_140160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140160 prefixEnd_140160 := by exact prefixLift 140160
  have htrace : WordTrace (prefixWord ++ tailWord_140160) baseStart_140160 baseEnd_140160 := by
    simpa [prefixWord, tailWord_140160, baseEnd_140160] using wordTrace_append hprefix tailTrace_140160
  have hstable : (prefixWord ++ tailWord_140160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140160).length < 2 ^ (prefixWord ++ tailWord_140160).sum := by decide
  have hdescent : baseEnd_140160 < baseStart_140160 := by decide
  rcases family_descends (prefixWord ++ tailWord_140160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140228 : List Nat := [2, 3, 3, 3, 1, 2, 2, 6]
def baseStart_140228 : Nat := 118140960795 + 140228 * 2 ^ 59
def prefixEnd_140228 : Nat := 4983230072969 + 3 ^ 40 * 140228 * 2
def baseEnd_140228 : Nat := 5333656682872784518897

theorem tailTrace_140228 : CollatzResearch.WordTrace tailWord_140228 prefixEnd_140228 5333656682872784518897 := by
  unfold tailWord_140228
  simp only [CollatzResearch.WordTrace]
  refine ⟨2557267667992689940414669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3409690223990253253886225 2557267667992689940414669)
  ·
    refine ⟨958975375497258727655501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2557267667992689940414669 958975375497258727655501)
    ·
      refine ⟨359615765811472022870813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 958975375497258727655501 359615765811472022870813)
      ·
        refine ⟨134855912179302008576555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359615765811472022870813 134855912179302008576555)
        ·
          refine ⟨202283868268953012864833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134855912179302008576555 202283868268953012864833)
          ·
            refine ⟨151712901201714759648625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202283868268953012864833 151712901201714759648625)
            ·
              refine ⟨113784675901286069736469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151712901201714759648625 113784675901286069736469)
              ·
                refine ⟨5333656682872784518897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113784675901286069736469 5333656682872784518897)
                ·
                  rfl

theorem cell22_140228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 6].length) (baseStart_140228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140228 prefixEnd_140228 := by exact prefixLift 140228
  have htrace : WordTrace (prefixWord ++ tailWord_140228) baseStart_140228 baseEnd_140228 := by
    simpa [prefixWord, tailWord_140228, baseEnd_140228] using wordTrace_append hprefix tailTrace_140228
  have hstable : (prefixWord ++ tailWord_140228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140228).length < 2 ^ (prefixWord ++ tailWord_140228).sum := by decide
  have hdescent : baseEnd_140228 < baseStart_140228 := by decide
  rcases family_descends (prefixWord ++ tailWord_140228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140282 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_140282 : Nat := 118140960795 + 140282 * 2 ^ 59
def prefixEnd_140282 : Nat := 4983230072969 + 3 ^ 40 * 140282 * 2
def baseEnd_140282 : Nat := 48021395449416919819907

theorem tailTrace_140282 : CollatzResearch.WordTrace tailWord_140282 prefixEnd_140282 48021395449416919819907 := by
  unfold tailWord_140282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1279126219447436775823775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3411003251859831402196733 1279126219447436775823775)
  ·
    refine ⟨1918689329171155163735663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1279126219447436775823775 1918689329171155163735663)
    ·
      refine ⟨2878033993756732745603495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1918689329171155163735663 2878033993756732745603495)
      ·
        refine ⟨4317050990635099118405243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2878033993756732745603495 4317050990635099118405243)
        ·
          refine ⟨6475576485952648677607865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4317050990635099118405243 6475576485952648677607865)
          ·
            refine ⟨4856682364464486508205899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6475576485952648677607865 4856682364464486508205899)
            ·
              refine ⟨7285023546696729762308849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856682364464486508205899 7285023546696729762308849)
              ·
                refine ⟨5463767660022547321731637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7285023546696729762308849 5463767660022547321731637)
                ·
                  refine ⟨512228218127113811412341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5463767660022547321731637 512228218127113811412341)
                  ·
                    refine ⟨48021395449416919819907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 512228218127113811412341 48021395449416919819907)
                    ·
                      rfl

theorem cell22_140282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_140282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140282 prefixEnd_140282 := by exact prefixLift 140282
  have htrace : WordTrace (prefixWord ++ tailWord_140282) baseStart_140282 baseEnd_140282 := by
    simpa [prefixWord, tailWord_140282, baseEnd_140282] using wordTrace_append hprefix tailTrace_140282
  have hstable : (prefixWord ++ tailWord_140282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140282).length < 2 ^ (prefixWord ++ tailWord_140282).sum := by decide
  have hdescent : baseEnd_140282 < baseStart_140282 := by decide
  rcases family_descends (prefixWord ++ tailWord_140282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140297 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 1, 6]
def baseStart_140297 : Nat := 118140960795 + 140297 * 2 ^ 59
def prefixEnd_140297 : Nat := 4983230072969 + 3 ^ 40 * 140297 * 2
def baseEnd_140297 : Nat := 48026530255961880694861

theorem tailTrace_140297 : CollatzResearch.WordTrace tailWord_140297 prefixEnd_140297 48026530255961880694861 := by
  unfold tailWord_140297
  simp only [CollatzResearch.WordTrace]
  refine ⟨5117051972735404665091145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3411367981823603110060763 5117051972735404665091145)
  ·
    refine ⟨3837788979551553498818359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5117051972735404665091145 3837788979551553498818359)
    ·
      refine ⟨5756683469327330248227539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3837788979551553498818359 5756683469327330248227539)
      ·
        refine ⟨8635025203990995372341309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5756683469327330248227539 8635025203990995372341309)
        ·
          refine ⟨3238134451496623264627991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8635025203990995372341309 3238134451496623264627991)
          ·
            refine ⟨4857201677244934896941987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3238134451496623264627991 4857201677244934896941987)
            ·
              refine ⟨7285802515867402345412981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4857201677244934896941987 7285802515867402345412981)
              ·
                refine ⟨683043985862568969882467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7285802515867402345412981 683043985862568969882467)
                ·
                  refine ⟨1024565978793853454823701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683043985862568969882467 1024565978793853454823701)
                  ·
                    refine ⟨48026530255961880694861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1024565978793853454823701 48026530255961880694861)
                    ·
                      rfl

theorem cell22_140297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_140297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140297 prefixEnd_140297 := by exact prefixLift 140297
  have htrace : WordTrace (prefixWord ++ tailWord_140297) baseStart_140297 baseEnd_140297 := by
    simpa [prefixWord, tailWord_140297, baseEnd_140297] using wordTrace_append hprefix tailTrace_140297
  have hstable : (prefixWord ++ tailWord_140297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140297).length < 2 ^ (prefixWord ++ tailWord_140297).sum := by decide
  have hdescent : baseEnd_140297 < baseStart_140297 := by decide
  rcases family_descends (prefixWord ++ tailWord_140297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140299 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 1, 5]
def baseStart_140299 : Nat := 118140960795 + 140299 * 2 ^ 59
def prefixEnd_140299 : Nat := 4983230072969 + 3 ^ 40 * 140299 * 2
def baseEnd_140299 : Nat := 48027214896834542144855

theorem tailTrace_140299 : CollatzResearch.WordTrace tailWord_140299 prefixEnd_140299 48027214896834542144855 := by
  unfold tailWord_140299
  simp only [CollatzResearch.WordTrace]
  refine ⟨5117124918728159006663951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3411416612485439337775967 5117124918728159006663951)
  ·
    refine ⟨7675687378092238509995927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5117124918728159006663951 7675687378092238509995927)
    ·
      refine ⟨11513531067138357764993891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7675687378092238509995927 11513531067138357764993891)
      ·
        refine ⟨17270296600707536647490837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11513531067138357764993891 17270296600707536647490837)
        ·
          refine ⟨809545153158165780351133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17270296600707536647490837 809545153158165780351133)
          ·
            refine ⟨303579432434312167631675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 809545153158165780351133 303579432434312167631675)
            ·
              refine ⟨455369148651468251447513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303579432434312167631675 455369148651468251447513)
              ·
                refine ⟨341526861488601188585635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455369148651468251447513 341526861488601188585635)
                ·
                  refine ⟨512290292232901782878453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341526861488601188585635 512290292232901782878453)
                  ·
                    refine ⟨48027214896834542144855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 512290292232901782878453 48027214896834542144855)
                    ·
                      rfl

theorem cell22_140299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 5].length) (baseStart_140299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140299 prefixEnd_140299 := by exact prefixLift 140299
  have htrace : WordTrace (prefixWord ++ tailWord_140299) baseStart_140299 baseEnd_140299 := by
    simpa [prefixWord, tailWord_140299, baseEnd_140299] using wordTrace_append hprefix tailTrace_140299
  have hstable : (prefixWord ++ tailWord_140299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140299).length < 2 ^ (prefixWord ++ tailWord_140299).sum := by decide
  have hdescent : baseEnd_140299 < baseStart_140299 := by decide
  rcases family_descends (prefixWord ++ tailWord_140299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140312 : List Nat := [2, 1, 2, 3, 2, 12]
def baseStart_140312 : Nat := 118140960795 + 140312 * 2 ^ 59
def prefixEnd_140312 : Nat := 4983230072969 + 3 ^ 40 * 140312 * 2
def baseEnd_140312 : Nat := 592983519290207920615

theorem tailTrace_140312 : CollatzResearch.WordTrace tailWord_140312 prefixEnd_140312 592983519290207920615 := by
  unfold tailWord_140312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2558799533840531113443595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3411732711787374817924793 2558799533840531113443595)
  ·
    refine ⟨3838199300760796670165393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2558799533840531113443595 3838199300760796670165393)
    ·
      refine ⟨2878649475570597502624045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3838199300760796670165393 2878649475570597502624045)
      ·
        refine ⟨1079493553338974063484017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2878649475570597502624045 1079493553338974063484017)
        ·
          refine ⟨809620165004230547613013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1079493553338974063484017 809620165004230547613013)
          ·
            refine ⟨592983519290207920615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 809620165004230547613013 592983519290207920615)
            ·
              rfl

theorem cell22_140312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 12].length) (baseStart_140312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140312 prefixEnd_140312 := by exact prefixLift 140312
  have htrace : WordTrace (prefixWord ++ tailWord_140312) baseStart_140312 baseEnd_140312 := by
    simpa [prefixWord, tailWord_140312, baseEnd_140312] using wordTrace_append hprefix tailTrace_140312
  have hstable : (prefixWord ++ tailWord_140312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140312).length < 2 ^ (prefixWord ++ tailWord_140312).sum := by decide
  have hdescent : baseEnd_140312 < baseStart_140312 := by decide
  rcases family_descends (prefixWord ++ tailWord_140312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140314 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_140314 : Nat := 118140960795 + 140314 * 2 ^ 59
def prefixEnd_140314 : Nat := 4983230072969 + 3 ^ 40 * 140314 * 2
def baseEnd_140314 : Nat := 48032349703379503019809

theorem tailTrace_140314 : CollatzResearch.WordTrace tailWord_140314 prefixEnd_140314 48032349703379503019809 := by
  unfold tailWord_140314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1279418003418454142114999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3411781342449211045639997 1279418003418454142114999)
  ·
    refine ⟨1919127005127681213172499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1279418003418454142114999 1919127005127681213172499)
    ·
      refine ⟨2878690507691521819758749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1919127005127681213172499 2878690507691521819758749)
      ·
        refine ⟨1079508940384320682409531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2878690507691521819758749 1079508940384320682409531)
        ·
          refine ⟨1619263410576481023614297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1079508940384320682409531 1619263410576481023614297)
          ·
            refine ⟨1214447557932360767710723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1619263410576481023614297 1214447557932360767710723)
            ·
              refine ⟨1821671336898541151566085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214447557932360767710723 1821671336898541151566085)
              ·
                refine ⟨341563375668476465918641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1821671336898541151566085 341563375668476465918641)
                ·
                  refine ⟨256172531751357349438981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341563375668476465918641 256172531751357349438981)
                  ·
                    refine ⟨48032349703379503019809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 256172531751357349438981 48032349703379503019809)
                    ·
                      rfl

theorem cell22_140314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_140314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140314 prefixEnd_140314 := by exact prefixLift 140314
  have htrace : WordTrace (prefixWord ++ tailWord_140314) baseStart_140314 baseEnd_140314 := by
    simpa [prefixWord, tailWord_140314, baseEnd_140314] using wordTrace_append hprefix tailTrace_140314
  have hstable : (prefixWord ++ tailWord_140314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140314).length < 2 ^ (prefixWord ++ tailWord_140314).sum := by decide
  have hdescent : baseEnd_140314 < baseStart_140314 := by decide
  rcases family_descends (prefixWord ++ tailWord_140314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140389 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_140389 : Nat := 118140960795 + 140389 * 2 ^ 59
def prefixEnd_140389 : Nat := 4983230072969 + 3 ^ 40 * 140389 * 2
def baseEnd_140389 : Nat := 48058023736104307394579

theorem tailTrace_140389 : CollatzResearch.WordTrace tailWord_140389 prefixEnd_140389 48058023736104307394579 := by
  unfold tailWord_140389
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120407488402104377440221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3413604992268069584960147 5120407488402104377440221)
  ·
    refine ⟨1920152808150789141540083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5120407488402104377440221 1920152808150789141540083)
    ·
      refine ⟨2880229212226183712310125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1920152808150789141540083 2880229212226183712310125)
      ·
        refine ⟨1080085954584818892116297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2880229212226183712310125 1080085954584818892116297)
        ·
          refine ⟨810064465938614169087223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1080085954584818892116297 810064465938614169087223)
          ·
            refine ⟨1215096698907921253630835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810064465938614169087223 1215096698907921253630835)
            ·
              refine ⟨1822645048361881880446253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215096698907921253630835 1822645048361881880446253)
              ·
                refine ⟨683491893135705705167345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1822645048361881880446253 683491893135705705167345)
                ·
                  refine ⟨512618919851779278875509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 683491893135705705167345 512618919851779278875509)
                  ·
                    refine ⟨48058023736104307394579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 512618919851779278875509 48058023736104307394579)
                    ·
                      rfl

theorem cell22_140389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_140389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140389 prefixEnd_140389 := by exact prefixLift 140389
  have htrace : WordTrace (prefixWord ++ tailWord_140389) baseStart_140389 baseEnd_140389 := by
    simpa [prefixWord, tailWord_140389, baseEnd_140389] using wordTrace_append hprefix tailTrace_140389
  have hstable : (prefixWord ++ tailWord_140389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140389).length < 2 ^ (prefixWord ++ tailWord_140389).sum := by decide
  have hdescent : baseEnd_140389 < baseStart_140389 := by decide
  rcases family_descends (prefixWord ++ tailWord_140389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140455 : List Nat := [1, 1, 6, 2, 1, 3, 1, 2, 1, 4]
def baseStart_140455 : Nat := 118140960795 + 140455 * 2 ^ 59
def prefixEnd_140455 : Nat := 4983230072969 + 3 ^ 40 * 140455 * 2
def baseEnd_140455 : Nat := 48080616884902135244377

theorem tailTrace_140455 : CollatzResearch.WordTrace tailWord_140455 prefixEnd_140455 48080616884902135244377 := by
  unfold tailWord_140455
  simp only [CollatzResearch.WordTrace]
  refine ⟨5122814706162997649342819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3415209804108665099561879 5122814706162997649342819)
  ·
    refine ⟨7684222059244496474014229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5122814706162997649342819 7684222059244496474014229)
    ·
      refine ⟨360197909027085772219417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7684222059244496474014229 360197909027085772219417)
      ·
        refine ⟨270148431770314329164563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360197909027085772219417 270148431770314329164563)
        ·
          refine ⟨405222647655471493746845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270148431770314329164563 405222647655471493746845)
          ·
            refine ⟨151958492870801810155067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 405222647655471493746845 151958492870801810155067)
            ·
              refine ⟨227937739306202715232601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151958492870801810155067 227937739306202715232601)
              ·
                refine ⟨170953304479652036424451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227937739306202715232601 170953304479652036424451)
                ·
                  refine ⟨256429956719478054636677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170953304479652036424451 256429956719478054636677)
                  ·
                    refine ⟨48080616884902135244377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 256429956719478054636677 48080616884902135244377)
                    ·
                      rfl

theorem cell22_140455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_140455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140455 prefixEnd_140455 := by exact prefixLift 140455
  have htrace : WordTrace (prefixWord ++ tailWord_140455) baseStart_140455 baseEnd_140455 := by
    simpa [prefixWord, tailWord_140455, baseEnd_140455] using wordTrace_append hprefix tailTrace_140455
  have hstable : (prefixWord ++ tailWord_140455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140455).length < 2 ^ (prefixWord ++ tailWord_140455).sum := by decide
  have hdescent : baseEnd_140455 < baseStart_140455 := by decide
  rcases family_descends (prefixWord ++ tailWord_140455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140466 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_140466 : Nat := 118140960795 + 140466 * 2 ^ 59
def prefixEnd_140466 : Nat := 4983230072969 + 3 ^ 40 * 140466 * 2
def baseEnd_140466 : Nat := 48084382409701773219343

theorem tailTrace_140466 : CollatzResearch.WordTrace tailWord_140466 prefixEnd_140466 48084382409701773219343 := by
  unfold tailWord_140466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1280803977280786631998313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3415477272748764351995501 1280803977280786631998313)
  ·
    refine ⟨960602982960589973998735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1280803977280786631998313 960602982960589973998735)
    ·
      refine ⟨1440904474440884960998103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960602982960589973998735 1440904474440884960998103)
      ·
        refine ⟨2161356711661327441497155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440904474440884960998103 2161356711661327441497155)
        ·
          refine ⟨3242035067491991162245733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161356711661327441497155 3242035067491991162245733)
          ·
            refine ⟨607881575154748342921075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3242035067491991162245733 607881575154748342921075)
            ·
              refine ⟨911822362732122514381613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607881575154748342921075 911822362732122514381613)
              ·
                refine ⟨341933386024545942893105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 911822362732122514381613 341933386024545942893105)
                ·
                  refine ⟨256450039518409457169829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341933386024545942893105 256450039518409457169829)
                  ·
                    refine ⟨48084382409701773219343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 256450039518409457169829 48084382409701773219343)
                    ·
                      rfl

theorem cell22_140466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_140466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140466 prefixEnd_140466 := by exact prefixLift 140466
  have htrace : WordTrace (prefixWord ++ tailWord_140466) baseStart_140466 baseEnd_140466 := by
    simpa [prefixWord, tailWord_140466, baseEnd_140466] using wordTrace_append hprefix tailTrace_140466
  have hstable : (prefixWord ++ tailWord_140466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140466).length < 2 ^ (prefixWord ++ tailWord_140466).sum := by decide
  have hdescent : baseEnd_140466 < baseStart_140466 := by decide
  rcases family_descends (prefixWord ++ tailWord_140466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140481 : List Nat := [1, 2, 6, 1, 1, 11]
def baseStart_140481 : Nat := 118140960795 + 140481 * 2 ^ 59
def prefixEnd_140481 : Nat := 4983230072969 + 3 ^ 40 * 140481 * 2
def baseEnd_140481 : Nat := 593697743410453507337

theorem tailTrace_140481 : CollatzResearch.WordTrace tailWord_140481 prefixEnd_140481 593697743410453507337 := by
  unfold tailWord_140481
  simp only [CollatzResearch.WordTrace]
  refine ⟨5123763004068804089789297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3415842002712536059859531 5123763004068804089789297)
  ·
    refine ⟨3842822253051603067341973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5123763004068804089789297 3842822253051603067341973)
    ·
      refine ⟨180132293111793893781655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3842822253051603067341973 180132293111793893781655)
      ·
        refine ⟨270198439667690840672483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180132293111793893781655 270198439667690840672483)
        ·
          refine ⟨405297659501536261008725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270198439667690840672483 405297659501536261008725)
          ·
            refine ⟨593697743410453507337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 405297659501536261008725 593697743410453507337)
            ·
              rfl

theorem cell22_140481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 11].length) (baseStart_140481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140481 prefixEnd_140481 := by exact prefixLift 140481
  have htrace : WordTrace (prefixWord ++ tailWord_140481) baseStart_140481 baseEnd_140481 := by
    simpa [prefixWord, tailWord_140481, baseEnd_140481] using wordTrace_append hprefix tailTrace_140481
  have hstable : (prefixWord ++ tailWord_140481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140481).length < 2 ^ (prefixWord ++ tailWord_140481).sum := by decide
  have hdescent : baseEnd_140481 < baseStart_140481 := by decide
  rcases family_descends (prefixWord ++ tailWord_140481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140513 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 3, 3]
def baseStart_140513 : Nat := 118140960795 + 140513 * 2 ^ 59
def prefixEnd_140513 : Nat := 4983230072969 + 3 ^ 40 * 140513 * 2
def baseEnd_140513 : Nat := 48100471470209317294199

theorem tailTrace_140513 : CollatzResearch.WordTrace tailWord_140513 prefixEnd_140513 48100471470209317294199 := by
  unfold tailWord_140513
  simp only [CollatzResearch.WordTrace]
  refine ⟨5124930139952873554954193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3416620093301915703302795 5124930139952873554954193)
  ·
    refine ⟨3843697604964655166215645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5124930139952873554954193 3843697604964655166215645)
    ·
      refine ⟨1441386601861745687330867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3843697604964655166215645 1441386601861745687330867)
      ·
        refine ⟨2162079902792618530996301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441386601861745687330867 2162079902792618530996301)
        ·
          refine ⟨810779963547231949123613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2162079902792618530996301 810779963547231949123613)
          ·
            refine ⟨304042486330211980921355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 810779963547231949123613 304042486330211980921355)
            ·
              refine ⟨456063729495317971382033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304042486330211980921355 456063729495317971382033)
              ·
                refine ⟨342047797121488478536525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456063729495317971382033 342047797121488478536525)
                ·
                  refine ⟨128267923920558179451197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 342047797121488478536525 128267923920558179451197)
                  ·
                    refine ⟨48100471470209317294199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128267923920558179451197 48100471470209317294199)
                    ·
                      rfl

theorem cell22_140513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_140513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140513 prefixEnd_140513 := by exact prefixLift 140513
  have htrace : WordTrace (prefixWord ++ tailWord_140513) baseStart_140513 baseEnd_140513 := by
    simpa [prefixWord, tailWord_140513, baseEnd_140513] using wordTrace_append hprefix tailTrace_140513
  have hstable : (prefixWord ++ tailWord_140513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140513).length < 2 ^ (prefixWord ++ tailWord_140513).sum := by decide
  have hdescent : baseEnd_140513 < baseStart_140513 := by decide
  rcases family_descends (prefixWord ++ tailWord_140513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140543 : List Nat := [1, 1, 2, 2, 1, 7, 1, 2, 5]
def baseStart_140543 : Nat := 118140960795 + 140543 * 2 ^ 59
def prefixEnd_140543 : Nat := 4983230072969 + 3 ^ 40 * 140543 * 2
def baseEnd_140543 : Nat := 16036913694433079681369

theorem tailTrace_140543 : CollatzResearch.WordTrace tailWord_140543 prefixEnd_140543 16036913694433079681369 := by
  unfold tailWord_140543
  simp only [CollatzResearch.WordTrace]
  refine ⟨5126024329844188678546283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3417349553229459119030855 5126024329844188678546283)
  ·
    refine ⟨7689036494766283017819425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5126024329844188678546283 7689036494766283017819425)
    ·
      refine ⟨5766777371074712263364569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7689036494766283017819425 5766777371074712263364569)
      ·
        refine ⟨4325083028306034197523427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5766777371074712263364569 4325083028306034197523427)
        ·
          refine ⟨6487624542459051296285141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4325083028306034197523427 6487624542459051296285141)
          ·
            refine ⟨152053700213884014756683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 6487624542459051296285141 152053700213884014756683)
            ·
              refine ⟨228080550320826022135025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152053700213884014756683 228080550320826022135025)
              ·
                refine ⟨171060412740619516601269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228080550320826022135025 171060412740619516601269)
                ·
                  refine ⟨16036913694433079681369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 171060412740619516601269 16036913694433079681369)
                  ·
                    rfl

theorem cell22_140543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 5].length) (baseStart_140543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140543 prefixEnd_140543 := by exact prefixLift 140543
  have htrace : WordTrace (prefixWord ++ tailWord_140543) baseStart_140543 baseEnd_140543 := by
    simpa [prefixWord, tailWord_140543, baseEnd_140543] using wordTrace_append hprefix tailTrace_140543
  have hstable : (prefixWord ++ tailWord_140543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140543).length < 2 ^ (prefixWord ++ tailWord_140543).sum := by decide
  have hdescent : baseEnd_140543 < baseStart_140543 := by decide
  rcases family_descends (prefixWord ++ tailWord_140543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140620 : List Nat := [2, 2, 1, 3, 2, 3, 1, 3, 2, 3]
def baseStart_140620 : Nat := 118140960795 + 140620 * 2 ^ 59
def prefixEnd_140620 : Nat := 4983230072969 + 3 ^ 40 * 140620 * 2
def baseEnd_140620 : Nat := 48137099756896704868871

theorem tailTrace_140620 : CollatzResearch.WordTrace tailWord_140620 prefixEnd_140620 48137099756896704868871 := by
  unfold tailWord_140620
  simp only [CollatzResearch.WordTrace]
  refine ⟨2564416375282615414549657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3419221833710153886066209 2564416375282615414549657)
  ·
    refine ⟨1923312281461961560912243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2564416375282615414549657 1923312281461961560912243)
    ·
      refine ⟨2884968422192942341368365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1923312281461961560912243 2884968422192942341368365)
      ·
        refine ⟨1081863158322353378013137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2884968422192942341368365 1081863158322353378013137)
        ·
          refine ⟨811397368741765033509853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1081863158322353378013137 811397368741765033509853)
          ·
            refine ⟨304274013278161887566195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 811397368741765033509853 304274013278161887566195)
            ·
              refine ⟨456411019917242831349293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304274013278161887566195 456411019917242831349293)
              ·
                refine ⟨171154132468966061755985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 456411019917242831349293 171154132468966061755985)
                ·
                  refine ⟨128365599351724546316989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171154132468966061755985 128365599351724546316989)
                  ·
                    refine ⟨48137099756896704868871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128365599351724546316989 48137099756896704868871)
                    ·
                      rfl

theorem cell22_140620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_140620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140620 prefixEnd_140620 := by exact prefixLift 140620
  have htrace : WordTrace (prefixWord ++ tailWord_140620) baseStart_140620 baseEnd_140620 := by
    simpa [prefixWord, tailWord_140620, baseEnd_140620] using wordTrace_append hprefix tailTrace_140620
  have hstable : (prefixWord ++ tailWord_140620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140620).length < 2 ^ (prefixWord ++ tailWord_140620).sum := by decide
  have hdescent : baseEnd_140620 < baseStart_140620 := by decide
  rcases family_descends (prefixWord ++ tailWord_140620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140654 : List Nat := [4, 1, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_140654 : Nat := 118140960795 + 140654 * 2 ^ 59
def prefixEnd_140654 : Nat := 4983230072969 + 3 ^ 40 * 140654 * 2
def baseEnd_140654 : Nat := 48148738651731949518767

theorem tailTrace_140654 : CollatzResearch.WordTrace tailWord_140654 prefixEnd_140654 48148738651731949518767 := by
  unfold tailWord_140654
  simp only [CollatzResearch.WordTrace]
  refine ⟨641259104055256829479627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3420048554961369757224677 641259104055256829479627)
  ·
    refine ⟨961888656082885244219441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 641259104055256829479627 961888656082885244219441)
    ·
      refine ⟨721416492062163933164581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 961888656082885244219441 721416492062163933164581)
      ·
        refine ⟨135265592261655737468359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 721416492062163933164581 135265592261655737468359)
        ·
          refine ⟨202898388392483606202539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135265592261655737468359 202898388392483606202539)
          ·
            refine ⟨304347582588725409303809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202898388392483606202539 304347582588725409303809)
            ·
              refine ⟨228260686941544056977857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304347582588725409303809 228260686941544056977857)
              ·
                refine ⟨171195515206158042733393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228260686941544056977857 171195515206158042733393)
                ·
                  refine ⟨128396636404618532050045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171195515206158042733393 128396636404618532050045)
                  ·
                    refine ⟨48148738651731949518767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128396636404618532050045 48148738651731949518767)
                    ·
                      rfl

theorem cell22_140654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_140654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140654 prefixEnd_140654 := by exact prefixLift 140654
  have htrace : WordTrace (prefixWord ++ tailWord_140654) baseStart_140654 baseEnd_140654 := by
    simpa [prefixWord, tailWord_140654, baseEnd_140654] using wordTrace_append hprefix tailTrace_140654
  have hstable : (prefixWord ++ tailWord_140654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140654).length < 2 ^ (prefixWord ++ tailWord_140654).sum := by decide
  have hdescent : baseEnd_140654 < baseStart_140654 := by decide
  rcases family_descends (prefixWord ++ tailWord_140654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140740 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 6]
def baseStart_140740 : Nat := 118140960795 + 140740 * 2 ^ 59
def prefixEnd_140740 : Nat := 4983230072969 + 3 ^ 40 * 140740 * 2
def baseEnd_140740 : Nat := 16059392736418797289501

theorem tailTrace_140740 : CollatzResearch.WordTrace tailWord_140740 prefixEnd_140740 16059392736418797289501 := by
  unfold tailWord_140740
  simp only [CollatzResearch.WordTrace]
  refine ⟨2566604755065245661733837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3422139673420327548978449 2566604755065245661733837)
  ·
    refine ⟨962476783149467123150189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2566604755065245661733837 962476783149467123150189)
    ·
      refine ⟨360928793681050171181321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 962476783149467123150189 360928793681050171181321)
      ·
        refine ⟨270696595260787628385991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360928793681050171181321 270696595260787628385991)
        ·
          refine ⟨406044892891181442578987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270696595260787628385991 406044892891181442578987)
          ·
            refine ⟨609067339336772163868481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406044892891181442578987 609067339336772163868481)
            ·
              refine ⟨456800504502579122901361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609067339336772163868481 456800504502579122901361)
              ·
                refine ⟨342600378376934342176021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456800504502579122901361 342600378376934342176021)
                ·
                  refine ⟨16059392736418797289501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 342600378376934342176021 16059392736418797289501)
                  ·
                    rfl

theorem cell22_140740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_140740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140740 prefixEnd_140740 := by exact prefixLift 140740
  have htrace : WordTrace (prefixWord ++ tailWord_140740) baseStart_140740 baseEnd_140740 := by
    simpa [prefixWord, tailWord_140740, baseEnd_140740] using wordTrace_append hprefix tailTrace_140740
  have hstable : (prefixWord ++ tailWord_140740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140740).length < 2 ^ (prefixWord ++ tailWord_140740).sum := by decide
  have hdescent : baseEnd_140740 < baseStart_140740 := by decide
  rcases family_descends (prefixWord ++ tailWord_140740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140789 : List Nat := [1, 3, 5, 1, 1, 2, 1, 3, 2, 3]
def baseStart_140789 : Nat := 118140960795 + 140789 * 2 ^ 59
def prefixEnd_140789 : Nat := 4983230072969 + 3 ^ 40 * 140789 * 2
def baseEnd_140789 : Nat := 48194951910636597393353

theorem tailTrace_140789 : CollatzResearch.WordTrace tailWord_140789 prefixEnd_140789 48194951910636597393353 := by
  unfold tailWord_140789
  simp only [CollatzResearch.WordTrace]
  refine ⟨5134996686952972692001421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3423331124635315128000947 5134996686952972692001421)
  ·
    refine ⟨1925623757607364759500533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5134996686952972692001421 1925623757607364759500533)
    ·
      refine ⟨180527227275690446203175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1925623757607364759500533 180527227275690446203175)
      ·
        refine ⟨270790840913535669304763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180527227275690446203175 270790840913535669304763)
        ·
          refine ⟨406186261370303503957145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270790840913535669304763 406186261370303503957145)
          ·
            refine ⟨304639696027727627967859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406186261370303503957145 304639696027727627967859)
            ·
              refine ⟨456959544041591441951789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304639696027727627967859 456959544041591441951789)
              ·
                refine ⟨171359829015596790731921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 456959544041591441951789 171359829015596790731921)
                ·
                  refine ⟨128519871761697593048941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171359829015596790731921 128519871761697593048941)
                  ·
                    refine ⟨48194951910636597393353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128519871761697593048941 48194951910636597393353)
                    ·
                      rfl

theorem cell22_140789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_140789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140789 prefixEnd_140789 := by exact prefixLift 140789
  have htrace : WordTrace (prefixWord ++ tailWord_140789) baseStart_140789 baseEnd_140789 := by
    simpa [prefixWord, tailWord_140789, baseEnd_140789] using wordTrace_append hprefix tailTrace_140789
  have hstable : (prefixWord ++ tailWord_140789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140789).length < 2 ^ (prefixWord ++ tailWord_140789).sum := by decide
  have hdescent : baseEnd_140789 < baseStart_140789 := by decide
  rcases family_descends (prefixWord ++ tailWord_140789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140806 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_140806 : Nat := 118140960795 + 140806 * 2 ^ 59
def prefixEnd_140806 : Nat := 4983230072969 + 3 ^ 40 * 140806 * 2
def baseEnd_140806 : Nat := 48200771358054219718301

theorem tailTrace_140806 : CollatzResearch.WordTrace tailWord_140806 prefixEnd_140806 48200771358054219718301 := by
  unfold tailWord_140806
  simp only [CollatzResearch.WordTrace]
  refine ⟨160488022746605768605321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3423744485260923063580181 160488022746605768605321)
  ·
    refine ⟨120366017059954326453991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160488022746605768605321 120366017059954326453991)
    ·
      refine ⟨180549025589931489680987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120366017059954326453991 180549025589931489680987)
      ·
        refine ⟨270823538384897234521481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180549025589931489680987 270823538384897234521481)
        ·
          refine ⟨203117653788672925891111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270823538384897234521481 203117653788672925891111)
          ·
            refine ⟨304676480683009388836667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203117653788672925891111 304676480683009388836667)
            ·
              refine ⟨457014721024514083255001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304676480683009388836667 457014721024514083255001)
              ·
                refine ⟨342761040768385562441251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457014721024514083255001 342761040768385562441251)
                ·
                  refine ⟨514141561152578343661877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342761040768385562441251 514141561152578343661877)
                  ·
                    refine ⟨48200771358054219718301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 514141561152578343661877 48200771358054219718301)
                    ·
                      rfl

theorem cell22_140806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_140806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140806 prefixEnd_140806 := by exact prefixLift 140806
  have htrace : WordTrace (prefixWord ++ tailWord_140806) baseStart_140806 baseEnd_140806 := by
    simpa [prefixWord, tailWord_140806, baseEnd_140806] using wordTrace_append hprefix tailTrace_140806
  have hstable : (prefixWord ++ tailWord_140806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140806).length < 2 ^ (prefixWord ++ tailWord_140806).sum := by decide
  have hdescent : baseEnd_140806 < baseStart_140806 := by decide
  rcases family_descends (prefixWord ++ tailWord_140806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140817 : List Nat := [1, 2, 2, 1, 1, 2, 4, 5, 1, 3]
def baseStart_140817 : Nat := 118140960795 + 140817 * 2 ^ 59
def prefixEnd_140817 : Nat := 4983230072969 + 3 ^ 40 * 140817 * 2
def baseEnd_140817 : Nat := 48204536882853857693267

theorem tailTrace_140817 : CollatzResearch.WordTrace tailWord_140817 prefixEnd_140817 48204536882853857693267 := by
  unfold tailWord_140817
  simp only [CollatzResearch.WordTrace]
  refine ⟨5136017930851533474020705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3424011953901022316013803 5136017930851533474020705)
  ·
    refine ⟨3852013448138650105515529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5136017930851533474020705 3852013448138650105515529)
    ·
      refine ⟨2889010086103987579136647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3852013448138650105515529 2889010086103987579136647)
      ·
        refine ⟨4333515129155981368704971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2889010086103987579136647 4333515129155981368704971)
        ·
          refine ⟨6500272693733972053057457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4333515129155981368704971 6500272693733972053057457)
          ·
            refine ⟨4875204520300479039793093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6500272693733972053057457 4875204520300479039793093)
            ·
              refine ⟨914100847556339819961205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4875204520300479039793093 914100847556339819961205)
              ·
                refine ⟨85696954458406858121363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 914100847556339819961205 85696954458406858121363)
                ·
                  refine ⟨128545431687610287182045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85696954458406858121363 128545431687610287182045)
                  ·
                    refine ⟨48204536882853857693267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128545431687610287182045 48204536882853857693267)
                    ·
                      rfl

theorem cell22_140817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_140817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140817 prefixEnd_140817 := by exact prefixLift 140817
  have htrace : WordTrace (prefixWord ++ tailWord_140817) baseStart_140817 baseEnd_140817 := by
    simpa [prefixWord, tailWord_140817, baseEnd_140817] using wordTrace_append hprefix tailTrace_140817
  have hstable : (prefixWord ++ tailWord_140817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140817).length < 2 ^ (prefixWord ++ tailWord_140817).sum := by decide
  have hdescent : baseEnd_140817 < baseStart_140817 := by decide
  rcases family_descends (prefixWord ++ tailWord_140817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140892 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 6]
def baseStart_140892 : Nat := 118140960795 + 140892 * 2 ^ 59
def prefixEnd_140892 : Nat := 4983230072969 + 3 ^ 40 * 140892 * 2
def baseEnd_140892 : Nat := 16076736971859554022679

theorem tailTrace_140892 : CollatzResearch.WordTrace tailWord_140892 prefixEnd_140892 16076736971859554022679 := by
  unfold tailWord_140892
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569376702789910641500465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3425835603719880855333953 2569376702789910641500465)
  ·
    refine ⟨1927032527092432981125349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2569376702789910641500465 1927032527092432981125349)
    ·
      refine ⟨361318598829831183961003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1927032527092432981125349 361318598829831183961003)
      ·
        refine ⟨541977898244746775941505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361318598829831183961003 541977898244746775941505)
        ·
          refine ⟨406483423683560081956129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541977898244746775941505 406483423683560081956129)
          ·
            refine ⟨304862567762670061467097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406483423683560081956129 304862567762670061467097)
            ·
              refine ⟨228646925822002546100323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304862567762670061467097 228646925822002546100323)
              ·
                refine ⟨342970388733003819150485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228646925822002546100323 342970388733003819150485)
                ·
                  refine ⟨16076736971859554022679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 342970388733003819150485 16076736971859554022679)
                  ·
                    rfl

theorem cell22_140892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_140892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140892 prefixEnd_140892 := by exact prefixLift 140892
  have htrace : WordTrace (prefixWord ++ tailWord_140892) baseStart_140892 baseEnd_140892 := by
    simpa [prefixWord, tailWord_140892, baseEnd_140892] using wordTrace_append hprefix tailTrace_140892
  have hstable : (prefixWord ++ tailWord_140892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140892).length < 2 ^ (prefixWord ++ tailWord_140892).sum := by decide
  have hdescent : baseEnd_140892 < baseStart_140892 := by decide
  rcases family_descends (prefixWord ++ tailWord_140892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140958 : List Nat := [4, 3, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_140958 : Nat := 118140960795 + 140958 * 2 ^ 59
def prefixEnd_140958 : Nat := 4983230072969 + 3 ^ 40 * 140958 * 2
def baseEnd_140958 : Nat := 48252804064376489917835

theorem tailTrace_140958 : CollatzResearch.WordTrace tailWord_140958 prefixEnd_140958 48252804064376489917835 := by
  unfold tailWord_140958
  simp only [CollatzResearch.WordTrace]
  refine ⟨642645077917589319362941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3427440415560476369935685 642645077917589319362941)
  ·
    refine ⟨240991904219095994761103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 642645077917589319362941 240991904219095994761103)
    ·
      refine ⟨361487856328643992141655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240991904219095994761103 361487856328643992141655)
      ·
        refine ⟨542231784492965988212483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361487856328643992141655 542231784492965988212483)
        ·
          refine ⟨813347676739448982318725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542231784492965988212483 813347676739448982318725)
          ·
            refine ⟨152502689388646684184761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 813347676739448982318725 152502689388646684184761)
            ·
              refine ⟨114377017041485013138571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152502689388646684184761 114377017041485013138571)
              ·
                refine ⟨171565525562227519707857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114377017041485013138571 171565525562227519707857)
                ·
                  refine ⟨128674144171670639780893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171565525562227519707857 128674144171670639780893)
                  ·
                    refine ⟨48252804064376489917835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128674144171670639780893 48252804064376489917835)
                    ·
                      rfl

theorem cell22_140958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_140958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_140958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_140958 prefixEnd_140958 := by exact prefixLift 140958
  have htrace : WordTrace (prefixWord ++ tailWord_140958) baseStart_140958 baseEnd_140958 := by
    simpa [prefixWord, tailWord_140958, baseEnd_140958] using wordTrace_append hprefix tailTrace_140958
  have hstable : (prefixWord ++ tailWord_140958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140958).length < 2 ^ (prefixWord ++ tailWord_140958).sum := by decide
  have hdescent : baseEnd_140958 < baseStart_140958 := by decide
  rcases family_descends (prefixWord ++ tailWord_140958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141042 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_141042 : Nat := 118140960795 + 141042 * 2 ^ 59
def prefixEnd_141042 : Nat := 4983230072969 + 3 ^ 40 * 141042 * 2
def baseEnd_141042 : Nat := 48281558981028270817577

theorem tailTrace_141042 : CollatzResearch.WordTrace tailWord_141042 prefixEnd_141042 48281558981028270817577 := by
  unfold tailWord_141042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1286056088759099225240345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3429482903357597933974253 1286056088759099225240345)
  ·
    refine ⟨964542066569324418930259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1286056088759099225240345 964542066569324418930259)
    ·
      refine ⟨1446813099853986628395389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 964542066569324418930259 1446813099853986628395389)
      ·
        refine ⟨542554912445244985648271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1446813099853986628395389 542554912445244985648271)
        ·
          refine ⟨813832368667867478472407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542554912445244985648271 813832368667867478472407)
          ·
            refine ⟨1220748553001801217708611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813832368667867478472407 1220748553001801217708611)
            ·
              refine ⟨1831122829502701826562917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220748553001801217708611 1831122829502701826562917)
              ·
                refine ⟨343335530531756592480547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1831122829502701826562917 343335530531756592480547)
                ·
                  refine ⟨515003295797634888720821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343335530531756592480547 515003295797634888720821)
                  ·
                    refine ⟨48281558981028270817577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 515003295797634888720821 48281558981028270817577)
                    ·
                      rfl

theorem cell22_141042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_141042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141042 prefixEnd_141042 := by exact prefixLift 141042
  have htrace : WordTrace (prefixWord ++ tailWord_141042) baseStart_141042 baseEnd_141042 := by
    simpa [prefixWord, tailWord_141042, baseEnd_141042] using wordTrace_append hprefix tailTrace_141042
  have hstable : (prefixWord ++ tailWord_141042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141042).length < 2 ^ (prefixWord ++ tailWord_141042).sum := by decide
  have hdescent : baseEnd_141042 < baseStart_141042 := by decide
  rcases family_descends (prefixWord ++ tailWord_141042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141046 : List Nat := [5, 1, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_141046 : Nat := 118140960795 + 141046 * 2 ^ 59
def prefixEnd_141046 : Nat := 4983230072969 + 3 ^ 40 * 141046 * 2
def baseEnd_141046 : Nat := 48282928262773593717565

theorem tailTrace_141046 : CollatzResearch.WordTrace tailWord_141046 prefixEnd_141046 48282928262773593717565 := by
  unfold tailWord_141046
  simp only [CollatzResearch.WordTrace]
  refine ⟨321523140438869099006687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3429580164681270389404661 321523140438869099006687)
  ·
    refine ⟨482284710658303648510031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 321523140438869099006687 482284710658303648510031)
    ·
      refine ⟨723427065987455472765047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482284710658303648510031 723427065987455472765047)
      ·
        refine ⟨1085140598981183209147571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723427065987455472765047 1085140598981183209147571)
        ·
          refine ⟨1627710898471774813721357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085140598981183209147571 1627710898471774813721357)
          ·
            refine ⟨610391586926915555145509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1627710898471774813721357 610391586926915555145509)
            ·
              refine ⟨114448422548796666589783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 610391586926915555145509 114448422548796666589783)
              ·
                refine ⟨171672633823194999884675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114448422548796666589783 171672633823194999884675)
                ·
                  refine ⟨257508950734792499827013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171672633823194999884675 257508950734792499827013)
                  ·
                    refine ⟨48282928262773593717565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 257508950734792499827013 48282928262773593717565)
                    ·
                      rfl

theorem cell22_141046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_141046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141046 prefixEnd_141046 := by exact prefixLift 141046
  have htrace : WordTrace (prefixWord ++ tailWord_141046) baseStart_141046 baseEnd_141046 := by
    simpa [prefixWord, tailWord_141046, baseEnd_141046] using wordTrace_append hprefix tailTrace_141046
  have hstable : (prefixWord ++ tailWord_141046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141046).length < 2 ^ (prefixWord ++ tailWord_141046).sum := by decide
  have hdescent : baseEnd_141046 < baseStart_141046 := by decide
  rcases family_descends (prefixWord ++ tailWord_141046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141057 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 2, 4]
def baseStart_141057 : Nat := 118140960795 + 141057 * 2 ^ 59
def prefixEnd_141057 : Nat := 4983230072969 + 3 ^ 40 * 141057 * 2
def baseEnd_141057 : Nat := 48286693787573231692531

theorem tailTrace_141057 : CollatzResearch.WordTrace tailWord_141057 prefixEnd_141057 48286693787573231692531 := by
  unfold tailWord_141057
  simp only [CollatzResearch.WordTrace]
  refine ⟨5144771449982054462757425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3429847633321369641838283 5144771449982054462757425)
  ·
    refine ⟨3858578587486540847068069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5144771449982054462757425 3858578587486540847068069)
    ·
      refine ⟨723483485153726408825263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3858578587486540847068069 723483485153726408825263)
      ·
        refine ⟨1085225227730589613237895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723483485153726408825263 1085225227730589613237895)
        ·
          refine ⟨1627837841595884419856843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085225227730589613237895 1627837841595884419856843)
          ·
            refine ⟨2441756762393826629785265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1627837841595884419856843 2441756762393826629785265)
            ·
              refine ⟨1831317571795369972338949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2441756762393826629785265 1831317571795369972338949)
              ·
                refine ⟨343372044711631869813553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1831317571795369972338949 343372044711631869813553)
                ·
                  refine ⟨257529033533723902360165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343372044711631869813553 257529033533723902360165)
                  ·
                    refine ⟨48286693787573231692531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 257529033533723902360165 48286693787573231692531)
                    ·
                      rfl

theorem cell22_141057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_141057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141057 prefixEnd_141057 := by exact prefixLift 141057
  have htrace : WordTrace (prefixWord ++ tailWord_141057) baseStart_141057 baseEnd_141057 := by
    simpa [prefixWord, tailWord_141057, baseEnd_141057] using wordTrace_append hprefix tailTrace_141057
  have hstable : (prefixWord ++ tailWord_141057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141057).length < 2 ^ (prefixWord ++ tailWord_141057).sum := by decide
  have hdescent : baseEnd_141057 < baseStart_141057 := by decide
  rcases family_descends (prefixWord ++ tailWord_141057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141059 : List Nat := [1, 1, 1, 3, 2, 2, 5, 2, 2, 3]
def baseStart_141059 : Nat := 118140960795 + 141059 * 2 ^ 59
def prefixEnd_141059 : Nat := 4983230072969 + 3 ^ 40 * 141059 * 2
def baseEnd_141059 : Nat := 48287378428445893142525

theorem tailTrace_141059 : CollatzResearch.WordTrace tailWord_141059 prefixEnd_141059 48287378428445893142525 := by
  unfold tailWord_141059
  simp only [CollatzResearch.WordTrace]
  refine ⟨5144844395974808804330231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3429896263983205869553487 5144844395974808804330231)
  ·
    refine ⟨7717266593962213206495347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5144844395974808804330231 7717266593962213206495347)
    ·
      refine ⟨11575899890943319809743021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7717266593962213206495347 11575899890943319809743021)
      ·
        refine ⟨4340962459103744928653633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11575899890943319809743021 4340962459103744928653633)
        ·
          refine ⟨3255721844327808696490225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4340962459103744928653633 3255721844327808696490225)
          ·
            refine ⟨2441791383245856522367669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3255721844327808696490225 2441791383245856522367669)
            ·
              refine ⟨228917942179299048971969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2441791383245856522367669 228917942179299048971969)
              ·
                refine ⟨171688456634474286728977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228917942179299048971969 171688456634474286728977)
                ·
                  refine ⟨128766342475855715046733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171688456634474286728977 128766342475855715046733)
                  ·
                    refine ⟨48287378428445893142525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128766342475855715046733 48287378428445893142525)
                    ·
                      rfl

theorem cell22_141059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 3].length) (baseStart_141059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141059 prefixEnd_141059 := by exact prefixLift 141059
  have htrace : WordTrace (prefixWord ++ tailWord_141059) baseStart_141059 baseEnd_141059 := by
    simpa [prefixWord, tailWord_141059, baseEnd_141059] using wordTrace_append hprefix tailTrace_141059
  have hstable : (prefixWord ++ tailWord_141059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141059).length < 2 ^ (prefixWord ++ tailWord_141059).sum := by decide
  have hdescent : baseEnd_141059 < baseStart_141059 := by decide
  rcases family_descends (prefixWord ++ tailWord_141059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141074 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_141074 : Nat := 118140960795 + 141074 * 2 ^ 59
def prefixEnd_141074 : Nat := 4983230072969 + 3 ^ 40 * 141074 * 2
def baseEnd_141074 : Nat := 48292513234990854017479

theorem tailTrace_141074 : CollatzResearch.WordTrace tailWord_141074 prefixEnd_141074 48292513234990854017479 := by
  unfold tailWord_141074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1286347872730116591531569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3430260993946977577417517 1286347872730116591531569)
  ·
    refine ⟨964760904547587443648677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1286347872730116591531569 964760904547587443648677)
    ·
      refine ⟨180892669602672645684127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 964760904547587443648677 180892669602672645684127)
      ·
        refine ⟨271339004404008968526191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180892669602672645684127 271339004404008968526191)
        ·
          refine ⟨407008506606013452789287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271339004404008968526191 407008506606013452789287)
          ·
            refine ⟨610512759909020179183931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407008506606013452789287 610512759909020179183931)
            ·
              refine ⟨915769139863530268775897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610512759909020179183931 915769139863530268775897)
              ·
                refine ⟨686826854897647701581923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 915769139863530268775897 686826854897647701581923)
                ·
                  refine ⟨1030240282346471552372885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686826854897647701581923 1030240282346471552372885)
                  ·
                    refine ⟨48292513234990854017479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1030240282346471552372885 48292513234990854017479)
                    ·
                      rfl

theorem cell22_141074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_141074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141074 prefixEnd_141074 := by exact prefixLift 141074
  have htrace : WordTrace (prefixWord ++ tailWord_141074) baseStart_141074 baseEnd_141074 := by
    simpa [prefixWord, tailWord_141074, baseEnd_141074] using wordTrace_append hprefix tailTrace_141074
  have hstable : (prefixWord ++ tailWord_141074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141074).length < 2 ^ (prefixWord ++ tailWord_141074).sum := by decide
  have hdescent : baseEnd_141074 < baseStart_141074 := by decide
  rcases family_descends (prefixWord ++ tailWord_141074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141089 : List Nat := [1, 2, 3, 2, 1, 5, 2, 6]
def baseStart_141089 : Nat := 118140960795 + 141089 * 2 ^ 59
def prefixEnd_141089 : Nat := 4983230072969 + 3 ^ 40 * 141089 * 2
def baseEnd_141089 : Nat := 5366405337948423876937

theorem tailTrace_141089 : CollatzResearch.WordTrace tailWord_141089 prefixEnd_141089 5366405337948423876937 := by
  unfold tailWord_141089
  simp only [CollatzResearch.WordTrace]
  refine ⟨5145938585866123927922321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3430625723910749285281547 5145938585866123927922321)
  ·
    refine ⟨3859453939399592945941741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5145938585866123927922321 3859453939399592945941741)
    ·
      refine ⟨1447295227274847354728153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3859453939399592945941741 1447295227274847354728153)
      ·
        refine ⟨1085471420456135516046115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1447295227274847354728153 1085471420456135516046115)
        ·
          refine ⟨1628207130684203274069173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085471420456135516046115 1628207130684203274069173)
          ·
            refine ⟨152644418501644056943985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1628207130684203274069173 152644418501644056943985)
            ·
              refine ⟨114483313876233042707989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152644418501644056943985 114483313876233042707989)
              ·
                refine ⟨5366405337948423876937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114483313876233042707989 5366405337948423876937)
                ·
                  rfl

theorem cell22_141089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 6].length) (baseStart_141089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141089 prefixEnd_141089 := by exact prefixLift 141089
  have htrace : WordTrace (prefixWord ++ tailWord_141089) baseStart_141089 baseEnd_141089 := by
    simpa [prefixWord, tailWord_141089, baseEnd_141089] using wordTrace_append hprefix tailTrace_141089
  have hstable : (prefixWord ++ tailWord_141089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141089).length < 2 ^ (prefixWord ++ tailWord_141089).sum := by decide
  have hdescent : baseEnd_141089 < baseStart_141089 := by decide
  rcases family_descends (prefixWord ++ tailWord_141089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141177 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 3, 5]
def baseStart_141177 : Nat := 118140960795 + 141177 * 2 ^ 59
def prefixEnd_141177 : Nat := 4983230072969 + 3 ^ 40 * 141177 * 2
def baseEnd_141177 : Nat := 48327772239932918692163

theorem tailTrace_141177 : CollatzResearch.WordTrace tailWord_141177 prefixEnd_141177 48327772239932918692163 := by
  unfold tailWord_141177
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149148209547314957125785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3432765473031543304750523 5149148209547314957125785)
  ·
    refine ⟨3861861157160486217844339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5149148209547314957125785 3861861157160486217844339)
    ·
      refine ⟨5792791735740729326766509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3861861157160486217844339 5792791735740729326766509)
      ·
        refine ⟨2172296900902773497537441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5792791735740729326766509 2172296900902773497537441)
        ·
          refine ⟨1629222675677080123153081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2172296900902773497537441 1629222675677080123153081)
          ·
            refine ⟨1221917006757810092364811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1629222675677080123153081 1221917006757810092364811)
            ·
              refine ⟨1832875510136715138547217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221917006757810092364811 1832875510136715138547217)
              ·
                refine ⟨1374656632602536353910413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1832875510136715138547217 1374656632602536353910413)
                ·
                  refine ⟨515496237225951132716405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1374656632602536353910413 515496237225951132716405)
                  ·
                    refine ⟨48327772239932918692163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 515496237225951132716405 48327772239932918692163)
                    ·
                      rfl

theorem cell22_141177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_141177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141177 prefixEnd_141177 := by exact prefixLift 141177
  have htrace : WordTrace (prefixWord ++ tailWord_141177) baseStart_141177 baseEnd_141177 := by
    simpa [prefixWord, tailWord_141177, baseEnd_141177] using wordTrace_append hprefix tailTrace_141177
  have hstable : (prefixWord ++ tailWord_141177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141177).length < 2 ^ (prefixWord ++ tailWord_141177).sum := by decide
  have hdescent : baseEnd_141177 < baseStart_141177 := by decide
  rcases family_descends (prefixWord ++ tailWord_141177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141209 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 2, 4]
def baseStart_141209 : Nat := 118140960795 + 141209 * 2 ^ 59
def prefixEnd_141209 : Nat := 4983230072969 + 3 ^ 40 * 141209 * 2
def baseEnd_141209 : Nat := 48338726493895501892065

theorem tailTrace_141209 : CollatzResearch.WordTrace tailWord_141209 prefixEnd_141209 48338726493895501892065 := by
  unfold tailWord_141209
  simp only [CollatzResearch.WordTrace]
  refine ⟨5150315345431384422290681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3433543563620922948193787 5150315345431384422290681)
  ·
    refine ⟨3862736509073538316718011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5150315345431384422290681 3862736509073538316718011)
    ·
      refine ⟨5794104763610307475077017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3862736509073538316718011 5794104763610307475077017)
      ·
        refine ⟨4345578572707730606307763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5794104763610307475077017 4345578572707730606307763)
        ·
          refine ⟨6518367859061595909461645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4345578572707730606307763 6518367859061595909461645)
          ·
            refine ⟨2444387947148098466048117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6518367859061595909461645 2444387947148098466048117)
            ·
              refine ⟨229161370045134231192011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2444387947148098466048117 229161370045134231192011)
              ·
                refine ⟨343742055067701346788017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229161370045134231192011 343742055067701346788017)
                ·
                  refine ⟨257806541300776010091013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343742055067701346788017 257806541300776010091013)
                  ·
                    refine ⟨48338726493895501892065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 257806541300776010091013 48338726493895501892065)
                    ·
                      rfl

theorem cell22_141209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_141209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141209 prefixEnd_141209 := by exact prefixLift 141209
  have htrace : WordTrace (prefixWord ++ tailWord_141209) baseStart_141209 baseEnd_141209 := by
    simpa [prefixWord, tailWord_141209, baseEnd_141209] using wordTrace_append hprefix tailTrace_141209
  have hstable : (prefixWord ++ tailWord_141209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141209).length < 2 ^ (prefixWord ++ tailWord_141209).sum := by decide
  have hdescent : baseEnd_141209 < baseStart_141209 := by decide
  rcases family_descends (prefixWord ++ tailWord_141209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141215 : List Nat := [1, 1, 2, 5, 4, 1, 2, 1, 1, 4]
def baseStart_141215 : Nat := 118140960795 + 141215 * 2 ^ 59
def prefixEnd_141215 : Nat := 4983230072969 + 3 ^ 40 * 141215 * 2
def baseEnd_141215 : Nat := 48340780416513486242047

theorem tailTrace_141215 : CollatzResearch.WordTrace tailWord_141215 prefixEnd_141215 48340780416513486242047 := by
  unfold tailWord_141215
  simp only [CollatzResearch.WordTrace]
  refine ⟨5150534183409647447009099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3433689455606431631339399 5150534183409647447009099)
  ·
    refine ⟨7725801275114471170513649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5150534183409647447009099 7725801275114471170513649)
    ·
      refine ⟨5794350956335853377885237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7725801275114471170513649 5794350956335853377885237)
      ·
        refine ⟨543220402156486254176741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5794350956335853377885237 543220402156486254176741)
        ·
          refine ⟨101853825404341172658139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 543220402156486254176741 101853825404341172658139)
          ·
            refine ⟨152780738106511758987209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101853825404341172658139 152780738106511758987209)
            ·
              refine ⟨114585553579883819240407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152780738106511758987209 114585553579883819240407)
              ·
                refine ⟨171878330369825728860611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114585553579883819240407 171878330369825728860611)
                ·
                  refine ⟨257817495554738593290917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171878330369825728860611 257817495554738593290917)
                  ·
                    refine ⟨48340780416513486242047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 257817495554738593290917 48340780416513486242047)
                    ·
                      rfl

theorem cell22_141215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 1, 4].length) (baseStart_141215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141215 prefixEnd_141215 := by exact prefixLift 141215
  have htrace : WordTrace (prefixWord ++ tailWord_141215) baseStart_141215 baseEnd_141215 := by
    simpa [prefixWord, tailWord_141215, baseEnd_141215] using wordTrace_append hprefix tailTrace_141215
  have hstable : (prefixWord ++ tailWord_141215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141215).length < 2 ^ (prefixWord ++ tailWord_141215).sum := by decide
  have hdescent : baseEnd_141215 < baseStart_141215 := by decide
  rcases family_descends (prefixWord ++ tailWord_141215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141230 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_141230 : Nat := 118140960795 + 141230 * 2 ^ 59
def prefixEnd_141230 : Nat := 4983230072969 + 3 ^ 40 * 141230 * 2
def baseEnd_141230 : Nat := 16115305074352815705667

theorem tailTrace_141230 : CollatzResearch.WordTrace tailWord_141230 prefixEnd_141230 16115305074352815705667 := by
  unfold tailWord_141230
  simp only [CollatzResearch.WordTrace]
  refine ⟨643885159794413126100643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3434054185570203339203429 643885159794413126100643)
  ·
    refine ⟨965827739691619689150965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 643885159794413126100643 965827739691619689150965)
    ·
      refine ⟨90546350596089345857903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 965827739691619689150965 90546350596089345857903)
      ·
        refine ⟨135819525894134018786855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90546350596089345857903 135819525894134018786855)
        ·
          refine ⟨203729288841201028180283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135819525894134018786855 203729288841201028180283)
          ·
            refine ⟨305593933261801542270425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203729288841201028180283 305593933261801542270425)
            ·
              refine ⟨229195449946351156702819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305593933261801542270425 229195449946351156702819)
              ·
                refine ⟨343793174919526735054229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229195449946351156702819 343793174919526735054229)
                ·
                  refine ⟨16115305074352815705667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 343793174919526735054229 16115305074352815705667)
                  ·
                    rfl

theorem cell22_141230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_141230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141230 prefixEnd_141230 := by exact prefixLift 141230
  have htrace : WordTrace (prefixWord ++ tailWord_141230) baseStart_141230 baseEnd_141230 := by
    simpa [prefixWord, tailWord_141230, baseEnd_141230] using wordTrace_append hprefix tailTrace_141230
  have hstable : (prefixWord ++ tailWord_141230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141230).length < 2 ^ (prefixWord ++ tailWord_141230).sum := by decide
  have hdescent : baseEnd_141230 < baseStart_141230 := by decide
  rcases family_descends (prefixWord ++ tailWord_141230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141256 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 3, 3]
def baseStart_141256 : Nat := 118140960795 + 141256 * 2 ^ 59
def prefixEnd_141256 : Nat := 4983230072969 + 3 ^ 40 * 141256 * 2
def baseEnd_141256 : Nat := 48354815554403045966921

theorem tailTrace_141256 : CollatzResearch.WordTrace tailWord_141256 prefixEnd_141256 48354815554403045966921 := by
  unfold tailWord_141256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2576014788130555724625811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3434686384174074299501081 2576014788130555724625811)
  ·
    refine ⟨3864022182195833586938717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2576014788130555724625811 3864022182195833586938717)
    ·
      refine ⟨1449008318323437595102019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3864022182195833586938717 1449008318323437595102019)
      ·
        refine ⟨2173512477485156392653029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1449008318323437595102019 2173512477485156392653029)
        ·
          refine ⟨407533589528466823622443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2173512477485156392653029 407533589528466823622443)
          ·
            refine ⟨611300384292700235433665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407533589528466823622443 611300384292700235433665)
            ·
              refine ⟨458475288219525176575249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611300384292700235433665 458475288219525176575249)
              ·
                refine ⟨343856466164643882431437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458475288219525176575249 343856466164643882431437)
                ·
                  refine ⟨128946174811741455911789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343856466164643882431437 128946174811741455911789)
                  ·
                    refine ⟨48354815554403045966921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128946174811741455911789 48354815554403045966921)
                    ·
                      rfl

theorem cell22_141256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_141256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141256 prefixEnd_141256 := by exact prefixLift 141256
  have htrace : WordTrace (prefixWord ++ tailWord_141256) baseStart_141256 baseEnd_141256 := by
    simpa [prefixWord, tailWord_141256, baseEnd_141256] using wordTrace_append hprefix tailTrace_141256
  have hstable : (prefixWord ++ tailWord_141256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141256).length < 2 ^ (prefixWord ++ tailWord_141256).sum := by decide
  have hdescent : baseEnd_141256 < baseStart_141256 := by decide
  rcases family_descends (prefixWord ++ tailWord_141256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141269 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 7]
def baseStart_141269 : Nat := 118140960795 + 141269 * 2 ^ 59
def prefixEnd_141269 : Nat := 4983230072969 + 3 ^ 40 * 141269 * 2
def baseEnd_141269 : Nat := 16119755240025115130627

theorem tailTrace_141269 : CollatzResearch.WordTrace tailWord_141269 prefixEnd_141269 16119755240025115130627 := by
  unfold tailWord_141269
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152503725214014669474861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3435002483476009779649907 5152503725214014669474861)
  ·
    refine ⟨1932188896955255501053073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5152503725214014669474861 1932188896955255501053073)
    ·
      refine ⟨1449141672716441625789805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1932188896955255501053073 1449141672716441625789805)
      ·
        refine ⟨543428127268665609671177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1449141672716441625789805 543428127268665609671177)
        ·
          refine ⟨407571095451499207253383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543428127268665609671177 407571095451499207253383)
          ·
            refine ⟨611356643177248810880075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407571095451499207253383 611356643177248810880075)
            ·
              refine ⟨917034964765873216320113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611356643177248810880075 917034964765873216320113)
              ·
                refine ⟨687776223574404912240085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917034964765873216320113 687776223574404912240085)
                ·
                  refine ⟨16119755240025115130627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 687776223574404912240085 16119755240025115130627)
                  ·
                    rfl

theorem cell22_141269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_141269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141269 prefixEnd_141269 := by exact prefixLift 141269
  have htrace : WordTrace (prefixWord ++ tailWord_141269) baseStart_141269 baseEnd_141269 := by
    simpa [prefixWord, tailWord_141269, baseEnd_141269] using wordTrace_append hprefix tailTrace_141269
  have hstable : (prefixWord ++ tailWord_141269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141269).length < 2 ^ (prefixWord ++ tailWord_141269).sum := by decide
  have hdescent : baseEnd_141269 < baseStart_141269 := by decide
  rcases family_descends (prefixWord ++ tailWord_141269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141290 : List Nat := [3, 1, 3, 1, 2, 1, 5, 2, 1, 3]
def baseStart_141290 : Nat := 118140960795 + 141290 * 2 ^ 59
def prefixEnd_141290 : Nat := 4983230072969 + 3 ^ 40 * 141290 * 2
def baseEnd_141290 : Nat := 48366454449238290616817

theorem tailTrace_141290 : CollatzResearch.WordTrace tailWord_141290 prefixEnd_141290 48366454449238290616817 := by
  unfold tailWord_141290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1288317414534483813997331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3435513105425290170659549 1288317414534483813997331)
  ·
    refine ⟨1932476121801725720995997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1288317414534483813997331 1932476121801725720995997)
    ·
      refine ⟨724678545675647145373499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1932476121801725720995997 724678545675647145373499)
      ·
        refine ⟨1087017818513470718060249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724678545675647145373499 1087017818513470718060249)
        ·
          refine ⟨815263363885103038545187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1087017818513470718060249 815263363885103038545187)
          ·
            refine ⟨1222895045827654557817781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815263363885103038545187 1222895045827654557817781)
            ·
              refine ⟨114646410546342614795417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1222895045827654557817781 114646410546342614795417)
              ·
                refine ⟨85984807909756961096563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114646410546342614795417 85984807909756961096563)
                ·
                  refine ⟨128977211864635441644845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85984807909756961096563 128977211864635441644845)
                  ·
                    refine ⟨48366454449238290616817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128977211864635441644845 48366454449238290616817)
                    ·
                      rfl

theorem cell22_141290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_141290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141290 prefixEnd_141290 := by exact prefixLift 141290
  have htrace : WordTrace (prefixWord ++ tailWord_141290) baseStart_141290 baseEnd_141290 := by
    simpa [prefixWord, tailWord_141290, baseEnd_141290] using wordTrace_append hprefix tailTrace_141290
  have hstable : (prefixWord ++ tailWord_141290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141290).length < 2 ^ (prefixWord ++ tailWord_141290).sum := by decide
  have hdescent : baseEnd_141290 < baseStart_141290 := by decide
  rcases family_descends (prefixWord ++ tailWord_141290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141376 : List Nat := [2, 1, 1, 2, 2, 5, 3, 6]
def baseStart_141376 : Nat := 118140960795 + 141376 * 2 ^ 59
def prefixEnd_141376 : Nat := 4983230072969 + 3 ^ 40 * 141376 * 2
def baseEnd_141376 : Nat := 5377321556306970329617

theorem tailTrace_141376 : CollatzResearch.WordTrace tailWord_141376 prefixEnd_141376 5377321556306970329617 := by
  unfold tailWord_141376
  simp only [CollatzResearch.WordTrace]
  refine ⟨2578203167913185971809991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3437604223884247962413321 2578203167913185971809991)
  ·
    refine ⟨3867304751869778957714987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2578203167913185971809991 3867304751869778957714987)
    ·
      refine ⟨5800957127804668436572481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3867304751869778957714987 5800957127804668436572481)
      ·
        refine ⟨4350717845853501327429361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5800957127804668436572481 4350717845853501327429361)
        ·
          refine ⟨3263038384390125995572021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4350717845853501327429361 3263038384390125995572021)
          ·
            refine ⟨305909848536574312084877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3263038384390125995572021 305909848536574312084877)
            ·
              refine ⟨114716193201215367031829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305909848536574312084877 114716193201215367031829)
              ·
                refine ⟨5377321556306970329617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114716193201215367031829 5377321556306970329617)
                ·
                  rfl

theorem cell22_141376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 6].length) (baseStart_141376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141376 prefixEnd_141376 := by exact prefixLift 141376
  have htrace : WordTrace (prefixWord ++ tailWord_141376) baseStart_141376 baseEnd_141376 := by
    simpa [prefixWord, tailWord_141376, baseEnd_141376] using wordTrace_append hprefix tailTrace_141376
  have hstable : (prefixWord ++ tailWord_141376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141376).length < 2 ^ (prefixWord ++ tailWord_141376).sum := by decide
  have hdescent : baseEnd_141376 < baseStart_141376 := by decide
  rcases family_descends (prefixWord ++ tailWord_141376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141408 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 3, 3]
def baseStart_141408 : Nat := 118140960795 + 141408 * 2 ^ 59
def prefixEnd_141408 : Nat := 4983230072969 + 3 ^ 40 * 141408 * 2
def baseEnd_141408 : Nat := 48406848260725316166455

theorem tailTrace_141408 : CollatzResearch.WordTrace tailWord_141408 prefixEnd_141408 48406848260725316166455 := by
  unfold tailWord_141408
  simp only [CollatzResearch.WordTrace]
  refine ⟨2578786735855220704392439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3438382314473627605856585 2578786735855220704392439)
  ·
    refine ⟨3868180103782831056588659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2578786735855220704392439 3868180103782831056588659)
    ·
      refine ⟨5802270155674246584882989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3868180103782831056588659 5802270155674246584882989)
      ·
        refine ⟨2175851308377842469331121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5802270155674246584882989 2175851308377842469331121)
        ·
          refine ⟨1631888481283381851998341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2175851308377842469331121 1631888481283381851998341)
          ·
            refine ⟨305979090240634097249689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1631888481283381851998341 305979090240634097249689)
            ·
              refine ⟨229484317680475572937267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305979090240634097249689 229484317680475572937267)
              ·
                refine ⟨344226476520713359405901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229484317680475572937267 344226476520713359405901)
                ·
                  refine ⟨129084928695267509777213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344226476520713359405901 129084928695267509777213)
                  ·
                    refine ⟨48406848260725316166455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 129084928695267509777213 48406848260725316166455)
                    ·
                      rfl

theorem cell22_141408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 3, 3].length) (baseStart_141408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141408 prefixEnd_141408 := by exact prefixLift 141408
  have htrace : WordTrace (prefixWord ++ tailWord_141408) baseStart_141408 baseEnd_141408 := by
    simpa [prefixWord, tailWord_141408, baseEnd_141408] using wordTrace_append hprefix tailTrace_141408
  have hstable : (prefixWord ++ tailWord_141408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141408).length < 2 ^ (prefixWord ++ tailWord_141408).sum := by decide
  have hdescent : baseEnd_141408 < baseStart_141408 := by decide
  rcases family_descends (prefixWord ++ tailWord_141408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141434 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_141434 : Nat := 118140960795 + 141434 * 2 ^ 59
def prefixEnd_141434 : Nat := 4983230072969 + 3 ^ 40 * 141434 * 2
def baseEnd_141434 : Nat := 48415748592069915016375

theorem tailTrace_141434 : CollatzResearch.WordTrace tailWord_141434 prefixEnd_141434 48415748592069915016375 := by
  unfold tailWord_141434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289630442404061962307839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3439014513077498566154237 1289630442404061962307839)
  ·
    refine ⟨1934445663606092943461759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289630442404061962307839 1934445663606092943461759)
    ·
      refine ⟨2901668495409139415192639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934445663606092943461759 2901668495409139415192639)
      ·
        refine ⟨4352502743113709122788959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2901668495409139415192639 4352502743113709122788959)
        ·
          refine ⟨6528754114670563684183439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4352502743113709122788959 6528754114670563684183439)
          ·
            refine ⟨9793131172005845526275159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6528754114670563684183439 9793131172005845526275159)
            ·
              refine ⟨14689696758008768289412739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9793131172005845526275159 14689696758008768289412739)
              ·
                refine ⟨22034545137013152434119109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14689696758008768289412739 22034545137013152434119109)
                ·
                  refine ⟨4131477213189966081397333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22034545137013152434119109 4131477213189966081397333)
                  ·
                    refine ⟨48415748592069915016375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4131477213189966081397333 48415748592069915016375)
                    ·
                      rfl

theorem cell22_141434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_141434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141434 prefixEnd_141434 := by exact prefixLift 141434
  have htrace : WordTrace (prefixWord ++ tailWord_141434) baseStart_141434 baseEnd_141434 := by
    simpa [prefixWord, tailWord_141434, baseEnd_141434] using wordTrace_append hprefix tailTrace_141434
  have hstable : (prefixWord ++ tailWord_141434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141434).length < 2 ^ (prefixWord ++ tailWord_141434).sum := by decide
  have hdescent : baseEnd_141434 < baseStart_141434 := by decide
  rcases family_descends (prefixWord ++ tailWord_141434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141485 : List Nat := [1, 5, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_141485 : Nat := 118140960795 + 141485 * 2 ^ 59
def prefixEnd_141485 : Nat := 4983230072969 + 3 ^ 40 * 141485 * 2
def baseEnd_141485 : Nat := 48433206934322781991219

theorem tailTrace_141485 : CollatzResearch.WordTrace tailWord_141485 prefixEnd_141485 48433206934322781991219 := by
  unfold tailWord_141485
  simp only [CollatzResearch.WordTrace]
  refine ⟨5160381892431483559337909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3440254594954322372891939 5160381892431483559337909)
  ·
    refine ⟨483785802415451583687929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5160381892431483559337909 483785802415451583687929)
    ·
      refine ⟨362839351811588687765947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 483785802415451583687929 362839351811588687765947)
      ·
        refine ⟨544259027717383031648921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362839351811588687765947 544259027717383031648921)
        ·
          refine ⟨408194270788037273736691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544259027717383031648921 408194270788037273736691)
          ·
            refine ⟨612291406182055910605037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408194270788037273736691 612291406182055910605037)
            ·
              refine ⟨229609277318270966476889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 612291406182055910605037 229609277318270966476889)
              ·
                refine ⟨172206957988703224857667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229609277318270966476889 172206957988703224857667)
                ·
                  refine ⟨258310436983054837286501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172206957988703224857667 258310436983054837286501)
                  ·
                    refine ⟨48433206934322781991219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 258310436983054837286501 48433206934322781991219)
                    ·
                      rfl

theorem cell22_141485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_141485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141485 prefixEnd_141485 := by exact prefixLift 141485
  have htrace : WordTrace (prefixWord ++ tailWord_141485) baseStart_141485 baseEnd_141485 := by
    simpa [prefixWord, tailWord_141485, baseEnd_141485] using wordTrace_append hprefix tailTrace_141485
  have hstable : (prefixWord ++ tailWord_141485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141485).length < 2 ^ (prefixWord ++ tailWord_141485).sum := by decide
  have hdescent : baseEnd_141485 < baseStart_141485 := by decide
  rcases family_descends (prefixWord ++ tailWord_141485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141502 : List Nat := [4, 2, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_141502 : Nat := 118140960795 + 141502 * 2 ^ 59
def prefixEnd_141502 : Nat := 4983230072969 + 3 ^ 40 * 141502 * 2
def baseEnd_141502 : Nat := 48439026381740404316167

theorem tailTrace_141502 : CollatzResearch.WordTrace tailWord_141502 prefixEnd_141502 48439026381740404316167 := by
  unfold tailWord_141502
  simp only [CollatzResearch.WordTrace]
  refine ⟨645125241671236932838345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3440667955579930308471173 645125241671236932838345)
  ·
    refine ⟨483843931253427699628759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 645125241671236932838345 483843931253427699628759)
    ·
      refine ⟨725765896880141549443139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 483843931253427699628759 725765896880141549443139)
      ·
        refine ⟨1088648845320212324164709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725765896880141549443139 1088648845320212324164709)
        ·
          refine ⟨204121658497539810780883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1088648845320212324164709 204121658497539810780883)
          ·
            refine ⟨306182487746309716171325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204121658497539810780883 306182487746309716171325)
            ·
              refine ⟨114818432904866143564247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 306182487746309716171325 114818432904866143564247)
              ·
                refine ⟨172227649357299215346371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114818432904866143564247 172227649357299215346371)
                ·
                  refine ⟨258341474035948823019557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172227649357299215346371 258341474035948823019557)
                  ·
                    refine ⟨48439026381740404316167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 258341474035948823019557 48439026381740404316167)
                    ·
                      rfl

theorem cell22_141502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_141502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141502 prefixEnd_141502 := by exact prefixLift 141502
  have htrace : WordTrace (prefixWord ++ tailWord_141502) baseStart_141502 baseEnd_141502 := by
    simpa [prefixWord, tailWord_141502, baseEnd_141502] using wordTrace_append hprefix tailTrace_141502
  have hstable : (prefixWord ++ tailWord_141502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141502).length < 2 ^ (prefixWord ++ tailWord_141502).sum := by decide
  have hdescent : baseEnd_141502 < baseStart_141502 := by decide
  rcases family_descends (prefixWord ++ tailWord_141502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141528 : List Nat := [2, 1, 2, 2, 4, 3, 1, 7]
def baseStart_141528 : Nat := 118140960795 + 141528 * 2 ^ 59
def prefixEnd_141528 : Nat := 4983230072969 + 3 ^ 40 * 141528 * 2
def baseEnd_141528 : Nat := 5383102968120555907343

theorem tailTrace_141528 : CollatzResearch.WordTrace tailWord_141528 prefixEnd_141528 5383102968120555907343 := by
  unfold tailWord_141528
  simp only [CollatzResearch.WordTrace]
  refine ⟨2580975115637850951576619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3441300154183801268768825 2580975115637850951576619)
  ·
    refine ⟨3871462673456776427364929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2580975115637850951576619 3871462673456776427364929)
    ·
      refine ⟨2903597005092582320523697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3871462673456776427364929 2903597005092582320523697)
      ·
        refine ⟨2177697753819436740392773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2903597005092582320523697 2177697753819436740392773)
        ·
          refine ⟨408318328841144388823645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2177697753819436740392773 408318328841144388823645)
          ·
            refine ⟨153119373315429145808867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 408318328841144388823645 153119373315429145808867)
            ·
              refine ⟨229679059973143718713301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153119373315429145808867 229679059973143718713301)
              ·
                refine ⟨5383102968120555907343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 229679059973143718713301 5383102968120555907343)
                ·
                  rfl

theorem cell22_141528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 7].length) (baseStart_141528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141528 prefixEnd_141528 := by exact prefixLift 141528
  have htrace : WordTrace (prefixWord ++ tailWord_141528) baseStart_141528 baseEnd_141528 := by
    simpa [prefixWord, tailWord_141528, baseEnd_141528] using wordTrace_append hprefix tailTrace_141528
  have hstable : (prefixWord ++ tailWord_141528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141528).length < 2 ^ (prefixWord ++ tailWord_141528).sum := by decide
  have hdescent : baseEnd_141528 < baseStart_141528 := by decide
  rcases family_descends (prefixWord ++ tailWord_141528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141532 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 1, 5]
def baseStart_141532 : Nat := 118140960795 + 141532 * 2 ^ 59
def prefixEnd_141532 : Nat := 4983230072969 + 3 ^ 40 * 141532 * 2
def baseEnd_141532 : Nat := 48449295994830326066075

theorem tailTrace_141532 : CollatzResearch.WordTrace tailWord_141532 prefixEnd_141532 48449295994830326066075 := by
  unfold tailWord_141532
  simp only [CollatzResearch.WordTrace]
  refine ⟨2581048061630605293149425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3441397415507473724199233 2581048061630605293149425)
  ·
    refine ⟨1935786046222953969862069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2581048061630605293149425 1935786046222953969862069)
    ·
      refine ⟨181479941833401934674569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1935786046222953969862069 181479941833401934674569)
      ·
        refine ⟨136109956375051451005927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181479941833401934674569 136109956375051451005927)
        ·
          refine ⟨204164934562577176508891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136109956375051451005927 204164934562577176508891)
          ·
            refine ⟨306247401843865764763337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204164934562577176508891 306247401843865764763337)
            ·
              refine ⟨229685551382899323572503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306247401843865764763337 229685551382899323572503)
              ·
                refine ⟨344528327074348985358755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229685551382899323572503 344528327074348985358755)
                ·
                  refine ⟨516792490611523478038133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344528327074348985358755 516792490611523478038133)
                  ·
                    refine ⟨48449295994830326066075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 516792490611523478038133 48449295994830326066075)
                    ·
                      rfl

theorem cell22_141532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_141532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141532 prefixEnd_141532 := by exact prefixLift 141532
  have htrace : WordTrace (prefixWord ++ tailWord_141532) baseStart_141532 baseEnd_141532 := by
    simpa [prefixWord, tailWord_141532, baseEnd_141532] using wordTrace_append hprefix tailTrace_141532
  have hstable : (prefixWord ++ tailWord_141532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141532).length < 2 ^ (prefixWord ++ tailWord_141532).sum := by decide
  have hdescent : baseEnd_141532 < baseStart_141532 := by decide
  rcases family_descends (prefixWord ++ tailWord_141532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141571 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 4, 5]
def baseStart_141571 : Nat := 118140960795 + 141571 * 2 ^ 59
def prefixEnd_141571 : Nat := 4983230072969 + 3 ^ 40 * 141571 * 2
def baseEnd_141571 : Nat := 48462646491847224340955

theorem tailTrace_141571 : CollatzResearch.WordTrace tailWord_141571 prefixEnd_141571 48462646491847224340955 := by
  unfold tailWord_141571
  simp only [CollatzResearch.WordTrace]
  refine ⟨5163518570119920246968567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3442345713413280164645711 5163518570119920246968567)
  ·
    refine ⟨7745277855179880370452851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5163518570119920246968567 7745277855179880370452851)
    ·
      refine ⟨11617916782769820555679277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7745277855179880370452851 11617916782769820555679277)
      ·
        refine ⟨4356718793538682708379729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11617916782769820555679277 4356718793538682708379729)
        ·
          refine ⟨3267539095154012031284797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4356718793538682708379729 3267539095154012031284797)
          ·
            refine ⟨1225327160682754511731799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3267539095154012031284797 1225327160682754511731799)
            ·
              refine ⟨1837990741024131767597699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225327160682754511731799 1837990741024131767597699)
              ·
                refine ⟨2756986111536197651396549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837990741024131767597699 2756986111536197651396549)
                ·
                  refine ⟨516934895913037059636853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2756986111536197651396549 516934895913037059636853)
                  ·
                    refine ⟨48462646491847224340955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 516934895913037059636853 48462646491847224340955)
                    ·
                      rfl

theorem cell22_141571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_141571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141571 prefixEnd_141571 := by exact prefixLift 141571
  have htrace : WordTrace (prefixWord ++ tailWord_141571) baseStart_141571 baseEnd_141571 := by
    simpa [prefixWord, tailWord_141571, baseEnd_141571] using wordTrace_append hprefix tailTrace_141571
  have hstable : (prefixWord ++ tailWord_141571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141571).length < 2 ^ (prefixWord ++ tailWord_141571).sum := by decide
  have hdescent : baseEnd_141571 < baseStart_141571 := by decide
  rcases family_descends (prefixWord ++ tailWord_141571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141693 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_141693 : Nat := 118140960795 + 141693 * 2 ^ 59
def prefixEnd_141693 : Nat := 4983230072969 + 3 ^ 40 * 141693 * 2
def baseEnd_141693 : Nat := 48504409585079572790581

theorem tailTrace_141693 : CollatzResearch.WordTrace tailWord_141693 prefixEnd_141693 48504409585079572790581 := by
  unfold tailWord_141693
  simp only [CollatzResearch.WordTrace]
  refine ⟨5167968275677935082909733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3445312183785290055273155 5167968275677935082909733)
  ·
    refine ⟨968994051689612828045575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5167968275677935082909733 968994051689612828045575)
    ·
      refine ⟨1453491077534419242068363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 968994051689612828045575 1453491077534419242068363)
      ·
        refine ⟨2180236616301628863102545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1453491077534419242068363 2180236616301628863102545)
        ·
          refine ⟨1635177462226221647326909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2180236616301628863102545 1635177462226221647326909)
          ·
            refine ⟨613191548334833117747591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1635177462226221647326909 613191548334833117747591)
            ·
              refine ⟨919787322502249676621387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613191548334833117747591 919787322502249676621387)
              ·
                refine ⟨1379680983753374514932081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919787322502249676621387 1379680983753374514932081)
                ·
                  refine ⟨1034760737815030886199061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1379680983753374514932081 1034760737815030886199061)
                  ·
                    refine ⟨48504409585079572790581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1034760737815030886199061 48504409585079572790581)
                    ·
                      rfl

theorem cell22_141693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_141693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141693 prefixEnd_141693 := by exact prefixLift 141693
  have htrace : WordTrace (prefixWord ++ tailWord_141693) baseStart_141693 baseEnd_141693 := by
    simpa [prefixWord, tailWord_141693, baseEnd_141693] using wordTrace_append hprefix tailTrace_141693
  have hstable : (prefixWord ++ tailWord_141693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141693).length < 2 ^ (prefixWord ++ tailWord_141693).sum := by decide
  have hdescent : baseEnd_141693 < baseStart_141693 := by decide
  rcases family_descends (prefixWord ++ tailWord_141693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141785 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 6, 3]
def baseStart_141785 : Nat := 118140960795 + 141785 * 2 ^ 59
def prefixEnd_141785 : Nat := 4983230072969 + 3 ^ 40 * 141785 * 2
def baseEnd_141785 : Nat := 48535903065221999490299

theorem tailTrace_141785 : CollatzResearch.WordTrace tailWord_141785 prefixEnd_141785 48535903065221999490299 := by
  unfold tailWord_141785
  simp only [CollatzResearch.WordTrace]
  refine ⟨5171323791344634795258809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3447549194229756530172539 5171323791344634795258809)
  ·
    refine ⟨3878492843508476096444107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5171323791344634795258809 3878492843508476096444107)
    ·
      refine ⟨5817739265262714144666161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3878492843508476096444107 5817739265262714144666161)
      ·
        refine ⟨4363304448947035608499621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5817739265262714144666161 4363304448947035608499621)
        ·
          refine ⟨818119584177569176593679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4363304448947035608499621 818119584177569176593679)
          ·
            refine ⟨1227179376266353764890519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818119584177569176593679 1227179376266353764890519)
            ·
              refine ⟨1840769064399530647335779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227179376266353764890519 1840769064399530647335779)
              ·
                refine ⟨2761153596599295971003669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840769064399530647335779 2761153596599295971003669)
                ·
                  refine ⟨129429074840591998640797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2761153596599295971003669 129429074840591998640797)
                  ·
                    refine ⟨48535903065221999490299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 129429074840591998640797 48535903065221999490299)
                    ·
                      rfl

theorem cell22_141785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 3].length) (baseStart_141785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141785 prefixEnd_141785 := by exact prefixLift 141785
  have htrace : WordTrace (prefixWord ++ tailWord_141785) baseStart_141785 baseEnd_141785 := by
    simpa [prefixWord, tailWord_141785, baseEnd_141785] using wordTrace_append hprefix tailTrace_141785
  have hstable : (prefixWord ++ tailWord_141785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141785).length < 2 ^ (prefixWord ++ tailWord_141785).sum := by decide
  have hdescent : baseEnd_141785 < baseStart_141785 := by decide
  rcases family_descends (prefixWord ++ tailWord_141785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141800 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 4, 4]
def baseStart_141800 : Nat := 118140960795 + 141800 * 2 ^ 59
def prefixEnd_141800 : Nat := 4983230072969 + 3 ^ 40 * 141800 * 2
def baseEnd_141800 : Nat := 48541037871766960365253

theorem tailTrace_141800 : CollatzResearch.WordTrace tailWord_141800 prefixEnd_141800 48541037871766960365253 := by
  unfold tailWord_141800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2585935443145146178527427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3447913924193528238036569 2585935443145146178527427)
  ·
    refine ⟨3878903164717719267791141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2585935443145146178527427 3878903164717719267791141)
    ·
      refine ⟨727294343384572362710839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3878903164717719267791141 727294343384572362710839)
      ·
        refine ⟨1090941515076858544066259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727294343384572362710839 1090941515076858544066259)
        ·
          refine ⟨1636412272615287816099389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090941515076858544066259 1636412272615287816099389)
          ·
            refine ⟨613654602230732931037271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1636412272615287816099389 613654602230732931037271)
            ·
              refine ⟨920481903346099396555907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613654602230732931037271 920481903346099396555907)
              ·
                refine ⟨1380722855019149094833861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920481903346099396555907 1380722855019149094833861)
                ·
                  refine ⟨258885535316090455281349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1380722855019149094833861 258885535316090455281349)
                  ·
                    refine ⟨48541037871766960365253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 258885535316090455281349 48541037871766960365253)
                    ·
                      rfl

theorem cell22_141800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_141800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141800 prefixEnd_141800 := by exact prefixLift 141800
  have htrace : WordTrace (prefixWord ++ tailWord_141800) baseStart_141800 baseEnd_141800 := by
    simpa [prefixWord, tailWord_141800, baseEnd_141800] using wordTrace_append hprefix tailTrace_141800
  have hstable : (prefixWord ++ tailWord_141800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141800).length < 2 ^ (prefixWord ++ tailWord_141800).sum := by decide
  have hdescent : baseEnd_141800 < baseStart_141800 := by decide
  rcases family_descends (prefixWord ++ tailWord_141800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141802 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 4, 3]
def baseStart_141802 : Nat := 118140960795 + 141802 * 2 ^ 59
def prefixEnd_141802 : Nat := 4983230072969 + 3 ^ 40 * 141802 * 2
def baseEnd_141802 : Nat := 48541722512639621815247

theorem tailTrace_141802 : CollatzResearch.WordTrace tailWord_141802 prefixEnd_141802 48541722512639621815247 := by
  unfold tailWord_141802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1292985958070761674656915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3447962554855364465751773 1292985958070761674656915)
  ·
    refine ⟨1939478937106142511985373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1292985958070761674656915 1939478937106142511985373)
    ·
      refine ⟨727304601414803441994515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1939478937106142511985373 727304601414803441994515)
      ·
        refine ⟨1090956902122205162991773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727304601414803441994515 1090956902122205162991773)
        ·
          refine ⟨409108838295826936121915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1090956902122205162991773 409108838295826936121915)
          ·
            refine ⟨613663257443740404182873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409108838295826936121915 613663257443740404182873)
            ·
              refine ⟨460247443082805303137155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613663257443740404182873 460247443082805303137155)
              ·
                refine ⟨690371164624207954705733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460247443082805303137155 690371164624207954705733)
                ·
                  refine ⟨129444593367038991507325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690371164624207954705733 129444593367038991507325)
                  ·
                    refine ⟨48541722512639621815247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 129444593367038991507325 48541722512639621815247)
                    ·
                      rfl

theorem cell22_141802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_141802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141802 prefixEnd_141802 := by exact prefixLift 141802
  have htrace : WordTrace (prefixWord ++ tailWord_141802) baseStart_141802 baseEnd_141802 := by
    simpa [prefixWord, tailWord_141802, baseEnd_141802] using wordTrace_append hprefix tailTrace_141802
  have hstable : (prefixWord ++ tailWord_141802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141802).length < 2 ^ (prefixWord ++ tailWord_141802).sum := by decide
  have hdescent : baseEnd_141802 < baseStart_141802 := by decide
  rcases family_descends (prefixWord ++ tailWord_141802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141875 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 2, 5]
def baseStart_141875 : Nat := 118140960795 + 141875 * 2 ^ 59
def prefixEnd_141875 : Nat := 4983230072969 + 3 ^ 40 * 141875 * 2
def baseEnd_141875 : Nat := 48566711904491764740023

theorem tailTrace_141875 : CollatzResearch.WordTrace tailWord_141875 prefixEnd_141875 48566711904491764740023 := by
  unfold tailWord_141875
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174606361018580166035079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3449737574012386777356719 5174606361018580166035079)
  ·
    refine ⟨7761909541527870249052619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5174606361018580166035079 7761909541527870249052619)
    ·
      refine ⟨11642864312291805373578929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7761909541527870249052619 11642864312291805373578929)
      ·
        refine ⟨8732148234218854030184197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11642864312291805373578929 8732148234218854030184197)
        ·
          refine ⟨1637277793916035130659537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8732148234218854030184197 1637277793916035130659537)
          ·
            refine ⟨1227958345437026347994653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1637277793916035130659537 1227958345437026347994653)
            ·
              refine ⟨460484379538884880497995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1227958345437026347994653 460484379538884880497995)
              ·
                refine ⟨690726569308327320746993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460484379538884880497995 690726569308327320746993)
                ·
                  refine ⟨518044926981245490560245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 690726569308327320746993 518044926981245490560245)
                  ·
                    refine ⟨48566711904491764740023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 518044926981245490560245 48566711904491764740023)
                    ·
                      rfl

theorem cell22_141875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 5].length) (baseStart_141875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141875 prefixEnd_141875 := by exact prefixLift 141875
  have htrace : WordTrace (prefixWord ++ tailWord_141875) baseStart_141875 baseEnd_141875 := by
    simpa [prefixWord, tailWord_141875, baseEnd_141875] using wordTrace_append hprefix tailTrace_141875
  have hstable : (prefixWord ++ tailWord_141875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141875).length < 2 ^ (prefixWord ++ tailWord_141875).sum := by decide
  have hdescent : baseEnd_141875 < baseStart_141875 := by decide
  rcases family_descends (prefixWord ++ tailWord_141875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141920 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 3, 5]
def baseStart_141920 : Nat := 118140960795 + 141920 * 2 ^ 59
def prefixEnd_141920 : Nat := 4983230072969 + 3 ^ 40 * 141920 * 2
def baseEnd_141920 : Nat := 48582116324126647364885

theorem tailTrace_141920 : CollatzResearch.WordTrace tailWord_141920 prefixEnd_141920 48582116324126647364885 := by
  unfold tailWord_141920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2588123822927776425711607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3450831763903701900948809 2588123822927776425711607)
  ·
    refine ⟨3882185734391664638567411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2588123822927776425711607 3882185734391664638567411)
    ·
      refine ⟨5823278601587496957851117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3882185734391664638567411 5823278601587496957851117)
      ·
        refine ⟨2183729475595311359194169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5823278601587496957851117 2183729475595311359194169)
        ·
          refine ⟨1637797106696483519395627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2183729475595311359194169 1637797106696483519395627)
          ·
            refine ⟨2456695660044725279093441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637797106696483519395627 2456695660044725279093441)
            ·
              refine ⟨1842521745033543959320081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2456695660044725279093441 1842521745033543959320081)
              ·
                refine ⟨1381891308775157969490061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1842521745033543959320081 1381891308775157969490061)
                ·
                  refine ⟨518209240790684238558773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1381891308775157969490061 518209240790684238558773)
                  ·
                    refine ⟨48582116324126647364885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 518209240790684238558773 48582116324126647364885)
                    ·
                      rfl

theorem cell22_141920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_141920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141920 prefixEnd_141920 := by exact prefixLift 141920
  have htrace : WordTrace (prefixWord ++ tailWord_141920) baseStart_141920 baseEnd_141920 := by
    simpa [prefixWord, tailWord_141920, baseEnd_141920] using wordTrace_append hprefix tailTrace_141920
  have hstable : (prefixWord ++ tailWord_141920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141920).length < 2 ^ (prefixWord ++ tailWord_141920).sum := by decide
  have hdescent : baseEnd_141920 < baseStart_141920 := by decide
  rcases family_descends (prefixWord ++ tailWord_141920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
