import V185TrunkScan21Chunk042

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_520540 : List Nat := [2, 2, 4, 3, 1, 1, 2, 6]
def baseStart_520540 : Nat := 118140960795 + 520540 * 2 ^ 59
def prefixEnd_520540 : Nat := 4983230072969 + 3 ^ 40 * 520540 * 2
def baseEnd_520540 : Nat := 39598106650592387934235

theorem tailTrace_520540 : CollatzResearch.WordTrace tailWord_520540 prefixEnd_520540 39598106650592387934235 := by
  unfold tailWord_520540
  simp only [CollatzResearch.WordTrace]
  refine ⟨9492826767089977999663537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12657102356119970666218049 9492826767089977999663537)
  ·
    refine ⟨7119620075317483499747653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9492826767089977999663537 7119620075317483499747653)
    ·
      refine ⟨1334928764122028156202685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7119620075317483499747653 1334928764122028156202685)
      ·
        refine ⟨500598286545760558576007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1334928764122028156202685 500598286545760558576007)
        ·
          refine ⟨750897429818640837864011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500598286545760558576007 750897429818640837864011)
          ·
            refine ⟨1126346144727961256796017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750897429818640837864011 1126346144727961256796017)
            ·
              refine ⟨844759608545970942597013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126346144727961256796017 844759608545970942597013)
              ·
                refine ⟨39598106650592387934235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 844759608545970942597013 39598106650592387934235)
                ·
                  rfl

theorem cell21_520540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_520540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520540 prefixEnd_520540 := by exact prefixLift 520540
  have htrace : WordTrace (prefixWord ++ tailWord_520540) baseStart_520540 baseEnd_520540 := by
    simpa [prefixWord, tailWord_520540, baseEnd_520540] using wordTrace_append hprefix tailTrace_520540
  have hstable : (prefixWord ++ tailWord_520540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520540).length < 2 ^ (prefixWord ++ tailWord_520540).sum := by decide
  have hdescent : baseEnd_520540 < baseStart_520540 := by decide
  rcases family_descends (prefixWord ++ tailWord_520540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520616 : List Nat := [2, 1, 6, 1, 1, 2, 3, 5]
def baseStart_520616 : Nat := 118140960795 + 520616 * 2 ^ 59
def prefixEnd_520616 : Nat := 4983230072969 + 3 ^ 40 * 520616 * 2
def baseEnd_520616 : Nat := 39603888062405973511961

theorem tailTrace_520616 : CollatzResearch.WordTrace tailWord_520616 prefixEnd_520616 39603888062405973511961 := by
  unfold tailWord_520616
  simp only [CollatzResearch.WordTrace]
  refine ⟨9494212740952310489546851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12658950321269747319395801 9494212740952310489546851)
  ·
    refine ⟨14241319111428465734320277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9494212740952310489546851 14241319111428465734320277)
    ·
      refine ⟨667561833348209331296263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14241319111428465734320277 667561833348209331296263)
      ·
        refine ⟨1001342750022313996944395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667561833348209331296263 1001342750022313996944395)
        ·
          refine ⟨1502014125033470995416593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001342750022313996944395 1502014125033470995416593)
          ·
            refine ⟨1126510593775103246562445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1502014125033470995416593 1126510593775103246562445)
            ·
              refine ⟨422441472665663717460917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1126510593775103246562445 422441472665663717460917)
              ·
                refine ⟨39603888062405973511961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 422441472665663717460917 39603888062405973511961)
                ·
                  rfl

theorem cell21_520616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_520616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520616 prefixEnd_520616 := by exact prefixLift 520616
  have htrace : WordTrace (prefixWord ++ tailWord_520616) baseStart_520616 baseEnd_520616 := by
    simpa [prefixWord, tailWord_520616, baseEnd_520616] using wordTrace_append hprefix tailTrace_520616
  have hstable : (prefixWord ++ tailWord_520616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520616).length < 2 ^ (prefixWord ++ tailWord_520616).sum := by decide
  have hdescent : baseEnd_520616 < baseStart_520616 := by decide
  rcases family_descends (prefixWord ++ tailWord_520616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520661 : List Nat := [1, 3, 2, 3, 1, 3, 3, 1, 4]
def baseStart_520661 : Nat := 118140960795 + 520661 * 2 ^ 59
def prefixEnd_520661 : Nat := 4983230072969 + 3 ^ 40 * 520661 * 2
def baseEnd_520661 : Nat := 118821933800307842285791

theorem tailTrace_520661 : CollatzResearch.WordTrace tailWord_520661 prefixEnd_520661 118821933800307842285791 := by
  unfold tailWord_520661
  simp only [CollatzResearch.WordTrace]
  refine ⟨18990066766741593664481837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12660044511161062442987891 18990066766741593664481837)
  ·
    refine ⟨7121275037528097624180689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18990066766741593664481837 7121275037528097624180689)
    ·
      refine ⟨5340956278146073218135517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7121275037528097624180689 5340956278146073218135517)
      ·
        refine ⟨2002858604304777456800819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5340956278146073218135517 2002858604304777456800819)
        ·
          refine ⟨3004287906457166185201229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002858604304777456800819 3004287906457166185201229)
          ·
            refine ⟨1126607964921437319450461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3004287906457166185201229 1126607964921437319450461)
            ·
              refine ⟨422477986845538994793923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1126607964921437319450461 422477986845538994793923)
              ·
                refine ⟨633716980268308492190885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422477986845538994793923 633716980268308492190885)
                ·
                  refine ⟨118821933800307842285791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 633716980268308492190885 118821933800307842285791)
                  ·
                    rfl

theorem cell21_520661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_520661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520661 prefixEnd_520661 := by exact prefixLift 520661
  have htrace : WordTrace (prefixWord ++ tailWord_520661) baseStart_520661 baseEnd_520661 := by
    simpa [prefixWord, tailWord_520661, baseEnd_520661] using wordTrace_append hprefix tailTrace_520661
  have hstable : (prefixWord ++ tailWord_520661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520661).length < 2 ^ (prefixWord ++ tailWord_520661).sum := by decide
  have hdescent : baseEnd_520661 < baseStart_520661 := by decide
  rcases family_descends (prefixWord ++ tailWord_520661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520672 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 5]
def baseStart_520672 : Nat := 118140960795 + 520672 * 2 ^ 59
def prefixEnd_520672 : Nat := 4983230072969 + 3 ^ 40 * 520672 * 2
def baseEnd_520672 : Nat := 118824444150174267602435

theorem tailTrace_520672 : CollatzResearch.WordTrace tailWord_520672 prefixEnd_520672 118824444150174267602435 := by
  unfold tailWord_520672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9495233984850871271566135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12660311979801161695421513 9495233984850871271566135)
  ·
    refine ⟨14242850977276306907349203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9495233984850871271566135 14242850977276306907349203)
    ·
      refine ⟨21364276465914460361023805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14242850977276306907349203 21364276465914460361023805)
      ·
        refine ⟨8011603674717922635383927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21364276465914460361023805 8011603674717922635383927)
        ·
          refine ⟨12017405512076883953075891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8011603674717922635383927 12017405512076883953075891)
          ·
            refine ⟨18026108268115325929613837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12017405512076883953075891 18026108268115325929613837)
            ·
              refine ⟨6759790600543247223605189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18026108268115325929613837 6759790600543247223605189)
              ·
                refine ⟨1267460737601858854425973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6759790600543247223605189 1267460737601858854425973)
                ·
                  refine ⟨118824444150174267602435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1267460737601858854425973 118824444150174267602435)
                  ·
                    rfl

theorem cell21_520672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_520672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520672 prefixEnd_520672 := by exact prefixLift 520672
  have htrace : WordTrace (prefixWord ++ tailWord_520672) baseStart_520672 baseEnd_520672 := by
    simpa [prefixWord, tailWord_520672, baseEnd_520672] using wordTrace_append hprefix tailTrace_520672
  have hstable : (prefixWord ++ tailWord_520672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520672).length < 2 ^ (prefixWord ++ tailWord_520672).sum := by decide
  have hdescent : baseEnd_520672 < baseStart_520672 := by decide
  rcases family_descends (prefixWord ++ tailWord_520672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520703 : List Nat := [1, 1, 2, 2, 1, 2, 4, 4, 4]
def baseStart_520703 : Nat := 118140960795 + 520703 * 2 ^ 59
def prefixEnd_520703 : Nat := 4983230072969 + 3 ^ 40 * 520703 * 2
def baseEnd_520703 : Nat := 118831518772525102585705

theorem tailTrace_520703 : CollatzResearch.WordTrace tailWord_520703 prefixEnd_520703 118831518772525102585705 := by
  unfold tailWord_520703
  simp only [CollatzResearch.WordTrace]
  refine ⟨18991598632589434837510763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12661065755059623225007175 18991598632589434837510763)
  ·
    refine ⟨28487397948884152256266145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18991598632589434837510763 28487397948884152256266145)
    ·
      refine ⟨21365548461663114192199609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28487397948884152256266145 21365548461663114192199609)
      ·
        refine ⟨16024161346247335644149707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21365548461663114192199609 16024161346247335644149707)
        ·
          refine ⟨24036242019371003466224561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16024161346247335644149707 24036242019371003466224561)
          ·
            refine ⟨18027181514528252599668421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24036242019371003466224561 18027181514528252599668421)
            ·
              refine ⟨3380096533974047362437829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18027181514528252599668421 3380096533974047362437829)
              ·
                refine ⟨633768100120133880457093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3380096533974047362437829 633768100120133880457093)
                ·
                  refine ⟨118831518772525102585705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 633768100120133880457093 118831518772525102585705)
                  ·
                    rfl

theorem cell21_520703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 4].length) (baseStart_520703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520703 prefixEnd_520703 := by exact prefixLift 520703
  have htrace : WordTrace (prefixWord ++ tailWord_520703) baseStart_520703 baseEnd_520703 := by
    simpa [prefixWord, tailWord_520703, baseEnd_520703] using wordTrace_append hprefix tailTrace_520703
  have hstable : (prefixWord ++ tailWord_520703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520703).length < 2 ^ (prefixWord ++ tailWord_520703).sum := by decide
  have hdescent : baseEnd_520703 < baseStart_520703 := by decide
  rcases family_descends (prefixWord ++ tailWord_520703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520779 : List Nat := [1, 1, 1, 1, 3, 1, 6, 3, 4]
def baseStart_520779 : Nat := 118140960795 + 520779 * 2 ^ 59
def prefixEnd_520779 : Nat := 4983230072969 + 3 ^ 40 * 520779 * 2
def baseEnd_520779 : Nat := 118848863007965859318883

theorem tailTrace_520779 : CollatzResearch.WordTrace tailWord_520779 prefixEnd_520779 118848863007965859318883 := by
  unfold tailWord_520779
  simp only [CollatzResearch.WordTrace]
  refine ⟨18994370580314099817277391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12662913720209399878184927 18994370580314099817277391)
  ·
    refine ⟨28491555870471149725916087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18994370580314099817277391 28491555870471149725916087)
    ·
      refine ⟨42737333805706724588874131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28491555870471149725916087 42737333805706724588874131)
      ·
        refine ⟨64106000708560086883311197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42737333805706724588874131 64106000708560086883311197)
        ·
          refine ⟨24039750265710032581241699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64106000708560086883311197 24039750265710032581241699)
          ·
            refine ⟨36059625398565048871862549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24039750265710032581241699 36059625398565048871862549)
            ·
              refine ⟨1690294940557736665868557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36059625398565048871862549 1690294940557736665868557)
              ·
                refine ⟨633860602709151249700709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1690294940557736665868557 633860602709151249700709)
                ·
                  refine ⟨118848863007965859318883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 633860602709151249700709 118848863007965859318883)
                  ·
                    rfl

theorem cell21_520779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 4].length) (baseStart_520779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520779 prefixEnd_520779 := by exact prefixLift 520779
  have htrace : WordTrace (prefixWord ++ tailWord_520779) baseStart_520779 baseEnd_520779 := by
    simpa [prefixWord, tailWord_520779, baseEnd_520779] using wordTrace_append hprefix tailTrace_520779
  have hstable : (prefixWord ++ tailWord_520779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520779).length < 2 ^ (prefixWord ++ tailWord_520779).sum := by decide
  have hdescent : baseEnd_520779 < baseStart_520779 := by decide
  rcases family_descends (prefixWord ++ tailWord_520779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520813 : List Nat := [1, 5, 1, 1, 3, 3, 1, 2, 4]
def baseStart_520813 : Nat := 118140960795 + 520813 * 2 ^ 59
def prefixEnd_520813 : Nat := 4983230072969 + 3 ^ 40 * 520813 * 2
def baseEnd_520813 : Nat := 118856622271189355752147

theorem tailTrace_520813 : CollatzResearch.WordTrace tailWord_520813 prefixEnd_520813 118856622271189355752147 := by
  unfold tailWord_520813
  simp only [CollatzResearch.WordTrace]
  refine ⟨18995610662190923624015093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12663740441460615749343395 18995610662190923624015093)
  ·
    refine ⟨1780838499580399089751415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18995610662190923624015093 1780838499580399089751415)
    ·
      refine ⟨2671257749370598634627123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1780838499580399089751415 2671257749370598634627123)
      ·
        refine ⟨4006886624055897951940685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671257749370598634627123 4006886624055897951940685)
        ·
          refine ⟨1502582484020961731977757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4006886624055897951940685 1502582484020961731977757)
          ·
            refine ⟨563468431507860649491659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1502582484020961731977757 563468431507860649491659)
            ·
              refine ⟨845202647261790974237489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563468431507860649491659 845202647261790974237489)
              ·
                refine ⟨633901985446343230678117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845202647261790974237489 633901985446343230678117)
                ·
                  refine ⟨118856622271189355752147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 633901985446343230678117 118856622271189355752147)
                  ·
                    rfl

theorem cell21_520813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_520813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520813 prefixEnd_520813 := by exact prefixLift 520813
  have htrace : WordTrace (prefixWord ++ tailWord_520813) baseStart_520813 baseEnd_520813 := by
    simpa [prefixWord, tailWord_520813, baseEnd_520813] using wordTrace_append hprefix tailTrace_520813
  have hstable : (prefixWord ++ tailWord_520813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520813).length < 2 ^ (prefixWord ++ tailWord_520813).sum := by decide
  have hdescent : baseEnd_520813 < baseStart_520813 := by decide
  rcases family_descends (prefixWord ++ tailWord_520813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520993 : List Nat := [1, 2, 3, 2, 1, 2, 1, 6, 3]
def baseStart_520993 : Nat := 118140960795 + 520993 * 2 ^ 59
def prefixEnd_520993 : Nat := 4983230072969 + 3 ^ 40 * 520993 * 2
def baseEnd_520993 : Nat := 118897700723549042751779

theorem tailTrace_520993 : CollatzResearch.WordTrace tailWord_520993 prefixEnd_520993 118897700723549042751779 := by
  unfold tailWord_520993
  simp only [CollatzResearch.WordTrace]
  refine ⟨19002175801538814365567633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12668117201025876243711755 19002175801538814365567633)
  ·
    refine ⟨14251631851154110774175725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19002175801538814365567633 14251631851154110774175725)
    ·
      refine ⟨5344361944182791540315897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14251631851154110774175725 5344361944182791540315897)
      ·
        refine ⟨4008271458137093655236923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5344361944182791540315897 4008271458137093655236923)
        ·
          refine ⟨6012407187205640482855385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008271458137093655236923 6012407187205640482855385)
          ·
            refine ⟨4509305390404230362141539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6012407187205640482855385 4509305390404230362141539)
            ·
              refine ⟨6763958085606345543212309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509305390404230362141539 6763958085606345543212309)
              ·
                refine ⟨317060535262797447338077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6763958085606345543212309 317060535262797447338077)
                ·
                  refine ⟨118897700723549042751779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317060535262797447338077 118897700723549042751779)
                  ·
                    rfl

theorem cell21_520993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 3].length) (baseStart_520993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_520993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_520993 prefixEnd_520993 := by exact prefixLift 520993
  have htrace : WordTrace (prefixWord ++ tailWord_520993) baseStart_520993 baseEnd_520993 := by
    simpa [prefixWord, tailWord_520993, baseEnd_520993] using wordTrace_append hprefix tailTrace_520993
  have hstable : (prefixWord ++ tailWord_520993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520993).length < 2 ^ (prefixWord ++ tailWord_520993).sum := by decide
  have hdescent : baseEnd_520993 < baseStart_520993 := by decide
  rcases family_descends (prefixWord ++ tailWord_520993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521058 : List Nat := [3, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_521058 : Nat := 118140960795 + 521058 * 2 ^ 59
def prefixEnd_521058 : Nat := 4983230072969 + 3 ^ 40 * 521058 * 2
def baseEnd_521058 : Nat := 118912534609123374168313

theorem tailTrace_521058 : CollatzResearch.WordTrace tailWord_521058 prefixEnd_521058 118912534609123374168313 := by
  unfold tailWord_521058
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751136636575832616670957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12669697697535553644455885 4751136636575832616670957)
  ·
    refine ⟨1781676238715937231251609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4751136636575832616670957 1781676238715937231251609)
    ·
      refine ⟨1336257179036952923438707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1781676238715937231251609 1336257179036952923438707)
      ·
        refine ⟨2004385768555429385158061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1336257179036952923438707 2004385768555429385158061)
        ·
          refine ⟨751644663208286019434273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2004385768555429385158061 751644663208286019434273)
          ·
            refine ⟨563733497406214514575705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751644663208286019434273 563733497406214514575705)
            ·
              refine ⟨422800123054660885931779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563733497406214514575705 422800123054660885931779)
              ·
                refine ⟨634200184581991328897669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422800123054660885931779 634200184581991328897669)
                ·
                  refine ⟨118912534609123374168313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634200184581991328897669 118912534609123374168313)
                  ·
                    rfl

theorem cell21_521058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_521058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521058 prefixEnd_521058 := by exact prefixLift 521058
  have htrace : WordTrace (prefixWord ++ tailWord_521058) baseStart_521058 baseEnd_521058 := by
    simpa [prefixWord, tailWord_521058, baseEnd_521058] using wordTrace_append hprefix tailTrace_521058
  have hstable : (prefixWord ++ tailWord_521058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521058).length < 2 ^ (prefixWord ++ tailWord_521058).sum := by decide
  have hdescent : baseEnd_521058 < baseStart_521058 := by decide
  rcases family_descends (prefixWord ++ tailWord_521058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521145 : List Nat := [1, 2, 1, 4, 2, 2, 1, 5, 3]
def baseStart_521145 : Nat := 118140960795 + 521145 * 2 ^ 59
def prefixEnd_521145 : Nat := 4983230072969 + 3 ^ 40 * 521145 * 2
def baseEnd_521145 : Nat := 118932389194430556218135

theorem tailTrace_521145 : CollatzResearch.WordTrace tailWord_521145 prefixEnd_521145 118932389194430556218135 := by
  unfold tailWord_521145
  simp only [CollatzResearch.WordTrace]
  refine ⟨19007719696988144325100889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12671813131325429550067259 19007719696988144325100889)
  ·
    refine ⟨14255789772741108243825667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19007719696988144325100889 14255789772741108243825667)
    ·
      refine ⟨21383684659111662365738501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14255789772741108243825667 21383684659111662365738501)
      ·
        refine ⟨4009440873583436693575969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21383684659111662365738501 4009440873583436693575969)
        ·
          refine ⟨3007080655187577520181977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4009440873583436693575969 3007080655187577520181977)
          ·
            refine ⟨2255310491390683140136483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3007080655187577520181977 2255310491390683140136483)
            ·
              refine ⟨3382965737086024710204725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255310491390683140136483 3382965737086024710204725)
              ·
                refine ⟨317153037851814816581693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3382965737086024710204725 317153037851814816581693)
                ·
                  refine ⟨118932389194430556218135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317153037851814816581693 118932389194430556218135)
                  ·
                    rfl

theorem cell21_521145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 3].length) (baseStart_521145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521145 prefixEnd_521145 := by exact prefixLift 521145
  have htrace : WordTrace (prefixWord ++ tailWord_521145) baseStart_521145 baseEnd_521145 := by
    simpa [prefixWord, tailWord_521145, baseEnd_521145] using wordTrace_append hprefix tailTrace_521145
  have hstable : (prefixWord ++ tailWord_521145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521145).length < 2 ^ (prefixWord ++ tailWord_521145).sum := by decide
  have hdescent : baseEnd_521145 < baseStart_521145 := by decide
  rcases family_descends (prefixWord ++ tailWord_521145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521159 : List Nat := [1, 1, 4, 1, 1, 2, 5, 2, 4]
def baseStart_521159 : Nat := 118140960795 + 521159 * 2 ^ 59
def prefixEnd_521159 : Nat := 4983230072969 + 3 ^ 40 * 521159 * 2
def baseEnd_521159 : Nat := 118935584185169642984773

theorem tailTrace_521159 : CollatzResearch.WordTrace tailWord_521159 prefixEnd_521159 118935584185169642984773 := by
  unfold tailWord_521159
  simp only [CollatzResearch.WordTrace]
  refine ⟨19008230318937424716110531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12672153545958283144073687 19008230318937424716110531)
  ·
    refine ⟨28512345478406137074165797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19008230318937424716110531 28512345478406137074165797)
    ·
      refine ⟨5346064777201150701406087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28512345478406137074165797 5346064777201150701406087)
      ·
        refine ⟨8019097165801726052109131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5346064777201150701406087 8019097165801726052109131)
        ·
          refine ⟨12028645748702589078163697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8019097165801726052109131 12028645748702589078163697)
          ·
            refine ⟨9021484311526941808622773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12028645748702589078163697 9021484311526941808622773)
            ·
              refine ⟨845764154205650794558385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9021484311526941808622773 845764154205650794558385)
              ·
                refine ⟨634323115654238095918789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845764154205650794558385 634323115654238095918789)
                ·
                  refine ⟨118935584185169642984773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634323115654238095918789 118935584185169642984773)
                  ·
                    rfl

theorem cell21_521159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 4].length) (baseStart_521159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521159 prefixEnd_521159 := by exact prefixLift 521159
  have htrace : WordTrace (prefixWord ++ tailWord_521159) baseStart_521159 baseEnd_521159 := by
    simpa [prefixWord, tailWord_521159, baseEnd_521159] using wordTrace_append hprefix tailTrace_521159
  have hstable : (prefixWord ++ tailWord_521159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521159).length < 2 ^ (prefixWord ++ tailWord_521159).sum := by decide
  have hdescent : baseEnd_521159 < baseStart_521159 := by decide
  rcases family_descends (prefixWord ++ tailWord_521159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521176 : List Nat := [2, 1, 2, 2, 2, 4, 3, 1, 4]
def baseStart_521176 : Nat := 118140960795 + 521176 * 2 ^ 59
def prefixEnd_521176 : Nat := 4983230072969 + 3 ^ 40 * 521176 * 2
def baseEnd_521176 : Nat := 118939463816781391201405

theorem tailTrace_521176 : CollatzResearch.WordTrace tailWord_521176 prefixEnd_521176 118939463816781391201405 := by
  unfold tailWord_521176
  simp only [CollatzResearch.WordTrace]
  refine ⟨9504425179937918309739691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12672566906583891079652921 9504425179937918309739691)
  ·
    refine ⟨14256637769906877464609537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9504425179937918309739691 14256637769906877464609537)
    ·
      refine ⟨10692478327430158098457153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14256637769906877464609537 10692478327430158098457153)
      ·
        refine ⟨8019358745572618573842865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10692478327430158098457153 8019358745572618573842865)
        ·
          refine ⟨6014519059179463930382149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8019358745572618573842865 6014519059179463930382149)
          ·
            refine ⟨1127722323596149486946653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6014519059179463930382149 1127722323596149486946653)
            ·
              refine ⟨422895871348556057604995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1127722323596149486946653 422895871348556057604995)
              ·
                refine ⟨634343807022834086407493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422895871348556057604995 634343807022834086407493)
                ·
                  refine ⟨118939463816781391201405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634343807022834086407493 118939463816781391201405)
                  ·
                    rfl

theorem cell21_521176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_521176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521176 prefixEnd_521176 := by exact prefixLift 521176
  have htrace : WordTrace (prefixWord ++ tailWord_521176) baseStart_521176 baseEnd_521176 := by
    simpa [prefixWord, tailWord_521176, baseEnd_521176] using wordTrace_append hprefix tailTrace_521176
  have hstable : (prefixWord ++ tailWord_521176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521176).length < 2 ^ (prefixWord ++ tailWord_521176).sum := by decide
  have hdescent : baseEnd_521176 < baseStart_521176 := by decide
  rcases family_descends (prefixWord ++ tailWord_521176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521249 : List Nat := [1, 2, 3, 2, 3, 1, 2, 7]
def baseStart_521249 : Nat := 118140960795 + 521249 * 2 ^ 59
def prefixEnd_521249 : Nat := 4983230072969 + 3 ^ 40 * 521249 * 2
def baseEnd_521249 : Nat := 39652041137116495494863

theorem tailTrace_521249 : CollatzResearch.WordTrace tailWord_521249 prefixEnd_521249 39652041137116495494863 := by
  unfold tailWord_521249
  simp only [CollatzResearch.WordTrace]
  refine ⟨19011512888611370086886801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12674341925740913391257867 19011512888611370086886801)
  ·
    refine ⟨14258634666458527565165101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19011512888611370086886801 14258634666458527565165101)
    ·
      refine ⟨5346987999921947836936913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14258634666458527565165101 5346987999921947836936913)
      ·
        refine ⟨4010240999941460877702685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5346987999921947836936913 4010240999941460877702685)
        ·
          refine ⟨1503840374978047829138507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4010240999941460877702685 1503840374978047829138507)
          ·
            refine ⟨2255760562467071743707761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503840374978047829138507 2255760562467071743707761)
            ·
              refine ⟨1691820421850303807780821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255760562467071743707761 1691820421850303807780821)
              ·
                refine ⟨39652041137116495494863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1691820421850303807780821 39652041137116495494863)
                ·
                  rfl

theorem cell21_521249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 7].length) (baseStart_521249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521249 prefixEnd_521249 := by exact prefixLift 521249
  have htrace : WordTrace (prefixWord ++ tailWord_521249) baseStart_521249 baseEnd_521249 := by
    simpa [prefixWord, tailWord_521249, baseEnd_521249] using wordTrace_append hprefix tailTrace_521249
  have hstable : (prefixWord ++ tailWord_521249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521249).length < 2 ^ (prefixWord ++ tailWord_521249).sum := by decide
  have hdescent : baseEnd_521249 < baseStart_521249 := by decide
  rcases family_descends (prefixWord ++ tailWord_521249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521314 : List Nat := [3, 3, 2, 2, 1, 1, 1, 5, 3]
def baseStart_521314 : Nat := 118140960795 + 521314 * 2 ^ 59
def prefixEnd_521314 : Nat := 4983230072969 + 3 ^ 40 * 521314 * 2
def baseEnd_521314 : Nat := 118970957296923817901123

theorem tailTrace_521314 : CollatzResearch.WordTrace tailWord_521314 prefixEnd_521314 118970957296923817901123 := by
  unfold tailWord_521314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4753470908343971547000749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12675922422250590792001997 4753470908343971547000749)
  ·
    refine ⟨1782551590628989330125281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4753470908343971547000749 1782551590628989330125281)
    ·
      refine ⟨1336913692971741997593961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1782551590628989330125281 1336913692971741997593961)
      ·
        refine ⟨1002685269728806498195471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1336913692971741997593961 1002685269728806498195471)
        ·
          refine ⟨1504027904593209747293207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002685269728806498195471 1504027904593209747293207)
          ·
            refine ⟨2256041856889814620939811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504027904593209747293207 2256041856889814620939811)
            ·
              refine ⟨3384062785334721931409717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256041856889814620939811 3384062785334721931409717)
              ·
                refine ⟨317255886125130181069661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3384062785334721931409717 317255886125130181069661)
                ·
                  refine ⟨118970957296923817901123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317255886125130181069661 118970957296923817901123)
                  ·
                    rfl

theorem cell21_521314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_521314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521314 prefixEnd_521314 := by exact prefixLift 521314
  have htrace : WordTrace (prefixWord ++ tailWord_521314) baseStart_521314 baseEnd_521314 := by
    simpa [prefixWord, tailWord_521314, baseEnd_521314] using wordTrace_append hprefix tailTrace_521314
  have hstable : (prefixWord ++ tailWord_521314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521314).length < 2 ^ (prefixWord ++ tailWord_521314).sum := by decide
  have hdescent : baseEnd_521314 < baseStart_521314 := by decide
  rcases family_descends (prefixWord ++ tailWord_521314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521325 : List Nat := [1, 5, 1, 1, 2, 3, 8]
def baseStart_521325 : Nat := 118140960795 + 521325 * 2 ^ 59
def prefixEnd_521325 : Nat := 4983230072969 + 3 ^ 40 * 521325 * 2
def baseEnd_521325 : Nat := 13219274182976693690863

theorem tailTrace_521325 : CollatzResearch.WordTrace tailWord_521325 prefixEnd_521325 13219274182976693690863 := by
  unfold tailWord_521325
  simp only [CollatzResearch.WordTrace]
  refine ⟨19014284836336035066653429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12676189890890690044435619 19014284836336035066653429)
  ·
    refine ⟨1782589203406503287498759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19014284836336035066653429 1782589203406503287498759)
    ·
      refine ⟨2673883805109754931248139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782589203406503287498759 2673883805109754931248139)
      ·
        refine ⟨4010825707664632396872209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673883805109754931248139 4010825707664632396872209)
        ·
          refine ⟨3008119280748474297654157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4010825707664632396872209 3008119280748474297654157)
          ·
            refine ⟨1128044730280677861620309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3008119280748474297654157 1128044730280677861620309)
            ·
              refine ⟨13219274182976693690863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1128044730280677861620309 13219274182976693690863)
              ·
                rfl

theorem cell21_521325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 8].length) (baseStart_521325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521325 prefixEnd_521325 := by exact prefixLift 521325
  have htrace : WordTrace (prefixWord ++ tailWord_521325) baseStart_521325 baseEnd_521325 := by
    simpa [prefixWord, tailWord_521325, baseEnd_521325] using wordTrace_append hprefix tailTrace_521325
  have hstable : (prefixWord ++ tailWord_521325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521325).length < 2 ^ (prefixWord ++ tailWord_521325).sum := by decide
  have hdescent : baseEnd_521325 < baseStart_521325 := by decide
  rcases family_descends (prefixWord ++ tailWord_521325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521401 : List Nat := [1, 2, 1, 4, 1, 4, 2, 6]
def baseStart_521401 : Nat := 118140960795 + 521401 * 2 ^ 59
def prefixEnd_521401 : Nat := 4983230072969 + 3 ^ 40 * 521401 * 2
def baseEnd_521401 : Nat := 39663603960743666650315

theorem tailTrace_521401 : CollatzResearch.WordTrace tailWord_521401 prefixEnd_521401 39663603960743666650315 := by
  unfold tailWord_521401
  simp only [CollatzResearch.WordTrace]
  refine ⟨19017056784060700046420057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12678037856040466697613371 19017056784060700046420057)
  ·
    refine ⟨14262792588045525034815043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19017056784060700046420057 14262792588045525034815043)
    ·
      refine ⟨21394188882068287552222565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14262792588045525034815043 21394188882068287552222565)
      ·
        refine ⟨4011410415387803916041731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21394188882068287552222565 4011410415387803916041731)
        ·
          refine ⟨6017115623081705874062597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4011410415387803916041731 6017115623081705874062597)
          ·
            refine ⟨1128209179327819851386737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6017115623081705874062597 1128209179327819851386737)
            ·
              refine ⟨846156884495864888540053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128209179327819851386737 846156884495864888540053)
              ·
                refine ⟨39663603960743666650315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 846156884495864888540053 39663603960743666650315)
                ·
                  rfl

theorem cell21_521401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 6].length) (baseStart_521401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521401 prefixEnd_521401 := by exact prefixLift 521401
  have htrace : WordTrace (prefixWord ++ tailWord_521401) baseStart_521401 baseEnd_521401 := by
    simpa [prefixWord, tailWord_521401, baseEnd_521401] using wordTrace_append hprefix tailTrace_521401
  have hstable : (prefixWord ++ tailWord_521401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521401).length < 2 ^ (prefixWord ++ tailWord_521401).sum := by decide
  have hdescent : baseEnd_521401 < baseStart_521401 := by decide
  rcases family_descends (prefixWord ++ tailWord_521401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521404 : List Nat := [2, 2, 2, 3, 2, 1, 4, 1, 4]
def baseStart_521404 : Nat := 118140960795 + 521404 * 2 ^ 59
def prefixEnd_521404 : Nat := 4983230072969 + 3 ^ 40 * 521404 * 2
def baseEnd_521404 : Nat := 118991496523103661400939

theorem tailTrace_521404 : CollatzResearch.WordTrace tailWord_521404 prefixEnd_521404 118991496523103661400939 := by
  unfold tailWord_521404
  simp only [CollatzResearch.WordTrace]
  refine ⟨9508583101524915779389633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12678110802033221039186177 9508583101524915779389633)
  ·
    refine ⟨7131437326143686834542225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9508583101524915779389633 7131437326143686834542225)
    ·
      refine ⟨5348577994607765125906669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7131437326143686834542225 5348577994607765125906669)
      ·
        refine ⟨2005716747977911922215001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5348577994607765125906669 2005716747977911922215001)
        ·
          refine ⟨1504287560983433941661251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2005716747977911922215001 1504287560983433941661251)
          ·
            refine ⟨2256431341475150912491877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504287560983433941661251 2256431341475150912491877)
            ·
              refine ⟨423080876526590796092227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2256431341475150912491877 423080876526590796092227)
              ·
                refine ⟨634621314789886194138341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423080876526590796092227 634621314789886194138341)
                ·
                  refine ⟨118991496523103661400939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634621314789886194138341 118991496523103661400939)
                  ·
                    rfl

theorem cell21_521404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_521404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521404 prefixEnd_521404 := by exact prefixLift 521404
  have htrace : WordTrace (prefixWord ++ tailWord_521404) baseStart_521404 baseEnd_521404 := by
    simpa [prefixWord, tailWord_521404, baseEnd_521404] using wordTrace_append hprefix tailTrace_521404
  have hstable : (prefixWord ++ tailWord_521404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521404).length < 2 ^ (prefixWord ++ tailWord_521404).sum := by decide
  have hdescent : baseEnd_521404 < baseStart_521404 := by decide
  rcases family_descends (prefixWord ++ tailWord_521404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521415 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 5]
def baseStart_521415 : Nat := 118140960795 + 521415 * 2 ^ 59
def prefixEnd_521415 : Nat := 4983230072969 + 3 ^ 40 * 521415 * 2
def baseEnd_521415 : Nat := 118994006872970086717583

theorem tailTrace_521415 : CollatzResearch.WordTrace tailWord_521415 prefixEnd_521415 118994006872970086717583 := by
  unfold tailWord_521415
  simp only [CollatzResearch.WordTrace]
  refine ⟨19017567406009980437429699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12678378270673320291619799 19017567406009980437429699)
  ·
    refine ⟨28526351109014970656144549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19017567406009980437429699 28526351109014970656144549)
    ·
      refine ⟨5348690832940306998027103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28526351109014970656144549 5348690832940306998027103)
      ·
        refine ⟨8023036249410460497040655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5348690832940306998027103 8023036249410460497040655)
        ·
          refine ⟨12034554374115690745560983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8023036249410460497040655 12034554374115690745560983)
          ·
            refine ⟨18051831561173536118341475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12034554374115690745560983 18051831561173536118341475)
            ·
              refine ⟨27077747341760304177512213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18051831561173536118341475 27077747341760304177512213)
              ·
                refine ⟨1269269406645014258320885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27077747341760304177512213 1269269406645014258320885)
                ·
                  refine ⟨118994006872970086717583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1269269406645014258320885 118994006872970086717583)
                  ·
                    rfl

theorem cell21_521415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_521415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521415 prefixEnd_521415 := by exact prefixLift 521415
  have htrace : WordTrace (prefixWord ++ tailWord_521415) baseStart_521415 baseEnd_521415 := by
    simpa [prefixWord, tailWord_521415, baseEnd_521415] using wordTrace_append hprefix tailTrace_521415
  have hstable : (prefixWord ++ tailWord_521415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521415).length < 2 ^ (prefixWord ++ tailWord_521415).sum := by decide
  have hdescent : baseEnd_521415 < baseStart_521415 := by decide
  rcases family_descends (prefixWord ++ tailWord_521415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521477 : List Nat := [1, 3, 1, 1, 2, 1, 7, 5]
def baseStart_521477 : Nat := 118140960795 + 521477 * 2 ^ 59
def prefixEnd_521477 : Nat := 4983230072969 + 3 ^ 40 * 521477 * 2
def baseEnd_521477 : Nat := 39669385372557252228041

theorem tailTrace_521477 : CollatzResearch.WordTrace tailWord_521477 prefixEnd_521477 39669385372557252228041 := by
  unfold tailWord_521477
  simp only [CollatzResearch.WordTrace]
  refine ⟨19019828731785365026186685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12679885821190243350791123 19019828731785365026186685)
  ·
    refine ⟨7132435774419511884820007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19019828731785365026186685 7132435774419511884820007)
    ·
      refine ⟨10698653661629267827230011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7132435774419511884820007 10698653661629267827230011)
      ·
        refine ⟨16047980492443901740845017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10698653661629267827230011 16047980492443901740845017)
        ·
          refine ⟨12035985369332926305633763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16047980492443901740845017 12035985369332926305633763)
          ·
            refine ⟨18053978053999389458450645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12035985369332926305633763 18053978053999389458450645)
            ·
              refine ⟨423140110640610690432437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18053978053999389458450645 423140110640610690432437)
              ·
                refine ⟨39669385372557252228041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 423140110640610690432437 39669385372557252228041)
                ·
                  rfl

theorem cell21_521477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 5].length) (baseStart_521477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521477 prefixEnd_521477 := by exact prefixLift 521477
  have htrace : WordTrace (prefixWord ++ tailWord_521477) baseStart_521477 baseEnd_521477 := by
    simpa [prefixWord, tailWord_521477, baseEnd_521477] using wordTrace_append hprefix tailTrace_521477
  have hstable : (prefixWord ++ tailWord_521477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521477).length < 2 ^ (prefixWord ++ tailWord_521477).sum := by decide
  have hdescent : baseEnd_521477 < baseStart_521477 := by decide
  rcases family_descends (prefixWord ++ tailWord_521477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521508 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 5]
def baseStart_521508 : Nat := 118140960795 + 521508 * 2 ^ 59
def prefixEnd_521508 : Nat := 4983230072969 + 3 ^ 40 * 521508 * 2
def baseEnd_521508 : Nat := 119015230740022591667393

theorem tailTrace_521508 : CollatzResearch.WordTrace tailWord_521508 prefixEnd_521508 119015230740022591667393 := by
  unfold tailWord_521508
  simp only [CollatzResearch.WordTrace]
  refine ⟨9510479697336528660282589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12680639596448704880376785 9510479697336528660282589)
  ·
    refine ⟨3566429886501198247605971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9510479697336528660282589 3566429886501198247605971)
    ·
      refine ⟨5349644829751797371408957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3566429886501198247605971 5349644829751797371408957)
      ·
        refine ⟨2006116811156924014278359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5349644829751797371408957 2006116811156924014278359)
        ·
          refine ⟨3009175216735386021417539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2006116811156924014278359 3009175216735386021417539)
          ·
            refine ⟨4513762825103079032126309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009175216735386021417539 4513762825103079032126309)
            ·
              refine ⟨846330529706827318523683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4513762825103079032126309 846330529706827318523683)
              ·
                refine ⟨1269495794560240977785525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846330529706827318523683 1269495794560240977785525)
                ·
                  refine ⟨119015230740022591667393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1269495794560240977785525 119015230740022591667393)
                  ·
                    rfl

theorem cell21_521508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_521508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521508 prefixEnd_521508 := by exact prefixLift 521508
  have htrace : WordTrace (prefixWord ++ tailWord_521508) baseStart_521508 baseEnd_521508 := by
    simpa [prefixWord, tailWord_521508, baseEnd_521508] using wordTrace_append hprefix tailTrace_521508
  have hstable : (prefixWord ++ tailWord_521508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521508).length < 2 ^ (prefixWord ++ tailWord_521508).sum := by decide
  have hdescent : baseEnd_521508 < baseStart_521508 := by decide
  rcases family_descends (prefixWord ++ tailWord_521508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521536 : List Nat := [2, 1, 1, 2, 2, 1, 5, 7]
def baseStart_521536 : Nat := 118140960795 + 521536 * 2 ^ 59
def prefixEnd_521536 : Nat := 4983230072969 + 3 ^ 40 * 521536 * 2
def baseEnd_521536 : Nat := 39673873573833588400223

theorem tailTrace_521536 : CollatzResearch.WordTrace tailWord_521536 prefixEnd_521536 39673873573833588400223 := by
  unfold tailWord_521536
  simp only [CollatzResearch.WordTrace]
  refine ⟨9510990319285809051292231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12681320425714412068389641 9510990319285809051292231)
  ·
    refine ⟨14266485478928713576938347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9510990319285809051292231 14266485478928713576938347)
    ·
      refine ⟨21399728218393070365407521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14266485478928713576938347 21399728218393070365407521)
      ·
        refine ⟨16049796163794802774055641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21399728218393070365407521 16049796163794802774055641)
        ·
          refine ⟨12037347122846102080541731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16049796163794802774055641 12037347122846102080541731)
          ·
            refine ⟨18056020684269153120812597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12037347122846102080541731 18056020684269153120812597)
            ·
              refine ⟨1692751939150233105076181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18056020684269153120812597 1692751939150233105076181)
              ·
                refine ⟨39673873573833588400223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1692751939150233105076181 39673873573833588400223)
                ·
                  rfl

theorem cell21_521536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_521536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521536 prefixEnd_521536 := by exact prefixLift 521536
  have htrace : WordTrace (prefixWord ++ tailWord_521536) baseStart_521536 baseEnd_521536 := by
    simpa [prefixWord, tailWord_521536, baseEnd_521536] using wordTrace_append hprefix tailTrace_521536
  have hstable : (prefixWord ++ tailWord_521536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521536).length < 2 ^ (prefixWord ++ tailWord_521536).sum := by decide
  have hdescent : baseEnd_521536 < baseStart_521536 := by decide
  rcases family_descends (prefixWord ++ tailWord_521536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521629 : List Nat := [1, 4, 2, 1, 3, 1, 3, 6]
def baseStart_521629 : Nat := 118140960795 + 521629 * 2 ^ 59
def prefixEnd_521629 : Nat := 4983230072969 + 3 ^ 40 * 521629 * 2
def baseEnd_521629 : Nat := 39680948196184423383493

theorem tailTrace_521629 : CollatzResearch.WordTrace tailWord_521629 prefixEnd_521629 39680948196184423383493 := by
  unfold tailWord_521629
  simp only [CollatzResearch.WordTrace]
  refine ⟨19025372627234694985719941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12683581751489796657146627 19025372627234694985719941)
  ·
    refine ⟨3567257367606505309822489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19025372627234694985719941 3567257367606505309822489)
    ·
      refine ⟨2675443025704878982366867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3567257367606505309822489 2675443025704878982366867)
      ·
        refine ⟨4013164538557318473550301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2675443025704878982366867 4013164538557318473550301)
        ·
          refine ⟨1504936701958994427581363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4013164538557318473550301 1504936701958994427581363)
          ·
            refine ⟨2257405052938491641372045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504936701958994427581363 2257405052938491641372045)
            ·
              refine ⟨846526894851934365514517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2257405052938491641372045 846526894851934365514517)
              ·
                refine ⟨39680948196184423383493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 846526894851934365514517 39680948196184423383493)
                ·
                  rfl

theorem cell21_521629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 6].length) (baseStart_521629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521629 prefixEnd_521629 := by exact prefixLift 521629
  have htrace : WordTrace (prefixWord ++ tailWord_521629) baseStart_521629 baseEnd_521629 := by
    simpa [prefixWord, tailWord_521629, baseEnd_521629] using wordTrace_append hprefix tailTrace_521629
  have hstable : (prefixWord ++ tailWord_521629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521629).length < 2 ^ (prefixWord ++ tailWord_521629).sum := by decide
  have hdescent : baseEnd_521629 < baseStart_521629 := by decide
  rcases family_descends (prefixWord ++ tailWord_521629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521666 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 6]
def baseStart_521666 : Nat := 118140960795 + 521666 * 2 ^ 59
def prefixEnd_521666 : Nat := 4983230072969 + 3 ^ 40 * 521666 * 2
def baseEnd_521666 : Nat := 119051288492649428033737

theorem tailTrace_521666 : CollatzResearch.WordTrace tailWord_521666 prefixEnd_521666 119051288492649428033737 := by
  unfold tailWord_521666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4756680532025162576204213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12684481418733766869877901 4756680532025162576204213)
  ·
    refine ⟨445938799877358991519145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4756680532025162576204213 445938799877358991519145)
    ·
      refine ⟨334454099908019243639359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445938799877358991519145 334454099908019243639359)
      ·
        refine ⟨501681149862028865459039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334454099908019243639359 501681149862028865459039)
        ·
          refine ⟨752521724793043298188559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501681149862028865459039 752521724793043298188559)
          ·
            refine ⟨1128782587189564947282839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752521724793043298188559 1128782587189564947282839)
            ·
              refine ⟨1693173880784347420924259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128782587189564947282839 1693173880784347420924259)
              ·
                refine ⟨2539760821176521131386389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693173880784347420924259 2539760821176521131386389)
                ·
                  refine ⟨119051288492649428033737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2539760821176521131386389 119051288492649428033737)
                  ·
                    rfl

theorem cell21_521666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_521666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521666 prefixEnd_521666 := by exact prefixLift 521666
  have htrace : WordTrace (prefixWord ++ tailWord_521666) baseStart_521666 baseEnd_521666 := by
    simpa [prefixWord, tailWord_521666, baseEnd_521666] using wordTrace_append hprefix tailTrace_521666
  have hstable : (prefixWord ++ tailWord_521666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521666).length < 2 ^ (prefixWord ++ tailWord_521666).sum := by decide
  have hdescent : baseEnd_521666 < baseStart_521666 := by decide
  rcases family_descends (prefixWord ++ tailWord_521666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521674 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_521674 : Nat := 118140960795 + 521674 * 2 ^ 59
def prefixEnd_521674 : Nat := 4983230072969 + 3 ^ 40 * 521674 * 2
def baseEnd_521674 : Nat := 119053114201643191900387

theorem tailTrace_521674 : CollatzResearch.WordTrace tailWord_521674 prefixEnd_521674 119053114201643191900387 := by
  unfold tailWord_521674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4756753478017916917777019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12684675941381111780738717 4756753478017916917777019)
  ·
    refine ⟨7135130217026875376665529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4756753478017916917777019 7135130217026875376665529)
    ·
      refine ⟨5351347662770156532499147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7135130217026875376665529 5351347662770156532499147)
      ·
        refine ⟨8027021494155234798748721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351347662770156532499147 8027021494155234798748721)
        ·
          refine ⟨6020266120616426099061541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8027021494155234798748721 6020266120616426099061541)
          ·
            refine ⟨1128799897615579893574039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6020266120616426099061541 1128799897615579893574039)
            ·
              refine ⟨1693199846423369840361059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128799897615579893574039 1693199846423369840361059)
              ·
                refine ⟨2539799769635054760541589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693199846423369840361059 2539799769635054760541589)
                ·
                  refine ⟨119053114201643191900387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2539799769635054760541589 119053114201643191900387)
                  ·
                    rfl

theorem cell21_521674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_521674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521674 prefixEnd_521674 := by exact prefixLift 521674
  have htrace : WordTrace (prefixWord ++ tailWord_521674) baseStart_521674 baseEnd_521674 := by
    simpa [prefixWord, tailWord_521674, baseEnd_521674] using wordTrace_append hprefix tailTrace_521674
  have hstable : (prefixWord ++ tailWord_521674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521674).length < 2 ^ (prefixWord ++ tailWord_521674).sum := by decide
  have hdescent : baseEnd_521674 < baseStart_521674 := by decide
  rcases family_descends (prefixWord ++ tailWord_521674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521736 : List Nat := [2, 1, 3, 2, 1, 1, 2, 6, 3]
def baseStart_521736 : Nat := 118140960795 + 521736 * 2 ^ 59
def prefixEnd_521736 : Nat := 4983230072969 + 3 ^ 40 * 521736 * 2
def baseEnd_521736 : Nat := 119067263446344861866927

theorem tailTrace_521736 : CollatzResearch.WordTrace tailWord_521736 prefixEnd_521736 119067263446344861866927 := by
  unfold tailWord_521736
  simp only [CollatzResearch.WordTrace]
  refine ⟨9514637618923526129932531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12686183491898034839910041 9514637618923526129932531)
  ·
    refine ⟨14271956428385289194898797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9514637618923526129932531 14271956428385289194898797)
    ·
      refine ⟨5351983660644483448087049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14271956428385289194898797 5351983660644483448087049)
      ·
        refine ⟨4013987745483362586065287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5351983660644483448087049 4013987745483362586065287)
        ·
          refine ⟨6020981618225043879097931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4013987745483362586065287 6020981618225043879097931)
          ·
            refine ⟨9031472427337565818646897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020981618225043879097931 9031472427337565818646897)
            ·
              refine ⟨6773604320503174363985173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9031472427337565818646897 6773604320503174363985173)
              ·
                refine ⟨317512702523586298311805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6773604320503174363985173 317512702523586298311805)
                ·
                  refine ⟨119067263446344861866927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317512702523586298311805 119067263446344861866927)
                  ·
                    rfl

theorem cell21_521736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 3].length) (baseStart_521736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521736 prefixEnd_521736 := by exact prefixLift 521736
  have htrace : WordTrace (prefixWord ++ tailWord_521736) baseStart_521736 baseEnd_521736 := by
    simpa [prefixWord, tailWord_521736, baseEnd_521736] using wordTrace_append hprefix tailTrace_521736
  have hstable : (prefixWord ++ tailWord_521736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521736).length < 2 ^ (prefixWord ++ tailWord_521736).sum := by decide
  have hdescent : baseEnd_521736 < baseStart_521736 := by decide
  rcases family_descends (prefixWord ++ tailWord_521736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521829 : List Nat := [1, 3, 1, 3, 3, 2, 2, 3, 3]
def baseStart_521829 : Nat := 118140960795 + 521829 * 2 ^ 59
def prefixEnd_521829 : Nat := 4983230072969 + 3 ^ 40 * 521829 * 2
def baseEnd_521829 : Nat := 119088487313397366816737

theorem tailTrace_521829 : CollatzResearch.WordTrace tailWord_521829 prefixEnd_521829 119088487313397366816737 := by
  unfold tailWord_521829
  simp only [CollatzResearch.WordTrace]
  refine ⟨19032667226510129143000541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12688444817673419428667027 19032667226510129143000541)
  ·
    refine ⟨7137250209941298428625203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19032667226510129143000541 7137250209941298428625203)
    ·
      refine ⟨10705875314911947642937805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7137250209941298428625203 10705875314911947642937805)
      ·
        refine ⟨4014703243091980366101677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10705875314911947642937805 4014703243091980366101677)
        ·
          refine ⟨1505513716159492637288129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4014703243091980366101677 1505513716159492637288129)
          ·
            refine ⟨1129135287119619477966097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1505513716159492637288129 1129135287119619477966097)
            ·
              refine ⟨846851465339714608474573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129135287119619477966097 846851465339714608474573)
              ·
                refine ⟨317569299502392978177965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 846851465339714608474573 317569299502392978177965)
                ·
                  refine ⟨119088487313397366816737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317569299502392978177965 119088487313397366816737)
                  ·
                    rfl

theorem cell21_521829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_521829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521829 prefixEnd_521829 := by exact prefixLift 521829
  have htrace : WordTrace (prefixWord ++ tailWord_521829) baseStart_521829 baseEnd_521829 := by
    simpa [prefixWord, tailWord_521829, baseEnd_521829] using wordTrace_append hprefix tailTrace_521829
  have hstable : (prefixWord ++ tailWord_521829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521829).length < 2 ^ (prefixWord ++ tailWord_521829).sum := by decide
  have hdescent : baseEnd_521829 < baseStart_521829 := by decide
  rcases family_descends (prefixWord ++ tailWord_521829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521840 : List Nat := [2, 1, 1, 1, 6, 2, 8]
def baseStart_521840 : Nat := 118140960795 + 521840 * 2 ^ 59
def prefixEnd_521840 : Nat := 4983230072969 + 3 ^ 40 * 521840 * 2
def baseEnd_521840 : Nat := 13232333073695976903709

theorem tailTrace_521840 : CollatzResearch.WordTrace tailWord_521840 prefixEnd_521840 13232333073695976903709 := by
  unfold tailWord_521840
  simp only [CollatzResearch.WordTrace]
  refine ⟨9516534214735139010825487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12688712286313518681100649 9516534214735139010825487)
  ·
    refine ⟨14274801322102708516238231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9516534214735139010825487 14274801322102708516238231)
    ·
      refine ⟨21412201983154062774357347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14274801322102708516238231 21412201983154062774357347)
      ·
        refine ⟨32118302974731094161536021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21412201983154062774357347 32118302974731094161536021)
        ·
          refine ⟨1505545451940520038822001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32118302974731094161536021 1505545451940520038822001)
          ·
            refine ⟨1129159088955390029116501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1505545451940520038822001 1129159088955390029116501)
            ·
              refine ⟨13232333073695976903709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1129159088955390029116501 13232333073695976903709)
              ·
                rfl

theorem cell21_521840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 8].length) (baseStart_521840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521840 prefixEnd_521840 := by exact prefixLift 521840
  have htrace : WordTrace (prefixWord ++ tailWord_521840) baseStart_521840 baseEnd_521840 := by
    simpa [prefixWord, tailWord_521840, baseEnd_521840] using wordTrace_append hprefix tailTrace_521840
  have hstable : (prefixWord ++ tailWord_521840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521840).length < 2 ^ (prefixWord ++ tailWord_521840).sum := by decide
  have hdescent : baseEnd_521840 < baseStart_521840 := by decide
  rcases family_descends (prefixWord ++ tailWord_521840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521860 : List Nat := [2, 3, 2, 1, 4, 1, 3, 1, 4]
def baseStart_521860 : Nat := 118140960795 + 521860 * 2 ^ 59
def prefixEnd_521860 : Nat := 4983230072969 + 3 ^ 40 * 521860 * 2
def baseEnd_521860 : Nat := 119095561935748201800007

theorem tailTrace_521860 : CollatzResearch.WordTrace tailWord_521860 prefixEnd_521860 119095561935748201800007 := by
  unfold tailWord_521860
  simp only [CollatzResearch.WordTrace]
  refine ⟨9516898944698910718689517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12689198592931880958252689 9516898944698910718689517)
  ·
    refine ⟨3568837104262091519508569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9516898944698910718689517 3568837104262091519508569)
    ·
      refine ⟨2676627828196568639631427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3568837104262091519508569 2676627828196568639631427)
      ·
        refine ⟨4014941742294852959447141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676627828196568639631427 4014941742294852959447141)
        ·
          refine ⟨752801576680284929896339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4014941742294852959447141 752801576680284929896339)
          ·
            refine ⟨1129202365020427394844509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752801576680284929896339 1129202365020427394844509)
            ·
              refine ⟨423450886882660273066691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1129202365020427394844509 423450886882660273066691)
              ·
                refine ⟨635176330323990409600037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423450886882660273066691 635176330323990409600037)
                ·
                  refine ⟨119095561935748201800007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635176330323990409600037 119095561935748201800007)
                  ·
                    rfl

theorem cell21_521860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_521860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521860 prefixEnd_521860 := by exact prefixLift 521860
  have htrace : WordTrace (prefixWord ++ tailWord_521860) baseStart_521860 baseEnd_521860 := by
    simpa [prefixWord, tailWord_521860, baseEnd_521860] using wordTrace_append hprefix tailTrace_521860
  have hstable : (prefixWord ++ tailWord_521860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521860).length < 2 ^ (prefixWord ++ tailWord_521860).sum := by decide
  have hdescent : baseEnd_521860 < baseStart_521860 := by decide
  rcases family_descends (prefixWord ++ tailWord_521860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521916 : List Nat := [2, 2, 2, 3, 1, 2, 1, 8]
def baseStart_521916 : Nat := 118140960795 + 521916 * 2 ^ 59
def prefixEnd_521916 : Nat := 4983230072969 + 3 ^ 40 * 521916 * 2
def baseEnd_521916 : Nat := 39702780632901516288853

theorem tailTrace_521916 : CollatzResearch.WordTrace tailWord_521916 prefixEnd_521916 39702780632901516288853 := by
  unfold tailWord_521916
  simp only [CollatzResearch.WordTrace]
  refine ⟨9517920188597471500708801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12690560251463295334278401 9517920188597471500708801)
  ·
    refine ⟨7138440141448103625531601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9517920188597471500708801 7138440141448103625531601)
    ·
      refine ⟨5353830106086077719148701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7138440141448103625531601 5353830106086077719148701)
      ·
        refine ⟨2007686289782279144680763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5353830106086077719148701 2007686289782279144680763)
        ·
          refine ⟨3011529434673418717021145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007686289782279144680763 3011529434673418717021145)
          ·
            refine ⟨2258647076005064037765859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3011529434673418717021145 2258647076005064037765859)
            ·
              refine ⟨3387970614007596056648789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2258647076005064037765859 3387970614007596056648789)
              ·
                refine ⟨39702780632901516288853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3387970614007596056648789 39702780632901516288853)
                ·
                  rfl

theorem cell21_521916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_521916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_521916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_521916 prefixEnd_521916 := by exact prefixLift 521916
  have htrace : WordTrace (prefixWord ++ tailWord_521916) baseStart_521916 baseEnd_521916 := by
    simpa [prefixWord, tailWord_521916, baseEnd_521916] using wordTrace_append hprefix tailTrace_521916
  have hstable : (prefixWord ++ tailWord_521916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521916).length < 2 ^ (prefixWord ++ tailWord_521916).sum := by decide
  have hdescent : baseEnd_521916 < baseStart_521916 := by decide
  rcases family_descends (prefixWord ++ tailWord_521916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522068 : List Nat := [2, 4, 1, 1, 3, 1, 9]
def baseStart_522068 : Nat := 118140960795 + 522068 * 2 ^ 59
def prefixEnd_522068 : Nat := 4983230072969 + 3 ^ 40 * 522068 * 2
def baseEnd_522068 : Nat := 13238114485509562481435

theorem tailTrace_522068 : CollatzResearch.WordTrace tailWord_522068 prefixEnd_522068 13238114485509562481435 := by
  unfold tailWord_522068
  simp only [CollatzResearch.WordTrace]
  refine ⟨9520692136322136480475429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12694256181762848640633905 9520692136322136480475429)
  ·
    refine ⟨1785129775560400590089143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9520692136322136480475429 1785129775560400590089143)
    ·
      refine ⟨2677694663340600885133715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785129775560400590089143 2677694663340600885133715)
      ·
        refine ⟨4016541995010901327700573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677694663340600885133715 4016541995010901327700573)
        ·
          refine ⟨1506203248129087997887715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4016541995010901327700573 1506203248129087997887715)
          ·
            refine ⟨2259304872193631996831573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506203248129087997887715 2259304872193631996831573)
            ·
              refine ⟨13238114485509562481435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2259304872193631996831573 13238114485509562481435)
              ·
                rfl

theorem cell21_522068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 9].length) (baseStart_522068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_522068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_522068 prefixEnd_522068 := by exact prefixLift 522068
  have htrace : WordTrace (prefixWord ++ tailWord_522068) baseStart_522068 baseEnd_522068 := by
    simpa [prefixWord, tailWord_522068, baseEnd_522068] using wordTrace_append hprefix tailTrace_522068
  have hstable : (prefixWord ++ tailWord_522068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522068).length < 2 ^ (prefixWord ++ tailWord_522068).sum := by decide
  have hdescent : baseEnd_522068 < baseStart_522068 := by decide
  rcases family_descends (prefixWord ++ tailWord_522068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522161 : List Nat := [1, 2, 2, 4, 2, 2, 3, 5]
def baseStart_522161 : Nat := 118140960795 + 522161 * 2 ^ 59
def prefixEnd_522161 : Nat := 4983230072969 + 3 ^ 40 * 522161 * 2
def baseEnd_522161 : Nat := 39721418078879522427575

theorem tailTrace_522161 : CollatzResearch.WordTrace tailWord_522161 prefixEnd_522161 39721418078879522427575 := by
  unfold tailWord_522161
  simp only [CollatzResearch.WordTrace]
  refine ⟨19044776261307349844086337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12696517507538233229390891 19044776261307349844086337)
  ·
    refine ⟨14283582195980512383064753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19044776261307349844086337 14283582195980512383064753)
    ·
      refine ⟨10712686646985384287298565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14283582195980512383064753 10712686646985384287298565)
      ·
        refine ⟨2008628746309759553868481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10712686646985384287298565 2008628746309759553868481)
        ·
          refine ⟨1506471559732319665401361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2008628746309759553868481 1506471559732319665401361)
          ·
            refine ⟨1129853669799239749051021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1506471559732319665401361 1129853669799239749051021)
            ·
              refine ⟨423695126174714905894133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1129853669799239749051021 423695126174714905894133)
              ·
                refine ⟨39721418078879522427575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 423695126174714905894133 39721418078879522427575)
                ·
                  rfl

theorem cell21_522161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 5].length) (baseStart_522161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_522161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_522161 prefixEnd_522161 := by exact prefixLift 522161
  have htrace : WordTrace (prefixWord ++ tailWord_522161) baseStart_522161 baseEnd_522161 := by
    simpa [prefixWord, tailWord_522161, baseEnd_522161] using wordTrace_append hprefix tailTrace_522161
  have hstable : (prefixWord ++ tailWord_522161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522161).length < 2 ^ (prefixWord ++ tailWord_522161).sum := by decide
  have hdescent : baseEnd_522161 < baseStart_522161 := by decide
  rcases family_descends (prefixWord ++ tailWord_522161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522296 : List Nat := [2, 1, 2, 1, 7, 8]
def baseStart_522296 : Nat := 118140960795 + 522296 * 2 ^ 59
def prefixEnd_522296 : Nat := 4983230072969 + 3 ^ 40 * 522296 * 2
def baseEnd_522296 : Nat := 4414631965774382686387

theorem tailTrace_522296 : CollatzResearch.WordTrace tailWord_522296 prefixEnd_522296 4414631965774382686387 := by
  unfold tailWord_522296
  simp only [CollatzResearch.WordTrace]
  refine ⟨9524850057909133950125371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12699800077212178600167161 9524850057909133950125371)
  ·
    refine ⟨14287275086863700925188057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9524850057909133950125371 14287275086863700925188057)
    ·
      refine ⟨10715456315147775693891043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14287275086863700925188057 10715456315147775693891043)
      ·
        refine ⟨16073184472721663540836565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10715456315147775693891043 16073184472721663540836565)
        ·
          refine ⟨376715261079413989238357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16073184472721663540836565 376715261079413989238357)
          ·
            refine ⟨4414631965774382686387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 376715261079413989238357 4414631965774382686387)
            ·
              rfl

theorem cell21_522296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 8].length) (baseStart_522296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_522296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_522296 prefixEnd_522296 := by exact prefixLift 522296
  have htrace : WordTrace (prefixWord ++ tailWord_522296) baseStart_522296 baseEnd_522296 := by
    simpa [prefixWord, tailWord_522296, baseEnd_522296] using wordTrace_append hprefix tailTrace_522296
  have hstable : (prefixWord ++ tailWord_522296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522296).length < 2 ^ (prefixWord ++ tailWord_522296).sum := by decide
  have hdescent : baseEnd_522296 < baseStart_522296 := by decide
  rcases family_descends (prefixWord ++ tailWord_522296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522358 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_522358 : Nat := 118140960795 + 522358 * 2 ^ 59
def prefixEnd_522358 : Nat := 4983230072969 + 3 ^ 40 * 522358 * 2
def baseEnd_522358 : Nat := 119209212320610002498989

theorem tailTrace_522358 : CollatzResearch.WordTrace tailWord_522358 prefixEnd_522358 119209212320610002498989 := by
  unfold tailWord_522358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1190747590099603280562983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12701307627729101659338485 1190747590099603280562983)
  ·
    refine ⟨1786121385149404920844475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1190747590099603280562983 1786121385149404920844475)
    ·
      refine ⟨2679182077724107381266713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1786121385149404920844475 2679182077724107381266713)
      ·
        refine ⟨2009386558293080535950035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2679182077724107381266713 2009386558293080535950035)
        ·
          refine ⟨3014079837439620803925053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009386558293080535950035 3014079837439620803925053)
          ·
            refine ⟨1130279939039857801471895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3014079837439620803925053 1130279939039857801471895)
            ·
              refine ⟨1695419908559786702207843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130279939039857801471895 1695419908559786702207843)
              ·
                refine ⟨2543129862839680053311765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695419908559786702207843 2543129862839680053311765)
                ·
                  refine ⟨119209212320610002498989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2543129862839680053311765 119209212320610002498989)
                  ·
                    rfl

theorem cell21_522358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_522358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_522358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_522358 prefixEnd_522358 := by exact prefixLift 522358
  have htrace : WordTrace (prefixWord ++ tailWord_522358) baseStart_522358 baseEnd_522358 := by
    simpa [prefixWord, tailWord_522358, baseEnd_522358] using wordTrace_append hprefix tailTrace_522358
  have hstable : (prefixWord ++ tailWord_522358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522358).length < 2 ^ (prefixWord ++ tailWord_522358).sum := by decide
  have hdescent : baseEnd_522358 < baseStart_522358 := by decide
  rcases family_descends (prefixWord ++ tailWord_522358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522600 : List Nat := [2, 1, 4, 2, 2, 2, 2, 6]
def baseStart_522600 : Nat := 118140960795 + 522600 * 2 ^ 59
def prefixEnd_522600 : Nat := 4983230072969 + 3 ^ 40 * 522600 * 2
def baseEnd_522600 : Nat := 39754813339223786488387

theorem tailTrace_522600 : CollatzResearch.WordTrace tailWord_522600 prefixEnd_522600 39754813339223786488387 := by
  unfold tailWord_522600
  simp only [CollatzResearch.WordTrace]
  refine ⟨9530393953358463909658627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12707191937811285212878169 9530393953358463909658627)
  ·
    refine ⟨14295590930037695864487941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9530393953358463909658627 14295590930037695864487941)
    ·
      refine ⟨2680423299382067974591489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14295590930037695864487941 2680423299382067974591489)
      ·
        refine ⟨2010317474536550980943617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2680423299382067974591489 2010317474536550980943617)
        ·
          refine ⟨1507738105902413235707713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2010317474536550980943617 1507738105902413235707713)
          ·
            refine ⟨1130803579426809926780785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1507738105902413235707713 1130803579426809926780785)
            ·
              refine ⟨848102684570107445085589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1130803579426809926780785 848102684570107445085589)
              ·
                refine ⟨39754813339223786488387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 848102684570107445085589 39754813339223786488387)
                ·
                  rfl

theorem cell21_522600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_522600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_522600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_522600 prefixEnd_522600 := by exact prefixLift 522600
  have htrace : WordTrace (prefixWord ++ tailWord_522600) baseStart_522600 baseEnd_522600 := by
    simpa [prefixWord, tailWord_522600, baseEnd_522600] using wordTrace_append hprefix tailTrace_522600
  have hstable : (prefixWord ++ tailWord_522600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522600).length < 2 ^ (prefixWord ++ tailWord_522600).sum := by decide
  have hdescent : baseEnd_522600 < baseStart_522600 := by decide
  rcases family_descends (prefixWord ++ tailWord_522600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522631 : List Nat := [1, 1, 4, 2, 2, 1, 2, 5, 3]
def baseStart_522631 : Nat := 118140960795 + 522631 * 2 ^ 59
def prefixEnd_522631 : Nat := 4983230072969 + 3 ^ 40 * 522631 * 2
def baseEnd_522631 : Nat := 119271514640022194448431

theorem tailTrace_522631 : CollatzResearch.WordTrace tailWord_522631 prefixEnd_522631 119271514640022194448431 := by
  unfold tailWord_522631
  simp only [CollatzResearch.WordTrace]
  refine ⟨19061918569604620113695747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12707945713069746742463831 19061918569604620113695747)
  ·
    refine ⟨28592877854406930170543621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19061918569604620113695747 28592877854406930170543621)
    ·
      refine ⟨5361164597701299406976929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28592877854406930170543621 5361164597701299406976929)
      ·
        refine ⟨4020873448275974555232697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5361164597701299406976929 4020873448275974555232697)
        ·
          refine ⟨3015655086206980916424523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4020873448275974555232697 3015655086206980916424523)
          ·
            refine ⟨4523482629310471374636785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015655086206980916424523 4523482629310471374636785)
            ·
              refine ⟨3392611971982853530977589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4523482629310471374636785 3392611971982853530977589)
              ·
                refine ⟨318057372373392518529149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3392611971982853530977589 318057372373392518529149)
                ·
                  refine ⟨119271514640022194448431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318057372373392518529149 119271514640022194448431)
                  ·
                    rfl

theorem cell21_522631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 3].length) (baseStart_522631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_522631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_522631 prefixEnd_522631 := by exact prefixLift 522631
  have htrace : WordTrace (prefixWord ++ tailWord_522631) baseStart_522631 baseEnd_522631 := by
    simpa [prefixWord, tailWord_522631, baseEnd_522631] using wordTrace_append hprefix tailTrace_522631
  have hstable : (prefixWord ++ tailWord_522631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522631).length < 2 ^ (prefixWord ++ tailWord_522631).sum := by decide
  have hdescent : baseEnd_522631 < baseStart_522631 := by decide
  rcases family_descends (prefixWord ++ tailWord_522631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522648 : List Nat := [2, 1, 2, 5, 1, 2, 1, 4, 3]
def baseStart_522648 : Nat := 118140960795 + 522648 * 2 ^ 59
def prefixEnd_522648 : Nat := 4983230072969 + 3 ^ 40 * 522648 * 2
def baseEnd_522648 : Nat := 119275394271633942665063

theorem tailTrace_522648 : CollatzResearch.WordTrace tailWord_522648 prefixEnd_522648 119275394271633942665063 := by
  unfold tailWord_522648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9531269305271516008532299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12708359073695354678043065 9531269305271516008532299)
  ·
    refine ⟨14296903957907274012798449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9531269305271516008532299 14296903957907274012798449)
    ·
      refine ⟨10722677968430455509598837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14296903957907274012798449 10722677968430455509598837)
      ·
        refine ⟨1005251059540355204024891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10722677968430455509598837 1005251059540355204024891)
        ·
          refine ⟨1507876589310532806037337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005251059540355204024891 1507876589310532806037337)
          ·
            refine ⟨1130907441982899604528003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1507876589310532806037337 1130907441982899604528003)
            ·
              refine ⟨1696361162974349406792005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130907441982899604528003 1696361162974349406792005)
              ·
                refine ⟨318067718057690513773501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1696361162974349406792005 318067718057690513773501)
                ·
                  refine ⟨119275394271633942665063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318067718057690513773501 119275394271633942665063)
                  ·
                    rfl

theorem cell21_522648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 3].length) (baseStart_522648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_522648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_522648 prefixEnd_522648 := by exact prefixLift 522648
  have htrace : WordTrace (prefixWord ++ tailWord_522648) baseStart_522648 baseEnd_522648 := by
    simpa [prefixWord, tailWord_522648, baseEnd_522648] using wordTrace_append hprefix tailTrace_522648
  have hstable : (prefixWord ++ tailWord_522648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522648).length < 2 ^ (prefixWord ++ tailWord_522648).sum := by decide
  have hdescent : baseEnd_522648 < baseStart_522648 := by decide
  rcases family_descends (prefixWord ++ tailWord_522648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522659 : List Nat := [1, 1, 1, 4, 1, 4, 3, 6]
def baseStart_522659 : Nat := 118140960795 + 522659 * 2 ^ 59
def prefixEnd_522659 : Nat := 4983230072969 + 3 ^ 40 * 522659 * 2
def baseEnd_522659 : Nat := 39759301540500122660569

theorem tailTrace_522659 : CollatzResearch.WordTrace tailWord_522659 prefixEnd_522659 39759301540500122660569 := by
  unfold tailWord_522659
  simp only [CollatzResearch.WordTrace]
  refine ⟨19062939813503180895715031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12708626542335453930476687 19062939813503180895715031)
  ·
    refine ⟨28594409720254771343572547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19062939813503180895715031 28594409720254771343572547)
    ·
      refine ⟨42891614580382157015358821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28594409720254771343572547 42891614580382157015358821)
      ·
        refine ⟨8042177733821654440379779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42891614580382157015358821 8042177733821654440379779)
        ·
          refine ⟨12063266600732481660569669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8042177733821654440379779 12063266600732481660569669)
          ·
            refine ⟨2261862487637340311356813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12063266600732481660569669 2261862487637340311356813)
            ·
              refine ⟨848198432864002616758805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2261862487637340311356813 848198432864002616758805)
              ·
                refine ⟨39759301540500122660569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 848198432864002616758805 39759301540500122660569)
                ·
                  rfl

theorem cell21_522659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 6].length) (baseStart_522659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_522659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_522659 prefixEnd_522659 := by exact prefixLift 522659
  have htrace : WordTrace (prefixWord ++ tailWord_522659) baseStart_522659 baseEnd_522659 := by
    simpa [prefixWord, tailWord_522659, baseEnd_522659] using wordTrace_append hprefix tailTrace_522659
  have hstable : (prefixWord ++ tailWord_522659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522659).length < 2 ^ (prefixWord ++ tailWord_522659).sum := by decide
  have hdescent : baseEnd_522659 < baseStart_522659 := by decide
  rcases family_descends (prefixWord ++ tailWord_522659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522758 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_522758 : Nat := 118140960795 + 522758 * 2 ^ 59
def prefixEnd_522758 : Nat := 4983230072969 + 3 ^ 40 * 522758 * 2
def baseEnd_522758 : Nat := 119300497770298195831505

theorem tailTrace_522758 : CollatzResearch.WordTrace tailWord_522758 prefixEnd_522758 119300497770298195831505 := by
  unfold tailWord_522758
  simp only [CollatzResearch.WordTrace]
  refine ⟨595829707504516275111529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12711033760096347202379285 595829707504516275111529)
  ·
    refine ⟨446872280628387206333647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 595829707504516275111529 446872280628387206333647)
    ·
      refine ⟨670308420942580809500471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446872280628387206333647 670308420942580809500471)
      ·
        refine ⟨1005462631413871214250707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670308420942580809500471 1005462631413871214250707)
        ·
          refine ⟨1508193947120806821376061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005462631413871214250707 1508193947120806821376061)
          ·
            refine ⟨565572730170302558016023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1508193947120806821376061 565572730170302558016023)
            ·
              refine ⟨848359095255453837024035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565572730170302558016023 848359095255453837024035)
              ·
                refine ⟨1272538642883180755536053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848359095255453837024035 1272538642883180755536053)
                ·
                  refine ⟨119300497770298195831505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1272538642883180755536053 119300497770298195831505)
                  ·
                    rfl

theorem cell21_522758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_522758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_522758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_522758 prefixEnd_522758 := by exact prefixLift 522758
  have htrace : WordTrace (prefixWord ++ tailWord_522758) baseStart_522758 baseEnd_522758 := by
    simpa [prefixWord, tailWord_522758, baseEnd_522758] using wordTrace_append hprefix tailTrace_522758
  have hstable : (prefixWord ++ tailWord_522758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522758).length < 2 ^ (prefixWord ++ tailWord_522758).sum := by decide
  have hdescent : baseEnd_522758 < baseStart_522758 := by decide
  rcases family_descends (prefixWord ++ tailWord_522758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522772 : List Nat := [2, 4, 3, 1, 1, 3, 2, 1, 4]
def baseStart_522772 : Nat := 118140960795 + 522772 * 2 ^ 59
def prefixEnd_522772 : Nat := 4983230072969 + 3 ^ 40 * 522772 * 2
def baseEnd_522772 : Nat := 119303692761037282598143

theorem tailTrace_522772 : CollatzResearch.WordTrace tailWord_522772 prefixEnd_522772 119303692761037282598143 := by
  unfold tailWord_522772
  simp only [CollatzResearch.WordTrace]
  refine ⟨9533530631046900597289285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12711374174729200796385713 9533530631046900597289285)
  ·
    refine ⟨1787536993321293861991741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9533530631046900597289285 1787536993321293861991741)
    ·
      refine ⟨670326372495485198246903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1787536993321293861991741 670326372495485198246903)
      ·
        refine ⟨1005489558743227797370355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670326372495485198246903 1005489558743227797370355)
        ·
          refine ⟨1508234338114841696055533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005489558743227797370355 1508234338114841696055533)
          ·
            refine ⟨565587876793065636020825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1508234338114841696055533 565587876793065636020825)
            ·
              refine ⟨424190907594799227015619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565587876793065636020825 424190907594799227015619)
              ·
                refine ⟨636286361392198840523429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424190907594799227015619 636286361392198840523429)
                ·
                  refine ⟨119303692761037282598143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 636286361392198840523429 119303692761037282598143)
                  ·
                    rfl

theorem cell21_522772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_522772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_522772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_522772 prefixEnd_522772 := by exact prefixLift 522772
  have htrace : WordTrace (prefixWord ++ tailWord_522772) baseStart_522772 baseEnd_522772 := by
    simpa [prefixWord, tailWord_522772, baseEnd_522772] using wordTrace_append hprefix tailTrace_522772
  have hstable : (prefixWord ++ tailWord_522772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522772).length < 2 ^ (prefixWord ++ tailWord_522772).sum := by decide
  have hdescent : baseEnd_522772 < baseStart_522772 := by decide
  rcases family_descends (prefixWord ++ tailWord_522772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522817 : List Nat := [1, 2, 5, 1, 1, 4, 2, 2, 3]
def baseStart_522817 : Nat := 118140960795 + 522817 * 2 ^ 59
def prefixEnd_522817 : Nat := 4983230072969 + 3 ^ 40 * 522817 * 2
def baseEnd_522817 : Nat := 119313962374127204348051

theorem tailTrace_522817 : CollatzResearch.WordTrace tailWord_522817 prefixEnd_522817 119313962374127204348051 := by
  unfold tailWord_522817
  simp only [CollatzResearch.WordTrace]
  refine ⟨19068702546930773879966705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12712468364620515919977803 19068702546930773879966705)
  ·
    refine ⟨14301526910198080409975029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19068702546930773879966705 14301526910198080409975029)
    ·
      refine ⟨1340768147831070038435159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14301526910198080409975029 1340768147831070038435159)
      ·
        refine ⟨2011152221746605057652739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340768147831070038435159 2011152221746605057652739)
        ·
          refine ⟨3016728332619907586479109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011152221746605057652739 3016728332619907586479109)
          ·
            refine ⟨565636562366232672464833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3016728332619907586479109 565636562366232672464833)
            ·
              refine ⟨424227421774674504348625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565636562366232672464833 424227421774674504348625)
              ·
                refine ⟨318170566331005878261469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424227421774674504348625 318170566331005878261469)
                ·
                  refine ⟨119313962374127204348051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318170566331005878261469 119313962374127204348051)
                  ·
                    rfl

theorem cell21_522817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 3].length) (baseStart_522817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_522817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_522817 prefixEnd_522817 := by exact prefixLift 522817
  have htrace : WordTrace (prefixWord ++ tailWord_522817) baseStart_522817 baseEnd_522817 := by
    simpa [prefixWord, tailWord_522817, baseEnd_522817] using wordTrace_append hprefix tailTrace_522817
  have hstable : (prefixWord ++ tailWord_522817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522817).length < 2 ^ (prefixWord ++ tailWord_522817).sum := by decide
  have hdescent : baseEnd_522817 < baseStart_522817 := by decide
  rcases family_descends (prefixWord ++ tailWord_522817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522873 : List Nat := [1, 2, 1, 3, 3, 2, 3, 2, 4]
def baseStart_522873 : Nat := 118140960795 + 522873 * 2 ^ 59
def prefixEnd_522873 : Nat := 4983230072969 + 3 ^ 40 * 522873 * 2
def baseEnd_522873 : Nat := 119326742337083551414603

theorem tailTrace_522873 : CollatzResearch.WordTrace tailWord_522873 prefixEnd_522873 119326742337083551414603 := by
  unfold tailWord_522873
  simp only [CollatzResearch.WordTrace]
  refine ⟨19070745034727895444005273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12713830023151930296003515 19070745034727895444005273)
  ·
    refine ⟨14303058776045921583003955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19070745034727895444005273 14303058776045921583003955)
    ·
      refine ⟨21454588164068882374505933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14303058776045921583003955 21454588164068882374505933)
      ·
        refine ⟨8045470561525830890439725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21454588164068882374505933 8045470561525830890439725)
        ·
          refine ⟨3017051460572186583914897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8045470561525830890439725 3017051460572186583914897)
          ·
            refine ⟨2262788595429139937936173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3017051460572186583914897 2262788595429139937936173)
            ·
              refine ⟨848545723285927476726065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2262788595429139937936173 848545723285927476726065)
              ·
                refine ⟨636409292464445607544549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848545723285927476726065 636409292464445607544549)
                ·
                  refine ⟨119326742337083551414603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 636409292464445607544549 119326742337083551414603)
                  ·
                    rfl

theorem cell21_522873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_522873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_522873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_522873 prefixEnd_522873 := by exact prefixLift 522873
  have htrace : WordTrace (prefixWord ++ tailWord_522873) baseStart_522873 baseEnd_522873 := by
    simpa [prefixWord, tailWord_522873, baseEnd_522873] using wordTrace_append hprefix tailTrace_522873
  have hstable : (prefixWord ++ tailWord_522873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522873).length < 2 ^ (prefixWord ++ tailWord_522873).sum := by decide
  have hdescent : baseEnd_522873 < baseStart_522873 := by decide
  rcases family_descends (prefixWord ++ tailWord_522873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522935 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 5]
def baseStart_522935 : Nat := 118140960795 + 522935 * 2 ^ 59
def prefixEnd_522935 : Nat := 4983230072969 + 3 ^ 40 * 522935 * 2
def baseEnd_522935 : Nat := 119340891581785221381143

theorem tailTrace_522935 : CollatzResearch.WordTrace tailWord_522935 prefixEnd_522935 119340891581785221381143 := by
  unfold tailWord_522935
  simp only [CollatzResearch.WordTrace]
  refine ⟨19073006360503280032762259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12715337573668853355174839 19073006360503280032762259)
  ·
    refine ⟨28609509540754920049143389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19073006360503280032762259 28609509540754920049143389)
    ·
      refine ⟨10728566077783095018428771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28609509540754920049143389 10728566077783095018428771)
      ·
        refine ⟨16092849116674642527643157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10728566077783095018428771 16092849116674642527643157)
        ·
          refine ⟨754352302344123868483273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16092849116674642527643157 754352302344123868483273)
          ·
            refine ⟨565764226758092901362455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754352302344123868483273 565764226758092901362455)
            ·
              refine ⟨848646340137139352043683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565764226758092901362455 848646340137139352043683)
              ·
                refine ⟨1272969510205709028065525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848646340137139352043683 1272969510205709028065525)
                ·
                  refine ⟨119340891581785221381143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1272969510205709028065525 119340891581785221381143)
                  ·
                    rfl

theorem cell21_522935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 5].length) (baseStart_522935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_522935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_522935 prefixEnd_522935 := by exact prefixLift 522935
  have htrace : WordTrace (prefixWord ++ tailWord_522935) baseStart_522935 baseEnd_522935 := by
    simpa [prefixWord, tailWord_522935, baseEnd_522935] using wordTrace_append hprefix tailTrace_522935
  have hstable : (prefixWord ++ tailWord_522935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522935).length < 2 ^ (prefixWord ++ tailWord_522935).sum := by decide
  have hdescent : baseEnd_522935 < baseStart_522935 := by decide
  rcases family_descends (prefixWord ++ tailWord_522935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523042 : List Nat := [3, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_523042 : Nat := 118140960795 + 523042 * 2 ^ 59
def prefixEnd_523042 : Nat := 4983230072969 + 3 ^ 40 * 523042 * 2
def baseEnd_523042 : Nat := 119365310439576813097591

theorem tailTrace_523042 : CollatzResearch.WordTrace tailWord_523042 prefixEnd_523042 119365310439576813097591 := by
  unfold tailWord_523042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4769227242778909326726845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12717939314077091537938253 4769227242778909326726845)
  ·
    refine ⟨1788460216042090997522567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4769227242778909326726845 1788460216042090997522567)
    ·
      refine ⟨2682690324063136496283851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1788460216042090997522567 2682690324063136496283851)
      ·
        refine ⟨4024035486094704744425777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2682690324063136496283851 4024035486094704744425777)
        ·
          refine ⟨3018026614571028558319333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4024035486094704744425777 3018026614571028558319333)
          ·
            refine ⟨565879990232067854684875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3018026614571028558319333 565879990232067854684875)
            ·
              refine ⟨848819985348101782027313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565879990232067854684875 848819985348101782027313)
              ·
                refine ⟨636614989011076336520485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848819985348101782027313 636614989011076336520485)
                ·
                  refine ⟨119365310439576813097591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 636614989011076336520485 119365310439576813097591)
                  ·
                    rfl

theorem cell21_523042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_523042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523042 prefixEnd_523042 := by exact prefixLift 523042
  have htrace : WordTrace (prefixWord ++ tailWord_523042) baseStart_523042 baseEnd_523042 := by
    simpa [prefixWord, tailWord_523042, baseEnd_523042] using wordTrace_append hprefix tailTrace_523042
  have hstable : (prefixWord ++ tailWord_523042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523042).length < 2 ^ (prefixWord ++ tailWord_523042).sum := by decide
  have hdescent : baseEnd_523042 < baseStart_523042 := by decide
  rcases family_descends (prefixWord ++ tailWord_523042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523084 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 6]
def baseStart_523084 : Nat := 118140960795 + 523084 * 2 ^ 59
def prefixEnd_523084 : Nat := 4983230072969 + 3 ^ 40 * 523084 * 2
def baseEnd_523084 : Nat := 119374895411794073397505

theorem tailTrace_523084 : CollatzResearch.WordTrace tailWord_523084 prefixEnd_523084 119374895411794073397505 := by
  unfold tailWord_523084
  simp only [CollatzResearch.WordTrace]
  refine ⟨9539220418481739239968153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12718960557975652319957537 9539220418481739239968153)
  ·
    refine ⟨7154415313861304429976115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9539220418481739239968153 7154415313861304429976115)
    ·
      refine ⟨10731622970791956644964173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7154415313861304429976115 10731622970791956644964173)
      ·
        refine ⟨4024358614046983741861565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10731622970791956644964173 4024358614046983741861565)
        ·
          refine ⟨1509134480267618903198087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4024358614046983741861565 1509134480267618903198087)
          ·
            refine ⟨2263701720401428354797131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509134480267618903198087 2263701720401428354797131)
            ·
              refine ⟨3395552580602142532195697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263701720401428354797131 3395552580602142532195697)
              ·
                refine ⟨2546664435451606899146773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395552580602142532195697 2546664435451606899146773)
                ·
                  refine ⟨119374895411794073397505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2546664435451606899146773 119374895411794073397505)
                  ·
                    rfl

theorem cell21_523084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_523084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523084 prefixEnd_523084 := by exact prefixLift 523084
  have htrace : WordTrace (prefixWord ++ tailWord_523084) baseStart_523084 baseEnd_523084 := by
    simpa [prefixWord, tailWord_523084, baseEnd_523084] using wordTrace_append hprefix tailTrace_523084
  have hstable : (prefixWord ++ tailWord_523084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523084).length < 2 ^ (prefixWord ++ tailWord_523084).sum := by decide
  have hdescent : baseEnd_523084 < baseStart_523084 := by decide
  rcases family_descends (prefixWord ++ tailWord_523084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523098 : List Nat := [3, 1, 1, 2, 1, 4, 9]
def baseStart_523098 : Nat := 118140960795 + 523098 * 2 ^ 59
def prefixEnd_523098 : Nat := 4983230072969 + 3 ^ 40 * 523098 * 2
def baseEnd_523098 : Nat := 13264232266948128907127

theorem tailTrace_523098 : CollatzResearch.WordTrace tailWord_523098 prefixEnd_523098 13264232266948128907127 := by
  unfold tailWord_523098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4769737864728189717736487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12719300972608505913963965 4769737864728189717736487)
  ·
    refine ⟨7154606797092284576604731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4769737864728189717736487 7154606797092284576604731)
    ·
      refine ⟨10731910195638426864907097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7154606797092284576604731 10731910195638426864907097)
      ·
        refine ⟨8048932646728820148680323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10731910195638426864907097 8048932646728820148680323)
        ·
          refine ⟨12073398970093230223020485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8048932646728820148680323 12073398970093230223020485)
          ·
            refine ⟨2263762306892480666816341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12073398970093230223020485 2263762306892480666816341)
            ·
              refine ⟨13264232266948128907127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2263762306892480666816341 13264232266948128907127)
              ·
                rfl

theorem cell21_523098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 9].length) (baseStart_523098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523098 prefixEnd_523098 := by exact prefixLift 523098
  have htrace : WordTrace (prefixWord ++ tailWord_523098) baseStart_523098 baseEnd_523098 := by
    simpa [prefixWord, tailWord_523098, baseEnd_523098] using wordTrace_append hprefix tailTrace_523098
  have hstable : (prefixWord ++ tailWord_523098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523098).length < 2 ^ (prefixWord ++ tailWord_523098).sum := by decide
  have hdescent : baseEnd_523098 < baseStart_523098 := by decide
  rcases family_descends (prefixWord ++ tailWord_523098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523118 : List Nat := [4, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_523118 : Nat := 118140960795 + 523118 * 2 ^ 59
def prefixEnd_523118 : Nat := 4983230072969 + 3 ^ 40 * 523118 * 2
def baseEnd_523118 : Nat := 119382654675017569830769

theorem tailTrace_523118 : CollatzResearch.WordTrace tailWord_523118 prefixEnd_523118 119382654675017569830769 := by
  unfold tailWord_523118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2384960114855037785834251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12719787279226868191116005 2384960114855037785834251)
  ·
    refine ⟨3577440172282556678751377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2384960114855037785834251 3577440172282556678751377)
    ·
      refine ⟨2683080129211917509063533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3577440172282556678751377 2683080129211917509063533)
      ·
        refine ⟨1006155048454469065898825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2683080129211917509063533 1006155048454469065898825)
        ·
          refine ⟨754616286340851799424119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006155048454469065898825 754616286340851799424119)
          ·
            refine ⟨1131924429511277699136179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754616286340851799424119 1131924429511277699136179)
            ·
              refine ⟨1697886644266916548704269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131924429511277699136179 1697886644266916548704269)
              ·
                refine ⟨636707491600093705764101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1697886644266916548704269 636707491600093705764101)
                ·
                  refine ⟨119382654675017569830769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 636707491600093705764101 119382654675017569830769)
                  ·
                    rfl

theorem cell21_523118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_523118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523118 prefixEnd_523118 := by exact prefixLift 523118
  have htrace : WordTrace (prefixWord ++ tailWord_523118) baseStart_523118 baseEnd_523118 := by
    simpa [prefixWord, tailWord_523118, baseEnd_523118] using wordTrace_append hprefix tailTrace_523118
  have hstable : (prefixWord ++ tailWord_523118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523118).length < 2 ^ (prefixWord ++ tailWord_523118).sum := by decide
  have hdescent : baseEnd_523118 < baseStart_523118 := by decide
  rcases family_descends (prefixWord ++ tailWord_523118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523402 : List Nat := [3, 1, 2, 3, 1, 1, 2, 8]
def baseStart_523402 : Nat := 118140960795 + 523402 * 2 ^ 59
def prefixEnd_523402 : Nat := 4983230072969 + 3 ^ 40 * 523402 * 2
def baseEnd_523402 : Nat := 39815822448098729032285

theorem tailTrace_523402 : CollatzResearch.WordTrace tailWord_523402 prefixEnd_523402 39815822448098729032285 := by
  unfold tailWord_523402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4772509812452854697503115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12726692833207612526674973 4772509812452854697503115)
  ·
    refine ⟨7158764718679282046254673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4772509812452854697503115 7158764718679282046254673)
    ·
      refine ⟨5369073539009461534691005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7158764718679282046254673 5369073539009461534691005)
      ·
        refine ⟨2013402577128548075509127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5369073539009461534691005 2013402577128548075509127)
        ·
          refine ⟨3020103865692822113263691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013402577128548075509127 3020103865692822113263691)
          ·
            refine ⟨4530155798539233169895537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020103865692822113263691 4530155798539233169895537)
            ·
              refine ⟨3397616848904424877421653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4530155798539233169895537 3397616848904424877421653)
              ·
                refine ⟨39815822448098729032285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3397616848904424877421653 39815822448098729032285)
                ·
                  rfl

theorem cell21_523402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_523402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523402 prefixEnd_523402 := by exact prefixLift 523402
  have htrace : WordTrace (prefixWord ++ tailWord_523402) baseStart_523402 baseEnd_523402 := by
    simpa [prefixWord, tailWord_523402, baseEnd_523402] using wordTrace_append hprefix tailTrace_523402
  have hstable : (prefixWord ++ tailWord_523402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523402).length < 2 ^ (prefixWord ++ tailWord_523402).sum := by decide
  have hdescent : baseEnd_523402 < baseStart_523402 := by decide
  rcases family_descends (prefixWord ++ tailWord_523402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523447 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 6]
def baseStart_523447 : Nat := 118140960795 + 523447 * 2 ^ 59
def prefixEnd_523447 : Nat := 4983230072969 + 3 ^ 40 * 523447 * 2
def baseEnd_523447 : Nat := 119457736957386108846763

theorem tailTrace_523447 : CollatzResearch.WordTrace tailWord_523447 prefixEnd_523447 119457736957386108846763 := by
  unfold tailWord_523447
  simp only [CollatzResearch.WordTrace]
  refine ⟨19091680534648391475400595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12727787023098927650267063 19091680534648391475400595)
  ·
    refine ⟨28637520801972587213100893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19091680534648391475400595 28637520801972587213100893)
    ·
      refine ⟨10739070300739720204912835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28637520801972587213100893 10739070300739720204912835)
      ·
        refine ⟨16108605451109580307369253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10739070300739720204912835 16108605451109580307369253)
        ·
          refine ⟨3020363522083046307631735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16108605451109580307369253 3020363522083046307631735)
          ·
            refine ⟨4530545283124569461447603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020363522083046307631735 4530545283124569461447603)
            ·
              refine ⟨6795817924686854192171405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4530545283124569461447603 6795817924686854192171405)
              ·
                refine ⟨2548431721757570322064277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6795817924686854192171405 2548431721757570322064277)
                ·
                  refine ⟨119457736957386108846763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2548431721757570322064277 119457736957386108846763)
                  ·
                    rfl

theorem cell21_523447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_523447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523447 prefixEnd_523447 := by exact prefixLift 523447
  have htrace : WordTrace (prefixWord ++ tailWord_523447) baseStart_523447 baseEnd_523447 := by
    simpa [prefixWord, tailWord_523447, baseEnd_523447] using wordTrace_append hprefix tailTrace_523447
  have hstable : (prefixWord ++ tailWord_523447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523447).length < 2 ^ (prefixWord ++ tailWord_523447).sum := by decide
  have hdescent : baseEnd_523447 < baseStart_523447 := by decide
  rcases family_descends (prefixWord ++ tailWord_523447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523495 : List Nat := [1, 1, 5, 3, 3, 8]
def baseStart_523495 : Nat := 118140960795 + 523495 * 2 ^ 59
def prefixEnd_523495 : Nat := 4983230072969 + 3 ^ 40 * 523495 * 2
def baseEnd_523495 : Nat := 4424766341161062668395

theorem tailTrace_523495 : CollatzResearch.WordTrace tailWord_523495 prefixEnd_523495 4424766341161062668395 := by
  unfold tailWord_523495
  simp only [CollatzResearch.WordTrace]
  refine ⟨19093431238474495673147939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12728954158982997115431959 19093431238474495673147939)
  ·
    refine ⟨28640146857711743509721909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19093431238474495673147939 28640146857711743509721909)
    ·
      refine ⟨2685013767910475954036429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28640146857711743509721909 2685013767910475954036429)
      ·
        refine ⟨1006880162966428482763661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2685013767910475954036429 1006880162966428482763661)
        ·
          refine ⟨377580061112410681036373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1006880162966428482763661 377580061112410681036373)
          ·
            refine ⟨4424766341161062668395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 377580061112410681036373 4424766341161062668395)
            ·
              rfl

theorem cell21_523495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 8].length) (baseStart_523495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523495 prefixEnd_523495 := by exact prefixLift 523495
  have htrace : WordTrace (prefixWord ++ tailWord_523495) baseStart_523495 baseEnd_523495 := by
    simpa [prefixWord, tailWord_523495, baseEnd_523495] using wordTrace_append hprefix tailTrace_523495
  have hstable : (prefixWord ++ tailWord_523495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523495).length < 2 ^ (prefixWord ++ tailWord_523495).sum := by decide
  have hdescent : baseEnd_523495 < baseStart_523495 := by decide
  rcases family_descends (prefixWord ++ tailWord_523495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523557 : List Nat := [1, 3, 1, 2, 4, 3, 1, 2, 4]
def baseStart_523557 : Nat := 118140960795 + 523557 * 2 ^ 59
def prefixEnd_523557 : Nat := 4983230072969 + 3 ^ 40 * 523557 * 2
def baseEnd_523557 : Nat := 119482840456050362013205

theorem tailTrace_523557 : CollatzResearch.WordTrace tailWord_523557 prefixEnd_523557 119482840456050362013205 := by
  unfold tailWord_523557
  simp only [CollatzResearch.WordTrace]
  refine ⟨19095692564249880261904925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12730461709499920174603283 19095692564249880261904925)
  ·
    refine ⟨7160884711593705098214347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19095692564249880261904925 7160884711593705098214347)
    ·
      refine ⟨10741327067390557647321521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7160884711593705098214347 10741327067390557647321521)
      ·
        refine ⟨8055995300542918235491141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10741327067390557647321521 8055995300542918235491141)
        ·
          refine ⟨1510499118851797169154589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8055995300542918235491141 1510499118851797169154589)
          ·
            refine ⟨566437169569423938432971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1510499118851797169154589 566437169569423938432971)
            ·
              refine ⟨849655754354135907649457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566437169569423938432971 849655754354135907649457)
              ·
                refine ⟨637241815765601930737093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849655754354135907649457 637241815765601930737093)
                ·
                  refine ⟨119482840456050362013205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 637241815765601930737093 119482840456050362013205)
                  ·
                    rfl

theorem cell21_523557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_523557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523557 prefixEnd_523557 := by exact prefixLift 523557
  have htrace : WordTrace (prefixWord ++ tailWord_523557) baseStart_523557 baseEnd_523557 := by
    simpa [prefixWord, tailWord_523557, baseEnd_523557] using wordTrace_append hprefix tailTrace_523557
  have hstable : (prefixWord ++ tailWord_523557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523557).length < 2 ^ (prefixWord ++ tailWord_523557).sum := by decide
  have hdescent : baseEnd_523557 < baseStart_523557 := by decide
  rcases family_descends (prefixWord ++ tailWord_523557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523588 : List Nat := [2, 3, 4, 1, 1, 1, 4, 5]
def baseStart_523588 : Nat := 118140960795 + 523588 * 2 ^ 59
def prefixEnd_523588 : Nat := 4983230072969 + 3 ^ 40 * 523588 * 2
def baseEnd_523588 : Nat := 39829971692800398998825

theorem tailTrace_523588 : CollatzResearch.WordTrace tailWord_523588 prefixEnd_523588 39829971692800398998825 := by
  unfold tailWord_523588
  simp only [CollatzResearch.WordTrace]
  refine ⟨9548411613568786278141709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12731215484758381704188945 9548411613568786278141709)
  ·
    refine ⟨3580654355088294854303141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9548411613568786278141709 3580654355088294854303141)
    ·
      refine ⟨671372691579055285181839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3580654355088294854303141 671372691579055285181839)
      ·
        refine ⟨1007059037368582927772759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671372691579055285181839 1007059037368582927772759)
        ·
          refine ⟨1510588556052874391659139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007059037368582927772759 1510588556052874391659139)
          ·
            refine ⟨2265882834079311587488709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510588556052874391659139 2265882834079311587488709)
            ·
              refine ⟨424853031389870922654133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2265882834079311587488709 424853031389870922654133)
              ·
                refine ⟨39829971692800398998825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424853031389870922654133 39829971692800398998825)
                ·
                  rfl

theorem cell21_523588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_523588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523588 prefixEnd_523588 := by exact prefixLift 523588
  have htrace : WordTrace (prefixWord ++ tailWord_523588) baseStart_523588 baseEnd_523588 := by
    simpa [prefixWord, tailWord_523588, baseEnd_523588] using wordTrace_append hprefix tailTrace_523588
  have hstable : (prefixWord ++ tailWord_523588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523588).length < 2 ^ (prefixWord ++ tailWord_523588).sum := by decide
  have hdescent : baseEnd_523588 < baseStart_523588 := by decide
  rcases family_descends (prefixWord ++ tailWord_523588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523619 : List Nat := [1, 1, 1, 5, 2, 3, 3, 2, 3]
def baseStart_523619 : Nat := 118140960795 + 523619 * 2 ^ 59
def prefixEnd_523619 : Nat := 4983230072969 + 3 ^ 40 * 523619 * 2
def baseEnd_523619 : Nat := 119496989700752031979745

theorem tailTrace_523619 : CollatzResearch.WordTrace tailWord_523619 prefixEnd_523619 119496989700752031979745 := by
  unfold tailWord_523619
  simp only [CollatzResearch.WordTrace]
  refine ⟨19097953890025264850661911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12731969260016843233774607 19097953890025264850661911)
  ·
    refine ⟨28646930835037897275992867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19097953890025264850661911 28646930835037897275992867)
    ·
      refine ⟨42970396252556845913989301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28646930835037897275992867 42970396252556845913989301)
      ·
        refine ⟨4028474648677204304436497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42970396252556845913989301 4028474648677204304436497)
        ·
          refine ⟨3021355986507903228327373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4028474648677204304436497 3021355986507903228327373)
          ·
            refine ⟨1133008494940463710622765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3021355986507903228327373 1133008494940463710622765)
            ·
              refine ⟨424878185602673891483537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1133008494940463710622765 424878185602673891483537)
              ·
                refine ⟨318658639202005418612653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424878185602673891483537 318658639202005418612653)
                ·
                  refine ⟨119496989700752031979745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318658639202005418612653 119496989700752031979745)
                  ·
                    rfl

theorem cell21_523619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 3].length) (baseStart_523619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523619 prefixEnd_523619 := by exact prefixLift 523619
  have htrace : WordTrace (prefixWord ++ tailWord_523619) baseStart_523619 baseEnd_523619 := by
    simpa [prefixWord, tailWord_523619, baseEnd_523619] using wordTrace_append hprefix tailTrace_523619
  have hstable : (prefixWord ++ tailWord_523619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523619).length < 2 ^ (prefixWord ++ tailWord_523619).sum := by decide
  have hdescent : baseEnd_523619 < baseStart_523619 := by decide
  rcases family_descends (prefixWord ++ tailWord_523619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523644 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 7]
def baseStart_523644 : Nat := 118140960795 + 523644 * 2 ^ 59
def prefixEnd_523644 : Nat := 4983230072969 + 3 ^ 40 * 523644 * 2
def baseEnd_523644 : Nat := 119502695041357544063027

theorem tailTrace_523644 : CollatzResearch.WordTrace tailWord_523644 prefixEnd_523644 119502695041357544063027 := by
  unfold tailWord_523644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549432857467347060160993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12732577143289796080214657 9549432857467347060160993)
  ·
    refine ⟨7162074643100510295120745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9549432857467347060160993 7162074643100510295120745)
    ·
      refine ⟨5371555982325382721340559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7162074643100510295120745 5371555982325382721340559)
      ·
        refine ⟨8057333973488074082010839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5371555982325382721340559 8057333973488074082010839)
        ·
          refine ⟨12086000960232111123016259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057333973488074082010839 12086000960232111123016259)
          ·
            refine ⟨18129001440348166684524389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12086000960232111123016259 18129001440348166684524389)
            ·
              refine ⟨3399187770065281253348323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18129001440348166684524389 3399187770065281253348323)
              ·
                refine ⟨5098781655097921880022485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399187770065281253348323 5098781655097921880022485)
                ·
                  refine ⟨119502695041357544063027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5098781655097921880022485 119502695041357544063027)
                  ·
                    rfl

theorem cell21_523644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_523644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523644 prefixEnd_523644 := by exact prefixLift 523644
  have htrace : WordTrace (prefixWord ++ tailWord_523644) baseStart_523644 baseEnd_523644 := by
    simpa [prefixWord, tailWord_523644, baseEnd_523644] using wordTrace_append hprefix tailTrace_523644
  have hstable : (prefixWord ++ tailWord_523644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523644).length < 2 ^ (prefixWord ++ tailWord_523644).sum := by decide
  have hdescent : baseEnd_523644 < baseStart_523644 := by decide
  rcases family_descends (prefixWord ++ tailWord_523644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523720 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 7]
def baseStart_523720 : Nat := 118140960795 + 523720 * 2 ^ 59
def prefixEnd_523720 : Nat := 4983230072969 + 3 ^ 40 * 523720 * 2
def baseEnd_523720 : Nat := 119520039276798300796205

theorem tailTrace_523720 : CollatzResearch.WordTrace tailWord_523720 prefixEnd_523720 119520039276798300796205 := by
  unfold tailWord_523720
  simp only [CollatzResearch.WordTrace]
  refine ⟨9550818831329679550044307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12734425108439572733392409 9550818831329679550044307)
  ·
    refine ⟨14326228246994519325066461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9550818831329679550044307 14326228246994519325066461)
    ·
      refine ⟨5372335592622944746899923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14326228246994519325066461 5372335592622944746899923)
      ·
        refine ⟨8058503388934417120349885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5372335592622944746899923 8058503388934417120349885)
        ·
          refine ⟨3021938770850406420131207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8058503388934417120349885 3021938770850406420131207)
          ·
            refine ⟨4532908156275609630196811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021938770850406420131207 4532908156275609630196811)
            ·
              refine ⟨6799362234413414445295217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532908156275609630196811 6799362234413414445295217)
              ·
                refine ⟨5099521675810060833971413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799362234413414445295217 5099521675810060833971413)
                ·
                  refine ⟨119520039276798300796205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5099521675810060833971413 119520039276798300796205)
                  ·
                    rfl

theorem cell21_523720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_523720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523720 prefixEnd_523720 := by exact prefixLift 523720
  have htrace : WordTrace (prefixWord ++ tailWord_523720) baseStart_523720 baseEnd_523720 := by
    simpa [prefixWord, tailWord_523720, baseEnd_523720] using wordTrace_append hprefix tailTrace_523720
  have hstable : (prefixWord ++ tailWord_523720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523720).length < 2 ^ (prefixWord ++ tailWord_523720).sum := by decide
  have hdescent : baseEnd_523720 < baseStart_523720 := by decide
  rcases family_descends (prefixWord ++ tailWord_523720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523737 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 5]
def baseStart_523737 : Nat := 118140960795 + 523737 * 2 ^ 59
def prefixEnd_523737 : Nat := 4983230072969 + 3 ^ 40 * 523737 * 2
def baseEnd_523737 : Nat := 119523918908410049012837

theorem tailTrace_523737 : CollatzResearch.WordTrace tailWord_523737 prefixEnd_523737 119523918908410049012837 := by
  unfold tailWord_523737
  simp only [CollatzResearch.WordTrace]
  refine ⟨19102257703597771003457465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12734838469065180668971643 19102257703597771003457465)
  ·
    refine ⟨14326693277698328252593099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19102257703597771003457465 14326693277698328252593099)
    ·
      refine ⟨21490039916547492378889649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14326693277698328252593099 21490039916547492378889649)
      ·
        refine ⟨16117529937410619284167237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21490039916547492378889649 16117529937410619284167237)
        ·
          refine ⟨3022036863264491115781357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16117529937410619284167237 3022036863264491115781357)
          ·
            refine ⟨1133263823724184168418009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3022036863264491115781357 1133263823724184168418009)
            ·
              refine ⟨849947867793138126313507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133263823724184168418009 849947867793138126313507)
              ·
                refine ⟨1274921801689707189470261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849947867793138126313507 1274921801689707189470261)
                ·
                  refine ⟨119523918908410049012837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1274921801689707189470261 119523918908410049012837)
                  ·
                    rfl

theorem cell21_523737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_523737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523737 prefixEnd_523737 := by exact prefixLift 523737
  have htrace : WordTrace (prefixWord ++ tailWord_523737) baseStart_523737 baseEnd_523737 := by
    simpa [prefixWord, tailWord_523737, baseEnd_523737] using wordTrace_append hprefix tailTrace_523737
  have hstable : (prefixWord ++ tailWord_523737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523737).length < 2 ^ (prefixWord ++ tailWord_523737).sum := by decide
  have hdescent : baseEnd_523737 < baseStart_523737 := by decide
  rcases family_descends (prefixWord ++ tailWord_523737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523757 : List Nat := [1, 5, 1, 3, 3, 1, 2, 5]
def baseStart_523757 : Nat := 118140960795 + 523757 * 2 ^ 59
def prefixEnd_523757 : Nat := 4983230072969 + 3 ^ 40 * 523757 * 2
def baseEnd_523757 : Nat := 39842827726964819559821

theorem tailTrace_523757 : CollatzResearch.WordTrace tailWord_523757 prefixEnd_523757 39842827726964819559821 := by
  unfold tailWord_523757
  simp only [CollatzResearch.WordTrace]
  refine ⟨19102987163525314419185525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12735324775683542946123683 19102987163525314419185525)
  ·
    refine ⟨1790905046580498226798643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19102987163525314419185525 1790905046580498226798643)
    ·
      refine ⟨2686357569870747340197965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1790905046580498226798643 2686357569870747340197965)
      ·
        refine ⟨1007384088701530252574237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2686357569870747340197965 1007384088701530252574237)
        ·
          refine ⟨377769033263073844715339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1007384088701530252574237 377769033263073844715339)
          ·
            refine ⟨566653549894610767073009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377769033263073844715339 566653549894610767073009)
            ·
              refine ⟨424990162420958075304757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566653549894610767073009 424990162420958075304757)
              ·
                refine ⟨39842827726964819559821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424990162420958075304757 39842827726964819559821)
                ·
                  rfl

theorem cell21_523757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 5].length) (baseStart_523757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523757 prefixEnd_523757 := by exact prefixLift 523757
  have htrace : WordTrace (prefixWord ++ tailWord_523757) baseStart_523757 baseEnd_523757 := by
    simpa [prefixWord, tailWord_523757, baseEnd_523757] using wordTrace_append hprefix tailTrace_523757
  have hstable : (prefixWord ++ tailWord_523757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523757).length < 2 ^ (prefixWord ++ tailWord_523757).sum := by decide
  have hdescent : baseEnd_523757 < baseStart_523757 := by decide
  rcases family_descends (prefixWord ++ tailWord_523757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523858 : List Nat := [3, 2, 2, 1, 2, 2, 3, 6]
def baseStart_523858 : Nat := 118140960795 + 523858 * 2 ^ 59
def prefixEnd_523858 : Nat := 4983230072969 + 3 ^ 40 * 523858 * 2
def baseEnd_523858 : Nat := 39850510918980242498641

theorem tailTrace_523858 : CollatzResearch.WordTrace tailWord_523858 prefixEnd_523858 39850510918980242498641 := by
  unfold tailWord_523858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4776667734039852167153057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12737780624106272445741485 4776667734039852167153057)
  ·
    refine ⟨3582500800529889125364793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4776667734039852167153057 3582500800529889125364793)
    ·
      refine ⟨2686875600397416844023595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3582500800529889125364793 2686875600397416844023595)
      ·
        refine ⟨4030313400596125266035393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2686875600397416844023595 4030313400596125266035393)
        ·
          refine ⟨3022735050447093949526545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4030313400596125266035393 3022735050447093949526545)
          ·
            refine ⟨2267051287835320462144909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3022735050447093949526545 2267051287835320462144909)
            ·
              refine ⟨850144232938245173304341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2267051287835320462144909 850144232938245173304341)
              ·
                refine ⟨39850510918980242498641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 850144232938245173304341 39850510918980242498641)
                ·
                  rfl

theorem cell21_523858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_523858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523858 prefixEnd_523858 := by exact prefixLift 523858
  have htrace : WordTrace (prefixWord ++ tailWord_523858) baseStart_523858 baseEnd_523858 := by
    simpa [prefixWord, tailWord_523858, baseEnd_523858] using wordTrace_append hprefix tailTrace_523858
  have hstable : (prefixWord ++ tailWord_523858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523858).length < 2 ^ (prefixWord ++ tailWord_523858).sum := by decide
  have hdescent : baseEnd_523858 < baseStart_523858 := by decide
  rcases family_descends (prefixWord ++ tailWord_523858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523993 : List Nat := [1, 2, 1, 2, 3, 3, 2, 7]
def baseStart_523993 : Nat := 118140960795 + 523993 * 2 ^ 59
def prefixEnd_523993 : Nat := 4983230072969 + 3 ^ 40 * 523993 * 2
def baseEnd_523993 : Nat := 39860780532070164248549

theorem tailTrace_523993 : CollatzResearch.WordTrace tailWord_523993 prefixEnd_523993 39860780532070164248549 := by
  unfold tailWord_523993
  simp only [CollatzResearch.WordTrace]
  refine ⟨19111594790670326724776633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12741063193780217816517755 19111594790670326724776633)
  ·
    refine ⟨14333696093002745043582475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19111594790670326724776633 14333696093002745043582475)
    ·
      refine ⟨21500544139504117565373713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14333696093002745043582475 21500544139504117565373713)
      ·
        refine ⟨16125408104628088174030285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21500544139504117565373713 16125408104628088174030285)
        ·
          refine ⟨6047028039235533065261357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16125408104628088174030285 6047028039235533065261357)
          ·
            refine ⟨2267635514713324899473009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6047028039235533065261357 2267635514713324899473009)
            ·
              refine ⟨1700726636034993674604757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2267635514713324899473009 1700726636034993674604757)
              ·
                refine ⟨39860780532070164248549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1700726636034993674604757 39860780532070164248549)
                ·
                  rfl

theorem cell21_523993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 7].length) (baseStart_523993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_523993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_523993 prefixEnd_523993 := by exact prefixLift 523993
  have htrace : WordTrace (prefixWord ++ tailWord_523993) baseStart_523993 baseEnd_523993 := by
    simpa [prefixWord, tailWord_523993, baseEnd_523993] using wordTrace_append hprefix tailTrace_523993
  have hstable : (prefixWord ++ tailWord_523993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523993).length < 2 ^ (prefixWord ++ tailWord_523993).sum := by decide
  have hdescent : baseEnd_523993 < baseStart_523993 := by decide
  rcases family_descends (prefixWord ++ tailWord_523993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524058 : List Nat := [3, 1, 1, 3, 2, 3, 2, 3, 3]
def baseStart_524058 : Nat := 118140960795 + 524058 * 2 ^ 59
def prefixEnd_524058 : Nat := 4983230072969 + 3 ^ 40 * 524058 * 2
def baseEnd_524058 : Nat := 119597175481784824162181

theorem tailTrace_524058 : CollatzResearch.WordTrace tailWord_524058 prefixEnd_524058 119597175481784824162181 := by
  unfold tailWord_524058
  simp only [CollatzResearch.WordTrace]
  refine ⟨4778491383858710706473207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12742643690289895217261885 4778491383858710706473207)
  ·
    refine ⟨7167737075788066059709811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4778491383858710706473207 7167737075788066059709811)
    ·
      refine ⟨10751605613682099089564717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7167737075788066059709811 10751605613682099089564717)
      ·
        refine ⟨4031852105130787158586769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10751605613682099089564717 4031852105130787158586769)
        ·
          refine ⟨3023889078848090368940077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4031852105130787158586769 3023889078848090368940077)
          ·
            refine ⟨1133958404568033888352529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3023889078848090368940077 1133958404568033888352529)
            ·
              refine ⟨850468803426025416264397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133958404568033888352529 850468803426025416264397)
              ·
                refine ⟨318925801284759531099149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 850468803426025416264397 318925801284759531099149)
                ·
                  refine ⟨119597175481784824162181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318925801284759531099149 119597175481784824162181)
                  ·
                    rfl

theorem cell21_524058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_524058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524058 prefixEnd_524058 := by exact prefixLift 524058
  have htrace : WordTrace (prefixWord ++ tailWord_524058) baseStart_524058 baseEnd_524058 := by
    simpa [prefixWord, tailWord_524058, baseEnd_524058] using wordTrace_append hprefix tailTrace_524058
  have hstable : (prefixWord ++ tailWord_524058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524058).length < 2 ^ (prefixWord ++ tailWord_524058).sum := by decide
  have hdescent : baseEnd_524058 < baseStart_524058 := by decide
  rcases family_descends (prefixWord ++ tailWord_524058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524069 : List Nat := [1, 3, 1, 2, 3, 3, 8]
def baseStart_524069 : Nat := 118140960795 + 524069 * 2 ^ 59
def prefixEnd_524069 : Nat := 4983230072969 + 3 ^ 40 * 524069 * 2
def baseEnd_524069 : Nat := 13288853981294583275425

theorem tailTrace_524069 : CollatzResearch.WordTrace tailWord_524069 prefixEnd_524069 13288853981294583275425 := by
  unfold tailWord_524069
  simp only [CollatzResearch.WordTrace]
  refine ⟨19114366738394991704543261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12742911158929994469695507 19114366738394991704543261)
  ·
    refine ⟨7167887526898121889203723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19114366738394991704543261 7167887526898121889203723)
    ·
      refine ⟨10751831290347182833805585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7167887526898121889203723 10751831290347182833805585)
      ·
        refine ⟨8063873467760387125354189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10751831290347182833805585 8063873467760387125354189)
        ·
          refine ⟨3023952550410145172007821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8063873467760387125354189 3023952550410145172007821)
          ·
            refine ⟨1133982206403804439502933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3023952550410145172007821 1133982206403804439502933)
            ·
              refine ⟨13288853981294583275425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1133982206403804439502933 13288853981294583275425)
              ·
                rfl

theorem cell21_524069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 8].length) (baseStart_524069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524069 prefixEnd_524069 := by exact prefixLift 524069
  have htrace : WordTrace (prefixWord ++ tailWord_524069) baseStart_524069 baseEnd_524069 := by
    simpa [prefixWord, tailWord_524069, baseEnd_524069] using wordTrace_append hprefix tailTrace_524069
  have hstable : (prefixWord ++ tailWord_524069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524069).length < 2 ^ (prefixWord ++ tailWord_524069).sum := by decide
  have hdescent : baseEnd_524069 < baseStart_524069 := by decide
  rcases family_descends (prefixWord ++ tailWord_524069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524072 : List Nat := [2, 1, 5, 1, 1, 2, 3, 2, 4]
def baseStart_524072 : Nat := 118140960795 + 524072 * 2 ^ 59
def prefixEnd_524072 : Nat := 4983230072969 + 3 ^ 40 * 524072 * 2
def baseEnd_524072 : Nat := 119600370472523910928819

theorem tailTrace_524072 : CollatzResearch.WordTrace tailWord_524072 prefixEnd_524072 119600370472523910928819 := by
  unfold tailWord_524072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9557238078692061608451235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12742984104922748811268313 9557238078692061608451235)
  ·
    refine ⟨14335857118038092412676853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9557238078692061608451235 14335857118038092412676853)
    ·
      refine ⟨1343986604816071163688455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14335857118038092412676853 1343986604816071163688455)
      ·
        refine ⟨2015979907224106745532683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343986604816071163688455 2015979907224106745532683)
        ·
          refine ⟨3023969860836160118299025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015979907224106745532683 3023969860836160118299025)
          ·
            refine ⟨2267977395627120088724269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3023969860836160118299025 2267977395627120088724269)
            ·
              refine ⟨850491523360170033271601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2267977395627120088724269 850491523360170033271601)
              ·
                refine ⟨637868642520127524953701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850491523360170033271601 637868642520127524953701)
                ·
                  refine ⟨119600370472523910928819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 637868642520127524953701 119600370472523910928819)
                  ·
                    rfl

theorem cell21_524072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_524072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524072 prefixEnd_524072 := by exact prefixLift 524072
  have htrace : WordTrace (prefixWord ++ tailWord_524072) baseStart_524072 baseEnd_524072 := by
    simpa [prefixWord, tailWord_524072, baseEnd_524072] using wordTrace_append hprefix tailTrace_524072
  have hstable : (prefixWord ++ tailWord_524072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524072).length < 2 ^ (prefixWord ++ tailWord_524072).sum := by decide
  have hdescent : baseEnd_524072 < baseStart_524072 := by decide
  rcases family_descends (prefixWord ++ tailWord_524072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524145 : List Nat := [1, 2, 2, 2, 1, 3, 4, 6]
def baseStart_524145 : Nat := 118140960795 + 524145 * 2 ^ 59
def prefixEnd_524145 : Nat := 4983230072969 + 3 ^ 40 * 524145 * 2
def baseEnd_524145 : Nat := 39872343355697335404001

theorem tailTrace_524145 : CollatzResearch.WordTrace tailWord_524145 prefixEnd_524145 39872343355697335404001 := by
  unfold tailWord_524145
  simp only [CollatzResearch.WordTrace]
  refine ⟨19117138686119656684309889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12744759124079771122873259 19117138686119656684309889)
  ·
    refine ⟨14337854014589742513232417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19117138686119656684309889 14337854014589742513232417)
    ·
      refine ⟨10753390510942306884924313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14337854014589742513232417 10753390510942306884924313)
      ·
        refine ⟨8065042883206730163693235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10753390510942306884924313 8065042883206730163693235)
        ·
          refine ⟨12097564324810095245539853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8065042883206730163693235 12097564324810095245539853)
          ·
            refine ⟨4536586621803785717077445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12097564324810095245539853 4536586621803785717077445)
            ·
              refine ⟨850609991588209821952021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4536586621803785717077445 850609991588209821952021)
              ·
                refine ⟨39872343355697335404001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 850609991588209821952021 39872343355697335404001)
                ·
                  rfl

theorem cell21_524145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 6].length) (baseStart_524145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524145 prefixEnd_524145 := by exact prefixLift 524145
  have htrace : WordTrace (prefixWord ++ tailWord_524145) baseStart_524145 baseEnd_524145 := by
    simpa [prefixWord, tailWord_524145, baseEnd_524145] using wordTrace_append hprefix tailTrace_524145
  have hstable : (prefixWord ++ tailWord_524145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524145).length < 2 ^ (prefixWord ++ tailWord_524145).sum := by decide
  have hdescent : baseEnd_524145 < baseStart_524145 := by decide
  rcases family_descends (prefixWord ++ tailWord_524145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524159 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 7]
def baseStart_524159 : Nat := 118140960795 + 524159 * 2 ^ 59
def prefixEnd_524159 : Nat := 4983230072969 + 3 ^ 40 * 524159 * 2
def baseEnd_524159 : Nat := 119620225057831092978641

theorem tailTrace_524159 : CollatzResearch.WordTrace tailWord_524159 prefixEnd_524159 119620225057831092978641 := by
  unfold tailWord_524159
  simp only [CollatzResearch.WordTrace]
  refine ⟨19117649308068937075319531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12745099538712624716879687 19117649308068937075319531)
  ·
    refine ⟨28676473962103405612979297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19117649308068937075319531 28676473962103405612979297)
    ·
      refine ⟨21507355471577554209734473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28676473962103405612979297 21507355471577554209734473)
      ·
        refine ⟨16130516603683165657300855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21507355471577554209734473 16130516603683165657300855)
        ·
          refine ⟨24195774905524748485951283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16130516603683165657300855 24195774905524748485951283)
          ·
            refine ⟨36293662358287122728926925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24195774905524748485951283 36293662358287122728926925)
            ·
              refine ⟨13610123384357671023347597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36293662358287122728926925 13610123384357671023347597)
              ·
                refine ⟨5103796269134126633755349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13610123384357671023347597 5103796269134126633755349)
                ·
                  refine ⟨119620225057831092978641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5103796269134126633755349 119620225057831092978641)
                  ·
                    rfl

theorem cell21_524159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_524159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524159 prefixEnd_524159 := by exact prefixLift 524159
  have htrace : WordTrace (prefixWord ++ tailWord_524159) baseStart_524159 baseEnd_524159 := by
    simpa [prefixWord, tailWord_524159, baseEnd_524159] using wordTrace_append hprefix tailTrace_524159
  have hstable : (prefixWord ++ tailWord_524159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524159).length < 2 ^ (prefixWord ++ tailWord_524159).sum := by decide
  have hdescent : baseEnd_524159 < baseStart_524159 := by decide
  rcases family_descends (prefixWord ++ tailWord_524159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524235 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 7]
def baseStart_524235 : Nat := 118140960795 + 524235 * 2 ^ 59
def prefixEnd_524235 : Nat := 4983230072969 + 3 ^ 40 * 524235 * 2
def baseEnd_524235 : Nat := 119637569293271849711819

theorem tailTrace_524235 : CollatzResearch.WordTrace tailWord_524235 prefixEnd_524235 119637569293271849711819 := by
  unfold tailWord_524235
  simp only [CollatzResearch.WordTrace]
  refine ⟨19120421255793602055086159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12746947503862401370057439 19120421255793602055086159)
  ·
    refine ⟨28680631883690403082629239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19120421255793602055086159 28680631883690403082629239)
    ·
      refine ⟨43020947825535604623943859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28680631883690403082629239 43020947825535604623943859)
      ·
        refine ⟨64531421738303406935915789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43020947825535604623943859 64531421738303406935915789)
        ·
          refine ⟨24199283151863777600968421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64531421738303406935915789 24199283151863777600968421)
          ·
            refine ⟨4537365590974458300181579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24199283151863777600968421 4537365590974458300181579)
            ·
              refine ⟨6806048386461687450272369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4537365590974458300181579 6806048386461687450272369)
              ·
                refine ⟨5104536289846265587704277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6806048386461687450272369 5104536289846265587704277)
                ·
                  refine ⟨119637569293271849711819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5104536289846265587704277 119637569293271849711819)
                  ·
                    rfl

theorem cell21_524235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_524235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524235 prefixEnd_524235 := by exact prefixLift 524235
  have htrace : WordTrace (prefixWord ++ tailWord_524235) baseStart_524235 baseEnd_524235 := by
    simpa [prefixWord, tailWord_524235, baseEnd_524235] using wordTrace_append hprefix tailTrace_524235
  have hstable : (prefixWord ++ tailWord_524235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524235).length < 2 ^ (prefixWord ++ tailWord_524235).sum := by decide
  have hdescent : baseEnd_524235 < baseStart_524235 := by decide
  rcases family_descends (prefixWord ++ tailWord_524235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524258 : List Nat := [3, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_524258 : Nat := 118140960795 + 524258 * 2 ^ 59
def prefixEnd_524258 : Nat := 4983230072969 + 3 ^ 40 * 524258 * 2
def baseEnd_524258 : Nat := 119642818206628920828439

theorem tailTrace_524258 : CollatzResearch.WordTrace tailWord_524258 prefixEnd_524258 119642818206628920828439 := by
  unfold tailWord_524258
  simp only [CollatzResearch.WordTrace]
  refine ⟨4780315033677569245793357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12747506756473517988782285 4780315033677569245793357)
  ·
    refine ⟨1792618137629088467172509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4780315033677569245793357 1792618137629088467172509)
    ·
      refine ⟨672231801610908175189691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1792618137629088467172509 672231801610908175189691)
      ·
        refine ⟨1008347702416362262784537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672231801610908175189691 1008347702416362262784537)
        ·
          refine ⟨756260776812271697088403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1008347702416362262784537 756260776812271697088403)
          ·
            refine ⟨1134391165218407545632605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756260776812271697088403 1134391165218407545632605)
            ·
              refine ⟨425396686956902829612227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1134391165218407545632605 425396686956902829612227)
              ·
                refine ⟨638095030435354244418341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425396686956902829612227 638095030435354244418341)
                ·
                  refine ⟨119642818206628920828439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638095030435354244418341 119642818206628920828439)
                  ·
                    rfl

theorem cell21_524258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_524258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524258 prefixEnd_524258 := by exact prefixLift 524258
  have htrace : WordTrace (prefixWord ++ tailWord_524258) baseStart_524258 baseEnd_524258 := by
    simpa [prefixWord, tailWord_524258, baseEnd_524258] using wordTrace_append hprefix tailTrace_524258
  have hstable : (prefixWord ++ tailWord_524258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524258).length < 2 ^ (prefixWord ++ tailWord_524258).sum := by decide
  have hdescent : baseEnd_524258 < baseStart_524258 := by decide
  rcases family_descends (prefixWord ++ tailWord_524258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524317 : List Nat := [1, 4, 2, 2, 2, 3, 2, 1, 4]
def baseStart_524317 : Nat := 118140960795 + 524317 * 2 ^ 59
def prefixEnd_524317 : Nat := 4983230072969 + 3 ^ 40 * 524317 * 2
def baseEnd_524317 : Nat := 119656282810457929344985

theorem tailTrace_524317 : CollatzResearch.WordTrace tailWord_524317 prefixEnd_524317 119656282810457929344985 := by
  unfold tailWord_524317
  simp only [CollatzResearch.WordTrace]
  refine ⟨19123412041496530059571205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12748941360997686706380803 19123412041496530059571205)
  ·
    refine ⟨3585639757780599386169601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19123412041496530059571205 3585639757780599386169601)
    ·
      refine ⟨2689229818335449539627201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3585639757780599386169601 2689229818335449539627201)
      ·
        refine ⟨2016922363751587154720401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2689229818335449539627201 2016922363751587154720401)
        ·
          refine ⟨1512691772813690366040301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2016922363751587154720401 1512691772813690366040301)
          ·
            refine ⟨567259414805133887265113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1512691772813690366040301 567259414805133887265113)
            ·
              refine ⟨425444561103850415448835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567259414805133887265113 425444561103850415448835)
              ·
                refine ⟨638166841655775623173253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425444561103850415448835 638166841655775623173253)
                ·
                  refine ⟨119656282810457929344985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638166841655775623173253 119656282810457929344985)
                  ·
                    rfl

theorem cell21_524317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_524317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524317 prefixEnd_524317 := by exact prefixLift 524317
  have htrace : WordTrace (prefixWord ++ tailWord_524317) baseStart_524317 baseEnd_524317 := by
    simpa [prefixWord, tailWord_524317, baseEnd_524317] using wordTrace_append hprefix tailTrace_524317
  have hstable : (prefixWord ++ tailWord_524317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524317).length < 2 ^ (prefixWord ++ tailWord_524317).sum := by decide
  have hdescent : baseEnd_524317 < baseStart_524317 := by decide
  rcases family_descends (prefixWord ++ tailWord_524317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524356 : List Nat := [2, 3, 16]
def baseStart_524356 : Nat := 118140960795 + 524356 * 2 ^ 59
def prefixEnd_524356 : Nat := 4983230072969 + 3 ^ 40 * 524356 * 2
def baseEnd_524356 : Nat := 164149771113583714945

theorem tailTrace_524356 : CollatzResearch.WordTrace tailWord_524356 prefixEnd_524356 164149771113583714945 := by
  unfold tailWord_524356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9562417244177619860120461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12749889658903493146827281 9562417244177619860120461)
  ·
    refine ⟨3585906466566607447545173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9562417244177619860120461 3585906466566607447545173)
    ·
      refine ⟨164149771113583714945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 3585906466566607447545173 164149771113583714945)
      ·
        rfl

theorem cell21_524356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 16].length) (baseStart_524356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524356 prefixEnd_524356 := by exact prefixLift 524356
  have htrace : WordTrace (prefixWord ++ tailWord_524356) baseStart_524356 baseEnd_524356 := by
    simpa [prefixWord, tailWord_524356, baseEnd_524356] using wordTrace_append hprefix tailTrace_524356
  have hstable : (prefixWord ++ tailWord_524356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524356).length < 2 ^ (prefixWord ++ tailWord_524356).sum := by decide
  have hdescent : baseEnd_524356 < baseStart_524356 := by decide
  rcases family_descends (prefixWord ++ tailWord_524356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524359 : List Nat := [1, 1, 4, 1, 3, 1, 4, 2, 4]
def baseStart_524359 : Nat := 118140960795 + 524359 * 2 ^ 59
def prefixEnd_524359 : Nat := 4983230072969 + 3 ^ 40 * 524359 * 2
def baseEnd_524359 : Nat := 119665867782675189644899

theorem tailTrace_524359 : CollatzResearch.WordTrace tailWord_524359 prefixEnd_524359 119665867782675189644899 := by
  unfold tailWord_524359
  simp only [CollatzResearch.WordTrace]
  refine ⟨19124943907344371232600131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12749962604896247488400087 19124943907344371232600131)
  ·
    refine ⟨28687415861016556848900197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19124943907344371232600131 28687415861016556848900197)
    ·
      refine ⟨5378890473940604409168787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28687415861016556848900197 5378890473940604409168787)
      ·
        refine ⟨8068335710910906613753181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5378890473940604409168787 8068335710910906613753181)
        ·
          refine ⟨3025625891591589980157443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8068335710910906613753181 3025625891591589980157443)
          ·
            refine ⟨4538438837387384970236165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025625891591589980157443 4538438837387384970236165)
            ·
              refine ⟨850957282010134681919281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4538438837387384970236165 850957282010134681919281)
              ·
                refine ⟨638217961507601011439461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850957282010134681919281 638217961507601011439461)
                ·
                  refine ⟨119665867782675189644899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638217961507601011439461 119665867782675189644899)
                  ·
                    rfl

theorem cell21_524359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 4].length) (baseStart_524359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524359 prefixEnd_524359 := by exact prefixLift 524359
  have htrace : WordTrace (prefixWord ++ tailWord_524359) baseStart_524359 baseEnd_524359 := by
    simpa [prefixWord, tailWord_524359, baseEnd_524359] using wordTrace_append hprefix tailTrace_524359
  have hstable : (prefixWord ++ tailWord_524359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524359).length < 2 ^ (prefixWord ++ tailWord_524359).sum := by decide
  have hdescent : baseEnd_524359 < baseStart_524359 := by decide
  rcases family_descends (prefixWord ++ tailWord_524359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524373 : List Nat := [1, 3, 2, 2, 1, 3, 3, 6]
def baseStart_524373 : Nat := 118140960795 + 524373 * 2 ^ 59
def prefixEnd_524373 : Nat := 4983230072969 + 3 ^ 40 * 524373 * 2
def baseEnd_524373 : Nat := 39889687591138092137179

theorem tailTrace_524373 : CollatzResearch.WordTrace tailWord_524373 prefixEnd_524373 39889687591138092137179 := by
  unfold tailWord_524373
  simp only [CollatzResearch.WordTrace]
  refine ⟨19125454529293651623609773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12750303019529101082406515 19125454529293651623609773)
  ·
    refine ⟨7172045448485119358853665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19125454529293651623609773 7172045448485119358853665)
    ·
      refine ⟨5379034086363839519140249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7172045448485119358853665 5379034086363839519140249)
      ·
        refine ⟨4034275564772879639355187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5379034086363839519140249 4034275564772879639355187)
        ·
          refine ⟨6051413347159319459032781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4034275564772879639355187 6051413347159319459032781)
          ·
            refine ⟨2269280005184744797137293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6051413347159319459032781 2269280005184744797137293)
            ·
              refine ⟨850980001944279298926485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2269280005184744797137293 850980001944279298926485)
              ·
                refine ⟨39889687591138092137179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 850980001944279298926485 39889687591138092137179)
                ·
                  rfl

theorem cell21_524373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 6].length) (baseStart_524373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524373 prefixEnd_524373 := by exact prefixLift 524373
  have htrace : WordTrace (prefixWord ++ tailWord_524373) baseStart_524373 baseEnd_524373 := by
    simpa [prefixWord, tailWord_524373, baseEnd_524373] using wordTrace_append hprefix tailTrace_524373
  have hstable : (prefixWord ++ tailWord_524373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524373).length < 2 ^ (prefixWord ++ tailWord_524373).sum := by decide
  have hdescent : baseEnd_524373 < baseStart_524373 := by decide
  rcases family_descends (prefixWord ++ tailWord_524373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524387 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 7]
def baseStart_524387 : Nat := 118140960795 + 524387 * 2 ^ 59
def prefixEnd_524387 : Nat := 4983230072969 + 3 ^ 40 * 524387 * 2
def baseEnd_524387 : Nat := 119672257764153363178175

theorem tailTrace_524387 : CollatzResearch.WordTrace tailWord_524387 prefixEnd_524387 119672257764153363178175 := by
  unfold tailWord_524387
  simp only [CollatzResearch.WordTrace]
  refine ⟨19125965151242932014619415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12750643434161954676412943 19125965151242932014619415)
  ·
    refine ⟨28688947726864398021929123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19125965151242932014619415 28688947726864398021929123)
    ·
      refine ⟨43033421590296597032893685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28688947726864398021929123 43033421590296597032893685)
      ·
        refine ⟨4034383274090305971833783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43033421590296597032893685 4034383274090305971833783)
        ·
          refine ⟨6051574911135458957750675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4034383274090305971833783 6051574911135458957750675)
          ·
            refine ⟨9077362366703188436626013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6051574911135458957750675 9077362366703188436626013)
            ·
              refine ⟨3404010887513695663734755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9077362366703188436626013 3404010887513695663734755)
              ·
                refine ⟨5106016331270543495602133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404010887513695663734755 5106016331270543495602133)
                ·
                  refine ⟨119672257764153363178175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5106016331270543495602133 119672257764153363178175)
                  ·
                    rfl

theorem cell21_524387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_524387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524387 prefixEnd_524387 := by exact prefixLift 524387
  have htrace : WordTrace (prefixWord ++ tailWord_524387) baseStart_524387 baseEnd_524387 := by
    simpa [prefixWord, tailWord_524387, baseEnd_524387] using wordTrace_append hprefix tailTrace_524387
  have hstable : (prefixWord ++ tailWord_524387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524387).length < 2 ^ (prefixWord ++ tailWord_524387).sum := by decide
  have hdescent : baseEnd_524387 < baseStart_524387 := by decide
  rcases family_descends (prefixWord ++ tailWord_524387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524421 : List Nat := [1, 3, 1, 1, 5, 1, 2, 4, 3]
def baseStart_524421 : Nat := 118140960795 + 524421 * 2 ^ 59
def prefixEnd_524421 : Nat := 4983230072969 + 3 ^ 40 * 524421 * 2
def baseEnd_524421 : Nat := 119680017027376859611439

theorem tailTrace_524421 : CollatzResearch.WordTrace tailWord_524421 prefixEnd_524421 119680017027376859611439 := by
  unfold tailWord_524421
  simp only [CollatzResearch.WordTrace]
  refine ⟨19127205233119755821357117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12751470155413170547571411 19127205233119755821357117)
  ·
    refine ⟨7172701962419908433008919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19127205233119755821357117 7172701962419908433008919)
    ·
      refine ⟨10759052943629862649513379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7172701962419908433008919 10759052943629862649513379)
      ·
        refine ⟨16138579415444793974270069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10759052943629862649513379 16138579415444793974270069)
        ·
          refine ⟨1512991820197949435087819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16138579415444793974270069 1512991820197949435087819)
          ·
            refine ⟨2269487730296924152631729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512991820197949435087819 2269487730296924152631729)
            ·
              refine ⟨1702115797722693114473797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2269487730296924152631729 1702115797722693114473797)
              ·
                refine ⟨319146712073004958963837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1702115797722693114473797 319146712073004958963837)
                ·
                  refine ⟨119680017027376859611439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319146712073004958963837 119680017027376859611439)
                  ·
                    rfl

theorem cell21_524421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_524421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524421 prefixEnd_524421 := by exact prefixLift 524421
  have htrace : WordTrace (prefixWord ++ tailWord_524421) baseStart_524421 baseEnd_524421 := by
    simpa [prefixWord, tailWord_524421, baseEnd_524421] using wordTrace_append hprefix tailTrace_524421
  have hstable : (prefixWord ++ tailWord_524421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524421).length < 2 ^ (prefixWord ++ tailWord_524421).sum := by decide
  have hdescent : baseEnd_524421 < baseStart_524421 := by decide
  rcases family_descends (prefixWord ++ tailWord_524421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524432 : List Nat := [2, 1, 1, 1, 1, 1, 6, 8]
def baseStart_524432 : Nat := 118140960795 + 524432 * 2 ^ 59
def prefixEnd_524432 : Nat := 4983230072969 + 3 ^ 40 * 524432 * 2
def baseEnd_524432 : Nat := 39894175792414428309361

theorem tailTrace_524432 : CollatzResearch.WordTrace tailWord_524432 prefixEnd_524432 39894175792414428309361 := by
  unfold tailWord_524432
  simp only [CollatzResearch.WordTrace]
  refine ⟨9563803218039952350003775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12751737624053269800005033 9563803218039952350003775)
  ·
    refine ⟨14345704827059928525005663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9563803218039952350003775 14345704827059928525005663)
    ·
      refine ⟨21518557240589892787508495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14345704827059928525005663 21518557240589892787508495)
      ·
        refine ⟨32277835860884839181262743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21518557240589892787508495 32277835860884839181262743)
        ·
          refine ⟨48416753791327258771894115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32277835860884839181262743 48416753791327258771894115)
          ·
            refine ⟨72625130686990888157841173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48416753791327258771894115 72625130686990888157841173)
            ·
              refine ⟨3404303000952697882398805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72625130686990888157841173 3404303000952697882398805)
              ·
                refine ⟨39894175792414428309361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3404303000952697882398805 39894175792414428309361)
                ·
                  rfl

theorem cell21_524432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_524432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524432 prefixEnd_524432 := by exact prefixLift 524432
  have htrace : WordTrace (prefixWord ++ tailWord_524432) baseStart_524432 baseEnd_524432 := by
    simpa [prefixWord, tailWord_524432, baseEnd_524432] using wordTrace_append hprefix tailTrace_524432
  have hstable : (prefixWord ++ tailWord_524432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524432).length < 2 ^ (prefixWord ++ tailWord_524432).sum := by decide
  have hdescent : baseEnd_524432 < baseStart_524432 := by decide
  rcases family_descends (prefixWord ++ tailWord_524432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524449 : List Nat := [1, 2, 3, 3, 1, 3, 1, 7]
def baseStart_524449 : Nat := 118140960795 + 524449 * 2 ^ 59
def prefixEnd_524449 : Nat := 4983230072969 + 3 ^ 40 * 524449 * 2
def baseEnd_524449 : Nat := 39895469002951677714905

theorem tailTrace_524449 : CollatzResearch.WordTrace tailWord_524449 prefixEnd_524449 39895469002951677714905 := by
  unfold tailWord_524449
  simp only [CollatzResearch.WordTrace]
  refine ⟨19128226477018316603376401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12752150984678877735584267 19128226477018316603376401)
  ·
    refine ⟨14346169857763737452532301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19128226477018316603376401 14346169857763737452532301)
    ·
      refine ⟨5379813696661401544699613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14346169857763737452532301 5379813696661401544699613)
      ·
        refine ⟨2017430136248025579262355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5379813696661401544699613 2017430136248025579262355)
        ·
          refine ⟨3026145204372038368893533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2017430136248025579262355 3026145204372038368893533)
          ·
            refine ⟨1134804451639514388335075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3026145204372038368893533 1134804451639514388335075)
            ·
              refine ⟨1702206677459271582502613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1134804451639514388335075 1702206677459271582502613)
              ·
                refine ⟨39895469002951677714905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1702206677459271582502613 39895469002951677714905)
                ·
                  rfl

theorem cell21_524449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 7].length) (baseStart_524449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524449 prefixEnd_524449 := by exact prefixLift 524449
  have htrace : WordTrace (prefixWord ++ tailWord_524449) baseStart_524449 baseEnd_524449 := by
    simpa [prefixWord, tailWord_524449, baseEnd_524449] using wordTrace_append hprefix tailTrace_524449
  have hstable : (prefixWord ++ tailWord_524449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524449).length < 2 ^ (prefixWord ++ tailWord_524449).sum := by decide
  have hdescent : baseEnd_524449 < baseStart_524449 := by decide
  rcases family_descends (prefixWord ++ tailWord_524449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524455 : List Nat := [1, 1, 6, 2, 2, 2, 1, 3, 3]
def baseStart_524455 : Nat := 118140960795 + 524455 * 2 ^ 59
def prefixEnd_524455 : Nat := 4983230072969 + 3 ^ 40 * 524455 * 2
def baseEnd_524455 : Nat := 119687776290600356044703

theorem tailTrace_524455 : CollatzResearch.WordTrace tailWord_524455 prefixEnd_524455 119687776290600356044703 := by
  unfold tailWord_524455
  simp only [CollatzResearch.WordTrace]
  refine ⟨19128445314996579628094819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12752296876664386418729879 19128445314996579628094819)
  ·
    refine ⟨28692667972494869442142229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19128445314996579628094819 28692667972494869442142229)
    ·
      refine ⟨1344968811210697005100417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28692667972494869442142229 1344968811210697005100417)
      ·
        refine ⟨1008726608408022753825313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1344968811210697005100417 1008726608408022753825313)
        ·
          refine ⟨756544956306017065368985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1008726608408022753825313 756544956306017065368985)
          ·
            refine ⟨567408717229512799026739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756544956306017065368985 567408717229512799026739)
            ·
              refine ⟨851113075844269198540109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567408717229512799026739 851113075844269198540109)
              ·
                refine ⟨319167403441600949452541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 851113075844269198540109 319167403441600949452541)
                ·
                  refine ⟨119687776290600356044703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319167403441600949452541 119687776290600356044703)
                  ·
                    rfl

theorem cell21_524455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 3].length) (baseStart_524455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524455 prefixEnd_524455 := by exact prefixLift 524455
  have htrace : WordTrace (prefixWord ++ tailWord_524455) baseStart_524455 baseEnd_524455 := by
    simpa [prefixWord, tailWord_524455, baseEnd_524455] using wordTrace_append hprefix tailTrace_524455
  have hstable : (prefixWord ++ tailWord_524455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524455).length < 2 ^ (prefixWord ++ tailWord_524455).sum := by decide
  have hdescent : baseEnd_524455 < baseStart_524455 := by decide
  rcases family_descends (prefixWord ++ tailWord_524455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524480 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 5]
def baseStart_524480 : Nat := 118140960795 + 524480 * 2 ^ 59
def prefixEnd_524480 : Nat := 4983230072969 + 3 ^ 40 * 524480 * 2
def baseEnd_524480 : Nat := 119693481631205868127985

theorem tailTrace_524480 : CollatzResearch.WordTrace tailWord_524480 prefixEnd_524480 119693481631205868127985 := by
  unfold tailWord_524480
  simp only [CollatzResearch.WordTrace]
  refine ⟨9564678569953004448877447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12752904759937339265169929 9564678569953004448877447)
  ·
    refine ⟨14347017854929506673316171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9564678569953004448877447 14347017854929506673316171)
    ·
      refine ⟨21520526782394260009974257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14347017854929506673316171 21520526782394260009974257)
      ·
        refine ⟨16140395086795695007480693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21520526782394260009974257 16140395086795695007480693)
        ·
          refine ⟨1513162039387096406951315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16140395086795695007480693 1513162039387096406951315)
          ·
            refine ⟨2269743059080644610426973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513162039387096406951315 2269743059080644610426973)
            ·
              refine ⟨851153647155241728910115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2269743059080644610426973 851153647155241728910115)
              ·
                refine ⟨1276730470732862593365173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851153647155241728910115 1276730470732862593365173)
                ·
                  refine ⟨119693481631205868127985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1276730470732862593365173 119693481631205868127985)
                  ·
                    rfl

theorem cell21_524480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_524480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524480 prefixEnd_524480 := by exact prefixLift 524480
  have htrace : WordTrace (prefixWord ++ tailWord_524480) baseStart_524480 baseEnd_524480 := by
    simpa [prefixWord, tailWord_524480, baseEnd_524480] using wordTrace_append hprefix tailTrace_524480
  have hstable : (prefixWord ++ tailWord_524480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524480).length < 2 ^ (prefixWord ++ tailWord_524480).sum := by decide
  have hdescent : baseEnd_524480 < baseStart_524480 := by decide
  rcases family_descends (prefixWord ++ tailWord_524480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524525 : List Nat := [1, 5, 1, 2, 3, 9]
def baseStart_524525 : Nat := 118140960795 + 524525 * 2 ^ 59
def prefixEnd_524525 : Nat := 4983230072969 + 3 ^ 40 * 524525 * 2
def baseEnd_524525 : Nat := 4433472268307251476959

theorem tailTrace_524525 : CollatzResearch.WordTrace tailWord_524525 prefixEnd_524525 4433472268307251476959 := by
  unfold tailWord_524525
  simp only [CollatzResearch.WordTrace]
  refine ⟨19130998424742981583143029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12753998949828654388762019 19130998424742981583143029)
  ·
    refine ⟨1793531102319654523419659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19130998424742981583143029 1793531102319654523419659)
    ·
      refine ⟨2690296653479481785129489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1793531102319654523419659 2690296653479481785129489)
      ·
        refine ⟨2017722490109611338847117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2690296653479481785129489 2017722490109611338847117)
        ·
          refine ⟨756645933791104252067669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2017722490109611338847117 756645933791104252067669)
          ·
            refine ⟨4433472268307251476959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 756645933791104252067669 4433472268307251476959)
            ·
              rfl

theorem cell21_524525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 9].length) (baseStart_524525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524525 prefixEnd_524525 := by exact prefixLift 524525
  have htrace : WordTrace (prefixWord ++ tailWord_524525) baseStart_524525 baseEnd_524525 := by
    simpa [prefixWord, tailWord_524525, baseEnd_524525] using wordTrace_append hprefix tailTrace_524525
  have hstable : (prefixWord ++ tailWord_524525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524525).length < 2 ^ (prefixWord ++ tailWord_524525).sum := by decide
  have hdescent : baseEnd_524525 < baseStart_524525 := by decide
  rcases family_descends (prefixWord ++ tailWord_524525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524590 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_524590 : Nat := 118140960795 + 524590 * 2 ^ 59
def prefixEnd_524590 : Nat := 4983230072969 + 3 ^ 40 * 524590 * 2
def baseEnd_524590 : Nat := 119718585129870121294427

theorem tailTrace_524590 : CollatzResearch.WordTrace tailWord_524590 prefixEnd_524590 119718585129870121294427 := by
  unfold tailWord_524590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2391671146188437210532403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12755579446338331789506149 2391671146188437210532403)
  ·
    refine ⟨3587506719282655815798605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2391671146188437210532403 3587506719282655815798605)
    ·
      refine ⟨1345315019730995930924477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3587506719282655815798605 1345315019730995930924477)
      ·
        refine ⟨504493132399123474096679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1345315019730995930924477 504493132399123474096679)
        ·
          refine ⟨756739698598685211145019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504493132399123474096679 756739698598685211145019)
          ·
            refine ⟨1135109547898027816717529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756739698598685211145019 1135109547898027816717529)
            ·
              refine ⟨851332160923520862538147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135109547898027816717529 851332160923520862538147)
              ·
                refine ⟨1276998241385281293807221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851332160923520862538147 1276998241385281293807221)
                ·
                  refine ⟨119718585129870121294427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1276998241385281293807221 119718585129870121294427)
                  ·
                    rfl

theorem cell21_524590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_524590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524590 prefixEnd_524590 := by exact prefixLift 524590
  have htrace : WordTrace (prefixWord ++ tailWord_524590) baseStart_524590 baseEnd_524590 := by
    simpa [prefixWord, tailWord_524590, baseEnd_524590] using wordTrace_append hprefix tailTrace_524590
  have hstable : (prefixWord ++ tailWord_524590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524590).length < 2 ^ (prefixWord ++ tailWord_524590).sum := by decide
  have hdescent : baseEnd_524590 < baseStart_524590 := by decide
  rcases family_descends (prefixWord ++ tailWord_524590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524615 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 5]
def baseStart_524615 : Nat := 118140960795 + 524615 * 2 ^ 59
def prefixEnd_524615 : Nat := 4983230072969 + 3 ^ 40 * 524615 * 2
def baseEnd_524615 : Nat := 119724290470475633377709

theorem tailTrace_524615 : CollatzResearch.WordTrace tailWord_524615 prefixEnd_524615 119724290470475633377709 := by
  unfold tailWord_524615
  simp only [CollatzResearch.WordTrace]
  refine ⟨19134280994416926953919299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12756187329611284635946199 19134280994416926953919299)
  ·
    refine ⟨28701421491625390430878949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19134280994416926953919299 28701421491625390430878949)
    ·
      refine ⟨5381516529679760705789803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28701421491625390430878949 5381516529679760705789803)
      ·
        refine ⟨8072274794519641058684705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5381516529679760705789803 8072274794519641058684705)
        ·
          refine ⟨6054206095889730794013529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8072274794519641058684705 6054206095889730794013529)
          ·
            refine ⟨4540654571917298095510147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6054206095889730794013529 4540654571917298095510147)
            ·
              refine ⟨6810981857875947143265221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4540654571917298095510147 6810981857875947143265221)
              ·
                refine ⟨1277059098351740089362229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6810981857875947143265221 1277059098351740089362229)
                ·
                  refine ⟨119724290470475633377709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1277059098351740089362229 119724290470475633377709)
                  ·
                    rfl

theorem cell21_524615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_524615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524615 prefixEnd_524615 := by exact prefixLift 524615
  have htrace : WordTrace (prefixWord ++ tailWord_524615) baseStart_524615 baseEnd_524615 := by
    simpa [prefixWord, tailWord_524615, baseEnd_524615] using wordTrace_append hprefix tailTrace_524615
  have hstable : (prefixWord ++ tailWord_524615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524615).length < 2 ^ (prefixWord ++ tailWord_524615).sum := by decide
  have hdescent : baseEnd_524615 < baseStart_524615 := by decide
  rcases family_descends (prefixWord ++ tailWord_524615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524632 : List Nat := [2, 1, 2, 2, 1, 1, 2, 7, 3]
def baseStart_524632 : Nat := 118140960795 + 524632 * 2 ^ 59
def prefixEnd_524632 : Nat := 4983230072969 + 3 ^ 40 * 524632 * 2
def baseEnd_524632 : Nat := 119728170102087381594341

theorem tailTrace_524632 : CollatzResearch.WordTrace tailWord_524632 prefixEnd_524632 119728170102087381594341 := by
  unfold tailWord_524632
  simp only [CollatzResearch.WordTrace]
  refine ⟨9567450517677669428644075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12756600690236892571525433 9567450517677669428644075)
  ·
    refine ⟨14351175776516504142966113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9567450517677669428644075 14351175776516504142966113)
    ·
      refine ⟨10763381832387378107224585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14351175776516504142966113 10763381832387378107224585)
      ·
        refine ⟨8072536374290533580418439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10763381832387378107224585 8072536374290533580418439)
        ·
          refine ⟨12108804561435800370627659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8072536374290533580418439 12108804561435800370627659)
          ·
            refine ⟨18163206842153700555941489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12108804561435800370627659 18163206842153700555941489)
            ·
              refine ⟨13622405131615275416956117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18163206842153700555941489 13622405131615275416956117)
              ·
                refine ⟨319275120272233017584909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13622405131615275416956117 319275120272233017584909)
                ·
                  refine ⟨119728170102087381594341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319275120272233017584909 119728170102087381594341)
                  ·
                    rfl

theorem cell21_524632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 3].length) (baseStart_524632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524632 prefixEnd_524632 := by exact prefixLift 524632
  have htrace : WordTrace (prefixWord ++ tailWord_524632) baseStart_524632 baseEnd_524632 := by
    simpa [prefixWord, tailWord_524632, baseEnd_524632] using wordTrace_append hprefix tailTrace_524632
  have hstable : (prefixWord ++ tailWord_524632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524632).length < 2 ^ (prefixWord ++ tailWord_524632).sum := by decide
  have hdescent : baseEnd_524632 < baseStart_524632 := by decide
  rcases family_descends (prefixWord ++ tailWord_524632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524649 : List Nat := [1, 2, 1, 1, 1, 3, 7, 2, 3]
def baseStart_524649 : Nat := 118140960795 + 524649 * 2 ^ 59
def prefixEnd_524649 : Nat := 4983230072969 + 3 ^ 40 * 524649 * 2
def baseEnd_524649 : Nat := 119732049733699129810973

theorem tailTrace_524649 : CollatzResearch.WordTrace tailWord_524649 prefixEnd_524649 119732049733699129810973 := by
  unfold tailWord_524649
  simp only [CollatzResearch.WordTrace]
  refine ⟨19135521076293750760657001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12757014050862500507104667 19135521076293750760657001)
  ·
    refine ⟨14351640807220313070492751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19135521076293750760657001 14351640807220313070492751)
    ·
      refine ⟨21527461210830469605739127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14351640807220313070492751 21527461210830469605739127)
      ·
        refine ⟨32291191816245704408608691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21527461210830469605739127 32291191816245704408608691)
        ·
          refine ⟨48436787724368556612913037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32291191816245704408608691 48436787724368556612913037)
          ·
            refine ⟨18163795396638208729842389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48436787724368556612913037 18163795396638208729842389)
            ·
              refine ⟨425713954608708017105681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18163795396638208729842389 425713954608708017105681)
              ·
                refine ⟨319285465956531012829261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425713954608708017105681 319285465956531012829261)
                ·
                  refine ⟨119732049733699129810973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319285465956531012829261 119732049733699129810973)
                  ·
                    rfl

theorem cell21_524649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 3].length) (baseStart_524649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524649 prefixEnd_524649 := by exact prefixLift 524649
  have htrace : WordTrace (prefixWord ++ tailWord_524649) baseStart_524649 baseEnd_524649 := by
    simpa [prefixWord, tailWord_524649, baseEnd_524649] using wordTrace_append hprefix tailTrace_524649
  have hstable : (prefixWord ++ tailWord_524649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524649).length < 2 ^ (prefixWord ++ tailWord_524649).sum := by decide
  have hdescent : baseEnd_524649 < baseStart_524649 := by decide
  rcases family_descends (prefixWord ++ tailWord_524649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524722 : List Nat := [3, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_524722 : Nat := 118140960795 + 524722 * 2 ^ 59
def prefixEnd_524722 : Nat := 4983230072969 + 3 ^ 40 * 524722 * 2
def baseEnd_524722 : Nat := 119748709328267225094157

theorem tailTrace_524722 : CollatzResearch.WordTrace tailWord_524722 prefixEnd_524722 119748709328267225094157 := by
  unfold tailWord_524722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4784545901257321057016105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12758789070019522818709613 4784545901257321057016105)
  ·
    refine ⟨3588409425942990792762079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4784545901257321057016105 3588409425942990792762079)
    ·
      refine ⟨5382614138914486189143119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3588409425942990792762079 5382614138914486189143119)
      ·
        refine ⟨8073921208371729283714679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5382614138914486189143119 8073921208371729283714679)
        ·
          refine ⟨12110881812557593925572019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8073921208371729283714679 12110881812557593925572019)
          ·
            refine ⟨18166322718836390888358029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12110881812557593925572019 18166322718836390888358029)
            ·
              refine ⟨6812371019563646583134261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18166322718836390888358029 6812371019563646583134261)
              ·
                refine ⟨638659783084091867168837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6812371019563646583134261 638659783084091867168837)
                ·
                  refine ⟨119748709328267225094157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638659783084091867168837 119748709328267225094157)
                  ·
                    rfl

theorem cell21_524722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_524722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524722 prefixEnd_524722 := by exact prefixLift 524722
  have htrace : WordTrace (prefixWord ++ tailWord_524722) baseStart_524722 baseEnd_524722 := by
    simpa [prefixWord, tailWord_524722, baseEnd_524722] using wordTrace_append hprefix tailTrace_524722
  have hstable : (prefixWord ++ tailWord_524722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524722).length < 2 ^ (prefixWord ++ tailWord_524722).sum := by decide
  have hdescent : baseEnd_524722 < baseStart_524722 := by decide
  rcases family_descends (prefixWord ++ tailWord_524722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524756 : List Nat := [2, 4, 1, 2, 2, 3, 1, 2, 4]
def baseStart_524756 : Nat := 118140960795 + 524756 * 2 ^ 59
def prefixEnd_524756 : Nat := 4983230072969 + 3 ^ 40 * 524756 * 2
def baseEnd_524756 : Nat := 119756468591490721527421

theorem tailTrace_524756 : CollatzResearch.WordTrace tailWord_524756 prefixEnd_524756 119756468591490721527421 := by
  unfold tailWord_524756
  simp only [CollatzResearch.WordTrace]
  refine ⟨9569711843453054017401061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12759615791270738689868081 9569711843453054017401061)
  ·
    refine ⟨1794320970647447628262699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9569711843453054017401061 1794320970647447628262699)
    ·
      refine ⟨2691481455971171442394049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1794320970647447628262699 2691481455971171442394049)
      ·
        refine ⟨2018611091978378581795537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2691481455971171442394049 2018611091978378581795537)
        ·
          refine ⟨1513958318983783936346653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2018611091978378581795537 1513958318983783936346653)
          ·
            refine ⟨567734369618918976129995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1513958318983783936346653 567734369618918976129995)
            ·
              refine ⟨851601554428378464194993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567734369618918976129995 851601554428378464194993)
              ·
                refine ⟨638701165821283848146245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851601554428378464194993 638701165821283848146245)
                ·
                  refine ⟨119756468591490721527421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638701165821283848146245 119756468591490721527421)
                  ·
                    rfl

theorem cell21_524756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_524756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524756 prefixEnd_524756 := by exact prefixLift 524756
  have htrace : WordTrace (prefixWord ++ tailWord_524756) baseStart_524756 baseEnd_524756 := by
    simpa [prefixWord, tailWord_524756, baseEnd_524756] using wordTrace_append hprefix tailTrace_524756
  have hstable : (prefixWord ++ tailWord_524756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524756).length < 2 ^ (prefixWord ++ tailWord_524756).sum := by decide
  have hdescent : baseEnd_524756 < baseStart_524756 := by decide
  rcases family_descends (prefixWord ++ tailWord_524756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524767 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 5]
def baseStart_524767 : Nat := 118140960795 + 524767 * 2 ^ 59
def prefixEnd_524767 : Nat := 4983230072969 + 3 ^ 40 * 524767 * 2
def baseEnd_524767 : Nat := 119758978941357146844065

theorem tailTrace_524767 : CollatzResearch.WordTrace tailWord_524767 prefixEnd_524767 119758978941357146844065 := by
  unfold tailWord_524767
  simp only [CollatzResearch.WordTrace]
  refine ⟨19139824889866256913452555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12759883259910837942301703 19139824889866256913452555)
  ·
    refine ⟨28709737334799385370178833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19139824889866256913452555 28709737334799385370178833)
    ·
      refine ⟨21532303001099539027634125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28709737334799385370178833 21532303001099539027634125)
      ·
        refine ⟨8074613625412327135362797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21532303001099539027634125 8074613625412327135362797)
        ·
          refine ⟨3027980109529622675761049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8074613625412327135362797 3027980109529622675761049)
          ·
            refine ⟨2270985082147217006820787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3027980109529622675761049 2270985082147217006820787)
            ·
              refine ⟨3406477623220825510231181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270985082147217006820787 3406477623220825510231181)
              ·
                refine ⟨1277429108707809566336693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3406477623220825510231181 1277429108707809566336693)
                ·
                  refine ⟨119758978941357146844065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1277429108707809566336693 119758978941357146844065)
                  ·
                    rfl

theorem cell21_524767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_524767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524767 prefixEnd_524767 := by exact prefixLift 524767
  have htrace : WordTrace (prefixWord ++ tailWord_524767) baseStart_524767 baseEnd_524767 := by
    simpa [prefixWord, tailWord_524767, baseEnd_524767] using wordTrace_append hprefix tailTrace_524767
  have hstable : (prefixWord ++ tailWord_524767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524767).length < 2 ^ (prefixWord ++ tailWord_524767).sum := by decide
  have hdescent : baseEnd_524767 < baseStart_524767 := by decide
  rcases family_descends (prefixWord ++ tailWord_524767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524801 : List Nat := [1, 2, 4, 1, 3, 1, 3, 3, 3]
def baseStart_524801 : Nat := 118140960795 + 524801 * 2 ^ 59
def prefixEnd_524801 : Nat := 4983230072969 + 3 ^ 40 * 524801 * 2
def baseEnd_524801 : Nat := 119766738204580643277329

theorem tailTrace_524801 : CollatzResearch.WordTrace tailWord_524801 prefixEnd_524801 119766738204580643277329 := by
  unfold tailWord_524801
  simp only [CollatzResearch.WordTrace]
  refine ⟨19141064971743080720190257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12760709981162053813460171 19141064971743080720190257)
  ·
    refine ⟨14355798728807310540142693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19141064971743080720190257 14355798728807310540142693)
    ·
      refine ⟨2691712261651370726276755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14355798728807310540142693 2691712261651370726276755)
      ·
        refine ⟨4037568392477056089415133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2691712261651370726276755 4037568392477056089415133)
        ·
          refine ⟨1514088147178896033530675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4037568392477056089415133 1514088147178896033530675)
          ·
            refine ⟨2271132220768344050296013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514088147178896033530675 2271132220768344050296013)
            ·
              refine ⟨851674582788129018861005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2271132220768344050296013 851674582788129018861005)
              ·
                refine ⟨319377968545548382072877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 851674582788129018861005 319377968545548382072877)
                ·
                  refine ⟨119766738204580643277329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319377968545548382072877 119766738204580643277329)
                  ·
                    rfl

theorem cell21_524801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 3].length) (baseStart_524801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524801 prefixEnd_524801 := by exact prefixLift 524801
  have htrace : WordTrace (prefixWord ++ tailWord_524801) baseStart_524801 baseEnd_524801 := by
    simpa [prefixWord, tailWord_524801, baseEnd_524801] using wordTrace_append hprefix tailTrace_524801
  have hstable : (prefixWord ++ tailWord_524801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524801).length < 2 ^ (prefixWord ++ tailWord_524801).sum := by decide
  have hdescent : baseEnd_524801 < baseStart_524801 := by decide
  rcases family_descends (prefixWord ++ tailWord_524801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524812 : List Nat := [2, 2, 1, 2, 4, 1, 9]
def baseStart_524812 : Nat := 118140960795 + 524812 * 2 ^ 59
def prefixEnd_524812 : Nat := 4983230072969 + 3 ^ 40 * 524812 * 2
def baseEnd_524812 : Nat := 13307694283827452065997

theorem tailTrace_524812 : CollatzResearch.WordTrace tailWord_524812 prefixEnd_524812 13307694283827452065997 := by
  unfold tailWord_524812
  simp only [CollatzResearch.WordTrace]
  refine ⟨9570733087351614799420345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12760977449802153065893793 9570733087351614799420345)
  ·
    refine ⟨7178049815513711099565259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9570733087351614799420345 7178049815513711099565259)
    ·
      refine ⟨10767074723270566649347889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7178049815513711099565259 10767074723270566649347889)
      ·
        refine ⟨8075306042452924987010917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10767074723270566649347889 8075306042452924987010917)
        ·
          refine ⟨1514119882959923435064547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8075306042452924987010917 1514119882959923435064547)
          ·
            refine ⟨2271179824439885152596821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514119882959923435064547 2271179824439885152596821)
            ·
              refine ⟨13307694283827452065997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2271179824439885152596821 13307694283827452065997)
              ·
                rfl

theorem cell21_524812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 9].length) (baseStart_524812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524812 prefixEnd_524812 := by exact prefixLift 524812
  have htrace : WordTrace (prefixWord ++ tailWord_524812) baseStart_524812 baseEnd_524812 := by
    simpa [prefixWord, tailWord_524812, baseEnd_524812] using wordTrace_append hprefix tailTrace_524812
  have hstable : (prefixWord ++ tailWord_524812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524812).length < 2 ^ (prefixWord ++ tailWord_524812).sum := by decide
  have hdescent : baseEnd_524812 < baseStart_524812 := by decide
  rcases family_descends (prefixWord ++ tailWord_524812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524829 : List Nat := [1, 4, 2, 2, 1, 3, 2, 6]
def baseStart_524829 : Nat := 118140960795 + 524829 * 2 ^ 59
def prefixEnd_524829 : Nat := 4983230072969 + 3 ^ 40 * 524829 * 2
def baseEnd_524829 : Nat := 39924376062019605603535

theorem tailTrace_524829 : CollatzResearch.WordTrace tailWord_524829 prefixEnd_524829 39924376062019605603535 := by
  unfold tailWord_524829
  simp only [CollatzResearch.WordTrace]
  refine ⟨19142086215641641502209541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12761390810427761001473027 19142086215641641502209541)
  ·
    refine ⟨3589141165432807781664289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19142086215641641502209541 3589141165432807781664289)
    ·
      refine ⟨2691855874074605836248217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3589141165432807781664289 2691855874074605836248217)
      ·
        refine ⟨2018891905555954377186163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2691855874074605836248217 2018891905555954377186163)
        ·
          refine ⟨3028337858333931565779245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018891905555954377186163 3028337858333931565779245)
          ·
            refine ⟨1135626696875224337167217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3028337858333931565779245 1135626696875224337167217)
            ·
              refine ⟨851720022656418252875413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135626696875224337167217 851720022656418252875413)
              ·
                refine ⟨39924376062019605603535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 851720022656418252875413 39924376062019605603535)
                ·
                  rfl

theorem cell21_524829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 6].length) (baseStart_524829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524829 prefixEnd_524829 := by exact prefixLift 524829
  have htrace : WordTrace (prefixWord ++ tailWord_524829) baseStart_524829 baseEnd_524829 := by
    simpa [prefixWord, tailWord_524829, baseEnd_524829] using wordTrace_append hprefix tailTrace_524829
  have hstable : (prefixWord ++ tailWord_524829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524829).length < 2 ^ (prefixWord ++ tailWord_524829).sum := by decide
  have hdescent : baseEnd_524829 < baseStart_524829 := by decide
  rcases family_descends (prefixWord ++ tailWord_524829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524874 : List Nat := [3, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_524874 : Nat := 118140960795 + 524874 * 2 ^ 59
def prefixEnd_524874 : Nat := 4983230072969 + 3 ^ 40 * 524874 * 2
def baseEnd_524874 : Nat := 119783397799148738560513

theorem tailTrace_524874 : CollatzResearch.WordTrace tailWord_524874 prefixEnd_524874 119783397799148738560513 := by
  unfold tailWord_524874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4785931875119653546899419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12762485000319076125065117 4785931875119653546899419)
  ·
    refine ⟨7178897812679480320349129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4785931875119653546899419 7178897812679480320349129)
    ·
      refine ⟨5384173359509610240261847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7178897812679480320349129 5384173359509610240261847)
      ·
        refine ⟨8076260039264415360392771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5384173359509610240261847 8076260039264415360392771)
        ·
          refine ⟨12114390058896623040589157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8076260039264415360392771 12114390058896623040589157)
          ·
            refine ⟨2271448136043116820110467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12114390058896623040589157 2271448136043116820110467)
            ·
              refine ⟨3407172204064675230165701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271448136043116820110467 3407172204064675230165701)
              ·
                refine ⟨638844788262126605656069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3407172204064675230165701 638844788262126605656069)
                ·
                  refine ⟨119783397799148738560513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638844788262126605656069 119783397799148738560513)
                  ·
                    rfl

theorem cell21_524874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_524874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524874 prefixEnd_524874 := by exact prefixLift 524874
  have htrace : WordTrace (prefixWord ++ tailWord_524874) baseStart_524874 baseEnd_524874 := by
    simpa [prefixWord, tailWord_524874, baseEnd_524874] using wordTrace_append hprefix tailTrace_524874
  have hstable : (prefixWord ++ tailWord_524874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524874).length < 2 ^ (prefixWord ++ tailWord_524874).sum := by decide
  have hdescent : baseEnd_524874 < baseStart_524874 := by decide
  rcases family_descends (prefixWord ++ tailWord_524874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524888 : List Nat := [2, 1, 2, 2, 1, 2, 5, 6]
def baseStart_524888 : Nat := 118140960795 + 524888 * 2 ^ 59
def prefixEnd_524888 : Nat := 4983230072969 + 3 ^ 40 * 524888 * 2
def baseEnd_524888 : Nat := 39928864263295941775717

theorem tailTrace_524888 : CollatzResearch.WordTrace tailWord_524888 prefixEnd_524888 39928864263295941775717 := by
  unfold tailWord_524888
  simp only [CollatzResearch.WordTrace]
  refine ⟨9572119061213947289303659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12762825414951929719071545 9572119061213947289303659)
  ·
    refine ⟨14358178591820920933955489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9572119061213947289303659 14358178591820920933955489)
    ·
      refine ⟨10768633943865690700466617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14358178591820920933955489 10768633943865690700466617)
      ·
        refine ⟨8076475457899268025349963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10768633943865690700466617 8076475457899268025349963)
        ·
          refine ⟨12114713186848902038024945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8076475457899268025349963 12114713186848902038024945)
          ·
            refine ⟨9086034890136676528518709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12114713186848902038024945 9086034890136676528518709)
            ·
              refine ⟨851815770950313424548629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9086034890136676528518709 851815770950313424548629)
              ·
                refine ⟨39928864263295941775717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 851815770950313424548629 39928864263295941775717)
                ·
                  rfl

theorem cell21_524888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_524888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524888 prefixEnd_524888 := by exact prefixLift 524888
  have htrace : WordTrace (prefixWord ++ tailWord_524888) baseStart_524888 baseEnd_524888 := by
    simpa [prefixWord, tailWord_524888, baseEnd_524888] using wordTrace_append hprefix tailTrace_524888
  have hstable : (prefixWord ++ tailWord_524888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524888).length < 2 ^ (prefixWord ++ tailWord_524888).sum := by decide
  have hdescent : baseEnd_524888 < baseStart_524888 := by decide
  rcases family_descends (prefixWord ++ tailWord_524888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524964 : List Nat := [2, 3, 1, 2, 2, 1, 3, 7]
def baseStart_524964 : Nat := 118140960795 + 524964 * 2 ^ 59
def prefixEnd_524964 : Nat := 4983230072969 + 3 ^ 40 * 524964 * 2
def baseEnd_524964 : Nat := 39934645675109527353443

theorem tailTrace_524964 : CollatzResearch.WordTrace tailWord_524964 prefixEnd_524964 39934645675109527353443 := by
  unfold tailWord_524964
  simp only [CollatzResearch.WordTrace]
  refine ⟨9573505035076279779186973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12764673380101706372249297 9573505035076279779186973)
  ·
    refine ⟨3590064388153604917195115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9573505035076279779186973 3590064388153604917195115)
    ·
      refine ⟨5385096582230407375792673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3590064388153604917195115 5385096582230407375792673)
      ·
        refine ⟨4038822436672805531844505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5385096582230407375792673 4038822436672805531844505)
        ·
          refine ⟨3029116827504604148883379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4038822436672805531844505 3029116827504604148883379)
          ·
            refine ⟨4543675241256906223325069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3029116827504604148883379 4543675241256906223325069)
            ·
              refine ⟨1703878215471339833746901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4543675241256906223325069 1703878215471339833746901)
              ·
                refine ⟨39934645675109527353443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1703878215471339833746901 39934645675109527353443)
                ·
                  rfl

theorem cell21_524964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_524964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524964 prefixEnd_524964 := by exact prefixLift 524964
  have htrace : WordTrace (prefixWord ++ tailWord_524964) baseStart_524964 baseEnd_524964 := by
    simpa [prefixWord, tailWord_524964, baseEnd_524964] using wordTrace_append hprefix tailTrace_524964
  have hstable : (prefixWord ++ tailWord_524964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524964).length < 2 ^ (prefixWord ++ tailWord_524964).sum := by decide
  have hdescent : baseEnd_524964 < baseStart_524964 := by decide
  rcases family_descends (prefixWord ++ tailWord_524964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524981 : List Nat := [1, 3, 3, 3, 1, 3, 7]
def baseStart_524981 : Nat := 118140960795 + 524981 * 2 ^ 59
def prefixEnd_524981 : Nat := 4983230072969 + 3 ^ 40 * 524981 * 2
def baseEnd_524981 : Nat := 13311979628548925586329

theorem tailTrace_524981 : CollatzResearch.WordTrace tailWord_524981 prefixEnd_524981 13311979628548925586329 := by
  unfold tailWord_524981
  simp only [CollatzResearch.WordTrace]
  refine ⟨19147630111090971461742797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12765086740727314307828531 19147630111090971461742797)
  ·
    refine ⟨7180361291659114298153549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19147630111090971461742797 7180361291659114298153549)
    ·
      refine ⟨2692635484372167861807581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7180361291659114298153549 2692635484372167861807581)
      ·
        refine ⟨1009738306639562948177843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2692635484372167861807581 1009738306639562948177843)
        ·
          refine ⟨1514607459959344422266765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009738306639562948177843 1514607459959344422266765)
          ·
            refine ⟨567977797484754158350037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1514607459959344422266765 567977797484754158350037)
            ·
              refine ⟨13311979628548925586329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 567977797484754158350037 13311979628548925586329)
              ·
                rfl

theorem cell21_524981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 7].length) (baseStart_524981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_524981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_524981 prefixEnd_524981 := by exact prefixLift 524981
  have htrace : WordTrace (prefixWord ++ tailWord_524981) baseStart_524981 baseEnd_524981 := by
    simpa [prefixWord, tailWord_524981, baseEnd_524981] using wordTrace_append hprefix tailTrace_524981
  have hstable : (prefixWord ++ tailWord_524981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524981).length < 2 ^ (prefixWord ++ tailWord_524981).sum := by decide
  have hdescent : baseEnd_524981 < baseStart_524981 := by decide
  rcases family_descends (prefixWord ++ tailWord_524981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525088 : List Nat := [2, 1, 1, 5, 1, 2, 1, 5, 3]
def baseStart_525088 : Nat := 118140960795 + 525088 * 2 ^ 59
def prefixEnd_525088 : Nat := 4983230072969 + 3 ^ 40 * 525088 * 2
def baseEnd_525088 : Nat := 119832235514731921993409

theorem tailTrace_525088 : CollatzResearch.WordTrace tailWord_525088 prefixEnd_525088 119832235514731921993409 := by
  unfold tailWord_525088
  simp only [CollatzResearch.WordTrace]
  refine ⟨9575766360851664367943959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12767688481135552490591945 9575766360851664367943959)
  ·
    refine ⟨14363649541277496551915939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9575766360851664367943959 14363649541277496551915939)
    ·
      refine ⟨21545474311916244827873909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14363649541277496551915939 21545474311916244827873909)
      ·
        refine ⟨2019888216742147952613179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21545474311916244827873909 2019888216742147952613179)
        ·
          refine ⟨3029832325113221928919769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2019888216742147952613179 3029832325113221928919769)
          ·
            refine ⟨2272374243834916446689827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3029832325113221928919769 2272374243834916446689827)
            ·
              refine ⟨3408561365752374670034741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272374243834916446689827 3408561365752374670034741)
              ·
                refine ⟨319552628039285125315757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3408561365752374670034741 319552628039285125315757)
                ·
                  refine ⟨119832235514731921993409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319552628039285125315757 119832235514731921993409)
                  ·
                    rfl

theorem cell21_525088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 3].length) (baseStart_525088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525088 prefixEnd_525088 := by exact prefixLift 525088
  have htrace : WordTrace (prefixWord ++ tailWord_525088) baseStart_525088 baseEnd_525088 := by
    simpa [prefixWord, tailWord_525088, baseEnd_525088] using wordTrace_append hprefix tailTrace_525088
  have hstable : (prefixWord ++ tailWord_525088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525088).length < 2 ^ (prefixWord ++ tailWord_525088).sum := by decide
  have hdescent : baseEnd_525088 < baseStart_525088 := by decide
  rcases family_descends (prefixWord ++ tailWord_525088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525119 : List Nat := [1, 1, 2, 2, 5, 2, 3, 1, 4]
def baseStart_525119 : Nat := 118140960795 + 525119 * 2 ^ 59
def prefixEnd_525119 : Nat := 4983230072969 + 3 ^ 40 * 525119 * 2
def baseEnd_525119 : Nat := 119839310137082756976679

theorem tailTrace_525119 : CollatzResearch.WordTrace tailWord_525119 prefixEnd_525119 119839310137082756976679 := by
  unfold tailWord_525119
  simp only [CollatzResearch.WordTrace]
  refine ⟨19152663384591021030266411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12768442256394014020177607 19152663384591021030266411)
  ·
    refine ⟨28728995076886531545399617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19152663384591021030266411 28728995076886531545399617)
    ·
      refine ⟨21546746307664898659049713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28728995076886531545399617 21546746307664898659049713)
      ·
        refine ⟨16160059730748673994287285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21546746307664898659049713 16160059730748673994287285)
        ·
          refine ⟨1515005599757688186964433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16160059730748673994287285 1515005599757688186964433)
          ·
            refine ⟨1136254199818266140223325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515005599757688186964433 1136254199818266140223325)
            ·
              refine ⟨426095324931849802583747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1136254199818266140223325 426095324931849802583747)
              ·
                refine ⟨639142987397774703875621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426095324931849802583747 639142987397774703875621)
                ·
                  refine ⟨119839310137082756976679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 639142987397774703875621 119839310137082756976679)
                  ·
                    rfl

theorem cell21_525119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 4].length) (baseStart_525119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525119 prefixEnd_525119 := by exact prefixLift 525119
  have htrace : WordTrace (prefixWord ++ tailWord_525119) baseStart_525119 baseEnd_525119 := by
    simpa [prefixWord, tailWord_525119, baseEnd_525119] using wordTrace_append hprefix tailTrace_525119
  have hstable : (prefixWord ++ tailWord_525119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525119).length < 2 ^ (prefixWord ++ tailWord_525119).sum := by decide
  have hdescent : baseEnd_525119 < baseStart_525119 := by decide
  rcases family_descends (prefixWord ++ tailWord_525119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525130 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_525130 : Nat := 118140960795 + 525130 * 2 ^ 59
def prefixEnd_525130 : Nat := 4983230072969 + 3 ^ 40 * 525130 * 2
def baseEnd_525130 : Nat := 119841820486949182293323

theorem tailTrace_525130 : CollatzResearch.WordTrace tailWord_525130 prefixEnd_525130 119841820486949182293323 := by
  unfold tailWord_525130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4788266146887792477229211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12768709725034113272611229 4788266146887792477229211)
  ·
    refine ⟨7182399220331688715843817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4788266146887792477229211 7182399220331688715843817)
    ·
      refine ⟨5386799415248766536882863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7182399220331688715843817 5386799415248766536882863)
      ·
        refine ⟨8080199122873149805324295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5386799415248766536882863 8080199122873149805324295)
        ·
          refine ⟨12120298684309724707986443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8080199122873149805324295 12120298684309724707986443)
          ·
            refine ⟨18180448026464587061979665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12120298684309724707986443 18180448026464587061979665)
            ·
              refine ⟨13635336019848440296484749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18180448026464587061979665 13635336019848440296484749)
              ·
                refine ⟨5113251007443165111181781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13635336019848440296484749 5113251007443165111181781)
                ·
                  refine ⟨119841820486949182293323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5113251007443165111181781 119841820486949182293323)
                  ·
                    rfl

theorem cell21_525130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_525130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525130 prefixEnd_525130 := by exact prefixLift 525130
  have htrace : WordTrace (prefixWord ++ tailWord_525130) baseStart_525130 baseEnd_525130 := by
    simpa [prefixWord, tailWord_525130, baseEnd_525130] using wordTrace_append hprefix tailTrace_525130
  have hstable : (prefixWord ++ tailWord_525130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525130).length < 2 ^ (prefixWord ++ tailWord_525130).sum := by decide
  have hdescent : baseEnd_525130 < baseStart_525130 := by decide
  rcases family_descends (prefixWord ++ tailWord_525130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525192 : List Nat := [2, 1, 3, 3, 2, 1, 2, 7]
def baseStart_525192 : Nat := 118140960795 + 525192 * 2 ^ 59
def prefixEnd_525192 : Nat := 4983230072969 + 3 ^ 40 * 525192 * 2
def baseEnd_525192 : Nat := 39951989910550284086621

theorem tailTrace_525192 : CollatzResearch.WordTrace tailWord_525192 prefixEnd_525192 39951989910550284086621 := by
  unfold tailWord_525192
  simp only [CollatzResearch.WordTrace]
  refine ⟨9577662956663277248836915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12770217275551036331782553 9577662956663277248836915)
  ·
    refine ⟨14366494434994915873255373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9577662956663277248836915 14366494434994915873255373)
    ·
      refine ⟨5387435413123093452470765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14366494434994915873255373 5387435413123093452470765)
      ·
        refine ⟨2020288279921160044676537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5387435413123093452470765 2020288279921160044676537)
        ·
          refine ⟨1515216209940870033507403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2020288279921160044676537 1515216209940870033507403)
          ·
            refine ⟨2272824314911305050261105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515216209940870033507403 2272824314911305050261105)
            ·
              refine ⟨1704618236183478787695829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2272824314911305050261105 1704618236183478787695829)
              ·
                refine ⟨39951989910550284086621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1704618236183478787695829 39951989910550284086621)
                ·
                  rfl

theorem cell21_525192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_525192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525192 prefixEnd_525192 := by exact prefixLift 525192
  have htrace : WordTrace (prefixWord ++ tailWord_525192) baseStart_525192 baseEnd_525192 := by
    simpa [prefixWord, tailWord_525192, baseEnd_525192] using wordTrace_append hprefix tailTrace_525192
  have hstable : (prefixWord ++ tailWord_525192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525192).length < 2 ^ (prefixWord ++ tailWord_525192).sum := by decide
  have hdescent : baseEnd_525192 < baseStart_525192 := by decide
  rcases family_descends (prefixWord ++ tailWord_525192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525268 : List Nat := [2, 4, 1, 2, 1, 3, 8]
def baseStart_525268 : Nat := 118140960795 + 525268 * 2 ^ 59
def prefixEnd_525268 : Nat := 4983230072969 + 3 ^ 40 * 525268 * 2
def baseEnd_525268 : Nat := 13319257107454623221449

theorem tailTrace_525268 : CollatzResearch.WordTrace tailWord_525268 prefixEnd_525268 13319257107454623221449 := by
  unfold tailWord_525268
  simp only [CollatzResearch.WordTrace]
  refine ⟨9579048930525609738720229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12772065240700812984960305 9579048930525609738720229)
  ·
    refine ⟨1796071674473551826010043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9579048930525609738720229 1796071674473551826010043)
    ·
      refine ⟨2694107511710327739015065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1796071674473551826010043 2694107511710327739015065)
      ·
        refine ⟨2020580633782745804261299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2694107511710327739015065 2020580633782745804261299)
        ·
          refine ⟨3030870950674118706391949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2020580633782745804261299 3030870950674118706391949)
          ·
            refine ⟨1136576606502794514896981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3030870950674118706391949 1136576606502794514896981)
            ·
              refine ⟨13319257107454623221449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1136576606502794514896981 13319257107454623221449)
              ·
                rfl

theorem cell21_525268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 8].length) (baseStart_525268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525268 prefixEnd_525268 := by exact prefixLift 525268
  have htrace : WordTrace (prefixWord ++ tailWord_525268) baseStart_525268 baseEnd_525268 := by
    simpa [prefixWord, tailWord_525268, baseEnd_525268] using wordTrace_append hprefix tailTrace_525268
  have hstable : (prefixWord ++ tailWord_525268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525268).length < 2 ^ (prefixWord ++ tailWord_525268).sum := by decide
  have hdescent : baseEnd_525268 < baseStart_525268 := by decide
  rcases family_descends (prefixWord ++ tailWord_525268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525302 : List Nat := [5, 1, 1, 1, 3, 3, 2, 5]
def baseStart_525302 : Nat := 118140960795 + 525302 * 2 ^ 59
def prefixEnd_525302 : Nat := 4983230072969 + 3 ^ 40 * 525302 * 2
def baseEnd_525302 : Nat := 39960357743438368475435

theorem tailTrace_525302 : CollatzResearch.WordTrace tailWord_525302 prefixEnd_525302 39960357743438368475435 := by
  unfold tailWord_525302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1197458621433002705261135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12772891961952028856118773 1197458621433002705261135)
  ·
    refine ⟨1796187932149504057891703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1197458621433002705261135 1796187932149504057891703)
    ·
      refine ⟨2694281898224256086837555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1796187932149504057891703 2694281898224256086837555)
      ·
        refine ⟨4041422847336384130256333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2694281898224256086837555 4041422847336384130256333)
        ·
          refine ⟨1515533567751144048846125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4041422847336384130256333 1515533567751144048846125)
          ·
            refine ⟨568325087906679018317297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1515533567751144048846125 568325087906679018317297)
            ·
              refine ⟨426243815930009263737973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568325087906679018317297 426243815930009263737973)
              ·
                refine ⟨39960357743438368475435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 426243815930009263737973 39960357743438368475435)
                ·
                  rfl

theorem cell21_525302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_525302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525302 prefixEnd_525302 := by exact prefixLift 525302
  have htrace : WordTrace (prefixWord ++ tailWord_525302) baseStart_525302 baseEnd_525302 := by
    simpa [prefixWord, tailWord_525302, baseEnd_525302] using wordTrace_append hprefix tailTrace_525302
  have hstable : (prefixWord ++ tailWord_525302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525302).length < 2 ^ (prefixWord ++ tailWord_525302).sum := by decide
  have hdescent : baseEnd_525302 < baseStart_525302 := by decide
  rcases family_descends (prefixWord ++ tailWord_525302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525313 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 6]
def baseStart_525313 : Nat := 118140960795 + 525313 * 2 ^ 59
def prefixEnd_525313 : Nat := 4983230072969 + 3 ^ 40 * 525313 * 2
def baseEnd_525313 : Nat := 119883583580181530742949

theorem tailTrace_525313 : CollatzResearch.WordTrace tailWord_525313 prefixEnd_525313 119883583580181530742949 := by
  unfold tailWord_525313
  simp only [CollatzResearch.WordTrace]
  refine ⟨19159739145888192162828593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12773159430592128108552395 19159739145888192162828593)
  ·
    refine ⟨14369804359416144122121445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19159739145888192162828593 14369804359416144122121445)
    ·
      refine ⟨2694338317390527022897771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14369804359416144122121445 2694338317390527022897771)
      ·
        refine ⟨4041507476085790534346657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2694338317390527022897771 4041507476085790534346657)
        ·
          refine ⟨3031130607064342900759993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4041507476085790534346657 3031130607064342900759993)
          ·
            refine ⟨2273347955298257175569995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3031130607064342900759993 2273347955298257175569995)
            ·
              refine ⟨3410021932947385763354993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273347955298257175569995 3410021932947385763354993)
              ·
                refine ⟨2557516449710539322516245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3410021932947385763354993 2557516449710539322516245)
                ·
                  refine ⟨119883583580181530742949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2557516449710539322516245 119883583580181530742949)
                  ·
                    rfl

theorem cell21_525313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_525313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525313 prefixEnd_525313 := by exact prefixLift 525313
  have htrace : WordTrace (prefixWord ++ tailWord_525313) baseStart_525313 baseEnd_525313 := by
    simpa [prefixWord, tailWord_525313, baseEnd_525313] using wordTrace_append hprefix tailTrace_525313
  have hstable : (prefixWord ++ tailWord_525313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525313).length < 2 ^ (prefixWord ++ tailWord_525313).sum := by decide
  have hdescent : baseEnd_525313 < baseStart_525313 := by decide
  rcases family_descends (prefixWord ++ tailWord_525313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525333 : List Nat := [1, 3, 2, 1, 4, 2, 3, 2, 3]
def baseStart_525333 : Nat := 118140960795 + 525333 * 2 ^ 59
def prefixEnd_525333 : Nat := 4983230072969 + 3 ^ 40 * 525333 * 2
def baseEnd_525333 : Nat := 119888147852665940409575

theorem tailTrace_525333 : CollatzResearch.WordTrace tailWord_525333 prefixEnd_525333 119888147852665940409575 := by
  unfold tailWord_525333
  simp only [CollatzResearch.WordTrace]
  refine ⟨19160468605815735578556653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12773645737210490385704435 19160468605815735578556653)
  ·
    refine ⟨7185175727180900841958745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19160468605815735578556653 7185175727180900841958745)
    ·
      refine ⟨5388881795385675631469059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7185175727180900841958745 5388881795385675631469059)
      ·
        refine ⟨8083322693078513447203589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5388881795385675631469059 8083322693078513447203589)
        ·
          refine ⟨1515623004952221271350673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8083322693078513447203589 1515623004952221271350673)
          ·
            refine ⟨1136717253714165953513005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515623004952221271350673 1136717253714165953513005)
            ·
              refine ⟨426268970142812232567377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1136717253714165953513005 426268970142812232567377)
              ·
                refine ⟨319701727607109174425533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426268970142812232567377 319701727607109174425533)
                ·
                  refine ⟨119888147852665940409575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319701727607109174425533 119888147852665940409575)
                  ·
                    rfl

theorem cell21_525333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_525333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525333 prefixEnd_525333 := by exact prefixLift 525333
  have htrace : WordTrace (prefixWord ++ tailWord_525333) baseStart_525333 baseEnd_525333 := by
    simpa [prefixWord, tailWord_525333, baseEnd_525333] using wordTrace_append hprefix tailTrace_525333
  have hstable : (prefixWord ++ tailWord_525333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525333).length < 2 ^ (prefixWord ++ tailWord_525333).sum := by decide
  have hdescent : baseEnd_525333 < baseStart_525333 := by decide
  rcases family_descends (prefixWord ++ tailWord_525333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525347 : List Nat := [1, 1, 1, 4, 3, 4, 2, 1, 4]
def baseStart_525347 : Nat := 118140960795 + 525347 * 2 ^ 59
def prefixEnd_525347 : Nat := 4983230072969 + 3 ^ 40 * 525347 * 2
def baseEnd_525347 : Nat := 119891342843405027176213

theorem tailTrace_525347 : CollatzResearch.WordTrace tailWord_525347 prefixEnd_525347 119891342843405027176213 := by
  unfold tailWord_525347
  simp only [CollatzResearch.WordTrace]
  refine ⟨19160979227765015969566295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12773986151843343979710863 19160979227765015969566295)
  ·
    refine ⟨28741468841647523954349443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19160979227765015969566295 28741468841647523954349443)
    ·
      refine ⟨43112203262471285931524165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28741468841647523954349443 43112203262471285931524165)
      ·
        refine ⟨8083538111713366112160781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43112203262471285931524165 8083538111713366112160781)
        ·
          refine ⟨3031326791892512292060293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8083538111713366112160781 3031326791892512292060293)
          ·
            refine ⟨568373773479846054761305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3031326791892512292060293 568373773479846054761305)
            ·
              refine ⟨426280330109884541070979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568373773479846054761305 426280330109884541070979)
              ·
                refine ⟨639420495164826811606469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426280330109884541070979 639420495164826811606469)
                ·
                  refine ⟨119891342843405027176213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 639420495164826811606469 119891342843405027176213)
                  ·
                    rfl

theorem cell21_525347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 4].length) (baseStart_525347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525347 prefixEnd_525347 := by exact prefixLift 525347
  have htrace : WordTrace (prefixWord ++ tailWord_525347) baseStart_525347 baseEnd_525347 := by
    simpa [prefixWord, tailWord_525347, baseEnd_525347] using wordTrace_append hprefix tailTrace_525347
  have hstable : (prefixWord ++ tailWord_525347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525347).length < 2 ^ (prefixWord ++ tailWord_525347).sum := by decide
  have hdescent : baseEnd_525347 < baseStart_525347 := by decide
  rcases family_descends (prefixWord ++ tailWord_525347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525375 : List Nat := [1, 1, 2, 2, 3, 1, 1, 7, 3]
def baseStart_525375 : Nat := 118140960795 + 525375 * 2 ^ 59
def prefixEnd_525375 : Nat := 4983230072969 + 3 ^ 40 * 525375 * 2
def baseEnd_525375 : Nat := 119897732824883200709489

theorem tailTrace_525375 : CollatzResearch.WordTrace tailWord_525375 prefixEnd_525375 119897732824883200709489 := by
  unfold tailWord_525375
  simp only [CollatzResearch.WordTrace]
  refine ⟨19162000471663576751585579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12774666981109051167723719 19162000471663576751585579)
  ·
    refine ⟨28743000707495365127378369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19162000471663576751585579 28743000707495365127378369)
    ·
      refine ⟨21557250530621523845533777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28743000707495365127378369 21557250530621523845533777)
      ·
        refine ⟨16167937897966142884150333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21557250530621523845533777 16167937897966142884150333)
        ·
          refine ⟨6062976711737303581556375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16167937897966142884150333 6062976711737303581556375)
          ·
            refine ⟨9094465067605955372334563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6062976711737303581556375 9094465067605955372334563)
            ·
              refine ⟨13641697601408933058501845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9094465067605955372334563 13641697601408933058501845)
              ·
                refine ⟨319727287533021868558637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13641697601408933058501845 319727287533021868558637)
                ·
                  refine ⟨119897732824883200709489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319727287533021868558637 119897732824883200709489)
                  ·
                    rfl

theorem cell21_525375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 3].length) (baseStart_525375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525375 prefixEnd_525375 := by exact prefixLift 525375
  have htrace : WordTrace (prefixWord ++ tailWord_525375) baseStart_525375 baseEnd_525375 := by
    simpa [prefixWord, tailWord_525375, baseEnd_525375] using wordTrace_append hprefix tailTrace_525375
  have hstable : (prefixWord ++ tailWord_525375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525375).length < 2 ^ (prefixWord ++ tailWord_525375).sum := by decide
  have hdescent : baseEnd_525375 < baseStart_525375 := by decide
  rcases family_descends (prefixWord ++ tailWord_525375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525420 : List Nat := [2, 2, 1, 1, 3, 2, 5, 5]
def baseStart_525420 : Nat := 118140960795 + 525420 * 2 ^ 59
def prefixEnd_525420 : Nat := 4983230072969 + 3 ^ 40 * 525420 * 2
def baseEnd_525420 : Nat := 39969334145991040819799

theorem tailTrace_525420 : CollatzResearch.WordTrace tailWord_525420 prefixEnd_525420 39969334145991040819799 := by
  unfold tailWord_525420
  simp only [CollatzResearch.WordTrace]
  refine ⟨9581820878250274718486857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12775761171000366291315809 9581820878250274718486857)
  ·
    refine ⟨7186365658687706038865143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9581820878250274718486857 7186365658687706038865143)
    ·
      refine ⟨10779548488031559058297715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7186365658687706038865143 10779548488031559058297715)
      ·
        refine ⟨16169322732047338587446573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10779548488031559058297715 16169322732047338587446573)
        ·
          refine ⟨6063496024517751970292465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16169322732047338587446573 6063496024517751970292465)
          ·
            refine ⟨4547622018388313977719349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6063496024517751970292465 4547622018388313977719349)
            ·
              refine ⟨426339564223904435411189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4547622018388313977719349 426339564223904435411189)
              ·
                refine ⟨39969334145991040819799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 426339564223904435411189 39969334145991040819799)
                ·
                  rfl

theorem cell21_525420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_525420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525420 prefixEnd_525420 := by exact prefixLift 525420
  have htrace : WordTrace (prefixWord ++ tailWord_525420) baseStart_525420 baseEnd_525420 := by
    simpa [prefixWord, tailWord_525420, baseEnd_525420] using wordTrace_append hprefix tailTrace_525420
  have hstable : (prefixWord ++ tailWord_525420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525420).length < 2 ^ (prefixWord ++ tailWord_525420).sum := by decide
  have hdescent : baseEnd_525420 < baseStart_525420 := by decide
  rcases family_descends (prefixWord ++ tailWord_525420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525482 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_525482 : Nat := 118140960795 + 525482 * 2 ^ 59
def prefixEnd_525482 : Nat := 4983230072969 + 3 ^ 40 * 525482 * 2
def baseEnd_525482 : Nat := 119922151682674792425937

theorem tailTrace_525482 : CollatzResearch.WordTrace tailWord_525482 prefixEnd_525482 119922151682674792425937 := by
  unfold tailWord_525482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4791475770568983506432675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12777268721517289350487133 4791475770568983506432675)
  ·
    refine ⟨7187213655853475259649013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4791475770568983506432675 7187213655853475259649013)
    ·
      refine ⟨673801280236263305592095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7187213655853475259649013 673801280236263305592095)
      ·
        refine ⟨1010701920354394958388143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673801280236263305592095 1010701920354394958388143)
        ·
          refine ⟨1516052880531592437582215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010701920354394958388143 1516052880531592437582215)
          ·
            refine ⟨2274079320797388656373323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516052880531592437582215 2274079320797388656373323)
            ·
              refine ⟨3411118981196082984559985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2274079320797388656373323 3411118981196082984559985)
              ·
                refine ⟨2558339235897062238419989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3411118981196082984559985 2558339235897062238419989)
                ·
                  refine ⟨119922151682674792425937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2558339235897062238419989 119922151682674792425937)
                  ·
                    rfl

theorem cell21_525482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_525482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525482 prefixEnd_525482 := by exact prefixLift 525482
  have htrace : WordTrace (prefixWord ++ tailWord_525482) baseStart_525482 baseEnd_525482 := by
    simpa [prefixWord, tailWord_525482, baseEnd_525482] using wordTrace_append hprefix tailTrace_525482
  have hstable : (prefixWord ++ tailWord_525482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525482).length < 2 ^ (prefixWord ++ tailWord_525482).sum := by decide
  have hdescent : baseEnd_525482 < baseStart_525482 := by decide
  rcases family_descends (prefixWord ++ tailWord_525482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525572 : List Nat := [2, 3, 2, 2, 2, 1, 3, 6]
def baseStart_525572 : Nat := 118140960795 + 525572 * 2 ^ 59
def prefixEnd_525572 : Nat := 4983230072969 + 3 ^ 40 * 525572 * 2
def baseEnd_525572 : Nat := 39980896969618211975251

theorem tailTrace_525572 : CollatzResearch.WordTrace tailWord_525572 prefixEnd_525572 39980896969618211975251 := by
  unfold tailWord_525572
  simp only [CollatzResearch.WordTrace]
  refine ⟨9584592825974939698253485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12779457101299919597671313 9584592825974939698253485)
  ·
    refine ⟨3594222309740602386845057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9584592825974939698253485 3594222309740602386845057)
    ·
      refine ⟨2695666732305451790133793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3594222309740602386845057 2695666732305451790133793)
      ·
        refine ⟨2021750049229088842600345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2695666732305451790133793 2021750049229088842600345)
        ·
          refine ⟨1516312536921816631950259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2021750049229088842600345 1516312536921816631950259)
          ·
            refine ⟨2274468805382724947925389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516312536921816631950259 2274468805382724947925389)
            ·
              refine ⟨852925802018521855472021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2274468805382724947925389 852925802018521855472021)
              ·
                refine ⟨39980896969618211975251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 852925802018521855472021 39980896969618211975251)
                ·
                  rfl

theorem cell21_525572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_525572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525572 prefixEnd_525572 := by exact prefixLift 525572
  have htrace : WordTrace (prefixWord ++ tailWord_525572) baseStart_525572 baseEnd_525572 := by
    simpa [prefixWord, tailWord_525572, baseEnd_525572] using wordTrace_append hprefix tailTrace_525572
  have hstable : (prefixWord ++ tailWord_525572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525572).length < 2 ^ (prefixWord ++ tailWord_525572).sum := by decide
  have hdescent : baseEnd_525572 < baseStart_525572 := by decide
  rcases family_descends (prefixWord ++ tailWord_525572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525603 : List Nat := [1, 1, 1, 4, 2, 3, 1, 5, 3]
def baseStart_525603 : Nat := 118140960795 + 525603 * 2 ^ 59
def prefixEnd_525603 : Nat := 4983230072969 + 3 ^ 40 * 525603 * 2
def baseEnd_525603 : Nat := 119949765531205470909023

theorem tailTrace_525603 : CollatzResearch.WordTrace tailWord_525603 prefixEnd_525603 119949765531205470909023 := by
  unfold tailWord_525603
  simp only [CollatzResearch.WordTrace]
  refine ⟨19170316314837571690885463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12780210876558381127256975 19170316314837571690885463)
  ·
    refine ⟨28755474472256357536328195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19170316314837571690885463 28755474472256357536328195)
    ·
      refine ⟨43133211708384536304492293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28755474472256357536328195 43133211708384536304492293)
      ·
        refine ⟨8087477195322100557092305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43133211708384536304492293 8087477195322100557092305)
        ·
          refine ⟨6065607896491575417819229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8087477195322100557092305 6065607896491575417819229)
          ·
            refine ⟨2274602961184340781682211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6065607896491575417819229 2274602961184340781682211)
            ·
              refine ⟨3411904441776511172523317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2274602961184340781682211 3411904441776511172523317)
              ·
                refine ⟨319866041416547922424061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3411904441776511172523317 319866041416547922424061)
                ·
                  refine ⟨119949765531205470909023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319866041416547922424061 119949765531205470909023)
                  ·
                    rfl

theorem cell21_525603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 3].length) (baseStart_525603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525603 prefixEnd_525603 := by exact prefixLift 525603
  have htrace : WordTrace (prefixWord ++ tailWord_525603) baseStart_525603 baseEnd_525603 := by
    simpa [prefixWord, tailWord_525603, baseEnd_525603] using wordTrace_append hprefix tailTrace_525603
  have hstable : (prefixWord ++ tailWord_525603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525603).length < 2 ^ (prefixWord ++ tailWord_525603).sum := by decide
  have hdescent : baseEnd_525603 < baseStart_525603 := by decide
  rcases family_descends (prefixWord ++ tailWord_525603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525617 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 6]
def baseStart_525617 : Nat := 118140960795 + 525617 * 2 ^ 59
def prefixEnd_525617 : Nat := 4983230072969 + 3 ^ 40 * 525617 * 2
def baseEnd_525617 : Nat := 119952960521944557675661

theorem tailTrace_525617 : CollatzResearch.WordTrace tailWord_525617 prefixEnd_525617 119952960521944557675661 := by
  unfold tailWord_525617
  simp only [CollatzResearch.WordTrace]
  refine ⟨19170826936786852081895105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12780551291191234721263403 19170826936786852081895105)
  ·
    refine ⟨14378120202590139061421329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19170826936786852081895105 14378120202590139061421329)
    ·
      refine ⟨10783590151942604296065997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14378120202590139061421329 10783590151942604296065997)
      ·
        refine ⟨4043846306978476611024749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10783590151942604296065997 4043846306978476611024749)
        ·
          refine ⟨1516442365116928729134281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4043846306978476611024749 1516442365116928729134281)
          ·
            refine ⟨1137331773837696546850711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1516442365116928729134281 1137331773837696546850711)
            ·
              refine ⟨1705997660756544820276067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137331773837696546850711 1705997660756544820276067)
              ·
                refine ⟨2558996491134817230414101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705997660756544820276067 2558996491134817230414101)
                ·
                  refine ⟨119952960521944557675661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2558996491134817230414101 119952960521944557675661)
                  ·
                    rfl

theorem cell21_525617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_525617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525617 prefixEnd_525617 := by exact prefixLift 525617
  have htrace : WordTrace (prefixWord ++ tailWord_525617) baseStart_525617 baseEnd_525617 := by
    simpa [prefixWord, tailWord_525617, baseEnd_525617] using wordTrace_append hprefix tailTrace_525617
  have hstable : (prefixWord ++ tailWord_525617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525617).length < 2 ^ (prefixWord ++ tailWord_525617).sum := by decide
  have hdescent : baseEnd_525617 < baseStart_525617 := by decide
  rcases family_descends (prefixWord ++ tailWord_525617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525620 : List Nat := [2, 5, 1, 1, 1, 1, 1, 6, 3]
def baseStart_525620 : Nat := 118140960795 + 525620 * 2 ^ 59
def prefixEnd_525620 : Nat := 4983230072969 + 3 ^ 40 * 525620 * 2
def baseEnd_525620 : Nat := 119953645162817219125655

theorem tailTrace_525620 : CollatzResearch.WordTrace tailWord_525620 prefixEnd_525620 119953645162817219125655 := by
  unfold tailWord_525620
  simp only [CollatzResearch.WordTrace]
  refine ⟨9585468177887991797127157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12780624237183989062836209 9585468177887991797127157)
  ·
    refine ⟨898637641676999230980671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9585468177887991797127157 898637641676999230980671)
    ·
      refine ⟨1347956462515498846471007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 898637641676999230980671 1347956462515498846471007)
      ·
        refine ⟨2021934693773248269706511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1347956462515498846471007 2021934693773248269706511)
        ·
          refine ⟨3032902040659872404559767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2021934693773248269706511 3032902040659872404559767)
          ·
            refine ⟨4549353060989808606839651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3032902040659872404559767 4549353060989808606839651)
            ·
              refine ⟨6824029591484712910259477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4549353060989808606839651 6824029591484712910259477)
              ·
                refine ⟨319876387100845917668413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6824029591484712910259477 319876387100845917668413)
                ·
                  refine ⟨119953645162817219125655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319876387100845917668413 119953645162817219125655)
                  ·
                    rfl

theorem cell21_525620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_525620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525620 prefixEnd_525620 := by exact prefixLift 525620
  have htrace : WordTrace (prefixWord ++ tailWord_525620) baseStart_525620 baseEnd_525620 := by
    simpa [prefixWord, tailWord_525620, baseEnd_525620] using wordTrace_append hprefix tailTrace_525620
  have hstable : (prefixWord ++ tailWord_525620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525620).length < 2 ^ (prefixWord ++ tailWord_525620).sum := by decide
  have hdescent : baseEnd_525620 < baseStart_525620 := by decide
  rcases family_descends (prefixWord ++ tailWord_525620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525693 : List Nat := [1, 4, 1, 1, 2, 2, 3, 3, 4]
def baseStart_525693 : Nat := 118140960795 + 525693 * 2 ^ 59
def prefixEnd_525693 : Nat := 4983230072969 + 3 ^ 40 * 525693 * 2
def baseEnd_525693 : Nat := 119970304757385314408839

theorem tailTrace_525693 : CollatzResearch.WordTrace tailWord_525693 prefixEnd_525693 119970304757385314408839 := by
  unfold tailWord_525693
  simp only [CollatzResearch.WordTrace]
  refine ⟨19173598884511517061661733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12782399256341011374441155 19173598884511517061661733)
  ·
    refine ⟨3595049790845909449061575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19173598884511517061661733 3595049790845909449061575)
    ·
      refine ⟨5392574686268864173592363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3595049790845909449061575 5392574686268864173592363)
      ·
        refine ⟨8088862029403296260388545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5392574686268864173592363 8088862029403296260388545)
        ·
          refine ⟨6066646522052472195291409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8088862029403296260388545 6066646522052472195291409)
          ·
            refine ⟨4549984891539354146468557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6066646522052472195291409 4549984891539354146468557)
            ·
              refine ⟨1706244334327257804925709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4549984891539354146468557 1706244334327257804925709)
              ·
                refine ⟨639841625372721676847141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1706244334327257804925709 639841625372721676847141)
                ·
                  refine ⟨119970304757385314408839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 639841625372721676847141 119970304757385314408839)
                  ·
                    rfl

theorem cell21_525693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_525693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525693 prefixEnd_525693 := by exact prefixLift 525693
  have htrace : WordTrace (prefixWord ++ tailWord_525693) baseStart_525693 baseEnd_525693 := by
    simpa [prefixWord, tailWord_525693, baseEnd_525693] using wordTrace_append hprefix tailTrace_525693
  have hstable : (prefixWord ++ tailWord_525693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525693).length < 2 ^ (prefixWord ++ tailWord_525693).sum := by decide
  have hdescent : baseEnd_525693 < baseStart_525693 := by decide
  rcases family_descends (prefixWord ++ tailWord_525693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525724 : List Nat := [2, 2, 3, 4, 1, 9]
def baseStart_525724 : Nat := 118140960795 + 525724 * 2 ^ 59
def prefixEnd_525724 : Nat := 4983230072969 + 3 ^ 40 * 525724 * 2
def baseEnd_525724 : Nat := 4443606643693931458967

theorem tailTrace_525724 : CollatzResearch.WordTrace tailWord_525724 prefixEnd_525724 4443606643693931458967 := by
  unfold tailWord_525724
  simp only [CollatzResearch.WordTrace]
  refine ⟨9587364773699604678020113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12783153031599472904026817 9587364773699604678020113)
  ·
    refine ⟨7190523580274703508515085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9587364773699604678020113 7190523580274703508515085)
    ·
      refine ⟨2696446342603013815693157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7190523580274703508515085 2696446342603013815693157)
      ·
        refine ⟨505583689238065090442467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2696446342603013815693157 505583689238065090442467)
        ·
          refine ⟨758375533857097635663701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505583689238065090442467 758375533857097635663701)
          ·
            refine ⟨4443606643693931458967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 758375533857097635663701 4443606643693931458967)
            ·
              rfl

theorem cell21_525724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 9].length) (baseStart_525724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525724 prefixEnd_525724 := by exact prefixLift 525724
  have htrace : WordTrace (prefixWord ++ tailWord_525724) baseStart_525724 baseEnd_525724 := by
    simpa [prefixWord, tailWord_525724, baseEnd_525724] using wordTrace_append hprefix tailTrace_525724
  have hstable : (prefixWord ++ tailWord_525724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525724).length < 2 ^ (prefixWord ++ tailWord_525724).sum := by decide
  have hdescent : baseEnd_525724 < baseStart_525724 := by decide
  rcases family_descends (prefixWord ++ tailWord_525724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525741 : List Nat := [1, 5, 2, 2, 1, 3, 1, 6]
def baseStart_525741 : Nat := 118140960795 + 525741 * 2 ^ 59
def prefixEnd_525741 : Nat := 4983230072969 + 3 ^ 40 * 525741 * 2
def baseEnd_525741 : Nat := 39993753003782632536247

theorem tailTrace_525741 : CollatzResearch.WordTrace tailWord_525741 prefixEnd_525741 39993753003782632536247 := by
  unfold tailWord_525741
  simp only [CollatzResearch.WordTrace]
  refine ⟨19175349588337621259409077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12783566392225080839606051 19175349588337621259409077)
  ·
    refine ⟨1797689023906651993069601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19175349588337621259409077 1797689023906651993069601)
    ·
      refine ⟨1348266767929988994802201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1797689023906651993069601 1348266767929988994802201)
      ·
        refine ⟨1011200075947491746101651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1348266767929988994802201 1011200075947491746101651)
        ·
          refine ⟨1516800113921237619152477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011200075947491746101651 1516800113921237619152477)
          ·
            refine ⟨568800042720464107182179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1516800113921237619152477 568800042720464107182179)
            ·
              refine ⟨853200064080696160773269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568800042720464107182179 853200064080696160773269)
              ·
                refine ⟨39993753003782632536247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 853200064080696160773269 39993753003782632536247)
                ·
                  rfl

theorem cell21_525741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 6].length) (baseStart_525741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525741 prefixEnd_525741 := by exact prefixLift 525741
  have htrace : WordTrace (prefixWord ++ tailWord_525741) baseStart_525741 baseEnd_525741 := by
    simpa [prefixWord, tailWord_525741, baseEnd_525741] using wordTrace_append hprefix tailTrace_525741
  have hstable : (prefixWord ++ tailWord_525741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525741).length < 2 ^ (prefixWord ++ tailWord_525741).sum := by decide
  have hdescent : baseEnd_525741 < baseStart_525741 := by decide
  rcases family_descends (prefixWord ++ tailWord_525741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525772 : List Nat := [2, 2, 1, 4, 2, 2, 2, 3, 3]
def baseStart_525772 : Nat := 118140960795 + 525772 * 2 ^ 59
def prefixEnd_525772 : Nat := 4983230072969 + 3 ^ 40 * 525772 * 2
def baseEnd_525772 : Nat := 119988333633698732592011

theorem tailTrace_525772 : CollatzResearch.WordTrace tailWord_525772 prefixEnd_525772 119988333633698732592011 := by
  unfold tailWord_525772
  simp only [CollatzResearch.WordTrace]
  refine ⟨9588240125612656776893785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12784320167483542369191713 9588240125612656776893785)
  ·
    refine ⟨7191180094209492582670339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9588240125612656776893785 7191180094209492582670339)
    ·
      refine ⟨10786770141314238874005509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7191180094209492582670339 10786770141314238874005509)
      ·
        refine ⟨2022519401496419788876033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10786770141314238874005509 2022519401496419788876033)
        ·
          refine ⟨1516889551122314841657025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022519401496419788876033 1516889551122314841657025)
          ·
            refine ⟨1137667163341736131242769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1516889551122314841657025 1137667163341736131242769)
            ·
              refine ⟨853250372506302098432077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1137667163341736131242769 853250372506302098432077)
              ·
                refine ⟨319968889689863286912029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 853250372506302098432077 319968889689863286912029)
                ·
                  refine ⟨119988333633698732592011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319968889689863286912029 119988333633698732592011)
                  ·
                    rfl

theorem cell21_525772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_525772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525772 prefixEnd_525772 := by exact prefixLift 525772
  have htrace : WordTrace (prefixWord ++ tailWord_525772) baseStart_525772 baseEnd_525772 := by
    simpa [prefixWord, tailWord_525772, baseEnd_525772] using wordTrace_append hprefix tailTrace_525772
  have hstable : (prefixWord ++ tailWord_525772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525772).length < 2 ^ (prefixWord ++ tailWord_525772).sum := by decide
  have hdescent : baseEnd_525772 < baseStart_525772 := by decide
  rcases family_descends (prefixWord ++ tailWord_525772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525786 : List Nat := [3, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_525786 : Nat := 118140960795 + 525786 * 2 ^ 59
def prefixEnd_525786 : Nat := 4983230072969 + 3 ^ 40 * 525786 * 2
def baseEnd_525786 : Nat := 119991528624437819358649

theorem tailTrace_525786 : CollatzResearch.WordTrace tailWord_525786 prefixEnd_525786 119991528624437819358649 := by
  unfold tailWord_525786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4794247718293648486199303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12784660582116395963198141 4794247718293648486199303)
  ·
    refine ⟨7191371577440472729298955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4794247718293648486199303 7191371577440472729298955)
    ·
      refine ⟨10787057366160709093948433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7191371577440472729298955 10787057366160709093948433)
      ·
        refine ⟨8090293024620531820461325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10787057366160709093948433 8090293024620531820461325)
        ·
          refine ⟨3033859884232699432672997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8090293024620531820461325 3033859884232699432672997)
          ·
            refine ⟨568848728293631143626187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3033859884232699432672997 568848728293631143626187)
            ·
              refine ⟨853273092440446715439281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568848728293631143626187 853273092440446715439281)
              ·
                refine ⟨639954819330335036579461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853273092440446715439281 639954819330335036579461)
                ·
                  refine ⟨119991528624437819358649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 639954819330335036579461 119991528624437819358649)
                  ·
                    rfl

theorem cell21_525786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_525786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525786 prefixEnd_525786 := by exact prefixLift 525786
  have htrace : WordTrace (prefixWord ++ tailWord_525786) baseStart_525786 baseEnd_525786 := by
    simpa [prefixWord, tailWord_525786, baseEnd_525786] using wordTrace_append hprefix tailTrace_525786
  have hstable : (prefixWord ++ tailWord_525786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525786).length < 2 ^ (prefixWord ++ tailWord_525786).sum := by decide
  have hdescent : baseEnd_525786 < baseStart_525786 := by decide
  rcases family_descends (prefixWord ++ tailWord_525786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525848 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 5]
def baseStart_525848 : Nat := 118140960795 + 525848 * 2 ^ 59
def prefixEnd_525848 : Nat := 4983230072969 + 3 ^ 40 * 525848 * 2
def baseEnd_525848 : Nat := 120005677869139489325189

theorem tailTrace_525848 : CollatzResearch.WordTrace tailWord_525848 prefixEnd_525848 120005677869139489325189 := by
  unfold tailWord_525848
  simp only [CollatzResearch.WordTrace]
  refine ⟨9589626099474989266777099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12786168132633319022369465 9589626099474989266777099)
  ·
    refine ⟨14384439149212483900165649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9589626099474989266777099 14384439149212483900165649)
    ·
      refine ⟨10788329361909362925124237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14384439149212483900165649 10788329361909362925124237)
      ·
        refine ⟨4045623510716011096921589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10788329361909362925124237 4045623510716011096921589)
        ·
          refine ⟨379277204129626040336399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4045623510716011096921589 379277204129626040336399)
          ·
            refine ⟨568915806194439060504599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379277204129626040336399 568915806194439060504599)
            ·
              refine ⟨853373709291658590756899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568915806194439060504599 853373709291658590756899)
              ·
                refine ⟨1280060563937487886135349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853373709291658590756899 1280060563937487886135349)
                ·
                  refine ⟨120005677869139489325189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1280060563937487886135349 120005677869139489325189)
                  ·
                    rfl

theorem cell21_525848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 5].length) (baseStart_525848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525848 prefixEnd_525848 := by exact prefixLift 525848
  have htrace : WordTrace (prefixWord ++ tailWord_525848) baseStart_525848 baseEnd_525848 := by
    simpa [prefixWord, tailWord_525848, baseEnd_525848] using wordTrace_append hprefix tailTrace_525848
  have hstable : (prefixWord ++ tailWord_525848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525848).length < 2 ^ (prefixWord ++ tailWord_525848).sum := by decide
  have hdescent : baseEnd_525848 < baseStart_525848 := by decide
  rcases family_descends (prefixWord ++ tailWord_525848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525854 : List Nat := [4, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_525854 : Nat := 118140960795 + 525854 * 2 ^ 59
def prefixEnd_525854 : Nat := 4983230072969 + 3 ^ 40 * 525854 * 2
def baseEnd_525854 : Nat := 120007047150884812225177

theorem tailTrace_525854 : CollatzResearch.WordTrace tailWord_525854 prefixEnd_525854 120007047150884812225177 := by
  unfold tailWord_525854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2397433879616030194784077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12786314024618827705515077 2397433879616030194784077)
  ·
    refine ⟨899037704856011323044029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2397433879616030194784077 899037704856011323044029)
    ·
      refine ⟨337139139321004246141511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 899037704856011323044029 337139139321004246141511)
      ·
        refine ⟨505708708981506369212267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337139139321004246141511 505708708981506369212267)
        ·
          refine ⟨758563063472259553818401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505708708981506369212267 758563063472259553818401)
          ·
            refine ⟨568922297604194665363801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758563063472259553818401 568922297604194665363801)
            ·
              refine ⟨426691723203145999022851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568922297604194665363801 426691723203145999022851)
              ·
                refine ⟨640037584804718998534277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426691723203145999022851 640037584804718998534277)
                ·
                  refine ⟨120007047150884812225177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640037584804718998534277 120007047150884812225177)
                  ·
                    rfl

theorem cell21_525854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_525854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525854 prefixEnd_525854 := by exact prefixLift 525854
  have htrace : WordTrace (prefixWord ++ tailWord_525854) baseStart_525854 baseEnd_525854 := by
    simpa [prefixWord, tailWord_525854, baseEnd_525854] using wordTrace_append hprefix tailTrace_525854
  have hstable : (prefixWord ++ tailWord_525854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525854).length < 2 ^ (prefixWord ++ tailWord_525854).sum := by decide
  have hdescent : baseEnd_525854 < baseStart_525854 := by decide
  rcases family_descends (prefixWord ++ tailWord_525854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525873 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 7]
def baseStart_525873 : Nat := 118140960795 + 525873 * 2 ^ 59
def prefixEnd_525873 : Nat := 4983230072969 + 3 ^ 40 * 525873 * 2
def baseEnd_525873 : Nat := 120011383209745001408471

theorem tailTrace_525873 : CollatzResearch.WordTrace tailWord_525873 prefixEnd_525873 120011383209745001408471 := by
  unfold tailWord_525873
  simp only [CollatzResearch.WordTrace]
  refine ⟨19180164023859407803214273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12786776015906271868809515 19180164023859407803214273)
  ·
    refine ⟨14385123017894555852410705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19180164023859407803214273 14385123017894555852410705)
    ·
      refine ⟨10788842263420916889308029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14385123017894555852410705 10788842263420916889308029)
      ·
        refine ⟨4045815848782843833490511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10788842263420916889308029 4045815848782843833490511)
        ·
          refine ⟨6068723773174265750235767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4045815848782843833490511 6068723773174265750235767)
          ·
            refine ⟨9103085659761398625353651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6068723773174265750235767 9103085659761398625353651)
            ·
              refine ⟨13654628489642097938030477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9103085659761398625353651 13654628489642097938030477)
              ·
                refine ⟨5120485683615786726761429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13654628489642097938030477 5120485683615786726761429)
                ·
                  refine ⟨120011383209745001408471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5120485683615786726761429 120011383209745001408471)
                  ·
                    rfl

theorem cell21_525873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_525873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525873 prefixEnd_525873 := by exact prefixLift 525873
  have htrace : WordTrace (prefixWord ++ tailWord_525873) baseStart_525873 baseEnd_525873 := by
    simpa [prefixWord, tailWord_525873, baseEnd_525873] using wordTrace_append hprefix tailTrace_525873
  have hstable : (prefixWord ++ tailWord_525873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525873).length < 2 ^ (prefixWord ++ tailWord_525873).sum := by decide
  have hdescent : baseEnd_525873 < baseStart_525873 := by decide
  rcases family_descends (prefixWord ++ tailWord_525873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525966 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_525966 : Nat := 118140960795 + 525966 * 2 ^ 59
def prefixEnd_525966 : Nat := 4983230072969 + 3 ^ 40 * 525966 * 2
def baseEnd_525966 : Nat := 120032607076797506358281

theorem tailTrace_525966 : CollatzResearch.WordTrace tailWord_525966 prefixEnd_525966 120032607076797506358281 := by
  unfold tailWord_525966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2397944501565310585793719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12789037341681656457566501 2397944501565310585793719)
  ·
    refine ⟨3596916752347965878690579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2397944501565310585793719 3596916752347965878690579)
    ·
      refine ⟨5395375128521948818035869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3596916752347965878690579 5395375128521948818035869)
      ·
        refine ⟨2023265673195730806763451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5395375128521948818035869 2023265673195730806763451)
        ·
          refine ⟨3034898509793596210145177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023265673195730806763451 3034898509793596210145177)
          ·
            refine ⟨2276173882345197157608883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3034898509793596210145177 2276173882345197157608883)
            ·
              refine ⟨3414260823517795736413325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276173882345197157608883 3414260823517795736413325)
              ·
                refine ⟨1280347808819173401154997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3414260823517795736413325 1280347808819173401154997)
                ·
                  refine ⟨120032607076797506358281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1280347808819173401154997 120032607076797506358281)
                  ·
                    rfl

theorem cell21_525966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_525966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525966 prefixEnd_525966 := by exact prefixLift 525966
  have htrace : WordTrace (prefixWord ++ tailWord_525966) baseStart_525966 baseEnd_525966 := by
    simpa [prefixWord, tailWord_525966, baseEnd_525966] using wordTrace_append hprefix tailTrace_525966
  have hstable : (prefixWord ++ tailWord_525966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525966).length < 2 ^ (prefixWord ++ tailWord_525966).sum := by decide
  have hdescent : baseEnd_525966 < baseStart_525966 := by decide
  rcases family_descends (prefixWord ++ tailWord_525966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525986 : List Nat := [3, 3, 1, 4, 1, 2, 2, 5]
def baseStart_525986 : Nat := 118140960795 + 525986 * 2 ^ 59
def prefixEnd_525986 : Nat := 4983230072969 + 3 ^ 40 * 525986 * 2
def baseEnd_525986 : Nat := 40012390449760638674969

theorem tailTrace_525986 : CollatzResearch.WordTrace tailWord_525986 prefixEnd_525986 40012390449760638674969 := by
  unfold tailWord_525986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4796071368112507025519453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12789523648300018734718541 4796071368112507025519453)
  ·
    refine ⟨1798526763042190134569795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4796071368112507025519453 1798526763042190134569795)
    ·
      refine ⟨2697790144563285201854693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1798526763042190134569795 2697790144563285201854693)
      ·
        refine ⟨505835652105615975347755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2697790144563285201854693 505835652105615975347755)
        ·
          refine ⟨758753478158423963021633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505835652105615975347755 758753478158423963021633)
          ·
            refine ⟨569065108618817972266225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758753478158423963021633 569065108618817972266225)
            ·
              refine ⟨426798831464113479199669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569065108618817972266225 426798831464113479199669)
              ·
                refine ⟨40012390449760638674969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 426798831464113479199669 40012390449760638674969)
                ·
                  rfl

theorem cell21_525986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_525986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525986 prefixEnd_525986 := by exact prefixLift 525986
  have htrace : WordTrace (prefixWord ++ tailWord_525986) baseStart_525986 baseEnd_525986 := by
    simpa [prefixWord, tailWord_525986, baseEnd_525986] using wordTrace_append hprefix tailTrace_525986
  have hstable : (prefixWord ++ tailWord_525986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525986).length < 2 ^ (prefixWord ++ tailWord_525986).sum := by decide
  have hdescent : baseEnd_525986 < baseStart_525986 := by decide
  rcases family_descends (prefixWord ++ tailWord_525986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526028 : List Nat := [2, 2, 1, 5, 2, 1, 2, 6]
def baseStart_526028 : Nat := 118140960795 + 526028 * 2 ^ 59
def prefixEnd_526028 : Nat := 4983230072969 + 3 ^ 40 * 526028 * 2
def baseEnd_526028 : Nat := 40015585440499725441607

theorem tailTrace_526028 : CollatzResearch.WordTrace tailWord_526028 prefixEnd_526028 40015585440499725441607 := by
  unfold tailWord_526028
  simp only [CollatzResearch.WordTrace]
  refine ⟨9592908669148934637553369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12790544892198579516737825 9592908669148934637553369)
  ·
    refine ⟨7194681501861700978165027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9592908669148934637553369 7194681501861700978165027)
    ·
      refine ⟨10792022252792551467247541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7194681501861700978165027 10792022252792551467247541)
      ·
        refine ⟨1011752086199301700054457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10792022252792551467247541 1011752086199301700054457)
        ·
          refine ⟨758814064649476275040843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1011752086199301700054457 758814064649476275040843)
          ·
            refine ⟨1138221096974214412561265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758814064649476275040843 1138221096974214412561265)
            ·
              refine ⟨853665822730660809420949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138221096974214412561265 853665822730660809420949)
              ·
                refine ⟨40015585440499725441607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 853665822730660809420949 40015585440499725441607)
                ·
                  rfl

theorem cell21_526028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_526028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526028 prefixEnd_526028 := by exact prefixLift 526028
  have htrace : WordTrace (prefixWord ++ tailWord_526028) baseStart_526028 baseEnd_526028 := by
    simpa [prefixWord, tailWord_526028, baseEnd_526028] using wordTrace_append hprefix tailTrace_526028
  have hstable : (prefixWord ++ tailWord_526028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526028).length < 2 ^ (prefixWord ++ tailWord_526028).sum := by decide
  have hdescent : baseEnd_526028 < baseStart_526028 := by decide
  rcases family_descends (prefixWord ++ tailWord_526028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526101 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 7]
def baseStart_526101 : Nat := 118140960795 + 526101 * 2 ^ 59
def prefixEnd_526101 : Nat := 4983230072969 + 3 ^ 40 * 526101 * 2
def baseEnd_526101 : Nat := 120063415916067271608005

theorem tailTrace_526101 : CollatzResearch.WordTrace tailWord_526101 prefixEnd_526101 120063415916067271608005 := by
  unfold tailWord_526101
  simp only [CollatzResearch.WordTrace]
  refine ⟨19188479867033402742514157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12792319911355601828342771 19188479867033402742514157)
  ·
    refine ⟨7195679950137526028442809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19188479867033402742514157 7195679950137526028442809)
    ·
      refine ⟨5396759962603144521332107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7195679950137526028442809 5396759962603144521332107)
      ·
        refine ⟨8095139943904716781998161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5396759962603144521332107 8095139943904716781998161)
        ·
          refine ⟨6071354957928537586498621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8095139943904716781998161 6071354957928537586498621)
          ·
            refine ⟨2276758109223201594936983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6071354957928537586498621 2276758109223201594936983)
            ·
              refine ⟨3415137163834802392405475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276758109223201594936983 3415137163834802392405475)
              ·
                refine ⟨5122705745752203588608213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3415137163834802392405475 5122705745752203588608213)
                ·
                  refine ⟨120063415916067271608005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5122705745752203588608213 120063415916067271608005)
                  ·
                    rfl

theorem cell21_526101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_526101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526101 prefixEnd_526101 := by exact prefixLift 526101
  have htrace : WordTrace (prefixWord ++ tailWord_526101) baseStart_526101 baseEnd_526101 := by
    simpa [prefixWord, tailWord_526101, baseEnd_526101] using wordTrace_append hprefix tailTrace_526101
  have hstable : (prefixWord ++ tailWord_526101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526101).length < 2 ^ (prefixWord ++ tailWord_526101).sum := by decide
  have hdescent : baseEnd_526101 < baseStart_526101 := by decide
  rcases family_descends (prefixWord ++ tailWord_526101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526110 : List Nat := [4, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_526110 : Nat := 118140960795 + 526110 * 2 ^ 59
def prefixEnd_526110 : Nat := 4983230072969 + 3 ^ 40 * 526110 * 2
def baseEnd_526110 : Nat := 120065469838685255957987

theorem tailTrace_526110 : CollatzResearch.WordTrace tailWord_526110 prefixEnd_526110 120065469838685255957987 := by
  unfold tailWord_526110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398601015500099659948973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12792538749333864853061189 2398601015500099659948973)
  ·
    refine ⟨899475380812537372480865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2398601015500099659948973 899475380812537372480865)
    ·
      refine ⟨674606535609403029360649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 899475380812537372480865 674606535609403029360649)
      ·
        refine ⟨505954901707052272020487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674606535609403029360649 505954901707052272020487)
        ·
          refine ⟨758932352560578408030731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505954901707052272020487 758932352560578408030731)
          ·
            refine ⟨1138398528840867612046097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758932352560578408030731 1138398528840867612046097)
            ·
              refine ⟨853798896630650709034573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138398528840867612046097 853798896630650709034573)
              ·
                refine ⟨320174586236494015887965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 853798896630650709034573 320174586236494015887965)
                ·
                  refine ⟨120065469838685255957987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320174586236494015887965 120065469838685255957987)
                  ·
                    rfl

theorem cell21_526110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_526110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526110 prefixEnd_526110 := by exact prefixLift 526110
  have htrace : WordTrace (prefixWord ++ tailWord_526110) baseStart_526110 baseEnd_526110 := by
    simpa [prefixWord, tailWord_526110, baseEnd_526110] using wordTrace_append hprefix tailTrace_526110
  have hstable : (prefixWord ++ tailWord_526110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526110).length < 2 ^ (prefixWord ++ tailWord_526110).sum := by decide
  have hdescent : baseEnd_526110 < baseStart_526110 := by decide
  rcases family_descends (prefixWord ++ tailWord_526110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526149 : List Nat := [1, 3, 1, 1, 1, 2, 7, 1, 4]
def baseStart_526149 : Nat := 118140960795 + 526149 * 2 ^ 59
def prefixEnd_526149 : Nat := 4983230072969 + 3 ^ 40 * 526149 * 2
def baseEnd_526149 : Nat := 120074370170029854807907

theorem tailTrace_526149 : CollatzResearch.WordTrace tailWord_526149 prefixEnd_526149 120074370170029854807907 := by
  unfold tailWord_526149
  simp only [CollatzResearch.WordTrace]
  refine ⟨19190230570859506940261501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12793487047239671293507667 19190230570859506940261501)
  ·
    refine ⟨7196336464072315102598063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19190230570859506940261501 7196336464072315102598063)
    ·
      refine ⟨10794504696108472653897095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7196336464072315102598063 10794504696108472653897095)
      ·
        refine ⟨16191757044162708980845643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10794504696108472653897095 16191757044162708980845643)
        ·
          refine ⟨24287635566244063471268465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16191757044162708980845643 24287635566244063471268465)
          ·
            refine ⟨18215726674683047603451349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24287635566244063471268465 18215726674683047603451349)
            ·
              refine ⟨426931093937883928205891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18215726674683047603451349 426931093937883928205891)
              ·
                refine ⟨640396640906825892308837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426931093937883928205891 640396640906825892308837)
                ·
                  refine ⟨120074370170029854807907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640396640906825892308837 120074370170029854807907)
                  ·
                    rfl

theorem cell21_526149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_526149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526149 prefixEnd_526149 := by exact prefixLift 526149
  have htrace : WordTrace (prefixWord ++ tailWord_526149) baseStart_526149 baseEnd_526149 := by
    simpa [prefixWord, tailWord_526149, baseEnd_526149] using wordTrace_append hprefix tailTrace_526149
  have hstable : (prefixWord ++ tailWord_526149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526149).length < 2 ^ (prefixWord ++ tailWord_526149).sum := by decide
  have hdescent : baseEnd_526149 < baseStart_526149 := by decide
  rcases family_descends (prefixWord ++ tailWord_526149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526180 : List Nat := [2, 3, 1, 1, 6, 1, 7]
def baseStart_526180 : Nat := 118140960795 + 526180 * 2 ^ 59
def prefixEnd_526180 : Nat := 4983230072969 + 3 ^ 40 * 526180 * 2
def baseEnd_526180 : Nat := 13342382754708965532353

theorem tailTrace_526180 : CollatzResearch.WordTrace tailWord_526180 prefixEnd_526180 13342382754708965532353 := by
  unfold tailWord_526180
  simp only [CollatzResearch.WordTrace]
  refine ⟨9595680616873599617319997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12794240822498132823093329 9595680616873599617319997)
  ·
    refine ⟨3598380231327599856494999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9595680616873599617319997 3598380231327599856494999)
    ·
      refine ⟨5397570346991399784742499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3598380231327599856494999 5397570346991399784742499)
      ·
        refine ⟨8096355520487099677113749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5397570346991399784742499 8096355520487099677113749)
        ·
          refine ⟨379516665022832797364707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8096355520487099677113749 379516665022832797364707)
          ·
            refine ⟨569274997534249196047061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379516665022832797364707 569274997534249196047061)
            ·
              refine ⟨13342382754708965532353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 569274997534249196047061 13342382754708965532353)
              ·
                rfl

theorem cell21_526180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 7].length) (baseStart_526180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526180 prefixEnd_526180 := by exact prefixLift 526180
  have htrace : WordTrace (prefixWord ++ tailWord_526180) baseStart_526180 baseEnd_526180 := by
    simpa [prefixWord, tailWord_526180, baseEnd_526180] using wordTrace_append hprefix tailTrace_526180
  have hstable : (prefixWord ++ tailWord_526180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526180).length < 2 ^ (prefixWord ++ tailWord_526180).sum := by decide
  have hdescent : baseEnd_526180 < baseStart_526180 := by decide
  rcases family_descends (prefixWord ++ tailWord_526180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526208 : List Nat := [2, 1, 1, 2, 1, 2, 5, 3, 4]
def baseStart_526208 : Nat := 118140960795 + 526208 * 2 ^ 59
def prefixEnd_526208 : Nat := 4983230072969 + 3 ^ 40 * 526208 * 2
def baseEnd_526208 : Nat := 120087834773858863324453

theorem tailTrace_526208 : CollatzResearch.WordTrace tailWord_526208 prefixEnd_526208 120087834773858863324453 := by
  unfold tailWord_526208
  simp only [CollatzResearch.WordTrace]
  refine ⟨9596191238822880008329639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12794921651763840011106185 9596191238822880008329639)
  ·
    refine ⟨14394286858234320012494459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9596191238822880008329639 14394286858234320012494459)
    ·
      refine ⟨21591430287351480018741689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14394286858234320012494459 21591430287351480018741689)
      ·
        refine ⟨16193572715513610014056267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21591430287351480018741689 16193572715513610014056267)
        ·
          refine ⟨24290359073270415021084401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16193572715513610014056267 24290359073270415021084401)
          ·
            refine ⟨18217769304952811265813301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24290359073270415021084401 18217769304952811265813301)
            ·
              refine ⟨1707915872339326056169997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18217769304952811265813301 1707915872339326056169997)
              ·
                refine ⟨640468452127247271063749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1707915872339326056169997 640468452127247271063749)
                ·
                  refine ⟨120087834773858863324453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640468452127247271063749 120087834773858863324453)
                  ·
                    rfl

theorem cell21_526208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_526208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526208 prefixEnd_526208 := by exact prefixLift 526208
  have htrace : WordTrace (prefixWord ++ tailWord_526208) baseStart_526208 baseEnd_526208 := by
    simpa [prefixWord, tailWord_526208, baseEnd_526208] using wordTrace_append hprefix tailTrace_526208
  have hstable : (prefixWord ++ tailWord_526208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526208).length < 2 ^ (prefixWord ++ tailWord_526208).sum := by decide
  have hdescent : baseEnd_526208 < baseStart_526208 := by decide
  rcases family_descends (prefixWord ++ tailWord_526208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526239 : List Nat := [1, 1, 2, 5, 4, 8]
def baseStart_526239 : Nat := 118140960795 + 526239 * 2 ^ 59
def prefixEnd_526239 : Nat := 4983230072969 + 3 ^ 40 * 526239 * 2
def baseEnd_526239 : Nat := 4447959607267025863249

theorem tailTrace_526239 : CollatzResearch.WordTrace tailWord_526239 prefixEnd_526239 4447959607267025863249 := by
  unfold tailWord_526239
  simp only [CollatzResearch.WordTrace]
  refine ⟨19193513140533452311037771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12795675427022301540691847 19193513140533452311037771)
  ·
    refine ⟨28790269710800178466556657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19193513140533452311037771 28790269710800178466556657)
    ·
      refine ⟨21592702283100133849917493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28790269710800178466556657 21592702283100133849917493)
      ·
        refine ⟨2024315839040637548429765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21592702283100133849917493 2024315839040637548429765)
        ·
          refine ⟨379559219820119540330581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2024315839040637548429765 379559219820119540330581)
          ·
            refine ⟨4447959607267025863249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 379559219820119540330581 4447959607267025863249)
            ·
              rfl

theorem cell21_526239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 8].length) (baseStart_526239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526239 prefixEnd_526239 := by exact prefixLift 526239
  have htrace : WordTrace (prefixWord ++ tailWord_526239) baseStart_526239 baseEnd_526239 := by
    simpa [prefixWord, tailWord_526239, baseEnd_526239] using wordTrace_append hprefix tailTrace_526239
  have hstable : (prefixWord ++ tailWord_526239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526239).length < 2 ^ (prefixWord ++ tailWord_526239).sum := by decide
  have hdescent : baseEnd_526239 < baseStart_526239 := by decide
  rcases family_descends (prefixWord ++ tailWord_526239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526242 : List Nat := [3, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_526242 : Nat := 118140960795 + 526242 * 2 ^ 59
def prefixEnd_526242 : Nat := 4983230072969 + 3 ^ 40 * 526242 * 2
def baseEnd_526242 : Nat := 120095594037082359757717

theorem tailTrace_526242 : CollatzResearch.WordTrace tailWord_526242 prefixEnd_526242 120095594037082359757717 := by
  unfold tailWord_526242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798405639880645955849245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12795748373015055882264653 4798405639880645955849245)
  ·
    refine ⟨1799402114955242233443467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4798405639880645955849245 1799402114955242233443467)
    ·
      refine ⟨2699103172432863350165201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1799402114955242233443467 2699103172432863350165201)
      ·
        refine ⟨2024327379324647512623901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2699103172432863350165201 2024327379324647512623901)
        ·
          refine ⟨759122767246742817233963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2024327379324647512623901 759122767246742817233963)
          ·
            refine ⟨1138684150870114225850945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759122767246742817233963 1138684150870114225850945)
            ·
              refine ⟨854013113152585669388209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138684150870114225850945 854013113152585669388209)
              ·
                refine ⟨640509834864439252041157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854013113152585669388209 640509834864439252041157)
                ·
                  refine ⟨120095594037082359757717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640509834864439252041157 120095594037082359757717)
                  ·
                    rfl

theorem cell21_526242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_526242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526242 prefixEnd_526242 := by exact prefixLift 526242
  have htrace : WordTrace (prefixWord ++ tailWord_526242) baseStart_526242 baseEnd_526242 := by
    simpa [prefixWord, tailWord_526242, baseEnd_526242] using wordTrace_append hprefix tailTrace_526242
  have hstable : (prefixWord ++ tailWord_526242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526242).length < 2 ^ (prefixWord ++ tailWord_526242).sum := by decide
  have hdescent : baseEnd_526242 < baseStart_526242 := by decide
  rcases family_descends (prefixWord ++ tailWord_526242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526270 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_526270 : Nat := 118140960795 + 526270 * 2 ^ 59
def prefixEnd_526270 : Nat := 4983230072969 + 3 ^ 40 * 526270 * 2
def baseEnd_526270 : Nat := 120101984018560533290993

theorem tailTrace_526270 : CollatzResearch.WordTrace tailWord_526270 prefixEnd_526270 120101984018560533290993 := by
  unfold tailWord_526270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2399330475427643075677033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12796429202280763070277509 2399330475427643075677033)
  ·
    refine ⟨1799497856570732306757775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2399330475427643075677033 1799497856570732306757775)
    ·
      refine ⟨2699246784856098460136663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1799497856570732306757775 2699246784856098460136663)
      ·
        refine ⟨4048870177284147690204995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2699246784856098460136663 4048870177284147690204995)
        ·
          refine ⟨6073305265926221535307493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4048870177284147690204995 6073305265926221535307493)
          ·
            refine ⟨1138744737361166537870155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6073305265926221535307493 1138744737361166537870155)
            ·
              refine ⟨1708117106041749806805233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138744737361166537870155 1708117106041749806805233)
              ·
                refine ⟨1281087829531312355103925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1708117106041749806805233 1281087829531312355103925)
                ·
                  refine ⟨120101984018560533290993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1281087829531312355103925 120101984018560533290993)
                  ·
                    rfl

theorem cell21_526270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_526270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526270 prefixEnd_526270 := by exact prefixLift 526270
  have htrace : WordTrace (prefixWord ++ tailWord_526270) baseStart_526270 baseEnd_526270 := by
    simpa [prefixWord, tailWord_526270, baseEnd_526270] using wordTrace_append hprefix tailTrace_526270
  have hstable : (prefixWord ++ tailWord_526270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526270).length < 2 ^ (prefixWord ++ tailWord_526270).sum := by decide
  have hdescent : baseEnd_526270 < baseStart_526270 := by decide
  rcases family_descends (prefixWord ++ tailWord_526270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526301 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 6]
def baseStart_526301 : Nat := 118140960795 + 526301 * 2 ^ 59
def prefixEnd_526301 : Nat := 4983230072969 + 3 ^ 40 * 526301 * 2
def baseEnd_526301 : Nat := 120109058640911368274263

theorem tailTrace_526301 : CollatzResearch.WordTrace tailWord_526301 prefixEnd_526301 120109058640911368274263 := by
  unfold tailWord_526301
  simp only [CollatzResearch.WordTrace]
  refine ⟨19195774466308836899794757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12797182977539224599863171 19195774466308836899794757)
  ·
    refine ⟨3599207712432906918711517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19195774466308836899794757 3599207712432906918711517)
    ·
      refine ⟨1349702892162340094516819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3599207712432906918711517 1349702892162340094516819)
      ·
        refine ⟨2024554338243510141775229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1349702892162340094516819 2024554338243510141775229)
        ·
          refine ⟨759207876841316303165711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2024554338243510141775229 759207876841316303165711)
          ·
            refine ⟨1138811815261974454748567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759207876841316303165711 1138811815261974454748567)
            ·
              refine ⟨1708217722892961682122851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138811815261974454748567 1708217722892961682122851)
              ·
                refine ⟨2562326584339442523184277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1708217722892961682122851 2562326584339442523184277)
                ·
                  refine ⟨120109058640911368274263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2562326584339442523184277 120109058640911368274263)
                  ·
                    rfl

theorem cell21_526301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_526301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526301 prefixEnd_526301 := by exact prefixLift 526301
  have htrace : WordTrace (prefixWord ++ tailWord_526301) baseStart_526301 baseEnd_526301 := by
    simpa [prefixWord, tailWord_526301, baseEnd_526301] using wordTrace_append hprefix tailTrace_526301
  have hstable : (prefixWord ++ tailWord_526301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526301).length < 2 ^ (prefixWord ++ tailWord_526301).sum := by decide
  have hdescent : baseEnd_526301 < baseStart_526301 := by decide
  rcases family_descends (prefixWord ++ tailWord_526301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526318 : List Nat := [4, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_526318 : Nat := 118140960795 + 526318 * 2 ^ 59
def prefixEnd_526318 : Nat := 4983230072969 + 3 ^ 40 * 526318 * 2
def baseEnd_526318 : Nat := 120112938272523116490895

theorem tailTrace_526318 : CollatzResearch.WordTrace tailWord_526318 prefixEnd_526318 120112938272523116490895 := by
  unfold tailWord_526318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2399549313405906100395451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12797596338164832535442405 2399549313405906100395451)
  ·
    refine ⟨3599323970108859150593177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2399549313405906100395451 3599323970108859150593177)
    ·
      refine ⟨2699492977581644362944883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3599323970108859150593177 2699492977581644362944883)
      ·
        refine ⟨4049239466372466544417325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2699492977581644362944883 4049239466372466544417325)
        ·
          refine ⟨1518464799889674954156497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4049239466372466544417325 1518464799889674954156497)
          ·
            refine ⟨1138848599917256215617373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1518464799889674954156497 1138848599917256215617373)
            ·
              refine ⟨427068224968971080856515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1138848599917256215617373 427068224968971080856515)
              ·
                refine ⟨640602337453456621284773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427068224968971080856515 640602337453456621284773)
                ·
                  refine ⟨120112938272523116490895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640602337453456621284773 120112938272523116490895)
                  ·
                    rfl

theorem cell21_526318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_526318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526318 prefixEnd_526318 := by exact prefixLift 526318
  have htrace : WordTrace (prefixWord ++ tailWord_526318) baseStart_526318 baseEnd_526318 := by
    simpa [prefixWord, tailWord_526318, baseEnd_526318] using wordTrace_append hprefix tailTrace_526318
  have hstable : (prefixWord ++ tailWord_526318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526318).length < 2 ^ (prefixWord ++ tailWord_526318).sum := by decide
  have hdescent : baseEnd_526318 < baseStart_526318 := by decide
  rcases family_descends (prefixWord ++ tailWord_526318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526329 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 5]
def baseStart_526329 : Nat := 118140960795 + 526329 * 2 ^ 59
def prefixEnd_526329 : Nat := 4983230072969 + 3 ^ 40 * 526329 * 2
def baseEnd_526329 : Nat := 120115448622389541807539

theorem tailTrace_526329 : CollatzResearch.WordTrace tailWord_526329 prefixEnd_526329 120115448622389541807539 := by
  unfold tailWord_526329
  simp only [CollatzResearch.WordTrace]
  refine ⟨19196795710207397681814041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12797863806804931787876027 19196795710207397681814041)
  ·
    refine ⟨14397596782655548261360531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19196795710207397681814041 14397596782655548261360531)
    ·
      refine ⟨21596395173983322392040797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14397596782655548261360531 21596395173983322392040797)
      ·
        refine ⟨8098648190243745897015299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21596395173983322392040797 8098648190243745897015299)
        ·
          refine ⟨12147972285365618845522949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8098648190243745897015299 12147972285365618845522949)
          ·
            refine ⟨2277744803506053533535553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12147972285365618845522949 2277744803506053533535553)
            ·
              refine ⟨1708308602629540150151665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2277744803506053533535553 1708308602629540150151665)
              ·
                refine ⟨1281231451972155112613749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1708308602629540150151665 1281231451972155112613749)
                ·
                  refine ⟨120115448622389541807539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1281231451972155112613749 120115448622389541807539)
                  ·
                    rfl

theorem cell21_526329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_526329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526329 prefixEnd_526329 := by exact prefixLift 526329
  have htrace : WordTrace (prefixWord ++ tailWord_526329) baseStart_526329 baseEnd_526329 := by
    simpa [prefixWord, tailWord_526329, baseEnd_526329] using wordTrace_append hprefix tailTrace_526329
  have hstable : (prefixWord ++ tailWord_526329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526329).length < 2 ^ (prefixWord ++ tailWord_526329).sum := by decide
  have hdescent : baseEnd_526329 < baseStart_526329 := by decide
  rcases family_descends (prefixWord ++ tailWord_526329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526360 : List Nat := [2, 1, 2, 3, 2, 1, 2, 4, 4]
def baseStart_526360 : Nat := 118140960795 + 526360 * 2 ^ 59
def prefixEnd_526360 : Nat := 4983230072969 + 3 ^ 40 * 526360 * 2
def baseEnd_526360 : Nat := 120122523244740376790809

theorem tailTrace_526360 : CollatzResearch.WordTrace tailWord_526360 prefixEnd_526360 120122523244740376790809 := by
  unfold tailWord_526360
  simp only [CollatzResearch.WordTrace]
  refine ⟨9598963186547544988096267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12798617582063393317461689 9598963186547544988096267)
  ·
    refine ⟨14398444779821317482144401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9598963186547544988096267 14398444779821317482144401)
    ·
      refine ⟨10798833584865988111608301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14398444779821317482144401 10798833584865988111608301)
      ·
        refine ⟨4049562594324745541853113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10798833584865988111608301 4049562594324745541853113)
        ·
          refine ⟨3037171945743559156389835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4049562594324745541853113 3037171945743559156389835)
          ·
            refine ⟨4555757918615338734584753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3037171945743559156389835 4555757918615338734584753)
            ·
              refine ⟨3416818438961504050938565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4555757918615338734584753 3416818438961504050938565)
              ·
                refine ⟨640653457305282009550981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3416818438961504050938565 640653457305282009550981)
                ·
                  refine ⟨120122523244740376790809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640653457305282009550981 120122523244740376790809)
                  ·
                    rfl

theorem cell21_526360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_526360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526360 prefixEnd_526360 := by exact prefixLift 526360
  have htrace : WordTrace (prefixWord ++ tailWord_526360) baseStart_526360 baseEnd_526360 := by
    simpa [prefixWord, tailWord_526360, baseEnd_526360] using wordTrace_append hprefix tailTrace_526360
  have hstable : (prefixWord ++ tailWord_526360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526360).length < 2 ^ (prefixWord ++ tailWord_526360).sum := by decide
  have hdescent : baseEnd_526360 < baseStart_526360 := by decide
  rcases family_descends (prefixWord ++ tailWord_526360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526436 : List Nat := [2, 3, 1, 1, 2, 1, 4, 3, 4]
def baseStart_526436 : Nat := 118140960795 + 526436 * 2 ^ 59
def prefixEnd_526436 : Nat := 4983230072969 + 3 ^ 40 * 526436 * 2
def baseEnd_526436 : Nat := 120139867480181133523987

theorem tailTrace_526436 : CollatzResearch.WordTrace tailWord_526436 prefixEnd_526436 120139867480181133523987 := by
  unfold tailWord_526436
  simp only [CollatzResearch.WordTrace]
  refine ⟨9600349160409877477979581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12800465547213169970639441 9600349160409877477979581)
  ·
    refine ⟨3600130935153704054242343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9600349160409877477979581 3600130935153704054242343)
    ·
      refine ⟨5400196402730556081363515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3600130935153704054242343 5400196402730556081363515)
      ·
        refine ⟨8100294604095834122045273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5400196402730556081363515 8100294604095834122045273)
        ·
          refine ⟨6075220953071875591533955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8100294604095834122045273 6075220953071875591533955)
          ·
            refine ⟨9112831429607813387300933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6075220953071875591533955 9112831429607813387300933)
            ·
              refine ⟨1708655893051465010118925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9112831429607813387300933 1708655893051465010118925)
              ·
                refine ⟨640745959894299378794597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1708655893051465010118925 640745959894299378794597)
                ·
                  refine ⟨120139867480181133523987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640745959894299378794597 120139867480181133523987)
                  ·
                    rfl

theorem cell21_526436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_526436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526436 prefixEnd_526436 := by exact prefixLift 526436
  have htrace : WordTrace (prefixWord ++ tailWord_526436) baseStart_526436 baseEnd_526436 := by
    simpa [prefixWord, tailWord_526436, baseEnd_526436] using wordTrace_append hprefix tailTrace_526436
  have hstable : (prefixWord ++ tailWord_526436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526436).length < 2 ^ (prefixWord ++ tailWord_526436).sum := by decide
  have hdescent : baseEnd_526436 < baseStart_526436 := by decide
  rcases family_descends (prefixWord ++ tailWord_526436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526464 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 9]
def baseStart_526464 : Nat := 118140960795 + 526464 * 2 ^ 59
def prefixEnd_526464 : Nat := 4983230072969 + 3 ^ 40 * 526464 * 2
def baseEnd_526464 : Nat := 120146257461659307057263

theorem tailTrace_526464 : CollatzResearch.WordTrace tailWord_526464 prefixEnd_526464 120146257461659307057263 := by
  unfold tailWord_526464
  simp only [CollatzResearch.WordTrace]
  refine ⟨9600859782359157868989223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12801146376478877158652297 9600859782359157868989223)
  ·
    refine ⟨14401289673538736803483835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9600859782359157868989223 14401289673538736803483835)
    ·
      refine ⟨21601934510308105205225753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14401289673538736803483835 21601934510308105205225753)
      ·
        refine ⟨16201450882731078903919315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21601934510308105205225753 16201450882731078903919315)
        ·
          refine ⟨24302176324096618355878973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16201450882731078903919315 24302176324096618355878973)
          ·
            refine ⟨9113316121536231883454615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24302176324096618355878973 9113316121536231883454615)
            ·
              refine ⟨13669974182304347825181923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9113316121536231883454615 13669974182304347825181923)
              ·
                refine ⟨20504961273456521737772885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13669974182304347825181923 20504961273456521737772885)
                ·
                  refine ⟨120146257461659307057263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20504961273456521737772885 120146257461659307057263)
                  ·
                    rfl

theorem cell21_526464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_526464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526464 prefixEnd_526464 := by exact prefixLift 526464
  have htrace : WordTrace (prefixWord ++ tailWord_526464) baseStart_526464 baseEnd_526464 := by
    simpa [prefixWord, tailWord_526464, baseEnd_526464] using wordTrace_append hprefix tailTrace_526464
  have hstable : (prefixWord ++ tailWord_526464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526464).length < 2 ^ (prefixWord ++ tailWord_526464).sum := by decide
  have hdescent : baseEnd_526464 < baseStart_526464 := by decide
  rcases family_descends (prefixWord ++ tailWord_526464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526498 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_526498 : Nat := 118140960795 + 526498 * 2 ^ 59
def prefixEnd_526498 : Nat := 4983230072969 + 3 ^ 40 * 526498 * 2
def baseEnd_526498 : Nat := 120154016724882803490527

theorem tailTrace_526498 : CollatzResearch.WordTrace tailWord_526498 prefixEnd_526498 120154016724882803490527 := by
  unfold tailWord_526498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4800739911648784886179037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12801973097730093029810765 4800739911648784886179037)
  ·
    refine ⟨1800277466868294332317139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4800739911648784886179037 1800277466868294332317139)
    ·
      refine ⟨2700416200302441498475709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1800277466868294332317139 2700416200302441498475709)
      ·
        refine ⟨1012656075113415561928391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2700416200302441498475709 1012656075113415561928391)
        ·
          refine ⟨1518984112670123342892587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012656075113415561928391 1518984112670123342892587)
          ·
            refine ⟨2278476169005185014338881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1518984112670123342892587 2278476169005185014338881)
            ·
              refine ⟨1708857126753888760754161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2278476169005185014338881 1708857126753888760754161)
              ·
                refine ⟨1281642845065416570565621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1708857126753888760754161 1281642845065416570565621)
                ·
                  refine ⟨120154016724882803490527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1281642845065416570565621 120154016724882803490527)
                  ·
                    rfl

theorem cell21_526498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_526498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526498 prefixEnd_526498 := by exact prefixLift 526498
  have htrace : WordTrace (prefixWord ++ tailWord_526498) baseStart_526498 baseEnd_526498 := by
    simpa [prefixWord, tailWord_526498, baseEnd_526498] using wordTrace_append hprefix tailTrace_526498
  have hstable : (prefixWord ++ tailWord_526498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526498).length < 2 ^ (prefixWord ++ tailWord_526498).sum := by decide
  have hdescent : baseEnd_526498 < baseStart_526498 := by decide
  rcases family_descends (prefixWord ++ tailWord_526498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526532 : List Nat := [2, 3, 3, 1, 2, 2, 3, 2, 3]
def baseStart_526532 : Nat := 118140960795 + 526532 * 2 ^ 59
def prefixEnd_526532 : Nat := 4983230072969 + 3 ^ 40 * 526532 * 2
def baseEnd_526532 : Nat := 120161775988106299923791

theorem tailTrace_526532 : CollatzResearch.WordTrace tailWord_526532 prefixEnd_526532 120161775988106299923791 := by
  unfold tailWord_526532
  simp only [CollatzResearch.WordTrace]
  refine ⟨9602099864235981675726925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12802799818981308900969233 9602099864235981675726925)
  ·
    refine ⟨3600787449088493128397597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9602099864235981675726925 3600787449088493128397597)
    ·
      refine ⟨1350295293408184923149099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3600787449088493128397597 1350295293408184923149099)
      ·
        refine ⟨2025442940112277384723649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350295293408184923149099 2025442940112277384723649)
        ·
          refine ⟨1519082205084208038542737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2025442940112277384723649 1519082205084208038542737)
          ·
            refine ⟨1139311653813156028907053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1519082205084208038542737 1139311653813156028907053)
            ·
              refine ⟨427241870179933510840145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1139311653813156028907053 427241870179933510840145)
              ·
                refine ⟨320431402634950133130109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427241870179933510840145 320431402634950133130109)
                ·
                  refine ⟨120161775988106299923791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320431402634950133130109 120161775988106299923791)
                  ·
                    rfl

theorem cell21_526532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_526532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526532 prefixEnd_526532 := by exact prefixLift 526532
  have htrace : WordTrace (prefixWord ++ tailWord_526532) baseStart_526532 baseEnd_526532 := by
    simpa [prefixWord, tailWord_526532, baseEnd_526532] using wordTrace_append hprefix tailTrace_526532
  have hstable : (prefixWord ++ tailWord_526532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526532).length < 2 ^ (prefixWord ++ tailWord_526532).sum := by decide
  have hdescent : baseEnd_526532 < baseStart_526532 := by decide
  rcases family_descends (prefixWord ++ tailWord_526532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526546 : List Nat := [3, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_526546 : Nat := 118140960795 + 526546 * 2 ^ 59
def prefixEnd_526546 : Nat := 4983230072969 + 3 ^ 40 * 526546 * 2
def baseEnd_526546 : Nat := 120164970978845386690429

theorem tailTrace_526546 : CollatzResearch.WordTrace tailWord_526546 prefixEnd_526546 120164970978845386690429 := by
  unfold tailWord_526546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4801177587605310935615873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12803140233614162494975661 4801177587605310935615873)
  ·
    refine ⟨3600883190703983201711905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4801177587605310935615873 3600883190703983201711905)
    ·
      refine ⟨2700662393027987401283929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3600883190703983201711905 2700662393027987401283929)
      ·
        refine ⟨2025496794770990550962947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2700662393027987401283929 2025496794770990550962947)
        ·
          refine ⟨3038245192156485826444421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025496794770990550962947 3038245192156485826444421)
          ·
            refine ⟨569670973529341092458329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3038245192156485826444421 569670973529341092458329)
            ·
              refine ⟨427253230147005819343747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569670973529341092458329 427253230147005819343747)
              ·
                refine ⟨640879845220508729015621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427253230147005819343747 640879845220508729015621)
                ·
                  refine ⟨120164970978845386690429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640879845220508729015621 120164970978845386690429)
                  ·
                    rfl

theorem cell21_526546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_526546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526546 prefixEnd_526546 := by exact prefixLift 526546
  have htrace : WordTrace (prefixWord ++ tailWord_526546) baseStart_526546 baseEnd_526546 := by
    simpa [prefixWord, tailWord_526546, baseEnd_526546] using wordTrace_append hprefix tailTrace_526546
  have hstable : (prefixWord ++ tailWord_526546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526546).length < 2 ^ (prefixWord ++ tailWord_526546).sum := by decide
  have hdescent : baseEnd_526546 < baseStart_526546 := by decide
  rcases family_descends (prefixWord ++ tailWord_526546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526574 : List Nat := [4, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_526574 : Nat := 118140960795 + 526574 * 2 ^ 59
def prefixEnd_526574 : Nat := 4983230072969 + 3 ^ 40 * 526574 * 2
def baseEnd_526574 : Nat := 120171360960323560223705

theorem tailTrace_526574 : CollatzResearch.WordTrace tailWord_526574 prefixEnd_526574 120171360960323560223705 := by
  unfold tailWord_526574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2400716449289975565560347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12803821062879869682988517 2400716449289975565560347)
  ·
    refine ⟨3601074673934963348340521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2400716449289975565560347 3601074673934963348340521)
    ·
      refine ⟨2700806005451222511255391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3601074673934963348340521 2700806005451222511255391)
      ·
        refine ⟨4051209008176833766883087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2700806005451222511255391 4051209008176833766883087)
        ·
          refine ⟨6076813512265250650324631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4051209008176833766883087 6076813512265250650324631)
          ·
            refine ⟨9115220268397875975486947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6076813512265250650324631 9115220268397875975486947)
            ·
              refine ⟨13672830402596813963230421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9115220268397875975486947 13672830402596813963230421)
              ·
                refine ⟨320456962560862827263213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13672830402596813963230421 320456962560862827263213)
                ·
                  refine ⟨120171360960323560223705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320456962560862827263213 120171360960323560223705)
                  ·
                    rfl

theorem cell21_526574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_526574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526574 prefixEnd_526574 := by exact prefixLift 526574
  have htrace : WordTrace (prefixWord ++ tailWord_526574) baseStart_526574 baseEnd_526574 := by
    simpa [prefixWord, tailWord_526574, baseEnd_526574] using wordTrace_append hprefix tailTrace_526574
  have hstable : (prefixWord ++ tailWord_526574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526574).length < 2 ^ (prefixWord ++ tailWord_526574).sum := by decide
  have hdescent : baseEnd_526574 < baseStart_526574 := by decide
  rcases family_descends (prefixWord ++ tailWord_526574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526588 : List Nat := [2, 2, 2, 1, 4, 1, 1, 4, 4]
def baseStart_526588 : Nat := 118140960795 + 526588 * 2 ^ 59
def prefixEnd_526588 : Nat := 4983230072969 + 3 ^ 40 * 526588 * 2
def baseEnd_526588 : Nat := 120174555951062646990343

theorem tailTrace_526588 : CollatzResearch.WordTrace tailWord_526588 prefixEnd_526588 120174555951062646990343 := by
  unfold tailWord_526588
  simp only [CollatzResearch.WordTrace]
  refine ⟨9603121108134542457746209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12804161477512723276994945 9603121108134542457746209)
  ·
    refine ⟨7202340831100906843309657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9603121108134542457746209 7202340831100906843309657)
    ·
      refine ⟨5401755623325680132482243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7202340831100906843309657 5401755623325680132482243)
      ·
        refine ⟨8102633434988520198723365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5401755623325680132482243 8102633434988520198723365)
        ·
          refine ⟨1519243769060347537260631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8102633434988520198723365 1519243769060347537260631)
          ·
            refine ⟨2278865653590521305890947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519243769060347537260631 2278865653590521305890947)
            ·
              refine ⟨3418298480385781958836421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278865653590521305890947 3418298480385781958836421)
              ·
                refine ⟨640930965072334117281829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3418298480385781958836421 640930965072334117281829)
                ·
                  refine ⟨120174555951062646990343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640930965072334117281829 120174555951062646990343)
                  ·
                    rfl

theorem cell21_526588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_526588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526588 prefixEnd_526588 := by exact prefixLift 526588
  have htrace : WordTrace (prefixWord ++ tailWord_526588) baseStart_526588 baseEnd_526588 := by
    simpa [prefixWord, tailWord_526588, baseEnd_526588] using wordTrace_append hprefix tailTrace_526588
  have hstable : (prefixWord ++ tailWord_526588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526588).length < 2 ^ (prefixWord ++ tailWord_526588).sum := by decide
  have hdescent : baseEnd_526588 < baseStart_526588 := by decide
  rcases family_descends (prefixWord ++ tailWord_526588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526602 : List Nat := [3, 1, 2, 2, 1, 1, 5, 6]
def baseStart_526602 : Nat := 118140960795 + 526602 * 2 ^ 59
def prefixEnd_526602 : Nat := 4983230072969 + 3 ^ 40 * 526602 * 2
def baseEnd_526602 : Nat := 40059250313933911252327

theorem tailTrace_526602 : CollatzResearch.WordTrace tailWord_526602 prefixEnd_526602 40059250313933911252327 := by
  unfold tailWord_526602
  simp only [CollatzResearch.WordTrace]
  refine ⟨4801688209554591326625515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12804501892145576871001373 4801688209554591326625515)
  ·
    refine ⟨7202532314331886989938273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4801688209554591326625515 7202532314331886989938273)
    ·
      refine ⟨5401899235748915242453705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7202532314331886989938273 5401899235748915242453705)
      ·
        refine ⟨4051424426811686431840279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5401899235748915242453705 4051424426811686431840279)
        ·
          refine ⟨6077136640217529647760419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4051424426811686431840279 6077136640217529647760419)
          ·
            refine ⟨9115704960326294471640629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6077136640217529647760419 9115704960326294471640629)
            ·
              refine ⟨854597340030590106716309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9115704960326294471640629 854597340030590106716309)
              ·
                refine ⟨40059250313933911252327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 854597340030590106716309 40059250313933911252327)
                ·
                  rfl

theorem cell21_526602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_526602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526602 prefixEnd_526602 := by exact prefixLift 526602
  have htrace : WordTrace (prefixWord ++ tailWord_526602) baseStart_526602 baseEnd_526602 := by
    simpa [prefixWord, tailWord_526602, baseEnd_526602] using wordTrace_append hprefix tailTrace_526602
  have hstable : (prefixWord ++ tailWord_526602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526602).length < 2 ^ (prefixWord ++ tailWord_526602).sum := by decide
  have hdescent : baseEnd_526602 < baseStart_526602 := by decide
  rcases family_descends (prefixWord ++ tailWord_526602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526650 : List Nat := [3, 1, 1, 1, 4, 2, 2, 4, 3]
def baseStart_526650 : Nat := 118140960795 + 526650 * 2 ^ 59
def prefixEnd_526650 : Nat := 4983230072969 + 3 ^ 40 * 526650 * 2
def baseEnd_526650 : Nat := 120188705195764316956883

theorem tailTrace_526650 : CollatzResearch.WordTrace tailWord_526650 prefixEnd_526650 120188705195764316956883 := by
  unfold tailWord_526650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4802125885511117376062351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12805669028029646336166269 4802125885511117376062351)
  ·
    refine ⟨7203188828266676064093527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4802125885511117376062351 7203188828266676064093527)
    ·
      refine ⟨10804783242400014096140291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7203188828266676064093527 10804783242400014096140291)
      ·
        refine ⟨16207174863600021144210437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10804783242400014096140291 16207174863600021144210437)
        ·
          refine ⟨3038845286925003964539457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16207174863600021144210437 3038845286925003964539457)
          ·
            refine ⟨2279133965193752973404593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3038845286925003964539457 2279133965193752973404593)
            ·
              refine ⟨1709350473895314730053445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2279133965193752973404593 1709350473895314730053445)
              ·
                refine ⟨320503213855371511885021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1709350473895314730053445 320503213855371511885021)
                ·
                  refine ⟨120188705195764316956883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320503213855371511885021 120188705195764316956883)
                  ·
                    rfl

theorem cell21_526650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_526650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526650 prefixEnd_526650 := by exact prefixLift 526650
  have htrace : WordTrace (prefixWord ++ tailWord_526650) baseStart_526650 baseEnd_526650 := by
    simpa [prefixWord, tailWord_526650, baseEnd_526650] using wordTrace_append hprefix tailTrace_526650
  have hstable : (prefixWord ++ tailWord_526650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526650).length < 2 ^ (prefixWord ++ tailWord_526650).sum := by decide
  have hdescent : baseEnd_526650 < baseStart_526650 := by decide
  rcases family_descends (prefixWord ++ tailWord_526650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526760 : List Nat := [2, 1, 6, 1, 1, 1, 4, 2, 3]
def baseStart_526760 : Nat := 118140960795 + 526760 * 2 ^ 59
def prefixEnd_526760 : Nat := 4983230072969 + 3 ^ 40 * 526760 * 2
def baseEnd_526760 : Nat := 120213808694428570123325

theorem tailTrace_526760 : CollatzResearch.WordTrace tailWord_526760 prefixEnd_526760 120213808694428570123325 := by
  unfold tailWord_526760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9606257785822979145376867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12808343714430638860502489 9606257785822979145376867)
  ·
    refine ⟨14409386678734468718065301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9606257785822979145376867 14409386678734468718065301)
    ·
      refine ⟨675440000565678221159311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14409386678734468718065301 675440000565678221159311)
      ·
        refine ⟨1013160000848517331738967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675440000565678221159311 1013160000848517331738967)
        ·
          refine ⟨1519740001272775997608451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013160000848517331738967 1519740001272775997608451)
          ·
            refine ⟨2279610001909163996412677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519740001272775997608451 2279610001909163996412677)
            ·
              refine ⟨427426875357968249327377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2279610001909163996412677 427426875357968249327377)
              ·
                refine ⟨320570156518476186995533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427426875357968249327377 320570156518476186995533)
                ·
                  refine ⟨120213808694428570123325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320570156518476186995533 120213808694428570123325)
                  ·
                    rfl

theorem cell21_526760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 3].length) (baseStart_526760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526760 prefixEnd_526760 := by exact prefixLift 526760
  have htrace : WordTrace (prefixWord ++ tailWord_526760) baseStart_526760 baseEnd_526760 := by
    simpa [prefixWord, tailWord_526760, baseEnd_526760] using wordTrace_append hprefix tailTrace_526760
  have hstable : (prefixWord ++ tailWord_526760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526760).length < 2 ^ (prefixWord ++ tailWord_526760).sum := by decide
  have hdescent : baseEnd_526760 < baseStart_526760 := by decide
  rcases family_descends (prefixWord ++ tailWord_526760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526788 : List Nat := [2, 3, 3, 2, 2, 1, 3, 5]
def baseStart_526788 : Nat := 118140960795 + 526788 * 2 ^ 59
def prefixEnd_526788 : Nat := 4983230072969 + 3 ^ 40 * 526788 * 2
def baseEnd_526788 : Nat := 40073399558635581218867

theorem tailTrace_526788 : CollatzResearch.WordTrace tailWord_526788 prefixEnd_526788 40073399558635581218867 := by
  unfold tailWord_526788
  simp only [CollatzResearch.WordTrace]
  refine ⟨9606768407772259536386509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12809024543696346048515345 9606768407772259536386509)
  ·
    refine ⟨3602538152914597326144941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9606768407772259536386509 3602538152914597326144941)
    ·
      refine ⟨1350951807342973997304353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3602538152914597326144941 1350951807342973997304353)
      ·
        refine ⟨1013213855507230497978265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1350951807342973997304353 1013213855507230497978265)
        ·
          refine ⟨759910391630422873483699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1013213855507230497978265 759910391630422873483699)
          ·
            refine ⟨1139865587445634310225549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759910391630422873483699 1139865587445634310225549)
            ·
              refine ⟨427449595292112866334581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1139865587445634310225549 427449595292112866334581)
              ·
                refine ⟨40073399558635581218867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 427449595292112866334581 40073399558635581218867)
                ·
                  rfl

theorem cell21_526788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_526788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526788 prefixEnd_526788 := by exact prefixLift 526788
  have htrace : WordTrace (prefixWord ++ tailWord_526788) baseStart_526788 baseEnd_526788 := by
    simpa [prefixWord, tailWord_526788, baseEnd_526788] using wordTrace_append hprefix tailTrace_526788
  have hstable : (prefixWord ++ tailWord_526788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526788).length < 2 ^ (prefixWord ++ tailWord_526788).sum := by decide
  have hdescent : baseEnd_526788 < baseStart_526788 := by decide
  rcases family_descends (prefixWord ++ tailWord_526788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526940 : List Nat := [2, 2, 4, 1, 4, 1, 1, 6]
def baseStart_526940 : Nat := 118140960795 + 526940 * 2 ^ 59
def prefixEnd_526940 : Nat := 4983230072969 + 3 ^ 40 * 526940 * 2
def baseEnd_526940 : Nat := 40084962382262752374319

theorem tailTrace_526940 : CollatzResearch.WordTrace tailWord_526940 prefixEnd_526940 40084962382262752374319 := by
  unfold tailWord_526940
  simp only [CollatzResearch.WordTrace]
  refine ⟨9609540355496924516153137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12812720473995899354870849 9609540355496924516153137)
  ·
    refine ⟨7207155266622693387114853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9609540355496924516153137 7207155266622693387114853)
    ·
      refine ⟨1351341612491755010084035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7207155266622693387114853 1351341612491755010084035)
      ·
        refine ⟨2027012418737632515126053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1351341612491755010084035 2027012418737632515126053)
        ·
          refine ⟨380064828513306096586135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2027012418737632515126053 380064828513306096586135)
          ·
            refine ⟨570097242769959144879203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380064828513306096586135 570097242769959144879203)
            ·
              refine ⟨855145864154938717318805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570097242769959144879203 855145864154938717318805)
              ·
                refine ⟨40084962382262752374319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 855145864154938717318805 40084962382262752374319)
                ·
                  rfl

theorem cell21_526940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 6].length) (baseStart_526940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_526940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_526940 prefixEnd_526940 := by exact prefixLift 526940
  have htrace : WordTrace (prefixWord ++ tailWord_526940) baseStart_526940 baseEnd_526940 := by
    simpa [prefixWord, tailWord_526940, baseEnd_526940] using wordTrace_append hprefix tailTrace_526940
  have hstable : (prefixWord ++ tailWord_526940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526940).length < 2 ^ (prefixWord ++ tailWord_526940).sum := by decide
  have hdescent : baseEnd_526940 < baseStart_526940 := by decide
  rcases family_descends (prefixWord ++ tailWord_526940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527002 : List Nat := [3, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_527002 : Nat := 118140960795 + 527002 * 2 ^ 59
def prefixEnd_527002 : Nat := 4983230072969 + 3 ^ 40 * 527002 * 2
def baseEnd_527002 : Nat := 120269036391489927089497

theorem tailTrace_527002 : CollatzResearch.WordTrace tailWord_527002 prefixEnd_527002 120269036391489927089497 := by
  unfold tailWord_527002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4805335509192308405265815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12814228024512822414042173 4805335509192308405265815)
  ·
    refine ⟨7208003263788462607898723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4805335509192308405265815 7208003263788462607898723)
    ·
      refine ⟨10812004895682693911848085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7208003263788462607898723 10812004895682693911848085)
      ·
        refine ⟨506812729485126277117879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10812004895682693911848085 506812729485126277117879)
        ·
          refine ⟨760219094227689415676819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506812729485126277117879 760219094227689415676819)
          ·
            refine ⟨1140328641341534123515229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760219094227689415676819 1140328641341534123515229)
            ·
              refine ⟨427623240503075296318211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140328641341534123515229 427623240503075296318211)
              ·
                refine ⟨641434860754612944477317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427623240503075296318211 641434860754612944477317)
                ·
                  refine ⟨120269036391489927089497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 641434860754612944477317 120269036391489927089497)
                  ·
                    rfl

theorem cell21_527002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_527002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527002 prefixEnd_527002 := by exact prefixLift 527002
  have htrace : WordTrace (prefixWord ++ tailWord_527002) baseStart_527002 baseEnd_527002 := by
    simpa [prefixWord, tailWord_527002, baseEnd_527002] using wordTrace_append hprefix tailTrace_527002
  have hstable : (prefixWord ++ tailWord_527002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527002).length < 2 ^ (prefixWord ++ tailWord_527002).sum := by decide
  have hdescent : baseEnd_527002 < baseStart_527002 := by decide
  rcases family_descends (prefixWord ++ tailWord_527002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527061 : List Nat := [1, 3, 2, 5, 1, 1, 1, 3, 4]
def baseStart_527061 : Nat := 118140960795 + 527061 * 2 ^ 59
def prefixEnd_527061 : Nat := 4983230072969 + 3 ^ 40 * 527061 * 2
def baseEnd_527061 : Nat := 120282500995318935606043

theorem tailTrace_527061 : CollatzResearch.WordTrace tailWord_527061 prefixEnd_527061 120282500995318935606043 := by
  unfold tailWord_527061
  simp only [CollatzResearch.WordTrace]
  refine ⟨19223493943555486697461037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12815662629036991131640691 19223493943555486697461037)
  ·
    refine ⟨7208810228833307511547889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19223493943555486697461037 7208810228833307511547889)
    ·
      refine ⟨5406607671624980633660917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7208810228833307511547889 5406607671624980633660917)
      ·
        refine ⟨506869469214841934405711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5406607671624980633660917 506869469214841934405711)
        ·
          refine ⟨760304203822262901608567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506869469214841934405711 760304203822262901608567)
          ·
            refine ⟨1140456305733394352412851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760304203822262901608567 1140456305733394352412851)
            ·
              refine ⟨1710684458600091528619277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140456305733394352412851 1710684458600091528619277)
              ·
                refine ⟨641506671975034323232229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1710684458600091528619277 641506671975034323232229)
                ·
                  refine ⟨120282500995318935606043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 641506671975034323232229 120282500995318935606043)
                  ·
                    rfl

theorem cell21_527061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_527061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527061 prefixEnd_527061 := by exact prefixLift 527061
  have htrace : WordTrace (prefixWord ++ tailWord_527061) baseStart_527061 baseEnd_527061 := by
    simpa [prefixWord, tailWord_527061, baseEnd_527061] using wordTrace_append hprefix tailTrace_527061
  have hstable : (prefixWord ++ tailWord_527061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527061).length < 2 ^ (prefixWord ++ tailWord_527061).sum := by decide
  have hdescent : baseEnd_527061 < baseStart_527061 := by decide
  rcases family_descends (prefixWord ++ tailWord_527061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527089 : List Nat := [1, 2, 2, 2, 2, 2, 2, 5, 3]
def baseStart_527089 : Nat := 118140960795 + 527089 * 2 ^ 59
def prefixEnd_527089 : Nat := 4983230072969 + 3 ^ 40 * 527089 * 2
def baseEnd_527089 : Nat := 120288890976797109139319

theorem tailTrace_527089 : CollatzResearch.WordTrace tailWord_527089 prefixEnd_527089 120288890976797109139319 := by
  unfold tailWord_527089
  simp only [CollatzResearch.WordTrace]
  refine ⟨19224515187454047479480321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12816343458302698319653547 19224515187454047479480321)
  ·
    refine ⟨14418386390590535609610241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19224515187454047479480321 14418386390590535609610241)
    ·
      refine ⟨10813789792942901707207681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14418386390590535609610241 10813789792942901707207681)
      ·
        refine ⟨8110342344707176280405761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10813789792942901707207681 8110342344707176280405761)
        ·
          refine ⟨6082756758530382210304321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8110342344707176280405761 6082756758530382210304321)
          ·
            refine ⟨4562067568897786657728241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6082756758530382210304321 4562067568897786657728241)
            ·
              refine ⟨3421550676673339993296181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4562067568897786657728241 3421550676673339993296181)
              ·
                refine ⟨320770375938125624371517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3421550676673339993296181 320770375938125624371517)
                ·
                  refine ⟨120288890976797109139319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320770375938125624371517 120288890976797109139319)
                  ·
                    rfl

theorem cell21_527089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 3].length) (baseStart_527089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527089 prefixEnd_527089 := by exact prefixLift 527089
  have htrace : WordTrace (prefixWord ++ tailWord_527089) baseStart_527089 baseEnd_527089 := by
    simpa [prefixWord, tailWord_527089, baseEnd_527089] using wordTrace_append hprefix tailTrace_527089
  have hstable : (prefixWord ++ tailWord_527089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527089).length < 2 ^ (prefixWord ++ tailWord_527089).sum := by decide
  have hdescent : baseEnd_527089 < baseStart_527089 := by decide
  rcases family_descends (prefixWord ++ tailWord_527089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527092 : List Nat := [2, 6, 1, 1, 3, 8]
def baseStart_527092 : Nat := 118140960795 + 527092 * 2 ^ 59
def prefixEnd_527092 : Nat := 4983230072969 + 3 ^ 40 * 527092 * 2
def baseEnd_527092 : Nat := 4455169467321102614419

theorem tailTrace_527092 : CollatzResearch.WordTrace tailWord_527092 prefixEnd_527092 4455169467321102614419 := by
  unfold tailWord_527092
  simp only [CollatzResearch.WordTrace]
  refine ⟨9612312303221589495919765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12816416404295452661226353 9612312303221589495919765)
  ·
    refine ⟨450577139213512007621239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9612312303221589495919765 450577139213512007621239)
    ·
      refine ⟨675865708820268011431859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450577139213512007621239 675865708820268011431859)
      ·
        refine ⟨1013798563230402017147789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675865708820268011431859 1013798563230402017147789)
        ·
          refine ⟨380174461211400756430421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1013798563230402017147789 380174461211400756430421)
          ·
            refine ⟨4455169467321102614419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 380174461211400756430421 4455169467321102614419)
            ·
              rfl

theorem cell21_527092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 8].length) (baseStart_527092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527092 prefixEnd_527092 := by exact prefixLift 527092
  have htrace : WordTrace (prefixWord ++ tailWord_527092) baseStart_527092 baseEnd_527092 := by
    simpa [prefixWord, tailWord_527092, baseEnd_527092] using wordTrace_append hprefix tailTrace_527092
  have hstable : (prefixWord ++ tailWord_527092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527092).length < 2 ^ (prefixWord ++ tailWord_527092).sum := by decide
  have hdescent : baseEnd_527092 < baseStart_527092 := by decide
  rcases family_descends (prefixWord ++ tailWord_527092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527193 : List Nat := [1, 2, 1, 2, 2, 5, 1, 7]
def baseStart_527193 : Nat := 118140960795 + 527193 * 2 ^ 59
def prefixEnd_527193 : Nat := 4983230072969 + 3 ^ 40 * 527193 * 2
def baseEnd_527193 : Nat := 40104208397905346468591

theorem tailTrace_527193 : CollatzResearch.WordTrace tailWord_527193 prefixEnd_527193 40104208397905346468591 := by
  unfold tailWord_527193
  simp only [CollatzResearch.WordTrace]
  refine ⟨19228308379077273241266233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12818872252718182160844155 19228308379077273241266233)
  ·
    refine ⟨14421231284307954930949675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19228308379077273241266233 14421231284307954930949675)
    ·
      refine ⟨21631846926461932396424513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14421231284307954930949675 21631846926461932396424513)
      ·
        refine ⟨16223885194846449297318385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21631846926461932396424513 16223885194846449297318385)
        ·
          refine ⟨12167913896134836972988789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16223885194846449297318385 12167913896134836972988789)
          ·
            refine ⟨1140741927762640966217699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12167913896134836972988789 1140741927762640966217699)
            ·
              refine ⟨1711112891643961449326549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140741927762640966217699 1711112891643961449326549)
              ·
                refine ⟨40104208397905346468591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1711112891643961449326549 40104208397905346468591)
                ·
                  rfl

theorem cell21_527193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 7].length) (baseStart_527193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527193 prefixEnd_527193 := by exact prefixLift 527193
  have htrace : WordTrace (prefixWord ++ tailWord_527193) baseStart_527193 baseEnd_527193 := by
    simpa [prefixWord, tailWord_527193, baseEnd_527193] using wordTrace_append hprefix tailTrace_527193
  have hstable : (prefixWord ++ tailWord_527193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527193).length < 2 ^ (prefixWord ++ tailWord_527193).sum := by decide
  have hdescent : baseEnd_527193 < baseStart_527193 := by decide
  rcases family_descends (prefixWord ++ tailWord_527193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527309 : List Nat := [1, 6, 3, 1, 1, 1, 2, 3, 3]
def baseStart_527309 : Nat := 118140960795 + 527309 * 2 ^ 59
def prefixEnd_527309 : Nat := 4983230072969 + 3 ^ 40 * 527309 * 2
def baseEnd_527309 : Nat := 120339097974125615472203

theorem tailTrace_527309 : CollatzResearch.WordTrace tailWord_527309 prefixEnd_527309 120339097974125615472203 := by
  unfold tailWord_527309
  simp only [CollatzResearch.WordTrace]
  refine ⟨19232539246657025052488981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12821692831104683368325987 19232539246657025052488981)
  ·
    refine ⟨901525277187048049335421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19232539246657025052488981 901525277187048049335421)
    ·
      refine ⟨338071978945143018500783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 901525277187048049335421 338071978945143018500783)
      ·
        refine ⟨507107968417714527751175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338071978945143018500783 507107968417714527751175)
        ·
          refine ⟨760661952626571791626763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507107968417714527751175 760661952626571791626763)
          ·
            refine ⟨1140992928939857687440145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760661952626571791626763 1140992928939857687440145)
            ·
              refine ⟨855744696704893265580109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140992928939857687440145 855744696704893265580109)
              ·
                refine ⟨320904261264334974592541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855744696704893265580109 320904261264334974592541)
                ·
                  refine ⟨120339097974125615472203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320904261264334974592541 120339097974125615472203)
                  ·
                    rfl

theorem cell21_527309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_527309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527309 prefixEnd_527309 := by exact prefixLift 527309
  have htrace : WordTrace (prefixWord ++ tailWord_527309) baseStart_527309 baseEnd_527309 := by
    simpa [prefixWord, tailWord_527309, baseEnd_527309] using wordTrace_append hprefix tailTrace_527309
  have hstable : (prefixWord ++ tailWord_527309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527309).length < 2 ^ (prefixWord ++ tailWord_527309).sum := by decide
  have hdescent : baseEnd_527309 < baseStart_527309 := by decide
  rcases family_descends (prefixWord ++ tailWord_527309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527393 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 5]
def baseStart_527393 : Nat := 118140960795 + 527393 * 2 ^ 59
def prefixEnd_527393 : Nat := 4983230072969 + 3 ^ 40 * 527393 * 2
def baseEnd_527393 : Nat := 120358267918560136072031

theorem tailTrace_527393 : CollatzResearch.WordTrace tailWord_527393 prefixEnd_527393 120358267918560136072031 := by
  unfold tailWord_527393
  simp only [CollatzResearch.WordTrace]
  refine ⟨19235602978352707398546833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12823735318901804932364555 19235602978352707398546833)
  ·
    refine ⟨14426702233764530548910125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19235602978352707398546833 14426702233764530548910125)
    ·
      refine ⟨5410013337661698955841297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14426702233764530548910125 5410013337661698955841297)
      ·
        refine ⟨4057510003246274216880973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5410013337661698955841297 4057510003246274216880973)
        ·
          refine ⟨1521566251217352831330365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4057510003246274216880973 1521566251217352831330365)
          ·
            refine ⟨570587344206507311748887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1521566251217352831330365 570587344206507311748887)
            ·
              refine ⟨855881016309760967623331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570587344206507311748887 855881016309760967623331)
              ·
                refine ⟨1283821524464641451434997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855881016309760967623331 1283821524464641451434997)
                ·
                  refine ⟨120358267918560136072031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1283821524464641451434997 120358267918560136072031)
                  ·
                    rfl

theorem cell21_527393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_527393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527393 prefixEnd_527393 := by exact prefixLift 527393
  have htrace : WordTrace (prefixWord ++ tailWord_527393) baseStart_527393 baseEnd_527393 := by
    simpa [prefixWord, tailWord_527393, baseEnd_527393] using wordTrace_append hprefix tailTrace_527393
  have hstable : (prefixWord ++ tailWord_527393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527393).length < 2 ^ (prefixWord ++ tailWord_527393).sum := by decide
  have hdescent : baseEnd_527393 < baseStart_527393 := by decide
  rcases family_descends (prefixWord ++ tailWord_527393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527421 : List Nat := [1, 4, 1, 3, 1, 2, 2, 7]
def baseStart_527421 : Nat := 118140960795 + 527421 * 2 ^ 59
def prefixEnd_527421 : Nat := 4983230072969 + 3 ^ 40 * 527421 * 2
def baseEnd_527421 : Nat := 40121552633346103201769

theorem tailTrace_527421 : CollatzResearch.WordTrace tailWord_527421 prefixEnd_527421 40121552633346103201769 := by
  unfold tailWord_527421
  simp only [CollatzResearch.WordTrace]
  refine ⟨19236624222251268180566117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12824416148167512120377411 19236624222251268180566117)
  ·
    refine ⟨3606867041672112783856147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19236624222251268180566117 3606867041672112783856147)
    ·
      refine ⟨5410300562508169175784221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3606867041672112783856147 5410300562508169175784221)
      ·
        refine ⟨2028862710940563440919083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5410300562508169175784221 2028862710940563440919083)
        ·
          refine ⟨3043294066410845161378625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2028862710940563440919083 3043294066410845161378625)
          ·
            refine ⟨2282470549808133871033969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3043294066410845161378625 2282470549808133871033969)
            ·
              refine ⟨1711852912356100403275477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2282470549808133871033969 1711852912356100403275477)
              ·
                refine ⟨40121552633346103201769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1711852912356100403275477 40121552633346103201769)
                ·
                  rfl

theorem cell21_527421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 7].length) (baseStart_527421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527421 prefixEnd_527421 := by exact prefixLift 527421
  have htrace : WordTrace (prefixWord ++ tailWord_527421) baseStart_527421 baseEnd_527421 := by
    simpa [prefixWord, tailWord_527421, baseEnd_527421] using wordTrace_append hprefix tailTrace_527421
  have hstable : (prefixWord ++ tailWord_527421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527421).length < 2 ^ (prefixWord ++ tailWord_527421).sum := by decide
  have hdescent : baseEnd_527421 < baseStart_527421 := by decide
  rcases family_descends (prefixWord ++ tailWord_527421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527452 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 5]
def baseStart_527452 : Nat := 118140960795 + 527452 * 2 ^ 59
def prefixEnd_527452 : Nat := 4983230072969 + 3 ^ 40 * 527452 * 2
def baseEnd_527452 : Nat := 120371732522389144588577

theorem tailTrace_527452 : CollatzResearch.WordTrace tailWord_527452 prefixEnd_527452 120371732522389144588577 := by
  unfold tailWord_527452
  simp only [CollatzResearch.WordTrace]
  refine ⟨9618877442569480237472305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12825169923425973649963073 9618877442569480237472305)
  ·
    refine ⟨7214158081927110178104229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9618877442569480237472305 7214158081927110178104229)
    ·
      refine ⟨1352654640361333158394543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7214158081927110178104229 1352654640361333158394543)
      ·
        refine ⟨2028981960541999737591815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1352654640361333158394543 2028981960541999737591815)
        ·
          refine ⟨3043472940812999606387723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2028981960541999737591815 3043472940812999606387723)
          ·
            refine ⟨4565209411219499409581585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3043472940812999606387723 4565209411219499409581585)
            ·
              refine ⟨3423907058414624557186189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4565209411219499409581585 3423907058414624557186189)
              ·
                refine ⟨1283965146905484208944821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3423907058414624557186189 1283965146905484208944821)
                ·
                  refine ⟨120371732522389144588577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1283965146905484208944821 120371732522389144588577)
                  ·
                    rfl

theorem cell21_527452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_527452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527452 prefixEnd_527452 := by exact prefixLift 527452
  have htrace : WordTrace (prefixWord ++ tailWord_527452) baseStart_527452 baseEnd_527452 := by
    simpa [prefixWord, tailWord_527452, baseEnd_527452] using wordTrace_append hprefix tailTrace_527452
  have hstable : (prefixWord ++ tailWord_527452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527452).length < 2 ^ (prefixWord ++ tailWord_527452).sum := by decide
  have hdescent : baseEnd_527452 < baseStart_527452 := by decide
  rcases family_descends (prefixWord ++ tailWord_527452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527480 : List Nat := [2, 1, 2, 1, 1, 1, 4, 9]
def baseStart_527480 : Nat := 118140960795 + 527480 * 2 ^ 59
def prefixEnd_527480 : Nat := 4983230072969 + 3 ^ 40 * 527480 * 2
def baseEnd_527480 : Nat := 40126040834622439373951

theorem tailTrace_527480 : CollatzResearch.WordTrace tailWord_527480 prefixEnd_527480 40126040834622439373951 := by
  unfold tailWord_527480
  simp only [CollatzResearch.WordTrace]
  refine ⟨9619388064518760628481947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12825850752691680837975929 9619388064518760628481947)
  ·
    refine ⟨14429082096778140942722921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9619388064518760628481947 14429082096778140942722921)
    ·
      refine ⟨10821811572583605707042191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14429082096778140942722921 10821811572583605707042191)
      ·
        refine ⟨16232717358875408560563287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10821811572583605707042191 16232717358875408560563287)
        ·
          refine ⟨24349076038313112840844931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16232717358875408560563287 24349076038313112840844931)
          ·
            refine ⟨36523614057469669261267397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24349076038313112840844931 36523614057469669261267397)
            ·
              refine ⟨6848177635775562986487637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36523614057469669261267397 6848177635775562986487637)
              ·
                refine ⟨40126040834622439373951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6848177635775562986487637 40126040834622439373951)
                ·
                  rfl

theorem cell21_527480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_527480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527480 prefixEnd_527480 := by exact prefixLift 527480
  have htrace : WordTrace (prefixWord ++ tailWord_527480) baseStart_527480 baseEnd_527480 := by
    simpa [prefixWord, tailWord_527480, baseEnd_527480] using wordTrace_append hprefix tailTrace_527480
  have hstable : (prefixWord ++ tailWord_527480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527480).length < 2 ^ (prefixWord ++ tailWord_527480).sum := by decide
  have hdescent : baseEnd_527480 < baseStart_527480 := by decide
  rcases family_descends (prefixWord ++ tailWord_527480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527545 : List Nat := [1, 2, 1, 4, 1, 3, 3, 3, 3]
def baseStart_527545 : Nat := 118140960795 + 527545 * 2 ^ 59
def prefixEnd_527545 : Nat := 4983230072969 + 3 ^ 40 * 527545 * 2
def baseEnd_527545 : Nat := 120392956389441649538387

theorem tailTrace_527545 : CollatzResearch.WordTrace tailWord_527545 prefixEnd_527545 120392956389441649538387 := by
  unfold tailWord_527545
  simp only [CollatzResearch.WordTrace]
  refine ⟨19241146873802037358080089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12827431249201358238720059 19241146873802037358080089)
  ·
    refine ⟨14430860155351528018560067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19241146873802037358080089 14430860155351528018560067)
    ·
      refine ⟨21646290233027292027840101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14430860155351528018560067 21646290233027292027840101)
      ·
        refine ⟨4058679418692617255220019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21646290233027292027840101 4058679418692617255220019)
        ·
          refine ⟨6088019128038925882830029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4058679418692617255220019 6088019128038925882830029)
          ·
            refine ⟨2283007173014597206061261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6088019128038925882830029 2283007173014597206061261)
            ·
              refine ⟨856127689880473952272973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2283007173014597206061261 856127689880473952272973)
              ·
                refine ⟨321047883705177732102365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 856127689880473952272973 321047883705177732102365)
                ·
                  refine ⟨120392956389441649538387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321047883705177732102365 120392956389441649538387)
                  ·
                    rfl

theorem cell21_527545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 3].length) (baseStart_527545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527545 prefixEnd_527545 := by exact prefixLift 527545
  have htrace : WordTrace (prefixWord ++ tailWord_527545) baseStart_527545 baseEnd_527545 := by
    simpa [prefixWord, tailWord_527545, baseEnd_527545] using wordTrace_append hprefix tailTrace_527545
  have hstable : (prefixWord ++ tailWord_527545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527545).length < 2 ^ (prefixWord ++ tailWord_527545).sum := by decide
  have hdescent : baseEnd_527545 < baseStart_527545 := by decide
  rcases family_descends (prefixWord ++ tailWord_527545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527562 : List Nat := [3, 1, 2, 1, 3, 3, 3, 2, 3]
def baseStart_527562 : Nat := 118140960795 + 527562 * 2 ^ 59
def prefixEnd_527562 : Nat := 4983230072969 + 3 ^ 40 * 527562 * 2
def baseEnd_527562 : Nat := 120396836021053397755019

theorem tailTrace_527562 : CollatzResearch.WordTrace tailWord_527562 prefixEnd_527562 120396836021053397755019 := by
  unfold tailWord_527562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4810441728685112315362235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12827844609826966174299293 4810441728685112315362235)
  ·
    refine ⟨7215662593027668473043353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4810441728685112315362235 7215662593027668473043353)
    ·
      refine ⟨5411746944770751354782515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7215662593027668473043353 5411746944770751354782515)
      ·
        refine ⟨8117620417156127032173773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5411746944770751354782515 8117620417156127032173773)
        ·
          refine ⟨3044107656433547637065165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8117620417156127032173773 3044107656433547637065165)
          ·
            refine ⟨1141540371162580363899437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3044107656433547637065165 1141540371162580363899437)
            ·
              refine ⟨428077639185967636462289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1141540371162580363899437 428077639185967636462289)
              ·
                refine ⟨321058229389475727346717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428077639185967636462289 321058229389475727346717)
                ·
                  refine ⟨120396836021053397755019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321058229389475727346717 120396836021053397755019)
                  ·
                    rfl

theorem cell21_527562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_527562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527562 prefixEnd_527562 := by exact prefixLift 527562
  have htrace : WordTrace (prefixWord ++ tailWord_527562) baseStart_527562 baseEnd_527562 := by
    simpa [prefixWord, tailWord_527562, baseEnd_527562] using wordTrace_append hprefix tailTrace_527562
  have hstable : (prefixWord ++ tailWord_527562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527562).length < 2 ^ (prefixWord ++ tailWord_527562).sum := by decide
  have hdescent : baseEnd_527562 < baseStart_527562 := by decide
  rcases family_descends (prefixWord ++ tailWord_527562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527573 : List Nat := [1, 3, 2, 4, 1, 1, 1, 8]
def baseStart_527573 : Nat := 118140960795 + 527573 * 2 ^ 59
def prefixEnd_527573 : Nat := 4983230072969 + 3 ^ 40 * 527573 * 2
def baseEnd_527573 : Nat := 40133115456973274357221

theorem tailTrace_527573 : CollatzResearch.WordTrace tailWord_527573 prefixEnd_527573 40133115456973274357221 := by
  unfold tailWord_527573
  simp only [CollatzResearch.WordTrace]
  refine ⟨19242168117700598140099373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12828112078467065426732915 19242168117700598140099373)
  ·
    refine ⟨7215813044137724302537265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19242168117700598140099373 7215813044137724302537265)
    ·
      refine ⟨5411859783103293226902949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7215813044137724302537265 5411859783103293226902949)
      ·
        refine ⟨1014723709331867480044303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5411859783103293226902949 1014723709331867480044303)
        ·
          refine ⟨1522085563997801220066455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014723709331867480044303 1522085563997801220066455)
          ·
            refine ⟨2283128345996701830099683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1522085563997801220066455 2283128345996701830099683)
            ·
              refine ⟨3424692518995052745149525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2283128345996701830099683 3424692518995052745149525)
              ·
                refine ⟨40133115456973274357221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3424692518995052745149525 40133115456973274357221)
                ·
                  rfl

theorem cell21_527573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 8].length) (baseStart_527573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527573 prefixEnd_527573 := by exact prefixLift 527573
  have htrace : WordTrace (prefixWord ++ tailWord_527573) baseStart_527573 baseEnd_527573 := by
    simpa [prefixWord, tailWord_527573, baseEnd_527573] using wordTrace_append hprefix tailTrace_527573
  have hstable : (prefixWord ++ tailWord_527573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527573).length < 2 ^ (prefixWord ++ tailWord_527573).sum := by decide
  have hdescent : baseEnd_527573 < baseStart_527573 := by decide
  rcases family_descends (prefixWord ++ tailWord_527573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527680 : List Nat := [2, 1, 1, 2, 2, 1, 3, 6, 3]
def baseStart_527680 : Nat := 118140960795 + 527680 * 2 ^ 59
def prefixEnd_527680 : Nat := 4983230072969 + 3 ^ 40 * 527680 * 2
def baseEnd_527680 : Nat := 120423765228711414788111

theorem tailTrace_527680 : CollatzResearch.WordTrace tailWord_527680 prefixEnd_527680 120423765228711414788111 := by
  unfold tailWord_527680
  simp only [CollatzResearch.WordTrace]
  refine ⟨9623035364156477707122247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12830713818875303609496329 9623035364156477707122247)
  ·
    refine ⟨14434553046234716560683371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9623035364156477707122247 14434553046234716560683371)
    ·
      refine ⟨21651829569352074841025057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14434553046234716560683371 21651829569352074841025057)
      ·
        refine ⟨16238872177014056130768793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21651829569352074841025057 16238872177014056130768793)
        ·
          refine ⟨12179154132760542098076595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16238872177014056130768793 12179154132760542098076595)
          ·
            refine ⟨18268731199140813147114893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12179154132760542098076595 18268731199140813147114893)
            ·
              refine ⟨6850774199677804930168085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18268731199140813147114893 6850774199677804930168085)
              ·
                refine ⟨321130040609897106101629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6850774199677804930168085 321130040609897106101629)
                ·
                  refine ⟨120423765228711414788111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321130040609897106101629 120423765228711414788111)
                  ·
                    rfl

theorem cell21_527680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 3].length) (baseStart_527680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527680 prefixEnd_527680 := by exact prefixLift 527680
  have htrace : WordTrace (prefixWord ++ tailWord_527680) baseStart_527680 baseEnd_527680 := by
    simpa [prefixWord, tailWord_527680, baseEnd_527680] using wordTrace_append hprefix tailTrace_527680
  have hstable : (prefixWord ++ tailWord_527680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527680).length < 2 ^ (prefixWord ++ tailWord_527680).sum := by decide
  have hdescent : baseEnd_527680 < baseStart_527680 := by decide
  rcases family_descends (prefixWord ++ tailWord_527680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527725 : List Nat := [1, 5, 1, 1, 1, 5, 7]
def baseStart_527725 : Nat := 118140960795 + 527725 * 2 ^ 59
def prefixEnd_527725 : Nat := 4983230072969 + 3 ^ 40 * 527725 * 2
def baseEnd_527725 : Nat := 13381559426866815170891

theorem tailTrace_527725 : CollatzResearch.WordTrace tailWord_527725 prefixEnd_527725 13381559426866815170891 := by
  unfold tailWord_527725
  simp only [CollatzResearch.WordTrace]
  refine ⟨19247712013149928099632629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12831808008766618733088419 19247712013149928099632629)
  ·
    refine ⟨1804473001232805759340559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19247712013149928099632629 1804473001232805759340559)
    ·
      refine ⟨2706709501849208639010839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1804473001232805759340559 2706709501849208639010839)
      ·
        refine ⟨4060064252773812958516259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2706709501849208639010839 4060064252773812958516259)
        ·
          refine ⟨6090096379160719437774389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4060064252773812958516259 6090096379160719437774389)
          ·
            refine ⟨570946535546317447291349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6090096379160719437774389 570946535546317447291349)
            ·
              refine ⟨13381559426866815170891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 570946535546317447291349 13381559426866815170891)
              ·
                rfl

theorem cell21_527725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 7].length) (baseStart_527725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527725 prefixEnd_527725 := by exact prefixLift 527725
  have htrace : WordTrace (prefixWord ++ tailWord_527725) baseStart_527725 baseEnd_527725 := by
    simpa [prefixWord, tailWord_527725, baseEnd_527725] using wordTrace_append hprefix tailTrace_527725
  have hstable : (prefixWord ++ tailWord_527725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527725).length < 2 ^ (prefixWord ++ tailWord_527725).sum := by decide
  have hdescent : baseEnd_527725 < baseStart_527725 := by decide
  rcases family_descends (prefixWord ++ tailWord_527725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527745 : List Nat := [1, 2, 4, 3, 2, 2, 2, 1, 4]
def baseStart_527745 : Nat := 118140960795 + 527745 * 2 ^ 59
def prefixEnd_527745 : Nat := 4983230072969 + 3 ^ 40 * 527745 * 2
def baseEnd_527745 : Nat := 120438599114285746204645

theorem tailTrace_527745 : CollatzResearch.WordTrace tailWord_527745 prefixEnd_527745 120438599114285746204645 := by
  unfold tailWord_527745
  simp only [CollatzResearch.WordTrace]
  refine ⟨19248441473077471515360689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12832294315384981010240459 19248441473077471515360689)
  ·
    refine ⟨14436331104808103636520517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19248441473077471515360689 14436331104808103636520517)
    ·
      refine ⟨2706812082151519431847597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14436331104808103636520517 2706812082151519431847597)
      ·
        refine ⟨1015054530806819786942849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2706812082151519431847597 1015054530806819786942849)
        ·
          refine ⟨761290898105114840207137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1015054530806819786942849 761290898105114840207137)
          ·
            refine ⟨570968173578836130155353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761290898105114840207137 570968173578836130155353)
            ·
              refine ⟨428226130184127097616515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570968173578836130155353 428226130184127097616515)
              ·
                refine ⟨642339195276190646424773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428226130184127097616515 642339195276190646424773)
                ·
                  refine ⟨120438599114285746204645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 642339195276190646424773 120438599114285746204645)
                  ·
                    rfl

theorem cell21_527745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_527745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527745 prefixEnd_527745 := by exact prefixLift 527745
  have htrace : WordTrace (prefixWord ++ tailWord_527745) baseStart_527745 baseEnd_527745 := by
    simpa [prefixWord, tailWord_527745, baseEnd_527745] using wordTrace_append hprefix tailTrace_527745
  have hstable : (prefixWord ++ tailWord_527745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527745).length < 2 ^ (prefixWord ++ tailWord_527745).sum := by decide
  have hdescent : baseEnd_527745 < baseStart_527745 := by decide
  rcases family_descends (prefixWord ++ tailWord_527745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527815 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 5]
def baseStart_527815 : Nat := 118140960795 + 527815 * 2 ^ 59
def prefixEnd_527815 : Nat := 4983230072969 + 3 ^ 40 * 527815 * 2
def baseEnd_527815 : Nat := 120454574067981180037835

theorem tailTrace_527815 : CollatzResearch.WordTrace tailWord_527815 prefixEnd_527815 120454574067981180037835 := by
  unfold tailWord_527815
  simp only [CollatzResearch.WordTrace]
  refine ⟨19250994582823873470408899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12833996388549248980272599 19250994582823873470408899)
  ·
    refine ⟨28876491874235810205613349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19250994582823873470408899 28876491874235810205613349)
    ·
      refine ⟨5414342226419214413552503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28876491874235810205613349 5414342226419214413552503)
      ·
        refine ⟨8121513339628821620328755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5414342226419214413552503 8121513339628821620328755)
        ·
          refine ⟨12182270009443232430493133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8121513339628821620328755 12182270009443232430493133)
          ·
            refine ⟨4568351253541212161434925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12182270009443232430493133 4568351253541212161434925)
            ·
              refine ⟨1713131720077954560538097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4568351253541212161434925 1713131720077954560538097)
              ·
                refine ⟨1284848790058465920403573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713131720077954560538097 1284848790058465920403573)
                ·
                  refine ⟨120454574067981180037835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1284848790058465920403573 120454574067981180037835)
                  ·
                    rfl

theorem cell21_527815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_527815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527815 prefixEnd_527815 := by exact prefixLift 527815
  have htrace : WordTrace (prefixWord ++ tailWord_527815) baseStart_527815 baseEnd_527815 := by
    simpa [prefixWord, tailWord_527815, baseEnd_527815] using wordTrace_append hprefix tailTrace_527815
  have hstable : (prefixWord ++ tailWord_527815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527815).length < 2 ^ (prefixWord ++ tailWord_527815).sum := by decide
  have hdescent : baseEnd_527815 < baseStart_527815 := by decide
  rcases family_descends (prefixWord ++ tailWord_527815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527832 : List Nat := [2, 1, 2, 2, 2, 1, 3, 5, 3]
def baseStart_527832 : Nat := 118140960795 + 527832 * 2 ^ 59
def prefixEnd_527832 : Nat := 4983230072969 + 3 ^ 40 * 527832 * 2
def baseEnd_527832 : Nat := 120458453699592928254467

theorem tailTrace_527832 : CollatzResearch.WordTrace tailWord_527832 prefixEnd_527832 120458453699592928254467 := by
  unfold tailWord_527832
  simp only [CollatzResearch.WordTrace]
  refine ⟨9625807311881142686888875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12834409749174856915851833 9625807311881142686888875)
  ·
    refine ⟨14438710967821714030333313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9625807311881142686888875 14438710967821714030333313)
    ·
      refine ⟨10829033225866285522749985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14438710967821714030333313 10829033225866285522749985)
      ·
        refine ⟨8121774919399714142062489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10829033225866285522749985 8121774919399714142062489)
        ·
          refine ⟨6091331189549785606546867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8121774919399714142062489 6091331189549785606546867)
          ·
            refine ⟨9136996784324678409820301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6091331189549785606546867 9136996784324678409820301)
            ·
              refine ⟨3426373794121754403682613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9136996784324678409820301 3426373794121754403682613)
              ·
                refine ⟨321222543198914475345245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3426373794121754403682613 321222543198914475345245)
                ·
                  refine ⟨120458453699592928254467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321222543198914475345245 120458453699592928254467)
                  ·
                    rfl

theorem cell21_527832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 3].length) (baseStart_527832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_527832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_527832 prefixEnd_527832 := by exact prefixLift 527832
  have htrace : WordTrace (prefixWord ++ tailWord_527832) baseStart_527832 baseEnd_527832 := by
    simpa [prefixWord, tailWord_527832, baseEnd_527832] using wordTrace_append hprefix tailTrace_527832
  have hstable : (prefixWord ++ tailWord_527832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527832).length < 2 ^ (prefixWord ++ tailWord_527832).sum := by decide
  have hdescent : baseEnd_527832 < baseStart_527832 := by decide
  rcases family_descends (prefixWord ++ tailWord_527832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528001 : List Nat := [1, 2, 4, 2, 1, 3, 2, 3, 3]
def baseStart_528001 : Nat := 118140960795 + 528001 * 2 ^ 59
def prefixEnd_528001 : Nat := 4983230072969 + 3 ^ 40 * 528001 * 2
def baseEnd_528001 : Nat := 120497021802086189937455

theorem tailTrace_528001 : CollatzResearch.WordTrace tailWord_528001 prefixEnd_528001 120497021802086189937455 := by
  unfold tailWord_528001
  simp only [CollatzResearch.WordTrace]
  refine ⟨19257778560150027236679857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12838519040100018157786571 19257778560150027236679857)
  ·
    refine ⟨14443333920112520427509893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19257778560150027236679857 14443333920112520427509893)
    ·
      refine ⟨2708125110021097580158105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14443333920112520427509893 2708125110021097580158105)
      ·
        refine ⟨2031093832515823185118579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2708125110021097580158105 2031093832515823185118579)
        ·
          refine ⟨3046640748773734777677869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031093832515823185118579 3046640748773734777677869)
          ·
            refine ⟨1142490280790150541629201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3046640748773734777677869 1142490280790150541629201)
            ·
              refine ⟨856867710592612906221901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142490280790150541629201 856867710592612906221901)
              ·
                refine ⟨321325391472229839833213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 856867710592612906221901 321325391472229839833213)
                ·
                  refine ⟨120497021802086189937455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321325391472229839833213 120497021802086189937455)
                  ·
                    rfl

theorem cell21_528001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 3].length) (baseStart_528001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528001 prefixEnd_528001 := by exact prefixLift 528001
  have htrace : WordTrace (prefixWord ++ tailWord_528001) baseStart_528001 baseEnd_528001 := by
    simpa [prefixWord, tailWord_528001, baseEnd_528001] using wordTrace_append hprefix tailTrace_528001
  have hstable : (prefixWord ++ tailWord_528001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528001).length < 2 ^ (prefixWord ++ tailWord_528001).sum := by decide
  have hdescent : baseEnd_528001 < baseStart_528001 := by decide
  rcases family_descends (prefixWord ++ tailWord_528001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528046 : List Nat := [4, 1, 4, 1, 2, 1, 1, 7]
def baseStart_528046 : Nat := 118140960795 + 528046 * 2 ^ 59
def prefixEnd_528046 : Nat := 4983230072969 + 3 ^ 40 * 528046 * 2
def baseEnd_528046 : Nat := 40169097138392037229121

theorem tailTrace_528046 : CollatzResearch.WordTrace tailWord_528046 prefixEnd_528046 40169097138392037229121 := by
  unfold tailWord_528046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2407427480623374990258499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12839613229991333281378661 2407427480623374990258499)
  ·
    refine ⟨3611141220935062485387749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2407427480623374990258499 3611141220935062485387749)
    ·
      refine ⟨677088978925324216010203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3611141220935062485387749 677088978925324216010203)
      ·
        refine ⟨1015633468387986324015305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677088978925324216010203 1015633468387986324015305)
        ·
          refine ⟨761725101290989743011479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1015633468387986324015305 761725101290989743011479)
          ·
            refine ⟨1142587651936484614517219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761725101290989743011479 1142587651936484614517219)
            ·
              refine ⟨1713881477904726921775829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142587651936484614517219 1713881477904726921775829)
              ·
                refine ⟨40169097138392037229121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1713881477904726921775829 40169097138392037229121)
                ·
                  rfl

theorem cell21_528046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_528046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528046 prefixEnd_528046 := by exact prefixLift 528046
  have htrace : WordTrace (prefixWord ++ tailWord_528046) baseStart_528046 baseEnd_528046 := by
    simpa [prefixWord, tailWord_528046, baseEnd_528046] using wordTrace_append hprefix tailTrace_528046
  have hstable : (prefixWord ++ tailWord_528046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528046).length < 2 ^ (prefixWord ++ tailWord_528046).sum := by decide
  have hdescent : baseEnd_528046 < baseStart_528046 := by decide
  rcases family_descends (prefixWord ++ tailWord_528046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528057 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 6]
def baseStart_528057 : Nat := 118140960795 + 528057 * 2 ^ 59
def prefixEnd_528057 : Nat := 4983230072969 + 3 ^ 40 * 528057 * 2
def baseEnd_528057 : Nat := 120509801765042537004007

theorem tailTrace_528057 : CollatzResearch.WordTrace tailWord_528057 prefixEnd_528057 120509801765042537004007 := by
  unfold tailWord_528057
  simp only [CollatzResearch.WordTrace]
  refine ⟨19259821047947148800718425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12839880698631432533812283 19259821047947148800718425)
  ·
    refine ⟨14444865785960361600538819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19259821047947148800718425 14444865785960361600538819)
    ·
      refine ⟨21667298678940542400808229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14444865785960361600538819 21667298678940542400808229)
      ·
        refine ⟨4062618502301351700151543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21667298678940542400808229 4062618502301351700151543)
        ·
          refine ⟨6093927753452027550227315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4062618502301351700151543 6093927753452027550227315)
          ·
            refine ⟨9140891630178041325340973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6093927753452027550227315 9140891630178041325340973)
            ·
              refine ⟨3427834361316765497002865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9140891630178041325340973 3427834361316765497002865)
              ·
                refine ⟨2570875770987574122752149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3427834361316765497002865 2570875770987574122752149)
                ·
                  refine ⟨120509801765042537004007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2570875770987574122752149 120509801765042537004007)
                  ·
                    rfl

theorem cell21_528057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_528057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528057 prefixEnd_528057 := by exact prefixLift 528057
  have htrace : WordTrace (prefixWord ++ tailWord_528057) baseStart_528057 baseEnd_528057 := by
    simpa [prefixWord, tailWord_528057, baseEnd_528057] using wordTrace_append hprefix tailTrace_528057
  have hstable : (prefixWord ++ tailWord_528057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528057).length < 2 ^ (prefixWord ++ tailWord_528057).sum := by decide
  have hdescent : baseEnd_528057 < baseStart_528057 := by decide
  rcases family_descends (prefixWord ++ tailWord_528057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528077 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 5]
def baseStart_528077 : Nat := 118140960795 + 528077 * 2 ^ 59
def prefixEnd_528077 : Nat := 4983230072969 + 3 ^ 40 * 528077 * 2
def baseEnd_528077 : Nat := 120514366037526946670633

theorem tailTrace_528077 : CollatzResearch.WordTrace tailWord_528077 prefixEnd_528077 120514366037526946670633 := by
  unfold tailWord_528077
  simp only [CollatzResearch.WordTrace]
  refine ⟨19260550507874692216446485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12840367005249794810964323 19260550507874692216446485)
  ·
    refine ⟨902838305056626197645929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19260550507874692216446485 902838305056626197645929)
    ·
      refine ⟨677128728792469648234447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 902838305056626197645929 677128728792469648234447)
      ·
        refine ⟨1015693093188704472351671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677128728792469648234447 1015693093188704472351671)
        ·
          refine ⟨1523539639783056708527507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015693093188704472351671 1523539639783056708527507)
          ·
            refine ⟨2285309459674585062791261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523539639783056708527507 2285309459674585062791261)
            ·
              refine ⟨856991047377969398546723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2285309459674585062791261 856991047377969398546723)
              ·
                refine ⟨1285486571066954097820085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856991047377969398546723 1285486571066954097820085)
                ·
                  refine ⟨120514366037526946670633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1285486571066954097820085 120514366037526946670633)
                  ·
                    rfl

theorem cell21_528077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_528077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528077 prefixEnd_528077 := by exact prefixLift 528077
  have htrace : WordTrace (prefixWord ++ tailWord_528077) baseStart_528077 baseEnd_528077 := by
    simpa [prefixWord, tailWord_528077, baseEnd_528077] using wordTrace_append hprefix tailTrace_528077
  have hstable : (prefixWord ++ tailWord_528077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528077).length < 2 ^ (prefixWord ++ tailWord_528077).sum := by decide
  have hdescent : baseEnd_528077 < baseStart_528077 := by decide
  rcases family_descends (prefixWord ++ tailWord_528077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528088 : List Nat := [2, 1, 2, 2, 3, 1, 4, 6]
def baseStart_528088 : Nat := 118140960795 + 528088 * 2 ^ 59
def prefixEnd_528088 : Nat := 4983230072969 + 3 ^ 40 * 528088 * 2
def baseEnd_528088 : Nat := 40172292129131123995759

theorem tailTrace_528088 : CollatzResearch.WordTrace tailWord_528088 prefixEnd_528088 40172292129131123995759 := by
  unfold tailWord_528088
  simp only [CollatzResearch.WordTrace]
  refine ⟨9630475855417420547548459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12840634473889894063397945 9630475855417420547548459)
  ·
    refine ⟨14445713783126130821322689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9630475855417420547548459 14445713783126130821322689)
    ·
      refine ⟨10834285337344598115992017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14445713783126130821322689 10834285337344598115992017)
      ·
        refine ⟨8125714003008448586994013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10834285337344598115992017 8125714003008448586994013)
        ·
          refine ⟨3047142751128168220122755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8125714003008448586994013 3047142751128168220122755)
          ·
            refine ⟨4570714126692252330184133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3047142751128168220122755 4570714126692252330184133)
            ·
              refine ⟨857008898754797311909525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4570714126692252330184133 857008898754797311909525)
              ·
                refine ⟨40172292129131123995759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 857008898754797311909525 40172292129131123995759)
                ·
                  rfl

theorem cell21_528088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_528088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528088 prefixEnd_528088 := by exact prefixLift 528088
  have htrace : WordTrace (prefixWord ++ tailWord_528088) baseStart_528088 baseEnd_528088 := by
    simpa [prefixWord, tailWord_528088, baseEnd_528088] using wordTrace_append hprefix tailTrace_528088
  have hstable : (prefixWord ++ tailWord_528088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528088).length < 2 ^ (prefixWord ++ tailWord_528088).sum := by decide
  have hdescent : baseEnd_528088 < baseStart_528088 := by decide
  rcases family_descends (prefixWord ++ tailWord_528088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528136 : List Nat := [2, 1, 3, 2, 2, 1, 3, 4, 3]
def baseStart_528136 : Nat := 118140960795 + 528136 * 2 ^ 59
def prefixEnd_528136 : Nat := 4983230072969 + 3 ^ 40 * 528136 * 2
def baseEnd_528136 : Nat := 120527830641355955187179

theorem tailTrace_528136 : CollatzResearch.WordTrace tailWord_528136 prefixEnd_528136 120527830641355955187179 := by
  unfold tailWord_528136
  simp only [CollatzResearch.WordTrace]
  refine ⟨9631351207330472646422131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12841801609773963528562841 9631351207330472646422131)
  ·
    refine ⟨14447026810995708969633197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9631351207330472646422131 14447026810995708969633197)
    ·
      refine ⟨5417635054123390863612449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14447026810995708969633197 5417635054123390863612449)
      ·
        refine ⟨4063226290592543147709337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5417635054123390863612449 4063226290592543147709337)
        ·
          refine ⟨3047419717944407360782003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4063226290592543147709337 3047419717944407360782003)
          ·
            refine ⟨4571129576916611041173005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3047419717944407360782003 4571129576916611041173005)
            ·
              refine ⟨1714173591343729140439877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4571129576916611041173005 1714173591343729140439877)
              ·
                refine ⟨321407548376949213832477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1714173591343729140439877 321407548376949213832477)
                ·
                  refine ⟨120527830641355955187179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321407548376949213832477 120527830641355955187179)
                  ·
                    rfl

theorem cell21_528136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 3].length) (baseStart_528136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528136 prefixEnd_528136 := by exact prefixLift 528136
  have htrace : WordTrace (prefixWord ++ tailWord_528136) baseStart_528136 baseEnd_528136 := by
    simpa [prefixWord, tailWord_528136, baseEnd_528136] using wordTrace_append hprefix tailTrace_528136
  have hstable : (prefixWord ++ tailWord_528136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528136).length < 2 ^ (prefixWord ++ tailWord_528136).sum := by decide
  have hdescent : baseEnd_528136 < baseStart_528136 := by decide
  rcases family_descends (prefixWord ++ tailWord_528136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528147 : List Nat := [1, 1, 1, 2, 1, 3, 2, 10]
def baseStart_528147 : Nat := 118140960795 + 528147 * 2 ^ 59
def prefixEnd_528147 : Nat := 4983230072969 + 3 ^ 40 * 528147 * 2
def baseEnd_528147 : Nat := 40176780330407460167941

theorem tailTrace_528147 : CollatzResearch.WordTrace tailWord_528147 prefixEnd_528147 40176780330407460167941 := by
  unfold tailWord_528147
  simp only [CollatzResearch.WordTrace]
  refine ⟨19263103617621094171494695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12842069078414062780996463 19263103617621094171494695)
  ·
    refine ⟨28894655426431641257242043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19263103617621094171494695 28894655426431641257242043)
    ·
      refine ⟨43341983139647461885863065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28894655426431641257242043 43341983139647461885863065)
      ·
        refine ⟨32506487354735596414397299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43341983139647461885863065 32506487354735596414397299)
        ·
          refine ⟨48759731032103394621595949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32506487354735596414397299 48759731032103394621595949)
          ·
            refine ⟨18284899137038772983098481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48759731032103394621595949 18284899137038772983098481)
            ·
              refine ⟨13713674352779079737323861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18284899137038772983098481 13713674352779079737323861)
              ·
                refine ⟨40176780330407460167941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13713674352779079737323861 40176780330407460167941)
                ·
                  rfl

theorem cell21_528147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 10].length) (baseStart_528147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528147 prefixEnd_528147 := by exact prefixLift 528147
  have htrace : WordTrace (prefixWord ++ tailWord_528147) baseStart_528147 baseEnd_528147 := by
    simpa [prefixWord, tailWord_528147, baseEnd_528147] using wordTrace_append hprefix tailTrace_528147
  have hstable : (prefixWord ++ tailWord_528147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528147).length < 2 ^ (prefixWord ++ tailWord_528147).sum := by decide
  have hdescent : baseEnd_528147 < baseStart_528147 := by decide
  rcases family_descends (prefixWord ++ tailWord_528147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528195 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 5]
def baseStart_528195 : Nat := 118140960795 + 528195 * 2 ^ 59
def prefixEnd_528195 : Nat := 4983230072969 + 3 ^ 40 * 528195 * 2
def baseEnd_528195 : Nat := 120541295245184963703725

theorem tailTrace_528195 : CollatzResearch.WordTrace tailWord_528195 prefixEnd_528195 120541295245184963703725 := by
  unfold tailWord_528195
  simp only [CollatzResearch.WordTrace]
  refine ⟨19264854321447198369242039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12843236214298132246161359 19264854321447198369242039)
  ·
    refine ⟨28897281482170797553863059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19264854321447198369242039 28897281482170797553863059)
    ·
      refine ⟨43345922223256196330794589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28897281482170797553863059 43345922223256196330794589)
      ·
        refine ⟨16254720833721073624047971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43345922223256196330794589 16254720833721073624047971)
        ·
          refine ⟨24382081250581610436071957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16254720833721073624047971 24382081250581610436071957)
          ·
            refine ⟨1142910058621012989190873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24382081250581610436071957 1142910058621012989190873)
            ·
              refine ⟨857182543965759741893155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142910058621012989190873 857182543965759741893155)
              ·
                refine ⟨1285773815948639612839733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857182543965759741893155 1285773815948639612839733)
                ·
                  refine ⟨120541295245184963703725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1285773815948639612839733 120541295245184963703725)
                  ·
                    rfl

theorem cell21_528195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 5].length) (baseStart_528195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528195 prefixEnd_528195 := by exact prefixLift 528195
  have htrace : WordTrace (prefixWord ++ tailWord_528195) baseStart_528195 baseEnd_528195 := by
    simpa [prefixWord, tailWord_528195, baseEnd_528195] using wordTrace_append hprefix tailTrace_528195
  have hstable : (prefixWord ++ tailWord_528195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528195).length < 2 ^ (prefixWord ++ tailWord_528195).sum := by decide
  have hdescent : baseEnd_528195 < baseStart_528195 := by decide
  rcases family_descends (prefixWord ++ tailWord_528195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528226 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_528226 : Nat := 118140960795 + 528226 * 2 ^ 59
def prefixEnd_528226 : Nat := 4983230072969 + 3 ^ 40 * 528226 * 2
def baseEnd_528226 : Nat := 120548369867535798686995

theorem tailTrace_528226 : CollatzResearch.WordTrace tailWord_528226 prefixEnd_528226 120548369867535798686995 := by
  unfold tailWord_528226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4816496246083722665905133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12843989989556593775747021 4816496246083722665905133)
  ·
    refine ⟨1806186092281395999714425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4816496246083722665905133 1806186092281395999714425)
    ·
      refine ⟨1354639569211046999785819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1806186092281395999714425 1354639569211046999785819)
      ·
        refine ⟨2031959353816570499678729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1354639569211046999785819 2031959353816570499678729)
        ·
          refine ⟨1523969515362427874759047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2031959353816570499678729 1523969515362427874759047)
          ·
            refine ⟨2285954273043641812138571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523969515362427874759047 2285954273043641812138571)
            ·
              refine ⟨3428931409565462718207857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2285954273043641812138571 3428931409565462718207857)
              ·
                refine ⟨2571698557174097038655893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3428931409565462718207857 2571698557174097038655893)
                ·
                  refine ⟨120548369867535798686995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2571698557174097038655893 120548369867535798686995)
                  ·
                    rfl

theorem cell21_528226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_528226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528226 prefixEnd_528226 := by exact prefixLift 528226
  have htrace : WordTrace (prefixWord ++ tailWord_528226) baseStart_528226 baseEnd_528226 := by
    simpa [prefixWord, tailWord_528226, baseEnd_528226] using wordTrace_append hprefix tailTrace_528226
  have hstable : (prefixWord ++ tailWord_528226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528226).length < 2 ^ (prefixWord ++ tailWord_528226).sum := by decide
  have hdescent : baseEnd_528226 < baseStart_528226 := by decide
  rcases family_descends (prefixWord ++ tailWord_528226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528246 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_528246 : Nat := 118140960795 + 528246 * 2 ^ 59
def prefixEnd_528246 : Nat := 4983230072969 + 3 ^ 40 * 528246 * 2
def baseEnd_528246 : Nat := 120552934140020208353621

theorem tailTrace_528246 : CollatzResearch.WordTrace tailWord_528246 prefixEnd_528246 120552934140020208353621 := by
  unfold tailWord_528246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204169652766402129959287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12844476296174956052899061 1204169652766402129959287)
  ·
    refine ⟨1806254479149603194938931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1204169652766402129959287 1806254479149603194938931)
    ·
      refine ⟨2709381718724404792408397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1806254479149603194938931 2709381718724404792408397)
      ·
        refine ⟨1016018144521651797153149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2709381718724404792408397 1016018144521651797153149)
        ·
          refine ⟨381006804195619423932431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1016018144521651797153149 381006804195619423932431)
          ·
            refine ⟨571510206293429135898647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381006804195619423932431 571510206293429135898647)
            ·
              refine ⟨857265309440143703847971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571510206293429135898647 857265309440143703847971)
              ·
                refine ⟨1285897964160215555771957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857265309440143703847971 1285897964160215555771957)
                ·
                  refine ⟨120552934140020208353621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1285897964160215555771957 120552934140020208353621)
                  ·
                    rfl

theorem cell21_528246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_528246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528246 prefixEnd_528246 := by exact prefixLift 528246
  have htrace : WordTrace (prefixWord ++ tailWord_528246) baseStart_528246 baseEnd_528246 := by
    simpa [prefixWord, tailWord_528246, baseEnd_528246] using wordTrace_append hprefix tailTrace_528246
  have hstable : (prefixWord ++ tailWord_528246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528246).length < 2 ^ (prefixWord ++ tailWord_528246).sum := by decide
  have hdescent : baseEnd_528246 < baseStart_528246 := by decide
  rcases family_descends (prefixWord ++ tailWord_528246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528305 : List Nat := [1, 2, 2, 4, 2, 1, 4, 2, 3]
def baseStart_528305 : Nat := 118140960795 + 528305 * 2 ^ 59
def prefixEnd_528305 : Nat := 4983230072969 + 3 ^ 40 * 528305 * 2
def baseEnd_528305 : Nat := 120566398743849216870167

theorem tailTrace_528305 : CollatzResearch.WordTrace tailWord_528305 prefixEnd_528305 120566398743849216870167 := by
  unfold tailWord_528305
  simp only [CollatzResearch.WordTrace]
  refine ⟨19268866351048687155746369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12845910900699124770497579 19268866351048687155746369)
  ·
    refine ⟨14451649763286515366809777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19268866351048687155746369 14451649763286515366809777)
    ·
      refine ⟨10838737322464886525107333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14451649763286515366809777 10838737322464886525107333)
      ·
        refine ⟨2032263247962166223457625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10838737322464886525107333 2032263247962166223457625)
        ·
          refine ⟨1524197435971624667593219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2032263247962166223457625 1524197435971624667593219)
          ·
            refine ⟨2286296153957437001389829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524197435971624667593219 2286296153957437001389829)
            ·
              refine ⟨428680528867019437760593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2286296153957437001389829 428680528867019437760593)
              ·
                refine ⟨321510396650264578320445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428680528867019437760593 321510396650264578320445)
                ·
                  refine ⟨120566398743849216870167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321510396650264578320445 120566398743849216870167)
                  ·
                    rfl

theorem cell21_528305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 3].length) (baseStart_528305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528305 prefixEnd_528305 := by exact prefixLift 528305
  have htrace : WordTrace (prefixWord ++ tailWord_528305) baseStart_528305 baseEnd_528305 := by
    simpa [prefixWord, tailWord_528305, baseEnd_528305] using wordTrace_append hprefix tailTrace_528305
  have hstable : (prefixWord ++ tailWord_528305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528305).length < 2 ^ (prefixWord ++ tailWord_528305).sum := by decide
  have hdescent : baseEnd_528305 < baseStart_528305 := by decide
  rcases family_descends (prefixWord ++ tailWord_528305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528330 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_528330 : Nat := 118140960795 + 528330 * 2 ^ 59
def prefixEnd_528330 : Nat := 4983230072969 + 3 ^ 40 * 528330 * 2
def baseEnd_528330 : Nat := 120572104084454728953449

theorem tailTrace_528330 : CollatzResearch.WordTrace tailWord_528330 prefixEnd_528330 120572104084454728953449 := by
  unfold tailWord_528330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4817444543989529106351611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12846518783972077616937629 4817444543989529106351611)
  ·
    refine ⟨7226166815984293659527417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4817444543989529106351611 7226166815984293659527417)
    ·
      refine ⟨5419625111988220244645563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7226166815984293659527417 5419625111988220244645563)
      ·
        refine ⟨8129437667982330366968345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5419625111988220244645563 8129437667982330366968345)
        ·
          refine ⟨6097078250986747775226259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8129437667982330366968345 6097078250986747775226259)
          ·
            refine ⟨9145617376480121662839389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6097078250986747775226259 9145617376480121662839389)
            ·
              refine ⟨3429606516180045623564771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9145617376480121662839389 3429606516180045623564771)
              ·
                refine ⟨5144409774270068435347157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3429606516180045623564771 5144409774270068435347157)
                ·
                  refine ⟨120572104084454728953449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5144409774270068435347157 120572104084454728953449)
                  ·
                    rfl

theorem cell21_528330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_528330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528330 prefixEnd_528330 := by exact prefixLift 528330
  have htrace : WordTrace (prefixWord ++ tailWord_528330) baseStart_528330 baseEnd_528330 := by
    simpa [prefixWord, tailWord_528330, baseEnd_528330] using wordTrace_append hprefix tailTrace_528330
  have hstable : (prefixWord ++ tailWord_528330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528330).length < 2 ^ (prefixWord ++ tailWord_528330).sum := by decide
  have hdescent : baseEnd_528330 < baseStart_528330 := by decide
  rcases family_descends (prefixWord ++ tailWord_528330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528516 : List Nat := [2, 3, 2, 1, 2, 1, 4, 3, 3]
def baseStart_528516 : Nat := 118140960795 + 528516 * 2 ^ 59
def prefixEnd_528516 : Nat := 4983230072969 + 3 ^ 40 * 528516 * 2
def baseEnd_528516 : Nat := 120614551818559738853069

theorem tailTrace_528516 : CollatzResearch.WordTrace tailWord_528516 prefixEnd_528516 120614551818559738853069 := by
  unfold tailWord_528516
  simp only [CollatzResearch.WordTrace]
  refine ⟨9638281076642135095838701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12851041435522846794451601 9638281076642135095838701)
  ·
    refine ⟨3614355403740800660939513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9638281076642135095838701 3614355403740800660939513)
    ·
      refine ⟨2710766552805600495704635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3614355403740800660939513 2710766552805600495704635)
      ·
        refine ⟨4066149829208400743556953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2710766552805600495704635 4066149829208400743556953)
        ·
          refine ⟨3049612371906300557667715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4066149829208400743556953 3049612371906300557667715)
          ·
            refine ⟨4574418557859450836501573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049612371906300557667715 4574418557859450836501573)
            ·
              refine ⟨857703479598647031844045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4574418557859450836501573 857703479598647031844045)
              ·
                refine ⟨321638804849492636941517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 857703479598647031844045 321638804849492636941517)
                ·
                  refine ⟨120614551818559738853069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321638804849492636941517 120614551818559738853069)
                  ·
                    rfl

theorem cell21_528516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_528516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528516 prefixEnd_528516 := by exact prefixLift 528516
  have htrace : WordTrace (prefixWord ++ tailWord_528516) baseStart_528516 baseEnd_528516 := by
    simpa [prefixWord, tailWord_528516, baseEnd_528516] using wordTrace_append hprefix tailTrace_528516
  have hstable : (prefixWord ++ tailWord_528516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528516).length < 2 ^ (prefixWord ++ tailWord_528516).sum := by decide
  have hdescent : baseEnd_528516 < baseStart_528516 := by decide
  rcases family_descends (prefixWord ++ tailWord_528516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528578 : List Nat := [3, 5, 1, 1, 1, 3, 7]
def baseStart_528578 : Nat := 118140960795 + 528578 * 2 ^ 59
def prefixEnd_528578 : Nat := 4983230072969 + 3 ^ 40 * 528578 * 2
def baseEnd_528578 : Nat := 13403189007029045424401

theorem tailTrace_528578 : CollatzResearch.WordTrace tailWord_528578 prefixEnd_528578 13403189007029045424401 := by
  unfold tailWord_528578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4819705869764913695108597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12852548986039769853622925 4819705869764913695108597)
  ·
    refine ⟨451847425290460658916431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4819705869764913695108597 451847425290460658916431)
    ·
      refine ⟨677771137935690988374647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451847425290460658916431 677771137935690988374647)
      ·
        refine ⟨1016656706903536482561971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677771137935690988374647 1016656706903536482561971)
        ·
          refine ⟨1524985060355304723842957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016656706903536482561971 1524985060355304723842957)
          ·
            refine ⟨571869397633239271441109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1524985060355304723842957 571869397633239271441109)
            ·
              refine ⟨13403189007029045424401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 571869397633239271441109 13403189007029045424401)
              ·
                rfl

theorem cell21_528578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 7].length) (baseStart_528578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528578 prefixEnd_528578 := by exact prefixLift 528578
  have htrace : WordTrace (prefixWord ++ tailWord_528578) baseStart_528578 baseEnd_528578 := by
    simpa [prefixWord, tailWord_528578, baseEnd_528578] using wordTrace_append hprefix tailTrace_528578
  have hstable : (prefixWord ++ tailWord_528578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528578).length < 2 ^ (prefixWord ++ tailWord_528578).sum := by decide
  have hdescent : baseEnd_528578 < baseStart_528578 := by decide
  rcases family_descends (prefixWord ++ tailWord_528578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528651 : List Nat := [1, 1, 1, 1, 5, 2, 3, 4, 3]
def baseStart_528651 : Nat := 118140960795 + 528651 * 2 ^ 59
def prefixEnd_528651 : Nat := 4983230072969 + 3 ^ 40 * 528651 * 2
def baseEnd_528651 : Nat := 120645360657829504102793

theorem tailTrace_528651 : CollatzResearch.WordTrace tailWord_528651 prefixEnd_528651 120645360657829504102793 := by
  unfold tailWord_528651
  simp only [CollatzResearch.WordTrace]
  refine ⟨19281486007795188247841807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12854324005196792165227871 19281486007795188247841807)
  ·
    refine ⟨28922229011692782371762711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19281486007795188247841807 28922229011692782371762711)
    ·
      refine ⟨43383343517539173557644067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28922229011692782371762711 43383343517539173557644067)
      ·
        refine ⟨65075015276308760336466101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43383343517539173557644067 65075015276308760336466101)
        ·
          refine ⟨6100782682153946281543697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65075015276308760336466101 6100782682153946281543697)
          ·
            refine ⟨4575587011615459711157773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6100782682153946281543697 4575587011615459711157773)
            ·
              refine ⟨1715845129355797391684165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4575587011615459711157773 1715845129355797391684165)
              ·
                refine ⟨321720961754212010940781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1715845129355797391684165 321720961754212010940781)
                ·
                  refine ⟨120645360657829504102793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321720961754212010940781 120645360657829504102793)
                  ·
                    rfl

theorem cell21_528651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 3].length) (baseStart_528651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528651 prefixEnd_528651 := by exact prefixLift 528651
  have htrace : WordTrace (prefixWord ++ tailWord_528651) baseStart_528651 baseEnd_528651 := by
    simpa [prefixWord, tailWord_528651, baseEnd_528651] using wordTrace_append hprefix tailTrace_528651
  have hstable : (prefixWord ++ tailWord_528651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528651).length < 2 ^ (prefixWord ++ tailWord_528651).sum := by decide
  have hdescent : baseEnd_528651 < baseStart_528651 := by decide
  rcases family_descends (prefixWord ++ tailWord_528651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528744 : List Nat := [2, 1, 4, 2, 2, 1, 3, 3, 3]
def baseStart_528744 : Nat := 118140960795 + 528744 * 2 ^ 59
def prefixEnd_528744 : Nat := 4983230072969 + 3 ^ 40 * 528744 * 2
def baseEnd_528744 : Nat := 120666584524882009052603

theorem tailTrace_528744 : CollatzResearch.WordTrace tailWord_528744 prefixEnd_528744 120666584524882009052603 := by
  unfold tailWord_528744
  simp only [CollatzResearch.WordTrace]
  refine ⟨9642438998229132565488643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12856585330972176753984857 9642438998229132565488643)
  ·
    refine ⟨14463658497343698848232965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9642438998229132565488643 14463658497343698848232965)
    ·
      refine ⟨2711935968251943534043681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14463658497343698848232965 2711935968251943534043681)
      ·
        refine ⟨2033951976188957650532761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2711935968251943534043681 2033951976188957650532761)
        ·
          refine ⟨1525463982141718237899571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2033951976188957650532761 1525463982141718237899571)
          ·
            refine ⟨2288195973212577356849357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525463982141718237899571 2288195973212577356849357)
            ·
              refine ⟨858073489954716508818509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2288195973212577356849357 858073489954716508818509)
              ·
                refine ⟨321777558733018690806941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 858073489954716508818509 321777558733018690806941)
                ·
                  refine ⟨120666584524882009052603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321777558733018690806941 120666584524882009052603)
                  ·
                    rfl

theorem cell21_528744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 3].length) (baseStart_528744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528744 prefixEnd_528744 := by exact prefixLift 528744
  have htrace : WordTrace (prefixWord ++ tailWord_528744) baseStart_528744 baseEnd_528744 := by
    simpa [prefixWord, tailWord_528744, baseEnd_528744] using wordTrace_append hprefix tailTrace_528744
  have hstable : (prefixWord ++ tailWord_528744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528744).length < 2 ^ (prefixWord ++ tailWord_528744).sum := by decide
  have hdescent : baseEnd_528744 < baseStart_528744 := by decide
  rcases family_descends (prefixWord ++ tailWord_528744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528817 : List Nat := [1, 2, 2, 4, 1, 2, 1, 4, 4]
def baseStart_528817 : Nat := 118140960795 + 528817 * 2 ^ 59
def prefixEnd_528817 : Nat := 4983230072969 + 3 ^ 40 * 528817 * 2
def baseEnd_528817 : Nat := 120683244119450104335787

theorem tailTrace_528817 : CollatzResearch.WordTrace tailWord_528817 prefixEnd_528817 120683244119450104335787 := by
  unfold tailWord_528817
  simp only [CollatzResearch.WordTrace]
  refine ⟨19287540525193798598384705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12858360350129199065589803 19287540525193798598384705)
  ·
    refine ⟨14465655393895348948788529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19287540525193798598384705 14465655393895348948788529)
    ·
      refine ⟨10849241545421511711591397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14465655393895348948788529 10849241545421511711591397)
      ·
        refine ⟨2034232789766533445923387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10849241545421511711591397 2034232789766533445923387)
        ·
          refine ⟨3051349184649800168885081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034232789766533445923387 3051349184649800168885081)
          ·
            refine ⟨2288511888487350126663811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3051349184649800168885081 2288511888487350126663811)
            ·
              refine ⟨3432767832731025189995717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288511888487350126663811 3432767832731025189995717)
              ·
                refine ⟨643643968637067223124197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3432767832731025189995717 643643968637067223124197)
                ·
                  refine ⟨120683244119450104335787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 643643968637067223124197 120683244119450104335787)
                  ·
                    rfl

theorem cell21_528817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_528817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528817 prefixEnd_528817 := by exact prefixLift 528817
  have htrace : WordTrace (prefixWord ++ tailWord_528817) baseStart_528817 baseEnd_528817 := by
    simpa [prefixWord, tailWord_528817, baseEnd_528817] using wordTrace_append hprefix tailTrace_528817
  have hstable : (prefixWord ++ tailWord_528817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528817).length < 2 ^ (prefixWord ++ tailWord_528817).sum := by decide
  have hdescent : baseEnd_528817 < baseStart_528817 := by decide
  rcases family_descends (prefixWord ++ tailWord_528817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528876 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 6]
def baseStart_528876 : Nat := 118140960795 + 528876 * 2 ^ 59
def prefixEnd_528876 : Nat := 4983230072969 + 3 ^ 40 * 528876 * 2
def baseEnd_528876 : Nat := 120696708723279112852333

theorem tailTrace_528876 : CollatzResearch.WordTrace tailWord_528876 prefixEnd_528876 120696708723279112852333 := by
  unfold tailWord_528876
  simp only [CollatzResearch.WordTrace]
  refine ⟨9644846215990025837391241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12859794954653367783188321 9644846215990025837391241)
  ·
    refine ⟨7233634661992519378043431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9644846215990025837391241 7233634661992519378043431)
    ·
      refine ⟨10850451992988779067065147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7233634661992519378043431 10850451992988779067065147)
      ·
        refine ⟨16275677989483168600597721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10850451992988779067065147 16275677989483168600597721)
        ·
          refine ⟨12206758492112376450448291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16275677989483168600597721 12206758492112376450448291)
          ·
            refine ⟨18310137738168564675672437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12206758492112376450448291 18310137738168564675672437)
            ·
              refine ⟨1716575412953302938344291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18310137738168564675672437 1716575412953302938344291)
              ·
                refine ⟨2574863119429954407516437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1716575412953302938344291 2574863119429954407516437)
                ·
                  refine ⟨120696708723279112852333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2574863119429954407516437 120696708723279112852333)
                  ·
                    rfl

theorem cell21_528876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_528876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528876 prefixEnd_528876 := by exact prefixLift 528876
  have htrace : WordTrace (prefixWord ++ tailWord_528876) baseStart_528876 baseEnd_528876 := by
    simpa [prefixWord, tailWord_528876, baseEnd_528876] using wordTrace_append hprefix tailTrace_528876
  have hstable : (prefixWord ++ tailWord_528876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528876).length < 2 ^ (prefixWord ++ tailWord_528876).sum := by decide
  have hdescent : baseEnd_528876 < baseStart_528876 := by decide
  rcases family_descends (prefixWord ++ tailWord_528876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528907 : List Nat := [1, 1, 1, 1, 7, 2, 1, 7]
def baseStart_528907 : Nat := 118140960795 + 528907 * 2 ^ 59
def prefixEnd_528907 : Nat := 4983230072969 + 3 ^ 40 * 528907 * 2
def baseEnd_528907 : Nat := 40234594448543315945201

theorem tailTrace_528907 : CollatzResearch.WordTrace tailWord_528907 prefixEnd_528907 40234594448543315945201 := by
  unfold tailWord_528907
  simp only [CollatzResearch.WordTrace]
  refine ⟨19290823094867743969160975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12860548729911829312773983 19290823094867743969160975)
  ·
    refine ⟨28936234642301615953741463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19290823094867743969160975 28936234642301615953741463)
    ·
      refine ⟨43404351963452423930612195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28936234642301615953741463 43404351963452423930612195)
      ·
        refine ⟨65106527945178635895918293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43404351963452423930612195 65106527945178635895918293)
        ·
          refine ⟨1525934248715124278810585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 65106527945178635895918293 1525934248715124278810585)
          ·
            refine ⟨1144450686536343209107939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1525934248715124278810585 1144450686536343209107939)
            ·
              refine ⟨1716676029804514813661909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144450686536343209107939 1716676029804514813661909)
              ·
                refine ⟨40234594448543315945201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1716676029804514813661909 40234594448543315945201)
                ·
                  rfl

theorem cell21_528907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 7].length) (baseStart_528907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_528907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_528907 prefixEnd_528907 := by exact prefixLift 528907
  have htrace : WordTrace (prefixWord ++ tailWord_528907) baseStart_528907 baseEnd_528907 := by
    simpa [prefixWord, tailWord_528907, baseEnd_528907] using wordTrace_append hprefix tailTrace_528907
  have hstable : (prefixWord ++ tailWord_528907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528907).length < 2 ^ (prefixWord ++ tailWord_528907).sum := by decide
  have hdescent : baseEnd_528907 < baseStart_528907 := by decide
  rcases family_descends (prefixWord ++ tailWord_528907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529031 : List Nat := [1, 1, 4, 2, 1, 2, 4, 3, 3]
def baseStart_529031 : Nat := 118140960795 + 529031 * 2 ^ 59
def prefixEnd_529031 : Nat := 4983230072969 + 3 ^ 40 * 529031 * 2
def baseEnd_529031 : Nat := 120732081835033287768683

theorem tailTrace_529031 : CollatzResearch.WordTrace tailWord_529031 prefixEnd_529031 120732081835033287768683 := by
  unfold tailWord_529031
  simp only [CollatzResearch.WordTrace]
  refine ⟨19295345746418513146674947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12863563830945675431116631 19295345746418513146674947)
  ·
    refine ⟨28943018619627769720012421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19295345746418513146674947 28943018619627769720012421)
    ·
      refine ⟨5426815991180206822502329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28943018619627769720012421 5426815991180206822502329)
      ·
        refine ⟨4070111993385155116876747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5426815991180206822502329 4070111993385155116876747)
        ·
          refine ⟨6105167990077732675315121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4070111993385155116876747 6105167990077732675315121)
          ·
            refine ⟨4578875992558299506486341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6105167990077732675315121 4578875992558299506486341)
            ·
              refine ⟨858539248604681157466189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4578875992558299506486341 858539248604681157466189)
              ·
                refine ⟨321952218226755434049821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 858539248604681157466189 321952218226755434049821)
                ·
                  refine ⟨120732081835033287768683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321952218226755434049821 120732081835033287768683)
                  ·
                    rfl

theorem cell21_529031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 3].length) (baseStart_529031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529031 prefixEnd_529031 := by exact prefixLift 529031
  have htrace : WordTrace (prefixWord ++ tailWord_529031) baseStart_529031 baseEnd_529031 := by
    simpa [prefixWord, tailWord_529031, baseEnd_529031] using wordTrace_append hprefix tailTrace_529031
  have hstable : (prefixWord ++ tailWord_529031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529031).length < 2 ^ (prefixWord ++ tailWord_529031).sum := by decide
  have hdescent : baseEnd_529031 < baseStart_529031 := by decide
  rcases family_descends (prefixWord ++ tailWord_529031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529121 : List Nat := [1, 2, 3, 1, 4, 2, 1, 3, 4]
def baseStart_529121 : Nat := 118140960795 + 529121 * 2 ^ 59
def prefixEnd_529121 : Nat := 4983230072969 + 3 ^ 40 * 529121 * 2
def baseEnd_529121 : Nat := 120752621061213131268499

theorem tailTrace_529121 : CollatzResearch.WordTrace tailWord_529121 prefixEnd_529121 120752621061213131268499 := by
  unfold tailWord_529121
  simp only [CollatzResearch.WordTrace]
  refine ⟨19298628316092458517451217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12865752210728305678300811 19298628316092458517451217)
  ·
    refine ⟨14473971237069343888088413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19298628316092458517451217 14473971237069343888088413)
    ·
      refine ⟨5427739213901003958033155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14473971237069343888088413 5427739213901003958033155)
      ·
        refine ⟨8141608820851505937049733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5427739213901003958033155 8141608820851505937049733)
        ·
          refine ⟨1526551653909657363196825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8141608820851505937049733 1526551653909657363196825)
          ·
            refine ⟨1144913740432243022397619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1526551653909657363196825 1144913740432243022397619)
            ·
              refine ⟨1717370610648364533596429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144913740432243022397619 1717370610648364533596429)
              ·
                refine ⟨644013978993136700098661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1717370610648364533596429 644013978993136700098661)
                ·
                  refine ⟨120752621061213131268499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 644013978993136700098661 120752621061213131268499)
                  ·
                    rfl

theorem cell21_529121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_529121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529121 prefixEnd_529121 := by exact prefixLift 529121
  have htrace : WordTrace (prefixWord ++ tailWord_529121) baseStart_529121 baseEnd_529121 := by
    simpa [prefixWord, tailWord_529121, baseEnd_529121] using wordTrace_append hprefix tailTrace_529121
  have hstable : (prefixWord ++ tailWord_529121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529121).length < 2 ^ (prefixWord ++ tailWord_529121).sum := by decide
  have hdescent : baseEnd_529121 < baseStart_529121 := by decide
  rcases family_descends (prefixWord ++ tailWord_529121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529225 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 5]
def baseStart_529225 : Nat := 118140960795 + 529225 * 2 ^ 59
def prefixEnd_529225 : Nat := 4983230072969 + 3 ^ 40 * 529225 * 2
def baseEnd_529225 : Nat := 120776355278132061534953

theorem tailTrace_529225 : CollatzResearch.WordTrace tailWord_529225 prefixEnd_529225 120776355278132061534953 := by
  unfold tailWord_529225
  simp only [CollatzResearch.WordTrace]
  refine ⟨19302421507715684279237129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12868281005143789519491419 19302421507715684279237129)
  ·
    refine ⟨14476816130786763209427847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19302421507715684279237129 14476816130786763209427847)
    ·
      refine ⟨21715224196180144814141771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14476816130786763209427847 21715224196180144814141771)
      ·
        refine ⟨32572836294270217221212657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21715224196180144814141771 32572836294270217221212657)
        ·
          refine ⟨24429627220702662915909493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32572836294270217221212657 24429627220702662915909493)
          ·
            refine ⟨2290277551940874648366515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24429627220702662915909493 2290277551940874648366515)
            ·
              refine ⟨3435416327911311972549773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290277551940874648366515 3435416327911311972549773)
              ·
                refine ⟨1288281122966741989706165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3435416327911311972549773 1288281122966741989706165)
                ·
                  refine ⟨120776355278132061534953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1288281122966741989706165 120776355278132061534953)
                  ·
                    rfl

theorem cell21_529225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_529225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529225 prefixEnd_529225 := by exact prefixLift 529225
  have htrace : WordTrace (prefixWord ++ tailWord_529225) baseStart_529225 baseEnd_529225 := by
    simpa [prefixWord, tailWord_529225, baseEnd_529225] using wordTrace_append hprefix tailTrace_529225
  have hstable : (prefixWord ++ tailWord_529225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529225).length < 2 ^ (prefixWord ++ tailWord_529225).sum := by decide
  have hdescent : baseEnd_529225 < baseStart_529225 := by decide
  rcases family_descends (prefixWord ++ tailWord_529225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529256 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 6]
def baseStart_529256 : Nat := 118140960795 + 529256 * 2 ^ 59
def prefixEnd_529256 : Nat := 4983230072969 + 3 ^ 40 * 529256 * 2
def baseEnd_529256 : Nat := 120783429900482896518223

theorem tailTrace_529256 : CollatzResearch.WordTrace tailWord_529256 prefixEnd_529256 120783429900482896518223 := by
  unfold tailWord_529256
  simp only [CollatzResearch.WordTrace]
  refine ⟨9651776085301688286807811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12869034780402251049077081 9651776085301688286807811)
  ·
    refine ⟨14477664127952532430211717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9651776085301688286807811 14477664127952532430211717)
    ·
      refine ⟨2714562023991099830664697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14477664127952532430211717 2714562023991099830664697)
      ·
        refine ⟨2035921517993324872998523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2714562023991099830664697 2035921517993324872998523)
        ·
          refine ⟨3053882276989987309497785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2035921517993324872998523 3053882276989987309497785)
          ·
            refine ⟨2290411707742490482123339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3053882276989987309497785 2290411707742490482123339)
            ·
              refine ⟨3435617561613735723185009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290411707742490482123339 3435617561613735723185009)
              ·
                refine ⟨2576713171210301792388757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3435617561613735723185009 2576713171210301792388757)
                ·
                  refine ⟨120783429900482896518223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2576713171210301792388757 120783429900482896518223)
                  ·
                    rfl

theorem cell21_529256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_529256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529256 prefixEnd_529256 := by exact prefixLift 529256
  have htrace : WordTrace (prefixWord ++ tailWord_529256) baseStart_529256 baseEnd_529256 := by
    simpa [prefixWord, tailWord_529256, baseEnd_529256] using wordTrace_append hprefix tailTrace_529256
  have hstable : (prefixWord ++ tailWord_529256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529256).length < 2 ^ (prefixWord ++ tailWord_529256).sum := by decide
  have hdescent : baseEnd_529256 < baseStart_529256 := by decide
  rcases family_descends (prefixWord ++ tailWord_529256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529287 : List Nat := [1, 1, 4, 2, 3, 2, 2, 6]
def baseStart_529287 : Nat := 118140960795 + 529287 * 2 ^ 59
def prefixEnd_529287 : Nat := 4983230072969 + 3 ^ 40 * 529287 * 2
def baseEnd_529287 : Nat := 40263501507611243833831

theorem tailTrace_529287 : CollatzResearch.WordTrace tailWord_529287 prefixEnd_529287 40263501507611243833831 := by
  unfold tailWord_529287
  simp only [CollatzResearch.WordTrace]
  refine ⟨19304682833491068867994115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12869788555660712578662743 19304682833491068867994115)
  ·
    refine ⟨28957024250236603301991173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19304682833491068867994115 28957024250236603301991173)
    ·
      refine ⟨5429442046919363119123345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28957024250236603301991173 5429442046919363119123345)
      ·
        refine ⟨4072081535189522339342509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5429442046919363119123345 4072081535189522339342509)
        ·
          refine ⟨1527030575696070877253441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4072081535189522339342509 1527030575696070877253441)
          ·
            refine ⟨1145272931772053157940081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1527030575696070877253441 1145272931772053157940081)
            ·
              refine ⟨858954698829039868455061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1145272931772053157940081 858954698829039868455061)
              ·
                refine ⟨40263501507611243833831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 858954698829039868455061 40263501507611243833831)
                ·
                  rfl

theorem cell21_529287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 6].length) (baseStart_529287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529287 prefixEnd_529287 := by exact prefixLift 529287
  have htrace : WordTrace (prefixWord ++ tailWord_529287) baseStart_529287 baseEnd_529287 := by
    simpa [prefixWord, tailWord_529287, baseEnd_529287] using wordTrace_append hprefix tailTrace_529287
  have hstable : (prefixWord ++ tailWord_529287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529287).length < 2 ^ (prefixWord ++ tailWord_529287).sum := by decide
  have hdescent : baseEnd_529287 < baseStart_529287 := by decide
  rcases family_descends (prefixWord ++ tailWord_529287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529290 : List Nat := [3, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_529290 : Nat := 118140960795 + 529290 * 2 ^ 59
def prefixEnd_529290 : Nat := 4983230072969 + 3 ^ 40 * 529290 * 2
def baseEnd_529290 : Nat := 120791189163706392951487

theorem tailTrace_529290 : CollatzResearch.WordTrace tailWord_529290 prefixEnd_529290 120791189163706392951487 := by
  unfold tailWord_529290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4826198063120050095088331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12869861501653466920235549 4826198063120050095088331)
  ·
    refine ⟨7239297094680075142632497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4826198063120050095088331 7239297094680075142632497)
    ·
      refine ⟨5429472821010056356974373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7239297094680075142632497 5429472821010056356974373)
      ·
        refine ⟨1018026153939385566932695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5429472821010056356974373 1018026153939385566932695)
        ·
          refine ⟨1527039230909078350399043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018026153939385566932695 1527039230909078350399043)
          ·
            refine ⟨2290558846363617525598565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527039230909078350399043 2290558846363617525598565)
            ·
              refine ⟨429479783693178286049731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2290558846363617525598565 429479783693178286049731)
              ·
                refine ⟨644219675539767429074597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429479783693178286049731 644219675539767429074597)
                ·
                  refine ⟨120791189163706392951487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 644219675539767429074597 120791189163706392951487)
                  ·
                    rfl

theorem cell21_529290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_529290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529290 prefixEnd_529290 := by exact prefixLift 529290
  have htrace : WordTrace (prefixWord ++ tailWord_529290) baseStart_529290 baseEnd_529290 := by
    simpa [prefixWord, tailWord_529290, baseEnd_529290] using wordTrace_append hprefix tailTrace_529290
  have hstable : (prefixWord ++ tailWord_529290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529290).length < 2 ^ (prefixWord ++ tailWord_529290).sum := by decide
  have hdescent : baseEnd_529290 < baseStart_529290 := by decide
  rcases family_descends (prefixWord ++ tailWord_529290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529315 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 8]
def baseStart_529315 : Nat := 118140960795 + 529315 * 2 ^ 59
def prefixEnd_529315 : Nat := 4983230072969 + 3 ^ 40 * 529315 * 2
def baseEnd_529315 : Nat := 120796894504311905034769

theorem tailTrace_529315 : CollatzResearch.WordTrace tailWord_529315 prefixEnd_529315 120796894504311905034769 := by
  unfold tailWord_529315
  simp only [CollatzResearch.WordTrace]
  refine ⟨19305704077389629650013399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12870469384926419766675599 19305704077389629650013399)
  ·
    refine ⟨28958556116084444475020099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19305704077389629650013399 28958556116084444475020099)
    ·
      refine ⟨43437834174126666712530149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28958556116084444475020099 43437834174126666712530149)
      ·
        refine ⟨8144593907648750008599403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43437834174126666712530149 8144593907648750008599403)
        ·
          refine ⟨12216890861473125012899105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8144593907648750008599403 12216890861473125012899105)
          ·
            refine ⟨9162668146104843759674329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12216890861473125012899105 9162668146104843759674329)
            ·
              refine ⟨6872001109578632819755747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9162668146104843759674329 6872001109578632819755747)
              ·
                refine ⟨10308001664367949229633621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6872001109578632819755747 10308001664367949229633621)
                ·
                  refine ⟨120796894504311905034769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10308001664367949229633621 120796894504311905034769)
                  ·
                    rfl

theorem cell21_529315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_529315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529315 prefixEnd_529315 := by exact prefixLift 529315
  have htrace : WordTrace (prefixWord ++ tailWord_529315) baseStart_529315 baseEnd_529315 := by
    simpa [prefixWord, tailWord_529315, baseEnd_529315] using wordTrace_append hprefix tailTrace_529315
  have hstable : (prefixWord ++ tailWord_529315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529315).length < 2 ^ (prefixWord ++ tailWord_529315).sum := by decide
  have hdescent : baseEnd_529315 < baseStart_529315 := by decide
  rcases family_descends (prefixWord ++ tailWord_529315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529335 : List Nat := [1, 1, 3, 1, 3, 1, 6, 2, 3]
def baseStart_529335 : Nat := 118140960795 + 529335 * 2 ^ 59
def prefixEnd_529335 : Nat := 4983230072969 + 3 ^ 40 * 529335 * 2
def baseEnd_529335 : Nat := 120801458776796314701395

theorem tailTrace_529335 : CollatzResearch.WordTrace tailWord_529335 prefixEnd_529335 120801458776796314701395 := by
  unfold tailWord_529335
  simp only [CollatzResearch.WordTrace]
  refine ⟨19306433537317173065741459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12870955691544782043827639 19306433537317173065741459)
  ·
    refine ⟨28959650305975759598612189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19306433537317173065741459 28959650305975759598612189)
    ·
      refine ⟨10859868864740909849479571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28959650305975759598612189 10859868864740909849479571)
      ·
        refine ⟨16289803297111364774219357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10859868864740909849479571 16289803297111364774219357)
        ·
          refine ⟨6108676236416761790332259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16289803297111364774219357 6108676236416761790332259)
          ·
            refine ⟨9163014354625142685498389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6108676236416761790332259 9163014354625142685498389)
            ·
              refine ⟨429516297873053563382737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9163014354625142685498389 429516297873053563382737)
              ·
                refine ⟨322137223404790172537053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429516297873053563382737 322137223404790172537053)
                ·
                  refine ⟨120801458776796314701395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322137223404790172537053 120801458776796314701395)
                  ·
                    rfl

theorem cell21_529335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 3].length) (baseStart_529335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529335 prefixEnd_529335 := by exact prefixLift 529335
  have htrace : WordTrace (prefixWord ++ tailWord_529335) baseStart_529335 baseEnd_529335 := by
    simpa [prefixWord, tailWord_529335, baseEnd_529335] using wordTrace_append hprefix tailTrace_529335
  have hstable : (prefixWord ++ tailWord_529335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529335).length < 2 ^ (prefixWord ++ tailWord_529335).sum := by decide
  have hdescent : baseEnd_529335 < baseStart_529335 := by decide
  rcases family_descends (prefixWord ++ tailWord_529335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529543 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 6]
def baseStart_529543 : Nat := 118140960795 + 529543 * 2 ^ 59
def prefixEnd_529543 : Nat := 4983230072969 + 3 ^ 40 * 529543 * 2
def baseEnd_529543 : Nat := 120848927210634175234303

theorem tailTrace_529543 : CollatzResearch.WordTrace tailWord_529543 prefixEnd_529543 120848927210634175234303 := by
  unfold tailWord_529543
  simp only [CollatzResearch.WordTrace]
  refine ⟨19314019920563624589313283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12876013280375749726208855 19314019920563624589313283)
  ·
    refine ⟨28971029880845436883969925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19314019920563624589313283 28971029880845436883969925)
    ·
      refine ⟨5432068102658519415744361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28971029880845436883969925 5432068102658519415744361)
      ·
        refine ⟨4074051076993889561808271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5432068102658519415744361 4074051076993889561808271)
        ·
          refine ⟨6111076615490834342712407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4074051076993889561808271 6111076615490834342712407)
          ·
            refine ⟨9166614923236251514068611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6111076615490834342712407 9166614923236251514068611)
            ·
              refine ⟨13749922384854377271102917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9166614923236251514068611 13749922384854377271102917)
              ·
                refine ⟨2578110447160195738331797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13749922384854377271102917 2578110447160195738331797)
                ·
                  refine ⟨120848927210634175234303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2578110447160195738331797 120848927210634175234303)
                  ·
                    rfl

theorem cell21_529543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_529543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529543 prefixEnd_529543 := by exact prefixLift 529543
  have htrace : WordTrace (prefixWord ++ tailWord_529543) baseStart_529543 baseEnd_529543 := by
    simpa [prefixWord, tailWord_529543, baseEnd_529543] using wordTrace_append hprefix tailTrace_529543
  have hstable : (prefixWord ++ tailWord_529543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529543).length < 2 ^ (prefixWord ++ tailWord_529543).sum := by decide
  have hdescent : baseEnd_529543 < baseStart_529543 := by decide
  rcases family_descends (prefixWord ++ tailWord_529543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529560 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 6]
def baseStart_529560 : Nat := 118140960795 + 529560 * 2 ^ 59
def prefixEnd_529560 : Nat := 4983230072969 + 3 ^ 40 * 529560 * 2
def baseEnd_529560 : Nat := 120852806842245923450935

theorem tailTrace_529560 : CollatzResearch.WordTrace tailWord_529560 prefixEnd_529560 120852806842245923450935 := by
  unfold tailWord_529560
  simp only [CollatzResearch.WordTrace]
  refine ⟨9657319980751018246341067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12876426641001357661788089 9657319980751018246341067)
  ·
    refine ⟨14485979971126527369511601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9657319980751018246341067 14485979971126527369511601)
    ·
      refine ⟨10864484978344895527133701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14485979971126527369511601 10864484978344895527133701)
      ·
        refine ⟨2037090933439667911337569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10864484978344895527133701 2037090933439667911337569)
        ·
          refine ⟨1527818200079750933503177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2037090933439667911337569 1527818200079750933503177)
          ·
            refine ⟨1145863650059813200127383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1527818200079750933503177 1145863650059813200127383)
            ·
              refine ⟨1718795475089719800191075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145863650059813200127383 1718795475089719800191075)
              ·
                refine ⟨2578193212634579700286613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718795475089719800191075 2578193212634579700286613)
                ·
                  refine ⟨120852806842245923450935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2578193212634579700286613 120852806842245923450935)
                  ·
                    rfl

theorem cell21_529560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_529560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529560 prefixEnd_529560 := by exact prefixLift 529560
  have htrace : WordTrace (prefixWord ++ tailWord_529560) baseStart_529560 baseEnd_529560 := by
    simpa [prefixWord, tailWord_529560, baseEnd_529560] using wordTrace_append hprefix tailTrace_529560
  have hstable : (prefixWord ++ tailWord_529560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529560).length < 2 ^ (prefixWord ++ tailWord_529560).sum := by decide
  have hdescent : baseEnd_529560 < baseStart_529560 := by decide
  rcases family_descends (prefixWord ++ tailWord_529560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529698 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_529698 : Nat := 118140960795 + 529698 * 2 ^ 59
def prefixEnd_529698 : Nat := 4983230072969 + 3 ^ 40 * 529698 * 2
def baseEnd_529698 : Nat := 120884300322388350150653

theorem tailTrace_529698 : CollatzResearch.WordTrace tailWord_529698 prefixEnd_529698 120884300322388350150653 := by
  unfold tailWord_529698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4829918308750521515301437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12879782156668057374137165 4829918308750521515301437)
  ·
    refine ⟨1811219365781445568238039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4829918308750521515301437 1811219365781445568238039)
    ·
      refine ⟨2716829048672168352357059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1811219365781445568238039 2716829048672168352357059)
      ·
        refine ⟨4075243573008252528535589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2716829048672168352357059 4075243573008252528535589)
        ·
          refine ⟨764108169939047349100423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4075243573008252528535589 764108169939047349100423)
          ·
            refine ⟨1146162254908571023650635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764108169939047349100423 1146162254908571023650635)
            ·
              refine ⟨1719243382362856535475953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146162254908571023650635 1719243382362856535475953)
              ·
                refine ⟨1289432536772142401606965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719243382362856535475953 1289432536772142401606965)
                ·
                  refine ⟨120884300322388350150653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1289432536772142401606965 120884300322388350150653)
                  ·
                    rfl

theorem cell21_529698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_529698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529698 prefixEnd_529698 := by exact prefixLift 529698
  have htrace : WordTrace (prefixWord ++ tailWord_529698) baseStart_529698 baseEnd_529698 := by
    simpa [prefixWord, tailWord_529698, baseEnd_529698] using wordTrace_append hprefix tailTrace_529698
  have hstable : (prefixWord ++ tailWord_529698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529698).length < 2 ^ (prefixWord ++ tailWord_529698).sum := by decide
  have hdescent : baseEnd_529698 < baseStart_529698 := by decide
  rcases family_descends (prefixWord ++ tailWord_529698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529726 : List Nat := [4, 2, 1, 2, 1, 1, 10]
def baseStart_529726 : Nat := 118140960795 + 529726 * 2 ^ 59
def prefixEnd_529726 : Nat := 4983230072969 + 3 ^ 40 * 529726 * 2
def baseEnd_529726 : Nat := 13432298922651835964881

theorem tailTrace_529726 : CollatzResearch.WordTrace tailWord_529726 prefixEnd_529726 13432298922651835964881 := by
  unfold tailWord_529726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415086809862580855403129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12880462985933764562150021 2415086809862580855403129)
  ·
    refine ⟨1811315107396935641552347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2415086809862580855403129 1811315107396935641552347)
    ·
      refine ⟨2716972661095403462328521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1811315107396935641552347 2716972661095403462328521)
      ·
        refine ⟨2037729495821552596746391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2716972661095403462328521 2037729495821552596746391)
        ·
          refine ⟨3056594243732328895119587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2037729495821552596746391 3056594243732328895119587)
          ·
            refine ⟨4584891365598493342679381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3056594243732328895119587 4584891365598493342679381)
            ·
              refine ⟨13432298922651835964881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4584891365598493342679381 13432298922651835964881)
              ·
                rfl

theorem cell21_529726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 10].length) (baseStart_529726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529726 prefixEnd_529726 := by exact prefixLift 529726
  have htrace : WordTrace (prefixWord ++ tailWord_529726) baseStart_529726 baseEnd_529726 := by
    simpa [prefixWord, tailWord_529726, baseEnd_529726] using wordTrace_append hprefix tailTrace_529726
  have hstable : (prefixWord ++ tailWord_529726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529726).length < 2 ^ (prefixWord ++ tailWord_529726).sum := by decide
  have hdescent : baseEnd_529726 < baseStart_529726 := by decide
  rcases family_descends (prefixWord ++ tailWord_529726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529729 : List Nat := [1, 2, 5, 2, 1, 1, 3, 2, 4]
def baseStart_529729 : Nat := 118140960795 + 529729 * 2 ^ 59
def prefixEnd_529729 : Nat := 4983230072969 + 3 ^ 40 * 529729 * 2
def baseEnd_529729 : Nat := 120891374944739185133923

theorem tailTrace_529729 : CollatzResearch.WordTrace tailWord_529729 prefixEnd_529729 120891374944739185133923 := by
  unfold tailWord_529729
  simp only [CollatzResearch.WordTrace]
  refine ⟨19320803897889778355584241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12880535931926518903722827 19320803897889778355584241)
  ·
    refine ⟨14490602923417333766688181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19320803897889778355584241 14490602923417333766688181)
    ·
      refine ⟨1358494024070375040627017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14490602923417333766688181 1358494024070375040627017)
      ·
        refine ⟨1018870518052781280470263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1358494024070375040627017 1018870518052781280470263)
        ·
          refine ⟨1528305777079171920705395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018870518052781280470263 1528305777079171920705395)
          ·
            refine ⟨2292458665618757881058093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528305777079171920705395 2292458665618757881058093)
            ·
              refine ⟨859671999607034205396785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2292458665618757881058093 859671999607034205396785)
              ·
                refine ⟨644753999705275654047589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859671999607034205396785 644753999705275654047589)
                ·
                  refine ⟨120891374944739185133923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 644753999705275654047589 120891374944739185133923)
                  ·
                    rfl

theorem cell21_529729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_529729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529729 prefixEnd_529729 := by exact prefixLift 529729
  have htrace : WordTrace (prefixWord ++ tailWord_529729) baseStart_529729 baseEnd_529729 := by
    simpa [prefixWord, tailWord_529729, baseEnd_529729] using wordTrace_append hprefix tailTrace_529729
  have hstable : (prefixWord ++ tailWord_529729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529729).length < 2 ^ (prefixWord ++ tailWord_529729).sum := by decide
  have hdescent : baseEnd_529729 < baseStart_529729 := by decide
  rcases family_descends (prefixWord ++ tailWord_529729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529785 : List Nat := [1, 2, 1, 3, 2, 1, 11]
def baseStart_529785 : Nat := 118140960795 + 529785 * 2 ^ 59
def prefixEnd_529785 : Nat := 4983230072969 + 3 ^ 40 * 529785 * 2
def baseEnd_529785 : Nat := 13433794989743948022275

theorem tailTrace_529785 : CollatzResearch.WordTrace tailWord_529785 prefixEnd_529785 13433794989743948022275 := by
  unfold tailWord_529785
  simp only [CollatzResearch.WordTrace]
  refine ⟨19322846385686899919622809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12881897590457933279748539 19322846385686899919622809)
  ·
    refine ⟨14492134789265174939717107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19322846385686899919622809 14492134789265174939717107)
    ·
      refine ⟨21738202183897762409575661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14492134789265174939717107 21738202183897762409575661)
      ·
        refine ⟨8151825818961660903590873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21738202183897762409575661 8151825818961660903590873)
        ·
          refine ⟨6113869364221245677693155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8151825818961660903590873 6113869364221245677693155)
          ·
            refine ⟨9170804046331868516539733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6113869364221245677693155 9170804046331868516539733)
            ·
              refine ⟨13433794989743948022275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9170804046331868516539733 13433794989743948022275)
              ·
                rfl

theorem cell21_529785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 11].length) (baseStart_529785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529785 prefixEnd_529785 := by exact prefixLift 529785
  have htrace : WordTrace (prefixWord ++ tailWord_529785) baseStart_529785 baseEnd_529785 := by
    simpa [prefixWord, tailWord_529785, baseEnd_529785] using wordTrace_append hprefix tailTrace_529785
  have hstable : (prefixWord ++ tailWord_529785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529785).length < 2 ^ (prefixWord ++ tailWord_529785).sum := by decide
  have hdescent : baseEnd_529785 < baseStart_529785 := by decide
  rcases family_descends (prefixWord ++ tailWord_529785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529898 : List Nat := [3, 1, 3, 1, 5, 1, 1, 2, 4]
def baseStart_529898 : Nat := 118140960795 + 529898 * 2 ^ 59
def prefixEnd_529898 : Nat := 4983230072969 + 3 ^ 40 * 529898 * 2
def baseEnd_529898 : Nat := 120929943047232446816911

theorem tailTrace_529898 : CollatzResearch.WordTrace tailWord_529898 prefixEnd_529898 120929943047232446816911 := by
  unfold tailWord_529898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4831741958569380054621587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12884645222851680145657565 4831741958569380054621587)
  ·
    refine ⟨7247612937854070081932381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4831741958569380054621587 7247612937854070081932381)
    ·
      refine ⟨2717854851695276280724643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7247612937854070081932381 2717854851695276280724643)
      ·
        refine ⟨4076782277542914421086965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2717854851695276280724643 4076782277542914421086965)
        ·
          refine ⟨382198338519648226976903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4076782277542914421086965 382198338519648226976903)
          ·
            refine ⟨573297507779472340465355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382198338519648226976903 573297507779472340465355)
            ·
              refine ⟨859946261669208510698033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573297507779472340465355 859946261669208510698033)
              ·
                refine ⟨644959696251906383023525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859946261669208510698033 644959696251906383023525)
                ·
                  refine ⟨120929943047232446816911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 644959696251906383023525 120929943047232446816911)
                  ·
                    rfl

theorem cell21_529898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_529898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529898 prefixEnd_529898 := by exact prefixLift 529898
  have htrace : WordTrace (prefixWord ++ tailWord_529898) baseStart_529898 baseEnd_529898 := by
    simpa [prefixWord, tailWord_529898, baseEnd_529898] using wordTrace_append hprefix tailTrace_529898
  have hstable : (prefixWord ++ tailWord_529898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529898).length < 2 ^ (prefixWord ++ tailWord_529898).sum := by decide
  have hdescent : baseEnd_529898 < baseStart_529898 := by decide
  rcases family_descends (prefixWord ++ tailWord_529898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529937 : List Nat := [1, 2, 2, 1, 1, 2, 5, 7]
def baseStart_529937 : Nat := 118140960795 + 529937 * 2 ^ 59
def prefixEnd_529937 : Nat := 4983230072969 + 3 ^ 40 * 529937 * 2
def baseEnd_529937 : Nat := 40312947792859015222277

theorem tailTrace_529937 : CollatzResearch.WordTrace tailWord_529937 prefixEnd_529937 40312947792859015222277 := by
  unfold tailWord_529937
  simp only [CollatzResearch.WordTrace]
  refine ⟨19328390281136229879156065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12885593520757486586104043 19328390281136229879156065)
  ·
    refine ⟨14496292710852172409367049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19328390281136229879156065 14496292710852172409367049)
    ·
      refine ⟨10872219533139129307025287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14496292710852172409367049 10872219533139129307025287)
      ·
        refine ⟨16308329299708693960537931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10872219533139129307025287 16308329299708693960537931)
        ·
          refine ⟨24462493949563040940806897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16308329299708693960537931 24462493949563040940806897)
          ·
            refine ⟨18346870462172280705605173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24462493949563040940806897 18346870462172280705605173)
            ·
              refine ⟨1720019105828651316150485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18346870462172280705605173 1720019105828651316150485)
              ·
                refine ⟨40312947792859015222277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1720019105828651316150485 40312947792859015222277)
                ·
                  rfl

theorem cell21_529937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 7].length) (baseStart_529937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529937 prefixEnd_529937 := by exact prefixLift 529937
  have htrace : WordTrace (prefixWord ++ tailWord_529937) baseStart_529937 baseEnd_529937 := by
    simpa [prefixWord, tailWord_529937, baseEnd_529937] using wordTrace_append hprefix tailTrace_529937
  have hstable : (prefixWord ++ tailWord_529937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529937).length < 2 ^ (prefixWord ++ tailWord_529937).sum := by decide
  have hdescent : baseEnd_529937 < baseStart_529937 := by decide
  rcases family_descends (prefixWord ++ tailWord_529937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529960 : List Nat := [2, 1, 5, 2, 2, 1, 3, 2, 3]
def baseStart_529960 : Nat := 118140960795 + 529960 * 2 ^ 59
def prefixEnd_529960 : Nat := 4983230072969 + 3 ^ 40 * 529960 * 2
def baseEnd_529960 : Nat := 120944092291934116783451

theorem tailTrace_529960 : CollatzResearch.WordTrace tailWord_529960 prefixEnd_529960 120944092291934116783451 := by
  unfold tailWord_529960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9664614580026452403621667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12886152773368603204828889 9664614580026452403621667)
  ·
    refine ⟨14496921870039678605432501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9664614580026452403621667 14496921870039678605432501)
    ·
      refine ⟨1359086425316219869259297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14496921870039678605432501 1359086425316219869259297)
      ·
        refine ⟨1019314818987164901944473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1359086425316219869259297 1019314818987164901944473)
        ·
          refine ⟨764486114240373676458355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019314818987164901944473 764486114240373676458355)
          ·
            refine ⟨1146729171360560514687533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764486114240373676458355 1146729171360560514687533)
            ·
              refine ⟨430023439260210193007825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1146729171360560514687533 430023439260210193007825)
              ·
                refine ⟨322517579445157644755869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430023439260210193007825 322517579445157644755869)
                ·
                  refine ⟨120944092291934116783451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322517579445157644755869 120944092291934116783451)
                  ·
                    rfl

theorem cell21_529960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 3].length) (baseStart_529960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_529960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_529960 prefixEnd_529960 := by exact prefixLift 529960
  have htrace : WordTrace (prefixWord ++ tailWord_529960) baseStart_529960 baseEnd_529960 := by
    simpa [prefixWord, tailWord_529960, baseEnd_529960] using wordTrace_append hprefix tailTrace_529960
  have hstable : (prefixWord ++ tailWord_529960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529960).length < 2 ^ (prefixWord ++ tailWord_529960).sum := by decide
  have hdescent : baseEnd_529960 < baseStart_529960 := by decide
  rcases family_descends (prefixWord ++ tailWord_529960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530019 : List Nat := [1, 1, 1, 5, 1, 5, 2, 2, 3]
def baseStart_530019 : Nat := 118140960795 + 530019 * 2 ^ 59
def prefixEnd_530019 : Nat := 4983230072969 + 3 ^ 40 * 530019 * 2
def baseEnd_530019 : Nat := 120957556895763125299997

theorem tailTrace_530019 : CollatzResearch.WordTrace tailWord_530019 prefixEnd_530019 120957556895763125299997 := by
  unfold tailWord_530019
  simp only [CollatzResearch.WordTrace]
  refine ⟨19331381066839157883641111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12887587377892771922427407 19331381066839157883641111)
  ·
    refine ⟨28997071600258736825461667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19331381066839157883641111 28997071600258736825461667)
    ·
      refine ⟨43495607400388105238192501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28997071600258736825461667 43495607400388105238192501)
      ·
        refine ⟨4077713193786384866080547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43495607400388105238192501 4077713193786384866080547)
        ·
          refine ⟨6116569790679577299120821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4077713193786384866080547 6116569790679577299120821)
          ·
            refine ⟨573428417876210371792577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6116569790679577299120821 573428417876210371792577)
            ·
              refine ⟨430071313407157778844433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573428417876210371792577 430071313407157778844433)
              ·
                refine ⟨322553485055368334133325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430071313407157778844433 322553485055368334133325)
                ·
                  refine ⟨120957556895763125299997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322553485055368334133325 120957556895763125299997)
                  ·
                    rfl

theorem cell21_530019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 3].length) (baseStart_530019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530019 prefixEnd_530019 := by exact prefixLift 530019
  have htrace : WordTrace (prefixWord ++ tailWord_530019) baseStart_530019 baseEnd_530019 := by
    simpa [prefixWord, tailWord_530019, baseEnd_530019] using wordTrace_append hprefix tailTrace_530019
  have hstable : (prefixWord ++ tailWord_530019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530019).length < 2 ^ (prefixWord ++ tailWord_530019).sum := by decide
  have hdescent : baseEnd_530019 < baseStart_530019 := by decide
  rcases family_descends (prefixWord ++ tailWord_530019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530078 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_530078 : Nat := 118140960795 + 530078 * 2 ^ 59
def prefixEnd_530078 : Nat := 4983230072969 + 3 ^ 40 * 530078 * 2
def baseEnd_530078 : Nat := 120971021499592133816543

theorem tailTrace_530078 : CollatzResearch.WordTrace tailWord_530078 prefixEnd_530078 120971021499592133816543 := by
  unfold tailWord_530078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2416691621703176370004861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12889021982416940640025925 2416691621703176370004861)
  ·
    refine ⟨906259358138691138751823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2416691621703176370004861 906259358138691138751823)
    ·
      refine ⟨1359389037208036708127735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906259358138691138751823 1359389037208036708127735)
      ·
        refine ⟨2039083555812055062191603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359389037208036708127735 2039083555812055062191603)
        ·
          refine ⟨3058625333718082593287405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2039083555812055062191603 3058625333718082593287405)
          ·
            refine ⟨1146984500144280972482777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3058625333718082593287405 1146984500144280972482777)
            ·
              refine ⟨860238375108210729362083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1146984500144280972482777 860238375108210729362083)
              ·
                refine ⟨1290357562662316094043125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860238375108210729362083 1290357562662316094043125)
                ·
                  refine ⟨120971021499592133816543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1290357562662316094043125 120971021499592133816543)
                  ·
                    rfl

theorem cell21_530078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_530078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530078 prefixEnd_530078 := by exact prefixLift 530078
  have htrace : WordTrace (prefixWord ++ tailWord_530078) baseStart_530078 baseEnd_530078 := by
    simpa [prefixWord, tailWord_530078, baseEnd_530078] using wordTrace_append hprefix tailTrace_530078
  have hstable : (prefixWord ++ tailWord_530078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530078).length < 2 ^ (prefixWord ++ tailWord_530078).sum := by decide
  have hdescent : baseEnd_530078 < baseStart_530078 := by decide
  rcases family_descends (prefixWord ++ tailWord_530078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530106 : List Nat := [3, 1, 1, 1, 2, 4, 4, 5]
def baseStart_530106 : Nat := 118140960795 + 530106 * 2 ^ 59
def prefixEnd_530106 : Nat := 4983230072969 + 3 ^ 40 * 530106 * 2
def baseEnd_530106 : Nat := 40325803827023435783273

theorem tailTrace_530106 : CollatzResearch.WordTrace tailWord_530106 prefixEnd_530106 40325803827023435783273 := by
  unfold tailWord_530106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4833638554380992935514543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12889702811682647828038781 4833638554380992935514543)
  ·
    refine ⟨7250457831571489403271815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4833638554380992935514543 7250457831571489403271815)
    ·
      refine ⟨10875686747357234104907723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7250457831571489403271815 10875686747357234104907723)
      ·
        refine ⟨16313530121035851157361585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10875686747357234104907723 16313530121035851157361585)
        ·
          refine ⟨12235147590776888368021189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16313530121035851157361585 12235147590776888368021189)
          ·
            refine ⟨2294090173270666569003973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12235147590776888368021189 2294090173270666569003973)
            ·
              refine ⟨430141907488249981688245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2294090173270666569003973 430141907488249981688245)
              ·
                refine ⟨40325803827023435783273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 430141907488249981688245 40325803827023435783273)
                ·
                  rfl

theorem cell21_530106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_530106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530106 prefixEnd_530106 := by exact prefixLift 530106
  have htrace : WordTrace (prefixWord ++ tailWord_530106) baseStart_530106 baseEnd_530106 := by
    simpa [prefixWord, tailWord_530106, baseEnd_530106] using wordTrace_append hprefix tailTrace_530106
  have hstable : (prefixWord ++ tailWord_530106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530106).length < 2 ^ (prefixWord ++ tailWord_530106).sum := by decide
  have hdescent : baseEnd_530106 < baseStart_530106 := by decide
  rcases family_descends (prefixWord ++ tailWord_530106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530137 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 5]
def baseStart_530137 : Nat := 118140960795 + 530137 * 2 ^ 59
def prefixEnd_530137 : Nat := 4983230072969 + 3 ^ 40 * 530137 * 2
def baseEnd_530137 : Nat := 120984486103421142333089

theorem tailTrace_530137 : CollatzResearch.WordTrace tailWord_530137 prefixEnd_530137 120984486103421142333089 := by
  unfold tailWord_530137
  simp only [CollatzResearch.WordTrace]
  refine ⟨19335684880411664036436665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12890456586941109357624443 19335684880411664036436665)
  ·
    refine ⟨14501763660308748027327499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19335684880411664036436665 14501763660308748027327499)
    ·
      refine ⟨21752645490463122040991249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14501763660308748027327499 21752645490463122040991249)
      ·
        refine ⟨16314484117847341530743437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21752645490463122040991249 16314484117847341530743437)
        ·
          refine ⟨6117931544192753074028789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16314484117847341530743437 6117931544192753074028789)
          ·
            refine ⟨573556082268070600690199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6117931544192753074028789 573556082268070600690199)
            ·
              refine ⟨860334123402105901035299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573556082268070600690199 860334123402105901035299)
              ·
                refine ⟨1290501185103158851552949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860334123402105901035299 1290501185103158851552949)
                ·
                  refine ⟨120984486103421142333089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1290501185103158851552949 120984486103421142333089)
                  ·
                    rfl

theorem cell21_530137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_530137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530137 prefixEnd_530137 := by exact prefixLift 530137
  have htrace : WordTrace (prefixWord ++ tailWord_530137) baseStart_530137 baseEnd_530137 := by
    simpa [prefixWord, tailWord_530137, baseEnd_530137] using wordTrace_append hprefix tailTrace_530137
  have hstable : (prefixWord ++ tailWord_530137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530137).length < 2 ^ (prefixWord ++ tailWord_530137).sum := by decide
  have hdescent : baseEnd_530137 < baseStart_530137 := by decide
  rcases family_descends (prefixWord ++ tailWord_530137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530272 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 5]
def baseStart_530272 : Nat := 118140960795 + 530272 * 2 ^ 59
def prefixEnd_530272 : Nat := 4983230072969 + 3 ^ 40 * 530272 * 2
def baseEnd_530272 : Nat := 121015294942690907582813

theorem tailTrace_530272 : CollatzResearch.WordTrace tailWord_530272 prefixEnd_530272 121015294942690907582813 := by
  unfold tailWord_530272
  simp only [CollatzResearch.WordTrace]
  refine ⟨9670304367461291046300535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12893739156615054728400713 9670304367461291046300535)
  ·
    refine ⟨14505456551191936569450803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9670304367461291046300535 14505456551191936569450803)
    ·
      refine ⟨21758184826787904854176205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14505456551191936569450803 21758184826787904854176205)
      ·
        refine ⟨8159319310045464320316077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21758184826787904854176205 8159319310045464320316077)
        ·
          refine ⟨3059744741267049120118529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8159319310045464320316077 3059744741267049120118529)
          ·
            refine ⟨2294808555950286840088897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3059744741267049120118529 2294808555950286840088897)
            ·
              refine ⟨1721106416962715130066673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2294808555950286840088897 1721106416962715130066673)
              ·
                refine ⟨1290829812722036347550005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721106416962715130066673 1290829812722036347550005)
                ·
                  refine ⟨121015294942690907582813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1290829812722036347550005 121015294942690907582813)
                  ·
                    rfl

theorem cell21_530272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_530272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530272 prefixEnd_530272 := by exact prefixLift 530272
  have htrace : WordTrace (prefixWord ++ tailWord_530272) baseStart_530272 baseEnd_530272 := by
    simpa [prefixWord, tailWord_530272, baseEnd_530272] using wordTrace_append hprefix tailTrace_530272
  have hstable : (prefixWord ++ tailWord_530272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530272).length < 2 ^ (prefixWord ++ tailWord_530272).sum := by decide
  have hdescent : baseEnd_530272 < baseStart_530272 := by decide
  rcases family_descends (prefixWord ++ tailWord_530272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530275 : List Nat := [1, 1, 1, 5, 4, 2, 2, 5]
def baseStart_530275 : Nat := 118140960795 + 530275 * 2 ^ 59
def prefixEnd_530275 : Nat := 4983230072969 + 3 ^ 40 * 530275 * 2
def baseEnd_530275 : Nat := 40338659861187856344269

theorem tailTrace_530275 : CollatzResearch.WordTrace tailWord_530275 prefixEnd_530275 40338659861187856344269 := by
  unfold tailWord_530275
  simp only [CollatzResearch.WordTrace]
  refine ⟨19340718153911713604960279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12893812102607809069973519 19340718153911713604960279)
  ·
    refine ⟨29011077230867570407440419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19340718153911713604960279 29011077230867570407440419)
    ·
      refine ⟨43516615846301355611160629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29011077230867570407440419 43516615846301355611160629)
      ·
        refine ⟨4079682735590752088546309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43516615846301355611160629 4079682735590752088546309)
        ·
          refine ⟨764940512923266016602433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4079682735590752088546309 764940512923266016602433)
          ·
            refine ⟨573705384692449512451825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764940512923266016602433 573705384692449512451825)
            ·
              refine ⟨430279038519337134338869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573705384692449512451825 430279038519337134338869)
              ·
                refine ⟨40338659861187856344269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 430279038519337134338869 40338659861187856344269)
                ·
                  rfl

theorem cell21_530275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 5].length) (baseStart_530275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530275 prefixEnd_530275 := by exact prefixLift 530275
  have htrace : WordTrace (prefixWord ++ tailWord_530275) baseStart_530275 baseEnd_530275 := by
    simpa [prefixWord, tailWord_530275, baseEnd_530275] using wordTrace_append hprefix tailTrace_530275
  have hstable : (prefixWord ++ tailWord_530275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530275).length < 2 ^ (prefixWord ++ tailWord_530275).sum := by decide
  have hdescent : baseEnd_530275 < baseStart_530275 := by decide
  rcases family_descends (prefixWord ++ tailWord_530275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530458 : List Nat := [3, 1, 1, 3, 1, 5, 1, 3, 3]
def baseStart_530458 : Nat := 118140960795 + 530458 * 2 ^ 59
def prefixEnd_530458 : Nat := 4983230072969 + 3 ^ 40 * 530458 * 2
def baseEnd_530458 : Nat := 121057742676795917482433

theorem tailTrace_530458 : CollatzResearch.WordTrace tailWord_530458 prefixEnd_530458 121057742676795917482433 := by
  unfold tailWord_530458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4836848178062183964718007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12898261808165823905914685 4836848178062183964718007)
  ·
    refine ⟨7255272267093275947077011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4836848178062183964718007 7255272267093275947077011)
    ·
      refine ⟨10882908400639913920615517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7255272267093275947077011 10882908400639913920615517)
      ·
        refine ⟨4081090650239967720230819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10882908400639913920615517 4081090650239967720230819)
        ·
          refine ⟨6121635975359951580346229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081090650239967720230819 6121635975359951580346229)
          ·
            refine ⟨573903372689995460657459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6121635975359951580346229 573903372689995460657459)
            ·
              refine ⟨860855059034993190986189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573903372689995460657459 860855059034993190986189)
              ·
                refine ⟨322820647138122446619821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 860855059034993190986189 322820647138122446619821)
                ·
                  refine ⟨121057742676795917482433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322820647138122446619821 121057742676795917482433)
                  ·
                    rfl

theorem cell21_530458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_530458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530458 prefixEnd_530458 := by exact prefixLift 530458
  have htrace : WordTrace (prefixWord ++ tailWord_530458) baseStart_530458 baseEnd_530458 := by
    simpa [prefixWord, tailWord_530458, baseEnd_530458] using wordTrace_append hprefix tailTrace_530458
  have hstable : (prefixWord ++ tailWord_530458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530458).length < 2 ^ (prefixWord ++ tailWord_530458).sum := by decide
  have hdescent : baseEnd_530458 < baseStart_530458 := by decide
  rcases family_descends (prefixWord ++ tailWord_530458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530469 : List Nat := [1, 3, 1, 2, 2, 5, 7]
def baseStart_530469 : Nat := 118140960795 + 530469 * 2 ^ 59
def prefixEnd_530469 : Nat := 4983230072969 + 3 ^ 40 * 530469 * 2
def baseEnd_530469 : Nat := 13451139225184704755453

theorem tailTrace_530469 : CollatzResearch.WordTrace tailWord_530469 prefixEnd_530469 13451139225184704755453 := by
  unfold tailWord_530469
  simp only [CollatzResearch.WordTrace]
  refine ⟨19347793915208884737522461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12898529276805923158348307 19347793915208884737522461)
  ·
    refine ⟨7255422718203331776570923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19347793915208884737522461 7255422718203331776570923)
    ·
      refine ⟨10883134077304997664856385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7255422718203331776570923 10883134077304997664856385)
      ·
        refine ⟨8162350557978748248642289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10883134077304997664856385 8162350557978748248642289)
        ·
          refine ⟨6121762918484061186481717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8162350557978748248642289 6121762918484061186481717)
          ·
            refine ⟨573915273607880736232661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6121762918484061186481717 573915273607880736232661)
            ·
              refine ⟨13451139225184704755453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 573915273607880736232661 13451139225184704755453)
              ·
                rfl

theorem cell21_530469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 7].length) (baseStart_530469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530469 prefixEnd_530469 := by exact prefixLift 530469
  have htrace : WordTrace (prefixWord ++ tailWord_530469) baseStart_530469 baseEnd_530469 := by
    simpa [prefixWord, tailWord_530469, baseEnd_530469] using wordTrace_append hprefix tailTrace_530469
  have hstable : (prefixWord ++ tailWord_530469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530469).length < 2 ^ (prefixWord ++ tailWord_530469).sum := by decide
  have hdescent : baseEnd_530469 < baseStart_530469 := by decide
  rcases family_descends (prefixWord ++ tailWord_530469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530486 : List Nat := [5, 1, 2, 1, 1, 1, 4, 6]
def baseStart_530486 : Nat := 118140960795 + 530486 * 2 ^ 59
def prefixEnd_530486 : Nat := 4983230072969 + 3 ^ 40 * 530486 * 2
def baseEnd_530486 : Nat := 40354710886091363671903

theorem tailTrace_530486 : CollatzResearch.WordTrace tailWord_530486 prefixEnd_530486 40354710886091363671903 := by
  unfold tailWord_530486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209275872259206040055707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12898942637431531093927541 1209275872259206040055707)
  ·
    refine ⟨1813913808388809060083561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1209275872259206040055707 1813913808388809060083561)
    ·
      refine ⟨1360435356291606795062671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1813913808388809060083561 1360435356291606795062671)
      ·
        refine ⟨2040653034437410192594007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1360435356291606795062671 2040653034437410192594007)
        ·
          refine ⟨3060979551656115288891011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2040653034437410192594007 3060979551656115288891011)
          ·
            refine ⟨4591469327484172933336517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3060979551656115288891011 4591469327484172933336517)
            ·
              refine ⟨860900498903282425000597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4591469327484172933336517 860900498903282425000597)
              ·
                refine ⟨40354710886091363671903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 860900498903282425000597 40354710886091363671903)
                ·
                  rfl

theorem cell21_530486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_530486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530486 prefixEnd_530486 := by exact prefixLift 530486
  have htrace : WordTrace (prefixWord ++ tailWord_530486) baseStart_530486 baseEnd_530486 := by
    simpa [prefixWord, tailWord_530486, baseEnd_530486] using wordTrace_append hprefix tailTrace_530486
  have hstable : (prefixWord ++ tailWord_530486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530486).length < 2 ^ (prefixWord ++ tailWord_530486).sum := by decide
  have hdescent : baseEnd_530486 < baseStart_530486 := by decide
  rcases family_descends (prefixWord ++ tailWord_530486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530489 : List Nat := [1, 2, 1, 5, 3, 2, 2, 1, 4]
def baseStart_530489 : Nat := 118140960795 + 530489 * 2 ^ 59
def prefixEnd_530489 : Nat := 4983230072969 + 3 ^ 40 * 530489 * 2
def baseEnd_530489 : Nat := 121064817299146752465703

theorem tailTrace_530489 : CollatzResearch.WordTrace tailWord_530489 prefixEnd_530489 121064817299146752465703 := by
  unfold tailWord_530489
  simp only [CollatzResearch.WordTrace]
  refine ⟨19348523375136428153250521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12899015583424285435500347 19348523375136428153250521)
  ·
    refine ⟨14511392531352321114937891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19348523375136428153250521 14511392531352321114937891)
    ·
      refine ⟨21767088797028481672406837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14511392531352321114937891 21767088797028481672406837)
      ·
        refine ⟨2040664574721420156788141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21767088797028481672406837 2040664574721420156788141)
        ·
          refine ⟨765249215520532558795553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2040664574721420156788141 765249215520532558795553)
          ·
            refine ⟨573936911640399419096665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765249215520532558795553 573936911640399419096665)
            ·
              refine ⟨430452683730299564322499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573936911640399419096665 430452683730299564322499)
              ·
                refine ⟨645679025595449346483749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430452683730299564322499 645679025595449346483749)
                ·
                  refine ⟨121064817299146752465703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 645679025595449346483749 121064817299146752465703)
                  ·
                    rfl

theorem cell21_530489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_530489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530489 prefixEnd_530489 := by exact prefixLift 530489
  have htrace : WordTrace (prefixWord ++ tailWord_530489) baseStart_530489 baseEnd_530489 := by
    simpa [prefixWord, tailWord_530489, baseEnd_530489] using wordTrace_append hprefix tailTrace_530489
  have hstable : (prefixWord ++ tailWord_530489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530489).length < 2 ^ (prefixWord ++ tailWord_530489).sum := by decide
  have hdescent : baseEnd_530489 < baseStart_530489 := by decide
  rcases family_descends (prefixWord ++ tailWord_530489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530526 : List Nat := [4, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_530526 : Nat := 118140960795 + 530526 * 2 ^ 59
def prefixEnd_530526 : Nat := 4983230072969 + 3 ^ 40 * 530526 * 2
def baseEnd_530526 : Nat := 121073261203242910348961

theorem tailTrace_530526 : CollatzResearch.WordTrace tailWord_530526 prefixEnd_530526 121073261203242910348961 := by
  unfold tailWord_530526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418734109500297934043429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12899915250668255648231621 2418734109500297934043429)
  ·
    refine ⟨453512645531305862633143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2418734109500297934043429 453512645531305862633143)
    ·
      refine ⟨680268968296958793949715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453512645531305862633143 680268968296958793949715)
      ·
        refine ⟨1020403452445438190924573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680268968296958793949715 1020403452445438190924573)
        ·
          refine ⟨382651294667039321596715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1020403452445438190924573 382651294667039321596715)
          ·
            refine ⟨573976942000558982395073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382651294667039321596715 573976942000558982395073)
            ·
              refine ⟨430482706500419236796305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573976942000558982395073 430482706500419236796305)
              ·
                refine ⟨322862029875314427597229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430482706500419236796305 322862029875314427597229)
                ·
                  refine ⟨121073261203242910348961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322862029875314427597229 121073261203242910348961)
                  ·
                    rfl

theorem cell21_530526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_530526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530526 prefixEnd_530526 := by exact prefixLift 530526
  have htrace : WordTrace (prefixWord ++ tailWord_530526) baseStart_530526 baseEnd_530526 := by
    simpa [prefixWord, tailWord_530526, baseEnd_530526] using wordTrace_append hprefix tailTrace_530526
  have hstable : (prefixWord ++ tailWord_530526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530526).length < 2 ^ (prefixWord ++ tailWord_530526).sum := by decide
  have hdescent : baseEnd_530526 < baseStart_530526 := by decide
  rcases family_descends (prefixWord ++ tailWord_530526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530528 : List Nat := [2, 1, 1, 3, 2, 12]
def baseStart_530528 : Nat := 118140960795 + 530528 * 2 ^ 59
def prefixEnd_530528 : Nat := 4983230072969 + 3 ^ 40 * 530528 * 2
def baseEnd_530528 : Nat := 4484211764092272270949

theorem tailTrace_530528 : CollatzResearch.WordTrace tailWord_530528 prefixEnd_530528 4484211764092272270949 := by
  unfold tailWord_530528
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674972910997568906960119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12899963881330091875946825 9674972910997568906960119)
  ·
    refine ⟨14512459366496353360440179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9674972910997568906960119 14512459366496353360440179)
    ·
      refine ⟨21768689049744530040660269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14512459366496353360440179 21768689049744530040660269)
      ·
        refine ⟨8163258393654198765247601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21768689049744530040660269 8163258393654198765247601)
        ·
          refine ⟨6122443795240649073935701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8163258393654198765247601 6122443795240649073935701)
          ·
            refine ⟨4484211764092272270949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6122443795240649073935701 4484211764092272270949)
            ·
              rfl

theorem cell21_530528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 12].length) (baseStart_530528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530528 prefixEnd_530528 := by exact prefixLift 530528
  have htrace : WordTrace (prefixWord ++ tailWord_530528) baseStart_530528 baseEnd_530528 := by
    simpa [prefixWord, tailWord_530528, baseEnd_530528] using wordTrace_append hprefix tailTrace_530528
  have hstable : (prefixWord ++ tailWord_530528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530528).length < 2 ^ (prefixWord ++ tailWord_530528).sum := by decide
  have hdescent : baseEnd_530528 < baseStart_530528 := by decide
  rcases family_descends (prefixWord ++ tailWord_530528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530593 : List Nat := [1, 2, 3, 3, 1, 2, 2, 4, 3]
def baseStart_530593 : Nat := 118140960795 + 530593 * 2 ^ 59
def prefixEnd_530593 : Nat := 4983230072969 + 3 ^ 40 * 530593 * 2
def baseEnd_530593 : Nat := 121088551516065682732157

theorem tailTrace_530593 : CollatzResearch.WordTrace tailWord_530593 prefixEnd_530593 121088551516065682732157 := by
  unfold tailWord_530593
  simp only [CollatzResearch.WordTrace]
  refine ⟨19352316566759653915036433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12901544377839769276690955 19352316566759653915036433)
  ·
    refine ⟨14514237425069740436277325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19352316566759653915036433 14514237425069740436277325)
    ·
      refine ⟨5442839034401152663603997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14514237425069740436277325 5442839034401152663603997)
      ·
        refine ⟨2041064637900432248851499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5442839034401152663603997 2041064637900432248851499)
        ·
          refine ⟨3061596956850648373277249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2041064637900432248851499 3061596956850648373277249)
          ·
            refine ⟨2296197717637986279957937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3061596956850648373277249 2296197717637986279957937)
            ·
              refine ⟨1722148288228489709968453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2296197717637986279957937 1722148288228489709968453)
              ·
                refine ⟨322902804042841820619085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1722148288228489709968453 322902804042841820619085)
                ·
                  refine ⟨121088551516065682732157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322902804042841820619085 121088551516065682732157)
                  ·
                    rfl

theorem cell21_530593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 3].length) (baseStart_530593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530593 prefixEnd_530593 := by exact prefixLift 530593
  have htrace : WordTrace (prefixWord ++ tailWord_530593) baseStart_530593 baseEnd_530593 := by
    simpa [prefixWord, tailWord_530593, baseEnd_530593] using wordTrace_append hprefix tailTrace_530593
  have hstable : (prefixWord ++ tailWord_530593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530593).length < 2 ^ (prefixWord ++ tailWord_530593).sum := by decide
  have hdescent : baseEnd_530593 < baseStart_530593 := by decide
  rcases family_descends (prefixWord ++ tailWord_530593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530658 : List Nat := [3, 3, 4, 1, 1, 1, 1, 3, 4]
def baseStart_530658 : Nat := 118140960795 + 530658 * 2 ^ 59
def prefixEnd_530658 : Nat := 4983230072969 + 3 ^ 40 * 530658 * 2
def baseEnd_530658 : Nat := 121103385401640014148691

theorem tailTrace_530658 : CollatzResearch.WordTrace tailWord_530658 prefixEnd_530658 121103385401640014148691 := by
  unfold tailWord_530658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4838671827881042504038157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12903124874349446677435085 4838671827881042504038157)
  ·
    refine ⟨1814501935455390939014309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4838671827881042504038157 1814501935455390939014309)
    ·
      refine ⟨340219112897885801065183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1814501935455390939014309 340219112897885801065183)
      ·
        refine ⟨510328669346828701597775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340219112897885801065183 510328669346828701597775)
        ·
          refine ⟨765493004020243052396663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510328669346828701597775 765493004020243052396663)
          ·
            refine ⟨1148239506030364578594995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765493004020243052396663 1148239506030364578594995)
            ·
              refine ⟨1722359259045546867892493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148239506030364578594995 1722359259045546867892493)
              ·
                refine ⟨645884722142080075459685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1722359259045546867892493 645884722142080075459685)
                ·
                  refine ⟨121103385401640014148691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 645884722142080075459685 121103385401640014148691)
                  ·
                    rfl

theorem cell21_530658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_530658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530658 prefixEnd_530658 := by exact prefixLift 530658
  have htrace : WordTrace (prefixWord ++ tailWord_530658) baseStart_530658 baseEnd_530658 := by
    simpa [prefixWord, tailWord_530658, baseEnd_530658] using wordTrace_append hprefix tailTrace_530658
  have hstable : (prefixWord ++ tailWord_530658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530658).length < 2 ^ (prefixWord ++ tailWord_530658).sum := by decide
  have hdescent : baseEnd_530658 < baseStart_530658 := by decide
  rcases family_descends (prefixWord ++ tailWord_530658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530714 : List Nat := [3, 1, 1, 3, 4, 2, 1, 6]
def baseStart_530714 : Nat := 118140960795 + 530714 * 2 ^ 59
def prefixEnd_530714 : Nat := 4983230072969 + 3 ^ 40 * 530714 * 2
def baseEnd_530714 : Nat := 40372055121532120405081

theorem tailTrace_530714 : CollatzResearch.WordTrace tailWord_530714 prefixEnd_530714 40372055121532120405081 := by
  unfold tailWord_530714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4839182449830322895047799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12904486532880861053460797 4839182449830322895047799)
  ·
    refine ⟨7258773674745484342571699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4839182449830322895047799 7258773674745484342571699)
    ·
      refine ⟨10888160512118226513857549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7258773674745484342571699 10888160512118226513857549)
      ·
        refine ⟨4083060192044334942696581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10888160512118226513857549 4083060192044334942696581)
        ·
          refine ⟨765573786008312801755609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4083060192044334942696581 765573786008312801755609)
          ·
            refine ⟨574180339506234601316707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765573786008312801755609 574180339506234601316707)
            ·
              refine ⟨861270509259351901975061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574180339506234601316707 861270509259351901975061)
              ·
                refine ⟨40372055121532120405081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 861270509259351901975061 40372055121532120405081)
                ·
                  rfl

theorem cell21_530714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_530714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530714 prefixEnd_530714 := by exact prefixLift 530714
  have htrace : WordTrace (prefixWord ++ tailWord_530714) baseStart_530714 baseEnd_530714 := by
    simpa [prefixWord, tailWord_530714, baseEnd_530714] using wordTrace_append hprefix tailTrace_530714
  have hstable : (prefixWord ++ tailWord_530714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530714).length < 2 ^ (prefixWord ++ tailWord_530714).sum := by decide
  have hdescent : baseEnd_530714 < baseStart_530714 := by decide
  rcases family_descends (prefixWord ++ tailWord_530714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530745 : List Nat := [1, 2, 1, 6, 1, 1, 1, 5, 3]
def baseStart_530745 : Nat := 118140960795 + 530745 * 2 ^ 59
def prefixEnd_530745 : Nat := 4983230072969 + 3 ^ 40 * 530745 * 2
def baseEnd_530745 : Nat := 121123239986947196198513

theorem tailTrace_530745 : CollatzResearch.WordTrace tailWord_530745 prefixEnd_530745 121123239986947196198513 := by
  unfold tailWord_530745
  simp only [CollatzResearch.WordTrace]
  refine ⟨19357860462208983874569689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12905240308139322583046459 19357860462208983874569689)
  ·
    refine ⟨14518395346656737905927267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19357860462208983874569689 14518395346656737905927267)
    ·
      refine ⟨21777593019985106858890901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14518395346656737905927267 21777593019985106858890901)
      ·
        refine ⟨1020824672811801884010511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21777593019985106858890901 1020824672811801884010511)
        ·
          refine ⟨1531237009217702826015767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020824672811801884010511 1531237009217702826015767)
          ·
            refine ⟨2296855513826554239023651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531237009217702826015767 2296855513826554239023651)
            ·
              refine ⟨3445283270739831358535477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296855513826554239023651 3445283270739831358535477)
              ·
                refine ⟨322995306631859189862701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3445283270739831358535477 322995306631859189862701)
                ·
                  refine ⟨121123239986947196198513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322995306631859189862701 121123239986947196198513)
                  ·
                    rfl

theorem cell21_530745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 3].length) (baseStart_530745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530745 prefixEnd_530745 := by exact prefixLift 530745
  have htrace : WordTrace (prefixWord ++ tailWord_530745) baseStart_530745 baseEnd_530745 := by
    simpa [prefixWord, tailWord_530745, baseEnd_530745] using wordTrace_append hprefix tailTrace_530745
  have hstable : (prefixWord ++ tailWord_530745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530745).length < 2 ^ (prefixWord ++ tailWord_530745).sum := by decide
  have hdescent : baseEnd_530745 < baseStart_530745 := by decide
  rcases family_descends (prefixWord ++ tailWord_530745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530782 : List Nat := [4, 4, 2, 1, 1, 2, 2, 5]
def baseStart_530782 : Nat := 118140960795 + 530782 * 2 ^ 59
def prefixEnd_530782 : Nat := 4983230072969 + 3 ^ 40 * 530782 * 2
def baseEnd_530782 : Nat := 40377227963681118027257

theorem tailTrace_530782 : CollatzResearch.WordTrace tailWord_530782 prefixEnd_530782 40377227963681118027257 := by
  unfold tailWord_530782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419901245384367399208325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12906139975383292795777733 2419901245384367399208325)
  ·
    refine ⟨453731483509568887351561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2419901245384367399208325 453731483509568887351561)
    ·
      refine ⟨340298612632176665513671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453731483509568887351561 340298612632176665513671)
      ·
        refine ⟨510447918948264998270507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340298612632176665513671 510447918948264998270507)
        ·
          refine ⟨765671878422397497405761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510447918948264998270507 765671878422397497405761)
          ·
            refine ⟨574253908816798123054321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765671878422397497405761 574253908816798123054321)
            ·
              refine ⟨430690431612598592290741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574253908816798123054321 430690431612598592290741)
              ·
                refine ⟨40377227963681118027257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 430690431612598592290741 40377227963681118027257)
                ·
                  rfl

theorem cell21_530782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_530782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530782 prefixEnd_530782 := by exact prefixLift 530782
  have htrace : WordTrace (prefixWord ++ tailWord_530782) baseStart_530782 baseEnd_530782 := by
    simpa [prefixWord, tailWord_530782, baseEnd_530782] using wordTrace_append hprefix tailTrace_530782
  have hstable : (prefixWord ++ tailWord_530782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530782).length < 2 ^ (prefixWord ++ tailWord_530782).sum := by decide
  have hdescent : baseEnd_530782 < baseStart_530782 := by decide
  rcases family_descends (prefixWord ++ tailWord_530782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530787 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 5]
def baseStart_530787 : Nat := 118140960795 + 530787 * 2 ^ 59
def prefixEnd_530787 : Nat := 4983230072969 + 3 ^ 40 * 530787 * 2
def baseEnd_530787 : Nat := 121132824959164456498427

theorem tailTrace_530787 : CollatzResearch.WordTrace tailWord_530787 prefixEnd_530787 121132824959164456498427 := by
  unfold tailWord_530787
  simp only [CollatzResearch.WordTrace]
  refine ⟨19359392328056825047598615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12906261552037883365065743 19359392328056825047598615)
  ·
    refine ⟨29039088492085237571397923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19359392328056825047598615 29039088492085237571397923)
    ·
      refine ⟨43558632738127856357096885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29039088492085237571397923 43558632738127856357096885)
      ·
        refine ⟨4083621819199486533477833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43558632738127856357096885 4083621819199486533477833)
        ·
          refine ⟨3062716364399614900108375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4083621819199486533477833 3062716364399614900108375)
          ·
            refine ⟨4594074546599422350162563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062716364399614900108375 4594074546599422350162563)
            ·
              refine ⟨6891111819899133525243845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594074546599422350162563 6891111819899133525243845)
              ·
                refine ⟨1292083466231087535983221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6891111819899133525243845 1292083466231087535983221)
                ·
                  refine ⟨121132824959164456498427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1292083466231087535983221 121132824959164456498427)
                  ·
                    rfl

theorem cell21_530787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_530787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530787 prefixEnd_530787 := by exact prefixLift 530787
  have htrace : WordTrace (prefixWord ++ tailWord_530787) baseStart_530787 baseEnd_530787 := by
    simpa [prefixWord, tailWord_530787, baseEnd_530787] using wordTrace_append hprefix tailTrace_530787
  have hstable : (prefixWord ++ tailWord_530787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530787).length < 2 ^ (prefixWord ++ tailWord_530787).sum := by decide
  have hdescent : baseEnd_530787 < baseStart_530787 := by decide
  rcases family_descends (prefixWord ++ tailWord_530787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530925 : List Nat := [1, 5, 1, 3, 1, 2, 8]
def baseStart_530925 : Nat := 118140960795 + 530925 * 2 ^ 59
def prefixEnd_530925 : Nat := 4983230072969 + 3 ^ 40 * 530925 * 2
def baseEnd_530925 : Nat := 13462702048811875910905

theorem tailTrace_530925 : CollatzResearch.WordTrace tailWord_530925 prefixEnd_530925 13462702048811875910905 := by
  unfold tailWord_530925
  simp only [CollatzResearch.WordTrace]
  refine ⟨19364425601556874616122229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12909617067704583077414819 19364425601556874616122229)
  ·
    refine ⟨1815414900145956995261459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19364425601556874616122229 1815414900145956995261459)
    ·
      refine ⟨2723122350218935492892189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1815414900145956995261459 2723122350218935492892189)
      ·
        refine ⟨1021170881332100809834571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2723122350218935492892189 1021170881332100809834571)
        ·
          refine ⟨1531756321998151214751857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021170881332100809834571 1531756321998151214751857)
          ·
            refine ⟨1148817241498613411063893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1531756321998151214751857 1148817241498613411063893)
            ·
              refine ⟨13462702048811875910905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1148817241498613411063893 13462702048811875910905)
              ·
                rfl

theorem cell21_530925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 8].length) (baseStart_530925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530925 prefixEnd_530925 := by exact prefixLift 530925
  have htrace : WordTrace (prefixWord ++ tailWord_530925) baseStart_530925 baseEnd_530925 := by
    simpa [prefixWord, tailWord_530925, baseEnd_530925] using wordTrace_append hprefix tailTrace_530925
  have hstable : (prefixWord ++ tailWord_530925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530925).length < 2 ^ (prefixWord ++ tailWord_530925).sum := by decide
  have hdescent : baseEnd_530925 < baseStart_530925 := by decide
  rcases family_descends (prefixWord ++ tailWord_530925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530973 : List Nat := [1, 4, 2, 2, 1, 2, 3, 3, 3]
def baseStart_530973 : Nat := 118140960795 + 530973 * 2 ^ 59
def prefixEnd_530973 : Nat := 4983230072969 + 3 ^ 40 * 530973 * 2
def baseEnd_530973 : Nat := 121175272693269466398047

theorem tailTrace_530973 : CollatzResearch.WordTrace tailWord_530973 prefixEnd_530973 121175272693269466398047 := by
  unfold tailWord_530973
  simp only [CollatzResearch.WordTrace]
  refine ⟨19366176305382978813869573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12910784203588652542579715 19366176305382978813869573)
  ·
    refine ⟨3631158057259308527600545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19366176305382978813869573 3631158057259308527600545)
    ·
      refine ⟨2723368542944481395700409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3631158057259308527600545 2723368542944481395700409)
      ·
        refine ⟨2042526407208361046775307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2723368542944481395700409 2042526407208361046775307)
        ·
          refine ⟨3063789610812541570162961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2042526407208361046775307 3063789610812541570162961)
          ·
            refine ⟨2297842208109406177622221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3063789610812541570162961 2297842208109406177622221)
            ·
              refine ⟨861690828041027316608333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2297842208109406177622221 861690828041027316608333)
              ·
                refine ⟨323134060515385243728125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 861690828041027316608333 323134060515385243728125)
                ·
                  refine ⟨121175272693269466398047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323134060515385243728125 121175272693269466398047)
                  ·
                    rfl

theorem cell21_530973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_530973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530973 prefixEnd_530973 := by exact prefixLift 530973
  have htrace : WordTrace (prefixWord ++ tailWord_530973) baseStart_530973 baseEnd_530973 := by
    simpa [prefixWord, tailWord_530973, baseEnd_530973] using wordTrace_append hprefix tailTrace_530973
  have hstable : (prefixWord ++ tailWord_530973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530973).length < 2 ^ (prefixWord ++ tailWord_530973).sum := by decide
  have hdescent : baseEnd_530973 < baseStart_530973 := by decide
  rcases family_descends (prefixWord ++ tailWord_530973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530990 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_530990 : Nat := 118140960795 + 530990 * 2 ^ 59
def prefixEnd_530990 : Nat := 4983230072969 + 3 ^ 40 * 530990 * 2
def baseEnd_530990 : Nat := 121179152324881214614679

theorem tailTrace_530990 : CollatzResearch.WordTrace tailWord_530990 prefixEnd_530990 121179152324881214614679 := by
  unfold tailWord_530990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2420849543290173839654803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12911197564214260478158949 2420849543290173839654803)
  ·
    refine ⟨3631274314935260759482205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2420849543290173839654803 3631274314935260759482205)
    ·
      refine ⟨1361727868100722784805827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3631274314935260759482205 1361727868100722784805827)
      ·
        refine ⟨2042591802151084177208741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1361727868100722784805827 2042591802151084177208741)
        ·
          refine ⟨382985962903328283226639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2042591802151084177208741 382985962903328283226639)
          ·
            refine ⟨574478944354992424839959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382985962903328283226639 574478944354992424839959)
            ·
              refine ⟨861718416532488637259939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574478944354992424839959 861718416532488637259939)
              ·
                refine ⟨1292577624798732955889909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 861718416532488637259939 1292577624798732955889909)
                ·
                  refine ⟨121179152324881214614679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1292577624798732955889909 121179152324881214614679)
                  ·
                    rfl

theorem cell21_530990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_530990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_530990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_530990 prefixEnd_530990 := by exact prefixLift 530990
  have htrace : WordTrace (prefixWord ++ tailWord_530990) baseStart_530990 baseEnd_530990 := by
    simpa [prefixWord, tailWord_530990, baseEnd_530990] using wordTrace_append hprefix tailTrace_530990
  have hstable : (prefixWord ++ tailWord_530990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530990).length < 2 ^ (prefixWord ++ tailWord_530990).sum := by decide
  have hdescent : baseEnd_530990 < baseStart_530990 := by decide
  rcases family_descends (prefixWord ++ tailWord_530990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531004 : List Nat := [2, 2, 2, 2, 3, 3, 2, 1, 4]
def baseStart_531004 : Nat := 118140960795 + 531004 * 2 ^ 59
def prefixEnd_531004 : Nat := 4983230072969 + 3 ^ 40 * 531004 * 2
def baseEnd_531004 : Nat := 121182347315620301381317

theorem tailTrace_531004 : CollatzResearch.WordTrace tailWord_531004 prefixEnd_531004 121182347315620301381317 := by
  unfold tailWord_531004
  simp only [CollatzResearch.WordTrace]
  refine ⟨9683653484135335554124033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12911537978847114072165377 9683653484135335554124033)
  ·
    refine ⟨7262740113101501665593025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9683653484135335554124033 7262740113101501665593025)
    ·
      refine ⟨5447055084826126249194769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7262740113101501665593025 5447055084826126249194769)
      ·
        refine ⟨4085291313619594686896077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5447055084826126249194769 4085291313619594686896077)
        ·
          refine ⟨1531984242607348007586029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4085291313619594686896077 1531984242607348007586029)
          ·
            refine ⟨574494090977755502844761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1531984242607348007586029 574494090977755502844761)
            ·
              refine ⟨430870568233316627133571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574494090977755502844761 430870568233316627133571)
              ·
                refine ⟨646305852349974940700357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430870568233316627133571 646305852349974940700357)
                ·
                  refine ⟨121182347315620301381317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646305852349974940700357 121182347315620301381317)
                  ·
                    rfl

theorem cell21_531004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_531004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531004 prefixEnd_531004 := by exact prefixLift 531004
  have htrace : WordTrace (prefixWord ++ tailWord_531004) baseStart_531004 baseEnd_531004 := by
    simpa [prefixWord, tailWord_531004, baseEnd_531004] using wordTrace_append hprefix tailTrace_531004
  have hstable : (prefixWord ++ tailWord_531004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531004).length < 2 ^ (prefixWord ++ tailWord_531004).sum := by decide
  have hdescent : baseEnd_531004 < baseStart_531004 := by decide
  rcases family_descends (prefixWord ++ tailWord_531004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531029 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 8]
def baseStart_531029 : Nat := 118140960795 + 531029 * 2 ^ 59
def prefixEnd_531029 : Nat := 4983230072969 + 3 ^ 40 * 531029 * 2
def baseEnd_531029 : Nat := 121188052656225813464599

theorem tailTrace_531029 : CollatzResearch.WordTrace tailWord_531029 prefixEnd_531029 121188052656225813464599 := by
  unfold tailWord_531029
  simp only [CollatzResearch.WordTrace]
  refine ⟨19368218793180100377908141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12912145862120066918605427 19368218793180100377908141)
  ·
    refine ⟨7263082047442537641715553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19368218793180100377908141 7263082047442537641715553)
    ·
      refine ⟨5447311535581903231286665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7263082047442537641715553 5447311535581903231286665)
      ·
        refine ⟨4085483651686427423464999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5447311535581903231286665 4085483651686427423464999)
        ·
          refine ⟨6128225477529641135197499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4085483651686427423464999 6128225477529641135197499)
          ·
            refine ⟨9192338216294461702796249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6128225477529641135197499 9192338216294461702796249)
            ·
              refine ⟨6894253662220846277097187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9192338216294461702796249 6894253662220846277097187)
              ·
                refine ⟨10341380493331269415645781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6894253662220846277097187 10341380493331269415645781)
                ·
                  refine ⟨121188052656225813464599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10341380493331269415645781 121188052656225813464599)
                  ·
                    rfl

theorem cell21_531029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_531029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531029 prefixEnd_531029 := by exact prefixLift 531029
  have htrace : WordTrace (prefixWord ++ tailWord_531029) baseStart_531029 baseEnd_531029 := by
    simpa [prefixWord, tailWord_531029, baseEnd_531029] using wordTrace_append hprefix tailTrace_531029
  have hstable : (prefixWord ++ tailWord_531029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531029).length < 2 ^ (prefixWord ++ tailWord_531029).sum := by decide
  have hdescent : baseEnd_531029 < baseStart_531029 := by decide
  rcases family_descends (prefixWord ++ tailWord_531029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531038 : List Nat := [4, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_531038 : Nat := 118140960795 + 531038 * 2 ^ 59
def prefixEnd_531038 : Nat := 4983230072969 + 3 ^ 40 * 531038 * 2
def baseEnd_531038 : Nat := 121190106578843797814581

theorem tailTrace_531038 : CollatzResearch.WordTrace tailWord_531038 prefixEnd_531038 121190106578843797814581 := by
  unfold tailWord_531038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421068381268436864373221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12912364700098329943323845 2421068381268436864373221)
  ·
    refine ⟨453950321487831912069979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2421068381268436864373221 453950321487831912069979)
    ·
      refine ⟨680925482231747868104969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453950321487831912069979 680925482231747868104969)
      ·
        refine ⟨510694111673810901078727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680925482231747868104969 510694111673810901078727)
        ·
          refine ⟨766041167510716351618091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510694111673810901078727 766041167510716351618091)
          ·
            refine ⟨1149061751266074527427137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766041167510716351618091 1149061751266074527427137)
            ·
              refine ⟨861796313449555895570353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149061751266074527427137 861796313449555895570353)
              ·
                refine ⟨646347235087166921677765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861796313449555895570353 646347235087166921677765)
                ·
                  refine ⟨121190106578843797814581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646347235087166921677765 121190106578843797814581)
                  ·
                    rfl

theorem cell21_531038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_531038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531038 prefixEnd_531038 := by exact prefixLift 531038
  have htrace : WordTrace (prefixWord ++ tailWord_531038) baseStart_531038 baseEnd_531038 := by
    simpa [prefixWord, tailWord_531038, baseEnd_531038] using wordTrace_append hprefix tailTrace_531038
  have hstable : (prefixWord ++ tailWord_531038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531038).length < 2 ^ (prefixWord ++ tailWord_531038).sum := by decide
  have hdescent : baseEnd_531038 < baseStart_531038 := by decide
  rcases family_descends (prefixWord ++ tailWord_531038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531077 : List Nat := [1, 3, 1, 1, 4, 3, 3, 5]
def baseStart_531077 : Nat := 118140960795 + 531077 * 2 ^ 59
def prefixEnd_531077 : Nat := 4983230072969 + 3 ^ 40 * 531077 * 2
def baseEnd_531077 : Nat := 40399668970062798888167

theorem tailTrace_531077 : CollatzResearch.WordTrace tailWord_531077 prefixEnd_531077 40399668970062798888167 := by
  unfold tailWord_531077
  simp only [CollatzResearch.WordTrace]
  refine ⟨19369969497006204575655485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12913312998004136383770323 19369969497006204575655485)
  ·
    refine ⟨7263738561377326715870807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19369969497006204575655485 7263738561377326715870807)
    ·
      refine ⟨10895607842065990073806211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7263738561377326715870807 10895607842065990073806211)
      ·
        refine ⟨16343411763098985110709317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10895607842065990073806211 16343411763098985110709317)
        ·
          refine ⟨3064389705581059708257997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16343411763098985110709317 3064389705581059708257997)
          ·
            refine ⟨1149146139592897390596749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3064389705581059708257997 1149146139592897390596749)
            ·
              refine ⟨430929802347336521473781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1149146139592897390596749 430929802347336521473781)
              ·
                refine ⟨40399668970062798888167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 430929802347336521473781 40399668970062798888167)
                ·
                  rfl

theorem cell21_531077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 5].length) (baseStart_531077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531077 prefixEnd_531077 := by exact prefixLift 531077
  have htrace : WordTrace (prefixWord ++ tailWord_531077) baseStart_531077 baseEnd_531077 := by
    simpa [prefixWord, tailWord_531077, baseEnd_531077] using wordTrace_append hprefix tailTrace_531077
  have hstable : (prefixWord ++ tailWord_531077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531077).length < 2 ^ (prefixWord ++ tailWord_531077).sum := by decide
  have hdescent : baseEnd_531077 < baseStart_531077 := by decide
  rcases family_descends (prefixWord ++ tailWord_531077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531108 : List Nat := [2, 3, 1, 2, 2, 1, 1, 6, 3]
def baseStart_531108 : Nat := 118140960795 + 531108 * 2 ^ 59
def prefixEnd_531108 : Nat := 4983230072969 + 3 ^ 40 * 531108 * 2
def baseEnd_531108 : Nat := 121206081532539231647771

theorem tailTrace_531108 : CollatzResearch.WordTrace tailWord_531108 prefixEnd_531108 121206081532539231647771 := by
  unfold tailWord_531108
  simp only [CollatzResearch.WordTrace]
  refine ⟨9685550079946948435016989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12914066773262597913355985 9685550079946948435016989)
  ·
    refine ⟨3632081279980105663131371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9685550079946948435016989 3632081279980105663131371)
    ·
      refine ⟨5448121919970158494697057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3632081279980105663131371 5448121919970158494697057)
      ·
        refine ⟨4086091439977618871022793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5448121919970158494697057 4086091439977618871022793)
        ·
          refine ⟨3064568579983214153267095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4086091439977618871022793 3064568579983214153267095)
          ·
            refine ⟨4596852869974821229900643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3064568579983214153267095 4596852869974821229900643)
            ·
              refine ⟨6895279304962231844850965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4596852869974821229900643 6895279304962231844850965)
              ·
                refine ⟨323216217420104617727389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6895279304962231844850965 323216217420104617727389)
                ·
                  refine ⟨121206081532539231647771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323216217420104617727389 121206081532539231647771)
                  ·
                    rfl

theorem cell21_531108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_531108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531108 prefixEnd_531108 := by exact prefixLift 531108
  have htrace : WordTrace (prefixWord ++ tailWord_531108) baseStart_531108 baseEnd_531108 := by
    simpa [prefixWord, tailWord_531108, baseEnd_531108] using wordTrace_append hprefix tailTrace_531108
  have hstable : (prefixWord ++ tailWord_531108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531108).length < 2 ^ (prefixWord ++ tailWord_531108).sum := by decide
  have hdescent : baseEnd_531108 < baseStart_531108 := by decide
  rcases family_descends (prefixWord ++ tailWord_531108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531136 : List Nat := [2, 1, 1, 2, 4, 3, 1, 7]
def baseStart_531136 : Nat := 118140960795 + 531136 * 2 ^ 59
def prefixEnd_531136 : Nat := 4983230072969 + 3 ^ 40 * 531136 * 2
def baseEnd_531136 : Nat := 40404157171339135060349

theorem tailTrace_531136 : CollatzResearch.WordTrace tailWord_531136 prefixEnd_531136 40404157171339135060349 := by
  unfold tailWord_531136
  simp only [CollatzResearch.WordTrace]
  refine ⟨9686060701896228826026631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12914747602528305101368841 9686060701896228826026631)
  ·
    refine ⟨14529091052844343239039947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9686060701896228826026631 14529091052844343239039947)
    ·
      refine ⟨21793636579266514858559921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14529091052844343239039947 21793636579266514858559921)
      ·
        refine ⟨16345227434449886143919941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21793636579266514858559921 16345227434449886143919941)
        ·
          refine ⟨3064730143959353651984989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16345227434449886143919941 3064730143959353651984989)
          ·
            refine ⟨1149273803984757619494371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3064730143959353651984989 1149273803984757619494371)
            ·
              refine ⟨1723910705977136429241557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149273803984757619494371 1723910705977136429241557)
              ·
                refine ⟨40404157171339135060349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1723910705977136429241557 40404157171339135060349)
                ·
                  rfl

theorem cell21_531136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_531136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531136 prefixEnd_531136 := by exact prefixLift 531136
  have htrace : WordTrace (prefixWord ++ tailWord_531136) baseStart_531136 baseEnd_531136 := by
    simpa [prefixWord, tailWord_531136, baseEnd_531136] using wordTrace_append hprefix tailTrace_531136
  have hstable : (prefixWord ++ tailWord_531136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531136).length < 2 ^ (prefixWord ++ tailWord_531136).sum := by decide
  have hdescent : baseEnd_531136 < baseStart_531136 := by decide
  rcases family_descends (prefixWord ++ tailWord_531136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531167 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 5]
def baseStart_531167 : Nat := 118140960795 + 531167 * 2 ^ 59
def prefixEnd_531167 : Nat := 4983230072969 + 3 ^ 40 * 531167 * 2
def baseEnd_531167 : Nat := 121219546136368240164317

theorem tailTrace_531167 : CollatzResearch.WordTrace tailWord_531167 prefixEnd_531167 121219546136368240164317 := by
  unfold tailWord_531167
  simp only [CollatzResearch.WordTrace]
  refine ⟨19373252066680149946431755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12915501377786766630954503 19373252066680149946431755)
  ·
    refine ⟨29059878100020224919647633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19373252066680149946431755 29059878100020224919647633)
    ·
      refine ⟨21794908575015168689735725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29059878100020224919647633 21794908575015168689735725)
      ·
        refine ⟨8173090715630688258650897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21794908575015168689735725 8173090715630688258650897)
        ·
          refine ⟨6129818036723016193988173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8173090715630688258650897 6129818036723016193988173)
          ·
            refine ⟨2298681763771131072745565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6129818036723016193988173 2298681763771131072745565)
            ·
              refine ⟨862005661414174152279587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2298681763771131072745565 862005661414174152279587)
              ·
                refine ⟨1293008492121261228419381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862005661414174152279587 1293008492121261228419381)
                ·
                  refine ⟨121219546136368240164317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1293008492121261228419381 121219546136368240164317)
                  ·
                    rfl

theorem cell21_531167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 5].length) (baseStart_531167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531167 prefixEnd_531167 := by exact prefixLift 531167
  have htrace : WordTrace (prefixWord ++ tailWord_531167) baseStart_531167 baseEnd_531167 := by
    simpa [prefixWord, tailWord_531167, baseEnd_531167] using wordTrace_append hprefix tailTrace_531167
  have hstable : (prefixWord ++ tailWord_531167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531167).length < 2 ^ (prefixWord ++ tailWord_531167).sum := by decide
  have hdescent : baseEnd_531167 < baseStart_531167 := by decide
  rcases family_descends (prefixWord ++ tailWord_531167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531218 : List Nat := [3, 2, 4, 1, 2, 1, 1, 4, 3]
def baseStart_531218 : Nat := 118140960795 + 531218 * 2 ^ 59
def prefixEnd_531218 : Nat := 4983230072969 + 3 ^ 40 * 531218 * 2
def baseEnd_531218 : Nat := 121231185031203484814213

theorem tailTrace_531218 : CollatzResearch.WordTrace tailWord_531218 prefixEnd_531218 121231185031203484814213 := by
  unfold tailWord_531218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4843778047373846414134577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12916741459663590437692205 4843778047373846414134577)
  ·
    refine ⟨3632833535530384810600933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4843778047373846414134577 3632833535530384810600933)
    ·
      refine ⟨681156287911947151987675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3632833535530384810600933 681156287911947151987675)
      ·
        refine ⟨1021734431867920727981513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681156287911947151987675 1021734431867920727981513)
        ·
          refine ⟨766300823900940545986135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1021734431867920727981513 766300823900940545986135)
          ·
            refine ⟨1149451235851410818979203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766300823900940545986135 1149451235851410818979203)
            ·
              refine ⟨1724176853777116228468805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149451235851410818979203 1724176853777116228468805)
              ·
                refine ⟨323283160083209292837901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1724176853777116228468805 323283160083209292837901)
                ·
                  refine ⟨121231185031203484814213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323283160083209292837901 121231185031203484814213)
                  ·
                    rfl

theorem cell21_531218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_531218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531218 prefixEnd_531218 := by exact prefixLift 531218
  have htrace : WordTrace (prefixWord ++ tailWord_531218) baseStart_531218 baseEnd_531218 := by
    simpa [prefixWord, tailWord_531218, baseEnd_531218] using wordTrace_append hprefix tailTrace_531218
  have hstable : (prefixWord ++ tailWord_531218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531218).length < 2 ^ (prefixWord ++ tailWord_531218).sum := by decide
  have hdescent : baseEnd_531218 < baseStart_531218 := by decide
  rcases family_descends (prefixWord ++ tailWord_531218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531246 : List Nat := [4, 1, 3, 2, 1, 2, 3, 5]
def baseStart_531246 : Nat := 118140960795 + 531246 * 2 ^ 59
def prefixEnd_531246 : Nat := 4983230072969 + 3 ^ 40 * 531246 * 2
def baseEnd_531246 : Nat := 40412525004227219449163

theorem tailTrace_531246 : CollatzResearch.WordTrace tailWord_531246 prefixEnd_531246 40412525004227219449163 := by
  unfold tailWord_531246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2422016679174243304819699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12917422288929297625705061 2422016679174243304819699)
  ·
    refine ⟨3633025018761364957229549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2422016679174243304819699 3633025018761364957229549)
    ·
      refine ⟨1362384382035511858961081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3633025018761364957229549 1362384382035511858961081)
      ·
        refine ⟨1021788286526633894220811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1362384382035511858961081 1021788286526633894220811)
        ·
          refine ⟨1532682429789950841331217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021788286526633894220811 1532682429789950841331217)
          ·
            refine ⟨1149511822342463130998413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1532682429789950841331217 1149511822342463130998413)
            ·
              refine ⟨431066933378423674124405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1149511822342463130998413 431066933378423674124405)
              ·
                refine ⟨40412525004227219449163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 431066933378423674124405 40412525004227219449163)
                ·
                  rfl

theorem cell21_531246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_531246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531246 prefixEnd_531246 := by exact prefixLift 531246
  have htrace : WordTrace (prefixWord ++ tailWord_531246) baseStart_531246 baseEnd_531246 := by
    simpa [prefixWord, tailWord_531246, baseEnd_531246] using wordTrace_append hprefix tailTrace_531246
  have hstable : (prefixWord ++ tailWord_531246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531246).length < 2 ^ (prefixWord ++ tailWord_531246).sum := by decide
  have hdescent : baseEnd_531246 < baseStart_531246 := by decide
  rcases family_descends (prefixWord ++ tailWord_531246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531277 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 5]
def baseStart_531277 : Nat := 118140960795 + 531277 * 2 ^ 59
def prefixEnd_531277 : Nat := 4983230072969 + 3 ^ 40 * 531277 * 2
def baseEnd_531277 : Nat := 121244649635032493330759

theorem tailTrace_531277 : CollatzResearch.WordTrace tailWord_531277 prefixEnd_531277 121244649635032493330759 := by
  unfold tailWord_531277
  simp only [CollatzResearch.WordTrace]
  refine ⟨19377264096281638732936085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12918176064187759155290723 19377264096281638732936085)
  ·
    refine ⟨908309254513201815606379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19377264096281638732936085 908309254513201815606379)
    ·
      refine ⟨1362463881769802723409569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 908309254513201815606379 1362463881769802723409569)
      ·
        refine ⟨1021847911327352042557177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1362463881769802723409569 1021847911327352042557177)
        ·
          refine ⟨766385933495514031917883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1021847911327352042557177 766385933495514031917883)
          ·
            refine ⟨1149578900243271047876825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766385933495514031917883 1149578900243271047876825)
            ·
              refine ⟨862184175182453285907619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149578900243271047876825 862184175182453285907619)
              ·
                refine ⟨1293276262773679928861429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862184175182453285907619 1293276262773679928861429)
                ·
                  refine ⟨121244649635032493330759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1293276262773679928861429 121244649635032493330759)
                  ·
                    rfl

theorem cell21_531277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_531277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531277 prefixEnd_531277 := by exact prefixLift 531277
  have htrace : WordTrace (prefixWord ++ tailWord_531277) baseStart_531277 baseEnd_531277 := by
    simpa [prefixWord, tailWord_531277, baseEnd_531277] using wordTrace_append hprefix tailTrace_531277
  have hstable : (prefixWord ++ tailWord_531277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531277).length < 2 ^ (prefixWord ++ tailWord_531277).sum := by decide
  have hdescent : baseEnd_531277 < baseStart_531277 := by decide
  rcases family_descends (prefixWord ++ tailWord_531277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531333 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 6]
def baseStart_531333 : Nat := 118140960795 + 531333 * 2 ^ 59
def prefixEnd_531333 : Nat := 4983230072969 + 3 ^ 40 * 531333 * 2
def baseEnd_531333 : Nat := 121257429597988840397311

theorem tailTrace_531333 : CollatzResearch.WordTrace tailWord_531333 prefixEnd_531333 121257429597988840397311 := by
  unfold tailWord_531333
  simp only [CollatzResearch.WordTrace]
  refine ⟨19379306584078760296974653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12919537722719173531316435 19379306584078760296974653)
  ·
    refine ⟨7267239969029535111365495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19379306584078760296974653 7267239969029535111365495)
    ·
      refine ⟨10900859953544302667048243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7267239969029535111365495 10900859953544302667048243)
      ·
        refine ⟨16351289930316454000572365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10900859953544302667048243 16351289930316454000572365)
        ·
          refine ⟨6131733723868670250214637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16351289930316454000572365 6131733723868670250214637)
          ·
            refine ⟨2299400146450751343830489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6131733723868670250214637 2299400146450751343830489)
            ·
              refine ⟨1724550109838063507872867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2299400146450751343830489 1724550109838063507872867)
              ·
                refine ⟨2586825164757095261809301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724550109838063507872867 2586825164757095261809301)
                ·
                  refine ⟨121257429597988840397311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2586825164757095261809301 121257429597988840397311)
                  ·
                    rfl

theorem cell21_531333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_531333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531333 prefixEnd_531333 := by exact prefixLift 531333
  have htrace : WordTrace (prefixWord ++ tailWord_531333) baseStart_531333 baseEnd_531333 := by
    simpa [prefixWord, tailWord_531333, baseEnd_531333] using wordTrace_append hprefix tailTrace_531333
  have hstable : (prefixWord ++ tailWord_531333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531333).length < 2 ^ (prefixWord ++ tailWord_531333).sum := by decide
  have hdescent : baseEnd_531333 < baseStart_531333 := by decide
  rcases family_descends (prefixWord ++ tailWord_531333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531336 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 5]
def baseStart_531336 : Nat := 118140960795 + 531336 * 2 ^ 59
def prefixEnd_531336 : Nat := 4983230072969 + 3 ^ 40 * 531336 * 2
def baseEnd_531336 : Nat := 121258114238861501847305

theorem tailTrace_531336 : CollatzResearch.WordTrace tailWord_531336 prefixEnd_531336 121258114238861501847305 := by
  unfold tailWord_531336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9689708001533945904666931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12919610668711927872889241 9689708001533945904666931)
  ·
    refine ⟨14534562002300918857000397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9689708001533945904666931 14534562002300918857000397)
    ·
      refine ⟨5450460750862844571375149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14534562002300918857000397 5450460750862844571375149)
      ·
        refine ⟨2043922781573566714265681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5450460750862844571375149 2043922781573566714265681)
        ·
          refine ⟨1532942086180175035699261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2043922781573566714265681 1532942086180175035699261)
          ·
            refine ⟨574853282317565638387223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1532942086180175035699261 574853282317565638387223)
            ·
              refine ⟨862279923476348457580835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574853282317565638387223 862279923476348457580835)
              ·
                refine ⟨1293419885214522686371253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862279923476348457580835 1293419885214522686371253)
                ·
                  refine ⟨121258114238861501847305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1293419885214522686371253 121258114238861501847305)
                  ·
                    rfl

theorem cell21_531336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_531336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531336 prefixEnd_531336 := by exact prefixLift 531336
  have htrace : WordTrace (prefixWord ++ tailWord_531336) baseStart_531336 baseEnd_531336 := by
    simpa [prefixWord, tailWord_531336, baseEnd_531336] using wordTrace_append hprefix tailTrace_531336
  have hstable : (prefixWord ++ tailWord_531336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531336).length < 2 ^ (prefixWord ++ tailWord_531336).sum := by decide
  have hdescent : baseEnd_531336 < baseStart_531336 := by decide
  rcases family_descends (prefixWord ++ tailWord_531336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531395 : List Nat := [1, 1, 1, 3, 1, 1, 2, 8, 3]
def baseStart_531395 : Nat := 118140960795 + 531395 * 2 ^ 59
def prefixEnd_531395 : Nat := 4983230072969 + 3 ^ 40 * 531395 * 2
def baseEnd_531395 : Nat := 121271578842690510363851

theorem tailTrace_531395 : CollatzResearch.WordTrace tailWord_531395 prefixEnd_531395 121271578842690510363851 := by
  unfold tailWord_531395
  simp only [CollatzResearch.WordTrace]
  refine ⟨19381567909854144885731639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12921045273236096590487759 19381567909854144885731639)
  ·
    refine ⟨29072351864781217328597459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19381567909854144885731639 29072351864781217328597459)
    ·
      refine ⟨43608527797171825992896189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29072351864781217328597459 43608527797171825992896189)
      ·
        refine ⟨16353197923939434747336071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43608527797171825992896189 16353197923939434747336071)
        ·
          refine ⟨24529796885909152121004107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16353197923939434747336071 24529796885909152121004107)
          ·
            refine ⟨36794695328863728181506161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24529796885909152121004107 36794695328863728181506161)
            ·
              refine ⟨27596021496647796136129621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36794695328863728181506161 27596021496647796136129621)
              ·
                refine ⟨323390876913841360970269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 27596021496647796136129621 323390876913841360970269)
                ·
                  refine ⟨121271578842690510363851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323390876913841360970269 121271578842690510363851)
                  ·
                    rfl

theorem cell21_531395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 3].length) (baseStart_531395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531395 prefixEnd_531395 := by exact prefixLift 531395
  have htrace : WordTrace (prefixWord ++ tailWord_531395) baseStart_531395 baseEnd_531395 := by
    simpa [prefixWord, tailWord_531395, baseEnd_531395] using wordTrace_append hprefix tailTrace_531395
  have hstable : (prefixWord ++ tailWord_531395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531395).length < 2 ^ (prefixWord ++ tailWord_531395).sum := by decide
  have hdescent : baseEnd_531395 < baseStart_531395 := by decide
  rcases family_descends (prefixWord ++ tailWord_531395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531409 : List Nat := [1, 2, 2, 1, 2, 1, 3, 5, 4]
def baseStart_531409 : Nat := 118140960795 + 531409 * 2 ^ 59
def prefixEnd_531409 : Nat := 4983230072969 + 3 ^ 40 * 531409 * 2
def baseEnd_531409 : Nat := 121274773833429597130489

theorem tailTrace_531409 : CollatzResearch.WordTrace tailWord_531409 prefixEnd_531409 121274773833429597130489 := by
  unfold tailWord_531409
  simp only [CollatzResearch.WordTrace]
  refine ⟨19382078531803425276741281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12921385687868950184494187 19382078531803425276741281)
  ·
    refine ⟨14536558898852568957555961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19382078531803425276741281 14536558898852568957555961)
    ·
      refine ⟨10902419174139426718166971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14536558898852568957555961 10902419174139426718166971)
      ·
        refine ⟨16353628761209140077250457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10902419174139426718166971 16353628761209140077250457)
        ·
          refine ⟨12265221570906855057937843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16353628761209140077250457 12265221570906855057937843)
          ·
            refine ⟨18397832356360282586906765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12265221570906855057937843 18397832356360282586906765)
            ·
              refine ⟨6899187133635105970090037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18397832356360282586906765 6899187133635105970090037)
              ·
                refine ⟨646798793778291184695941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6899187133635105970090037 646798793778291184695941)
                ·
                  refine ⟨121274773833429597130489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646798793778291184695941 121274773833429597130489)
                  ·
                    rfl

theorem cell21_531409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_531409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531409 prefixEnd_531409 := by exact prefixLift 531409
  have htrace : WordTrace (prefixWord ++ tailWord_531409) baseStart_531409 baseEnd_531409 := by
    simpa [prefixWord, tailWord_531409, baseEnd_531409] using wordTrace_append hprefix tailTrace_531409
  have hstable : (prefixWord ++ tailWord_531409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531409).length < 2 ^ (prefixWord ++ tailWord_531409).sum := by decide
  have hdescent : baseEnd_531409 < baseStart_531409 := by decide
  rcases family_descends (prefixWord ++ tailWord_531409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531502 : List Nat := [4, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_531502 : Nat := 118140960795 + 531502 * 2 ^ 59
def prefixEnd_531502 : Nat := 4983230072969 + 3 ^ 40 * 531502 * 2
def baseEnd_531502 : Nat := 121295997700482102080299

theorem tailTrace_531502 : CollatzResearch.WordTrace tailWord_531502 prefixEnd_531502 121295997700482102080299 := by
  unfold tailWord_531502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423183815058312769984595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12923647013644334773251173 2423183815058312769984595)
  ·
    refine ⟨3634775722587469154976893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2423183815058312769984595 3634775722587469154976893)
    ·
      refine ⟨1363040895970300933116335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3634775722587469154976893 1363040895970300933116335)
      ·
        refine ⟨2044561343955451399674503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1363040895970300933116335 2044561343955451399674503)
        ·
          refine ⟨3066842015933177099511755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2044561343955451399674503 3066842015933177099511755)
          ·
            refine ⟨4600263023899765649267633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3066842015933177099511755 4600263023899765649267633)
            ·
              refine ⟨3450197267924824236950725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4600263023899765649267633 3450197267924824236950725)
              ·
                refine ⟨646911987735904544428261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3450197267924824236950725 646911987735904544428261)
                ·
                  refine ⟨121295997700482102080299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646911987735904544428261 121295997700482102080299)
                  ·
                    rfl

theorem cell21_531502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_531502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531502 prefixEnd_531502 := by exact prefixLift 531502
  have htrace : WordTrace (prefixWord ++ tailWord_531502) baseStart_531502 baseEnd_531502 := by
    simpa [prefixWord, tailWord_531502, baseEnd_531502] using wordTrace_append hprefix tailTrace_531502
  have hstable : (prefixWord ++ tailWord_531502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531502).length < 2 ^ (prefixWord ++ tailWord_531502).sum := by decide
  have hdescent : baseEnd_531502 < baseStart_531502 := by decide
  rcases family_descends (prefixWord ++ tailWord_531502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531516 : List Nat := [2, 2, 2, 2, 2, 3, 2, 6]
def baseStart_531516 : Nat := 118140960795 + 531516 * 2 ^ 59
def prefixEnd_531516 : Nat := 4983230072969 + 3 ^ 40 * 531516 * 2
def baseEnd_531516 : Nat := 40433064230407062948979

theorem tailTrace_531516 : CollatzResearch.WordTrace tailWord_531516 prefixEnd_531516 40433064230407062948979 := by
  unfold tailWord_531516
  simp only [CollatzResearch.WordTrace]
  refine ⟨9692990571207891275443201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12923987428277188367257601 9692990571207891275443201)
  ·
    refine ⟨7269742928405918456582401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9692990571207891275443201 7269742928405918456582401)
    ·
      refine ⟨5452307196304438842436801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7269742928405918456582401 5452307196304438842436801)
      ·
        refine ⟨4089230397228329131827601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5452307196304438842436801 4089230397228329131827601)
        ·
          refine ⟨3066922797921246848870701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4089230397228329131827601 3066922797921246848870701)
          ·
            refine ⟨1150096049220467568326513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3066922797921246848870701 1150096049220467568326513)
            ·
              refine ⟨862572036915350676244885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150096049220467568326513 862572036915350676244885)
              ·
                refine ⟨40433064230407062948979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 862572036915350676244885 40433064230407062948979)
                ·
                  rfl

theorem cell21_531516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_531516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531516 prefixEnd_531516 := by exact prefixLift 531516
  have htrace : WordTrace (prefixWord ++ tailWord_531516) baseStart_531516 baseEnd_531516 := by
    simpa [prefixWord, tailWord_531516, baseEnd_531516] using wordTrace_append hprefix tailTrace_531516
  have hstable : (prefixWord ++ tailWord_531516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531516).length < 2 ^ (prefixWord ++ tailWord_531516).sum := by decide
  have hdescent : baseEnd_531516 < baseStart_531516 := by decide
  rcases family_descends (prefixWord ++ tailWord_531516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531530 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_531530 : Nat := 118140960795 + 531530 * 2 ^ 59
def prefixEnd_531530 : Nat := 4983230072969 + 3 ^ 40 * 531530 * 2
def baseEnd_531530 : Nat := 121302387681960275613575

theorem tailTrace_531530 : CollatzResearch.WordTrace tailWord_531530 prefixEnd_531530 121302387681960275613575 := by
  unfold tailWord_531530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4846622941091265735474011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12924327842910041961264029 4846622941091265735474011)
  ·
    refine ⟨7269934411636898603211017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4846622941091265735474011 7269934411636898603211017)
    ·
      refine ⟨5452450808727673952408263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7269934411636898603211017 5452450808727673952408263)
      ·
        refine ⟨8178676213091510928612395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5452450808727673952408263 8178676213091510928612395)
        ·
          refine ⟨12268014319637266392918593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8178676213091510928612395 12268014319637266392918593)
          ·
            refine ⟨9201010739727949794688945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12268014319637266392918593 9201010739727949794688945)
            ·
              refine ⟨6900758054795962346016709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9201010739727949794688945 6900758054795962346016709)
              ·
                refine ⟨1293892135274242939878133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6900758054795962346016709 1293892135274242939878133)
                ·
                  refine ⟨121302387681960275613575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1293892135274242939878133 121302387681960275613575)
                  ·
                    rfl

theorem cell21_531530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_531530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531530 prefixEnd_531530 := by exact prefixLift 531530
  have htrace : WordTrace (prefixWord ++ tailWord_531530) baseStart_531530 baseEnd_531530 := by
    simpa [prefixWord, tailWord_531530, baseEnd_531530] using wordTrace_append hprefix tailTrace_531530
  have hstable : (prefixWord ++ tailWord_531530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531530).length < 2 ^ (prefixWord ++ tailWord_531530).sum := by decide
  have hdescent : baseEnd_531530 < baseStart_531530 := by decide
  rcases family_descends (prefixWord ++ tailWord_531530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531561 : List Nat := [1, 2, 1, 1, 1, 6, 1, 4, 4]
def baseStart_531561 : Nat := 118140960795 + 531561 * 2 ^ 59
def prefixEnd_531561 : Nat := 4983230072969 + 3 ^ 40 * 531561 * 2
def baseEnd_531561 : Nat := 121309462304311110596845

theorem tailTrace_531561 : CollatzResearch.WordTrace tailWord_531561 prefixEnd_531561 121309462304311110596845 := by
  unfold tailWord_531561
  simp only [CollatzResearch.WordTrace]
  refine ⟨19387622427252755236274537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12925081618168503490849691 19387622427252755236274537)
  ·
    refine ⟨14540716820439566427205903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19387622427252755236274537 14540716820439566427205903)
    ·
      refine ⟨21811075230659349640808855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14540716820439566427205903 21811075230659349640808855)
      ·
        refine ⟨32716612845989024461213283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21811075230659349640808855 32716612845989024461213283)
        ·
          refine ⟨49074919268983536691819925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32716612845989024461213283 49074919268983536691819925)
          ·
            refine ⟨2300386840733603282429059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49074919268983536691819925 2300386840733603282429059)
            ·
              refine ⟨3450580261100404923643589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2300386840733603282429059 3450580261100404923643589)
              ·
                refine ⟨646983798956325923183173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3450580261100404923643589 646983798956325923183173)
                ·
                  refine ⟨121309462304311110596845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646983798956325923183173 121309462304311110596845)
                  ·
                    rfl

theorem cell21_531561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_531561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531561 prefixEnd_531561 := by exact prefixLift 531561
  have htrace : WordTrace (prefixWord ++ tailWord_531561) baseStart_531561 baseEnd_531561 := by
    simpa [prefixWord, tailWord_531561, baseEnd_531561] using wordTrace_append hprefix tailTrace_531561
  have hstable : (prefixWord ++ tailWord_531561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531561).length < 2 ^ (prefixWord ++ tailWord_531561).sum := by decide
  have hdescent : baseEnd_531561 < baseStart_531561 := by decide
  rcases family_descends (prefixWord ++ tailWord_531561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531623 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 5]
def baseStart_531623 : Nat := 118140960795 + 531623 * 2 ^ 59
def prefixEnd_531623 : Nat := 4983230072969 + 3 ^ 40 * 531623 * 2
def baseEnd_531623 : Nat := 121323611549012780563385

theorem tailTrace_531623 : CollatzResearch.WordTrace tailWord_531623 prefixEnd_531623 121323611549012780563385 := by
  unfold tailWord_531623
  simp only [CollatzResearch.WordTrace]
  refine ⟨19389883753028139825031523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12926589168685426550021015 19389883753028139825031523)
  ·
    refine ⟨29084825629542209737547285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19389883753028139825031523 29084825629542209737547285)
    ·
      refine ⟨1363351201384791081447529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29084825629542209737547285 1363351201384791081447529)
      ·
        refine ⟨1022513401038593311085647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1363351201384791081447529 1022513401038593311085647)
        ·
          refine ⟨1533770101557889966628471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022513401038593311085647 1533770101557889966628471)
          ·
            refine ⟨2300655152336834949942707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533770101557889966628471 2300655152336834949942707)
            ·
              refine ⟨3450982728505252424914061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2300655152336834949942707 3450982728505252424914061)
              ·
                refine ⟨1294118523189469659342773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3450982728505252424914061 1294118523189469659342773)
                ·
                  refine ⟨121323611549012780563385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1294118523189469659342773 121323611549012780563385)
                  ·
                    rfl

theorem cell21_531623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 5].length) (baseStart_531623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531623 prefixEnd_531623 := by exact prefixLift 531623
  have htrace : WordTrace (prefixWord ++ tailWord_531623) baseStart_531623 baseEnd_531623 := by
    simpa [prefixWord, tailWord_531623, baseEnd_531623] using wordTrace_append hprefix tailTrace_531623
  have hstable : (prefixWord ++ tailWord_531623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531623).length < 2 ^ (prefixWord ++ tailWord_531623).sum := by decide
  have hdescent : baseEnd_531623 < baseStart_531623 := by decide
  rcases family_descends (prefixWord ++ tailWord_531623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531775 : List Nat := [1, 1, 2, 2, 4, 2, 1, 5, 3]
def baseStart_531775 : Nat := 118140960795 + 531775 * 2 ^ 59
def prefixEnd_531775 : Nat := 4983230072969 + 3 ^ 40 * 531775 * 2
def baseEnd_531775 : Nat := 121358300019894294029741

theorem tailTrace_531775 : CollatzResearch.WordTrace tailWord_531775 prefixEnd_531775 121358300019894294029741 := by
  unfold tailWord_531775
  simp only [CollatzResearch.WordTrace]
  refine ⟨19395427648477469784564779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12930285098984979856376519 19395427648477469784564779)
  ·
    refine ⟨29093141472716204676847169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19395427648477469784564779 29093141472716204676847169)
    ·
      refine ⟨21819856104537153507635377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29093141472716204676847169 21819856104537153507635377)
      ·
        refine ⟨16364892078402865130726533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21819856104537153507635377 16364892078402865130726533)
        ·
          refine ⟨3068417264700537212011225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16364892078402865130726533 3068417264700537212011225)
          ·
            refine ⟨2301312948525402909008419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3068417264700537212011225 2301312948525402909008419)
            ·
              refine ⟨3451969422788104363512629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301312948525402909008419 3451969422788104363512629)
              ·
                refine ⟨323622133386384784079309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3451969422788104363512629 323622133386384784079309)
                ·
                  refine ⟨121358300019894294029741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323622133386384784079309 121358300019894294029741)
                  ·
                    rfl

theorem cell21_531775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 3].length) (baseStart_531775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531775 prefixEnd_531775 := by exact prefixLift 531775
  have htrace : WordTrace (prefixWord ++ tailWord_531775) baseStart_531775 baseEnd_531775 := by
    simpa [prefixWord, tailWord_531775, baseEnd_531775] using wordTrace_append hprefix tailTrace_531775
  have hstable : (prefixWord ++ tailWord_531775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531775).length < 2 ^ (prefixWord ++ tailWord_531775).sum := by decide
  have hdescent : baseEnd_531775 < baseStart_531775 := by decide
  rcases family_descends (prefixWord ++ tailWord_531775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531798 : List Nat := [5, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_531798 : Nat := 118140960795 + 531798 * 2 ^ 59
def prefixEnd_531798 : Nat := 4983230072969 + 3 ^ 40 * 531798 * 2
def baseEnd_531798 : Nat := 121363548933251365146361

theorem tailTrace_531798 : CollatzResearch.WordTrace tailWord_531798 prefixEnd_531798 121363548933251365146361 := by
  unfold tailWord_531798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1212266657962134044540753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12930844351596096475101365 1212266657962134044540753)
  ·
    refine ⟨909199993471600533405565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1212266657962134044540753 909199993471600533405565)
    ·
      refine ⟨340949997551850200027087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 909199993471600533405565 340949997551850200027087)
      ·
        refine ⟨511424996327775300040631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340949997551850200027087 511424996327775300040631)
        ·
          refine ⟨767137494491662950060947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511424996327775300040631 767137494491662950060947)
          ·
            refine ⟨1150706241737494425091421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767137494491662950060947 1150706241737494425091421)
            ·
              refine ⟨431514840651560409409283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1150706241737494425091421 431514840651560409409283)
              ·
                refine ⟨647272260977340614113925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431514840651560409409283 647272260977340614113925)
                ·
                  refine ⟨121363548933251365146361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647272260977340614113925 121363548933251365146361)
                  ·
                    rfl

theorem cell21_531798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_531798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531798 prefixEnd_531798 := by exact prefixLift 531798
  have htrace : WordTrace (prefixWord ++ tailWord_531798) baseStart_531798 baseEnd_531798 := by
    simpa [prefixWord, tailWord_531798, baseEnd_531798] using wordTrace_append hprefix tailTrace_531798
  have hstable : (prefixWord ++ tailWord_531798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531798).length < 2 ^ (prefixWord ++ tailWord_531798).sum := by decide
  have hdescent : baseEnd_531798 < baseStart_531798 := by decide
  rcases family_descends (prefixWord ++ tailWord_531798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531817 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 7]
def baseStart_531817 : Nat := 118140960795 + 531817 * 2 ^ 59
def prefixEnd_531817 : Nat := 4983230072969 + 3 ^ 40 * 531817 * 2
def baseEnd_531817 : Nat := 121367884992111554329655

theorem tailTrace_531817 : CollatzResearch.WordTrace tailWord_531817 prefixEnd_531817 121367884992111554329655 := by
  unfold tailWord_531817
  simp only [CollatzResearch.WordTrace]
  refine ⟨19396959514325310957593705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12931306342883540638395803 19396959514325310957593705)
  ·
    refine ⟨14547719635743983218195279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19396959514325310957593705 14547719635743983218195279)
    ·
      refine ⟨21821579453615974827292919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14547719635743983218195279 21821579453615974827292919)
      ·
        refine ⟨32732369180423962240939379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21821579453615974827292919 32732369180423962240939379)
        ·
          refine ⟨49098553770635943361409069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32732369180423962240939379 49098553770635943361409069)
          ·
            refine ⟨18411957663988478760528401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49098553770635943361409069 18411957663988478760528401)
            ·
              refine ⟨13808968247991359070396301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18411957663988478760528401 13808968247991359070396301)
              ·
                refine ⟨5178363092996759651398613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13808968247991359070396301 5178363092996759651398613)
                ·
                  refine ⟨121367884992111554329655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5178363092996759651398613 121367884992111554329655)
                  ·
                    rfl

theorem cell21_531817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_531817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531817 prefixEnd_531817 := by exact prefixLift 531817
  have htrace : WordTrace (prefixWord ++ tailWord_531817) baseStart_531817 baseEnd_531817 := by
    simpa [prefixWord, tailWord_531817, baseEnd_531817] using wordTrace_append hprefix tailTrace_531817
  have hstable : (prefixWord ++ tailWord_531817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531817).length < 2 ^ (prefixWord ++ tailWord_531817).sum := by decide
  have hdescent : baseEnd_531817 < baseStart_531817 := by decide
  rcases family_descends (prefixWord ++ tailWord_531817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531820 : List Nat := [2, 2, 1, 1, 5, 1, 4, 5]
def baseStart_531820 : Nat := 118140960795 + 531820 * 2 ^ 59
def prefixEnd_531820 : Nat := 4983230072969 + 3 ^ 40 * 531820 * 2
def baseEnd_531820 : Nat := 40456189877661405259883

theorem tailTrace_531820 : CollatzResearch.WordTrace tailWord_531820 prefixEnd_531820 40456189877661405259883 := by
  unfold tailWord_531820
  simp only [CollatzResearch.WordTrace]
  refine ⟨9698534466657221234976457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12931379288876294979968609 9698534466657221234976457)
  ·
    refine ⟨7273900849992915926232343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9698534466657221234976457 7273900849992915926232343)
    ·
      refine ⟨10910851274989373889348515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7273900849992915926232343 10910851274989373889348515)
      ·
        refine ⟨16366276912484060834022773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10910851274989373889348515 16366276912484060834022773)
        ·
          refine ⟨1534338460545380703189635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16366276912484060834022773 1534338460545380703189635)
          ·
            refine ⟨2301507690818071054784453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534338460545380703189635 2301507690818071054784453)
            ·
              refine ⟨431532692028388322772085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2301507690818071054784453 431532692028388322772085)
              ·
                refine ⟨40456189877661405259883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 431532692028388322772085 40456189877661405259883)
                ·
                  rfl

theorem cell21_531820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_531820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531820 prefixEnd_531820 := by exact prefixLift 531820
  have htrace : WordTrace (prefixWord ++ tailWord_531820) baseStart_531820 baseEnd_531820 := by
    simpa [prefixWord, tailWord_531820, baseEnd_531820] using wordTrace_append hprefix tailTrace_531820
  have hstable : (prefixWord ++ tailWord_531820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531820).length < 2 ^ (prefixWord ++ tailWord_531820).sum := by decide
  have hdescent : baseEnd_531820 < baseStart_531820 := by decide
  rcases family_descends (prefixWord ++ tailWord_531820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531865 : List Nat := [1, 2, 1, 2, 1, 6, 1, 3, 4]
def baseStart_531865 : Nat := 118140960795 + 531865 * 2 ^ 59
def prefixEnd_531865 : Nat := 4983230072969 + 3 ^ 40 * 531865 * 2
def baseEnd_531865 : Nat := 121378839246074137529557

theorem tailTrace_531865 : CollatzResearch.WordTrace tailWord_531865 prefixEnd_531865 121378839246074137529557 := by
  unfold tailWord_531865
  simp only [CollatzResearch.WordTrace]
  refine ⟨19398710218151415155341049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12932473478767610103560699 19398710218151415155341049)
  ·
    refine ⟨14549032663613561366505787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19398710218151415155341049 14549032663613561366505787)
    ·
      refine ⟨21823548995420342049758681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14549032663613561366505787 21823548995420342049758681)
      ·
        refine ⟨16367661746565256537319011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21823548995420342049758681 16367661746565256537319011)
        ·
          refine ⟨24551492619847884805978517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16367661746565256537319011 24551492619847884805978517)
          ·
            refine ⟨1150851216555369600280243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24551492619847884805978517 1150851216555369600280243)
            ·
              refine ⟨1726276824833054400420365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1150851216555369600280243 1726276824833054400420365)
              ·
                refine ⟨647353809312395400157637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1726276824833054400420365 647353809312395400157637)
                ·
                  refine ⟨121378839246074137529557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647353809312395400157637 121378839246074137529557)
                  ·
                    rfl

theorem cell21_531865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_531865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531865 prefixEnd_531865 := by exact prefixLift 531865
  have htrace : WordTrace (prefixWord ++ tailWord_531865) baseStart_531865 baseEnd_531865 := by
    simpa [prefixWord, tailWord_531865, baseEnd_531865] using wordTrace_append hprefix tailTrace_531865
  have hstable : (prefixWord ++ tailWord_531865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531865).length < 2 ^ (prefixWord ++ tailWord_531865).sum := by decide
  have hdescent : baseEnd_531865 < baseStart_531865 := by decide
  rcases family_descends (prefixWord ++ tailWord_531865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531879 : List Nat := [1, 1, 6, 1, 1, 1, 1, 9]
def baseStart_531879 : Nat := 118140960795 + 531879 * 2 ^ 59
def prefixEnd_531879 : Nat := 4983230072969 + 3 ^ 40 * 531879 * 2
def baseEnd_531879 : Nat := 40460678078937741432065

theorem tailTrace_531879 : CollatzResearch.WordTrace tailWord_531879 prefixEnd_531879 40460678078937741432065 := by
  unfold tailWord_531879
  simp only [CollatzResearch.WordTrace]
  refine ⟨19399220840100695546350691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12932813893400463697567127 19399220840100695546350691)
  ·
    refine ⟨29098831260151043319526037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19399220840100695546350691 29098831260151043319526037)
    ·
      refine ⟨1364007715319580155602783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29098831260151043319526037 1364007715319580155602783)
      ·
        refine ⟨2046011572979370233404175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364007715319580155602783 2046011572979370233404175)
        ·
          refine ⟨3069017359469055350106263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2046011572979370233404175 3069017359469055350106263)
          ·
            refine ⟨4603526039203583025159395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069017359469055350106263 4603526039203583025159395)
            ·
              refine ⟨6905289058805374537739093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4603526039203583025159395 6905289058805374537739093)
              ·
                refine ⟨40460678078937741432065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6905289058805374537739093 40460678078937741432065)
                ·
                  rfl

theorem cell21_531879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 9].length) (baseStart_531879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531879 prefixEnd_531879 := by exact prefixLift 531879
  have htrace : WordTrace (prefixWord ++ tailWord_531879) baseStart_531879 baseEnd_531879 := by
    simpa [prefixWord, tailWord_531879, baseEnd_531879] using wordTrace_append hprefix tailTrace_531879
  have hstable : (prefixWord ++ tailWord_531879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531879).length < 2 ^ (prefixWord ++ tailWord_531879).sum := by decide
  have hdescent : baseEnd_531879 < baseStart_531879 := by decide
  rcases family_descends (prefixWord ++ tailWord_531879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531958 : List Nat := [5, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_531958 : Nat := 118140960795 + 531958 * 2 ^ 59
def prefixEnd_531958 : Nat := 4983230072969 + 3 ^ 40 * 531958 * 2
def baseEnd_531958 : Nat := 121400063113126642479367

theorem tailTrace_531958 : CollatzResearch.WordTrace tailWord_531958 prefixEnd_531958 121400063113126642479367 := by
  unfold tailWord_531958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1212631387925905752404783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12934734804542994692317685 1212631387925905752404783)
  ·
    refine ⟨1818947081888858628607175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1212631387925905752404783 1818947081888858628607175)
    ·
      refine ⟨2728420622833287942910763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1818947081888858628607175 2728420622833287942910763)
      ·
        refine ⟨4092630934249931914366145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2728420622833287942910763 4092630934249931914366145)
        ·
          refine ⟨3069473200687448935774609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4092630934249931914366145 3069473200687448935774609)
          ·
            refine ⟨2302104900515586701830957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3069473200687448935774609 2302104900515586701830957)
            ·
              refine ⟨863289337693345013186609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2302104900515586701830957 863289337693345013186609)
              ·
                refine ⟨647467003270008759889957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863289337693345013186609 647467003270008759889957)
                ·
                  refine ⟨121400063113126642479367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647467003270008759889957 121400063113126642479367)
                  ·
                    rfl

theorem cell21_531958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_531958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_531958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_531958 prefixEnd_531958 := by exact prefixLift 531958
  have htrace : WordTrace (prefixWord ++ tailWord_531958) baseStart_531958 baseEnd_531958 := by
    simpa [prefixWord, tailWord_531958, baseEnd_531958] using wordTrace_append hprefix tailTrace_531958
  have hstable : (prefixWord ++ tailWord_531958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531958).length < 2 ^ (prefixWord ++ tailWord_531958).sum := by decide
  have hdescent : baseEnd_531958 < baseStart_531958 := by decide
  rcases family_descends (prefixWord ++ tailWord_531958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532031 : List Nat := [1, 1, 2, 2, 3, 4, 2, 6]
def baseStart_532031 : Nat := 118140960795 + 532031 * 2 ^ 59
def prefixEnd_532031 : Nat := 4983230072969 + 3 ^ 40 * 532031 * 2
def baseEnd_532031 : Nat := 40472240902564912587517

theorem tailTrace_532031 : CollatzResearch.WordTrace tailWord_532031 prefixEnd_532031 40472240902564912587517 := by
  unfold tailWord_532031
  simp only [CollatzResearch.WordTrace]
  refine ⟨19404764735550025505883947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12936509823700017003922631 19404764735550025505883947)
  ·
    refine ⟨29107147103325038258825921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19404764735550025505883947 29107147103325038258825921)
    ·
      refine ⟨21830360327493778694119441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29107147103325038258825921 21830360327493778694119441)
      ·
        refine ⟨16372770245620334020589581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21830360327493778694119441 16372770245620334020589581)
        ·
          refine ⟨6139788842107625257721093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16372770245620334020589581 6139788842107625257721093)
          ·
            refine ⟨1151210407895179735822705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6139788842107625257721093 1151210407895179735822705)
            ·
              refine ⟨863407805921384801867029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151210407895179735822705 863407805921384801867029)
              ·
                refine ⟨40472240902564912587517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 863407805921384801867029 40472240902564912587517)
                ·
                  rfl

theorem cell21_532031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 6].length) (baseStart_532031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532031 prefixEnd_532031 := by exact prefixLift 532031
  have htrace : WordTrace (prefixWord ++ tailWord_532031) baseStart_532031 baseEnd_532031 := by
    simpa [prefixWord, tailWord_532031, baseEnd_532031] using wordTrace_append hprefix tailTrace_532031
  have hstable : (prefixWord ++ tailWord_532031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532031).length < 2 ^ (prefixWord ++ tailWord_532031).sum := by decide
  have hdescent : baseEnd_532031 < baseStart_532031 := by decide
  rcases family_descends (prefixWord ++ tailWord_532031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532090 : List Nat := [3, 1, 1, 1, 1, 1, 1, 12]
def baseStart_532090 : Nat := 118140960795 + 532090 * 2 ^ 59
def prefixEnd_532090 : Nat := 4983230072969 + 3 ^ 40 * 532090 * 2
def baseEnd_532090 : Nat := 40476729103841248759699

theorem tailTrace_532090 : CollatzResearch.WordTrace tailWord_532090 prefixEnd_532090 40476729103841248759699 := by
  unfold tailWord_532090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4851729160584069645570431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12937944428224185721521149 4851729160584069645570431)
  ·
    refine ⟨7277593740876104468355647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4851729160584069645570431 7277593740876104468355647)
    ·
      refine ⟨10916390611314156702533471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7277593740876104468355647 10916390611314156702533471)
      ·
        refine ⟨16374585916971235053800207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10916390611314156702533471 16374585916971235053800207)
        ·
          refine ⟨24561878875456852580700311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16374585916971235053800207 24561878875456852580700311)
          ·
            refine ⟨36842818313185278871050467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24561878875456852580700311 36842818313185278871050467)
            ·
              refine ⟨55264227469777918306575701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36842818313185278871050467 55264227469777918306575701)
              ·
                refine ⟨40476729103841248759699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 55264227469777918306575701 40476729103841248759699)
                ·
                  rfl

theorem cell21_532090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_532090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532090 prefixEnd_532090 := by exact prefixLift 532090
  have htrace : WordTrace (prefixWord ++ tailWord_532090) baseStart_532090 baseEnd_532090 := by
    simpa [prefixWord, tailWord_532090, baseEnd_532090] using wordTrace_append hprefix tailTrace_532090
  have hstable : (prefixWord ++ tailWord_532090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532090).length < 2 ^ (prefixWord ++ tailWord_532090).sum := by decide
  have hdescent : baseEnd_532090 < baseStart_532090 := by decide
  rcases family_descends (prefixWord ++ tailWord_532090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532093 : List Nat := [1, 4, 1, 1, 4, 1, 2, 3, 4]
def baseStart_532093 : Nat := 118140960795 + 532093 * 2 ^ 59
def prefixEnd_532093 : Nat := 4983230072969 + 3 ^ 40 * 532093 * 2
def baseEnd_532093 : Nat := 121430871952396407729091

theorem tailTrace_532093 : CollatzResearch.WordTrace tailWord_532093 prefixEnd_532093 121430871952396407729091 := by
  unfold tailWord_532093
  simp only [CollatzResearch.WordTrace]
  refine ⟨19407026061325410094640933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12938017374216940063093955 19407026061325410094640933)
  ·
    refine ⟨3638817386498514392745175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19407026061325410094640933 3638817386498514392745175)
    ·
      refine ⟨5458226079747771589117763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3638817386498514392745175 5458226079747771589117763)
      ·
        refine ⟨8187339119621657383676645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5458226079747771589117763 8187339119621657383676645)
        ·
          refine ⟨1535126084929060759439371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8187339119621657383676645 1535126084929060759439371)
          ·
            refine ⟨2302689127393591139159057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535126084929060759439371 2302689127393591139159057)
            ·
              refine ⟨1727016845545193354369293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2302689127393591139159057 1727016845545193354369293)
              ·
                refine ⟨647631317079447507888485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1727016845545193354369293 647631317079447507888485)
                ·
                  refine ⟨121430871952396407729091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647631317079447507888485 121430871952396407729091)
                  ·
                    rfl

theorem cell21_532093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_532093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532093 prefixEnd_532093 := by exact prefixLift 532093
  have htrace : WordTrace (prefixWord ++ tailWord_532093) baseStart_532093 baseEnd_532093 := by
    simpa [prefixWord, tailWord_532093, baseEnd_532093] using wordTrace_append hprefix tailTrace_532093
  have hstable : (prefixWord ++ tailWord_532093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532093).length < 2 ^ (prefixWord ++ tailWord_532093).sum := by decide
  have hdescent : baseEnd_532093 < baseStart_532093 := by decide
  rcases family_descends (prefixWord ++ tailWord_532093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532107 : List Nat := [1, 1, 1, 1, 4, 1, 7, 5]
def baseStart_532107 : Nat := 118140960795 + 532107 * 2 ^ 59
def prefixEnd_532107 : Nat := 4983230072969 + 3 ^ 40 * 532107 * 2
def baseEnd_532107 : Nat := 40478022314378498165243

theorem tailTrace_532107 : CollatzResearch.WordTrace tailWord_532107 prefixEnd_532107 40478022314378498165243 := by
  unfold tailWord_532107
  simp only [CollatzResearch.WordTrace]
  refine ⟨19407536683274690485650575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12938357788849793657100383 19407536683274690485650575)
  ·
    refine ⟨29111305024912035728475863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19407536683274690485650575 29111305024912035728475863)
    ·
      refine ⟨43666957537368053592713795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29111305024912035728475863 43666957537368053592713795)
      ·
        refine ⟨65500436306052080389070693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43666957537368053592713795 65500436306052080389070693)
        ·
          refine ⟨12281331807384765072950755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65500436306052080389070693 12281331807384765072950755)
          ·
            refine ⟨18421997711077147609426133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12281331807384765072950755 18421997711077147609426133)
            ·
              refine ⟨431765571353370647095925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18421997711077147609426133 431765571353370647095925)
              ·
                refine ⟨40478022314378498165243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 431765571353370647095925 40478022314378498165243)
                ·
                  rfl

theorem cell21_532107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 5].length) (baseStart_532107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532107 prefixEnd_532107 := by exact prefixLift 532107
  have htrace : WordTrace (prefixWord ++ tailWord_532107) baseStart_532107 baseEnd_532107 := by
    simpa [prefixWord, tailWord_532107, baseEnd_532107] using wordTrace_append hprefix tailTrace_532107
  have hstable : (prefixWord ++ tailWord_532107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532107).length < 2 ^ (prefixWord ++ tailWord_532107).sum := by decide
  have hdescent : baseEnd_532107 < baseStart_532107 := by decide
  rcases family_descends (prefixWord ++ tailWord_532107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532127 : List Nat := [1, 1, 2, 7, 1, 2, 1, 2, 4]
def baseStart_532127 : Nat := 118140960795 + 532127 * 2 ^ 59
def prefixEnd_532127 : Nat := 4983230072969 + 3 ^ 40 * 532127 * 2
def baseEnd_532127 : Nat := 121438631215619904162355

theorem tailTrace_532127 : CollatzResearch.WordTrace tailWord_532127 prefixEnd_532127 121438631215619904162355 := by
  unfold tailWord_532127
  simp only [CollatzResearch.WordTrace]
  refine ⟨19408266143202233901378635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12938844095468155934252423 19408266143202233901378635)
  ·
    refine ⟨29112399214803350852067953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19408266143202233901378635 29112399214803350852067953)
    ·
      refine ⟨21834299411102513139050965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29112399214803350852067953 21834299411102513139050965)
      ·
        refine ⟨511741392447715151696507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 21834299411102513139050965 511741392447715151696507)
        ·
          refine ⟨767612088671572727544761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511741392447715151696507 767612088671572727544761)
          ·
            refine ⟨575709066503679545658571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767612088671572727544761 575709066503679545658571)
            ·
              refine ⟨863563599755519318487857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575709066503679545658571 863563599755519318487857)
              ·
                refine ⟨647672699816639488865893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863563599755519318487857 647672699816639488865893)
                ·
                  refine ⟨121438631215619904162355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647672699816639488865893 121438631215619904162355)
                  ·
                    rfl

theorem cell21_532127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 4].length) (baseStart_532127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532127 prefixEnd_532127 := by exact prefixLift 532127
  have htrace : WordTrace (prefixWord ++ tailWord_532127) baseStart_532127 baseEnd_532127 := by
    simpa [prefixWord, tailWord_532127, baseEnd_532127] using wordTrace_append hprefix tailTrace_532127
  have hstable : (prefixWord ++ tailWord_532127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532127).length < 2 ^ (prefixWord ++ tailWord_532127).sum := by decide
  have hdescent : baseEnd_532127 < baseStart_532127 := by decide
  rcases family_descends (prefixWord ++ tailWord_532127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532152 : List Nat := [2, 1, 2, 1, 2, 1, 1, 7, 4]
def baseStart_532152 : Nat := 118140960795 + 532152 * 2 ^ 59
def prefixEnd_532152 : Nat := 4983230072969 + 3 ^ 40 * 532152 * 2
def baseEnd_532152 : Nat := 121444336556225416245637

theorem tailTrace_532152 : CollatzResearch.WordTrace tailWord_532152 prefixEnd_532152 121444336556225416245637 := by
  unfold tailWord_532152
  simp only [CollatzResearch.WordTrace]
  refine ⟨9704588984055831585519355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12939451978741108780692473 9704588984055831585519355)
  ·
    refine ⟨14556883476083747378279033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9704588984055831585519355 14556883476083747378279033)
    ·
      refine ⟨10917662607062810533709275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14556883476083747378279033 10917662607062810533709275)
      ·
        refine ⟨16376493910594215800563913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10917662607062810533709275 16376493910594215800563913)
        ·
          refine ⟨12282370432945661850422935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16376493910594215800563913 12282370432945661850422935)
          ·
            refine ⟨18423555649418492775634403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12282370432945661850422935 18423555649418492775634403)
            ·
              refine ⟨27635333474127739163451605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18423555649418492775634403 27635333474127739163451605)
              ·
                refine ⟨647703128299868886643397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27635333474127739163451605 647703128299868886643397)
                ·
                  refine ⟨121444336556225416245637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647703128299868886643397 121444336556225416245637)
                  ·
                    rfl

theorem cell21_532152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_532152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532152 prefixEnd_532152 := by exact prefixLift 532152
  have htrace : WordTrace (prefixWord ++ tailWord_532152) baseStart_532152 baseEnd_532152 := by
    simpa [prefixWord, tailWord_532152, baseEnd_532152] using wordTrace_append hprefix tailTrace_532152
  have hstable : (prefixWord ++ tailWord_532152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532152).length < 2 ^ (prefixWord ++ tailWord_532152).sum := by decide
  have hdescent : baseEnd_532152 < baseStart_532152 := by decide
  rcases family_descends (prefixWord ++ tailWord_532152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532189 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 5]
def baseStart_532189 : Nat := 118140960795 + 532189 * 2 ^ 59
def prefixEnd_532189 : Nat := 4983230072969 + 3 ^ 40 * 532189 * 2
def baseEnd_532189 : Nat := 121452780460321574128895

theorem tailTrace_532189 : CollatzResearch.WordTrace tailWord_532189 prefixEnd_532189 121452780460321574128895 := by
  unfold tailWord_532189
  simp only [CollatzResearch.WordTrace]
  refine ⟨19410527468977618490135621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12940351645985078993423747 19410527468977618490135621)
  ·
    refine ⟨3639473900433303466900429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19410527468977618490135621 3639473900433303466900429)
    ·
      refine ⟨1364802712662488800087661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3639473900433303466900429 1364802712662488800087661)
      ·
        refine ⟨511801017248433300032873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1364802712662488800087661 511801017248433300032873)
        ·
          refine ⟨383850762936324975024655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511801017248433300032873 383850762936324975024655)
          ·
            refine ⟨575776144404487462536983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383850762936324975024655 575776144404487462536983)
            ·
              refine ⟨863664216606731193805475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575776144404487462536983 863664216606731193805475)
              ·
                refine ⟨1295496324910096790708213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863664216606731193805475 1295496324910096790708213)
                ·
                  refine ⟨121452780460321574128895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1295496324910096790708213 121452780460321574128895)
                  ·
                    rfl

theorem cell21_532189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_532189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532189 prefixEnd_532189 := by exact prefixLift 532189
  have htrace : WordTrace (prefixWord ++ tailWord_532189) baseStart_532189 baseEnd_532189 := by
    simpa [prefixWord, tailWord_532189, baseEnd_532189] using wordTrace_append hprefix tailTrace_532189
  have hstable : (prefixWord ++ tailWord_532189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532189).length < 2 ^ (prefixWord ++ tailWord_532189).sum := by decide
  have hdescent : baseEnd_532189 < baseStart_532189 := by decide
  rcases family_descends (prefixWord ++ tailWord_532189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532237 : List Nat := [1, 7, 2, 1, 1, 1, 2, 2, 4]
def baseStart_532237 : Nat := 118140960795 + 532237 * 2 ^ 59
def prefixEnd_532237 : Nat := 4983230072969 + 3 ^ 40 * 532237 * 2
def baseEnd_532237 : Nat := 121463734714284157328797

theorem tailTrace_532237 : CollatzResearch.WordTrace tailWord_532237 prefixEnd_532237 121463734714284157328797 := by
  unfold tailWord_532237
  simp only [CollatzResearch.WordTrace]
  refine ⟨19412278172803722687882965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12941518781869148458588643 19412278172803722687882965)
  ·
    refine ⟨454975269675087250497257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 19412278172803722687882965 454975269675087250497257)
    ·
      refine ⟨341231452256315437872943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454975269675087250497257 341231452256315437872943)
      ·
        refine ⟨511847178384473156809415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341231452256315437872943 511847178384473156809415)
        ·
          refine ⟨767770767576709735214123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511847178384473156809415 767770767576709735214123)
          ·
            refine ⟨1151656151365064602821185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767770767576709735214123 1151656151365064602821185)
            ·
              refine ⟨863742113523798452115889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151656151365064602821185 863742113523798452115889)
              ·
                refine ⟨647806585142848839086917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863742113523798452115889 647806585142848839086917)
                ·
                  refine ⟨121463734714284157328797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647806585142848839086917 121463734714284157328797)
                  ·
                    rfl

theorem cell21_532237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_532237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532237 prefixEnd_532237 := by exact prefixLift 532237
  have htrace : WordTrace (prefixWord ++ tailWord_532237) baseStart_532237 baseEnd_532237 := by
    simpa [prefixWord, tailWord_532237, baseEnd_532237] using wordTrace_append hprefix tailTrace_532237
  have hstable : (prefixWord ++ tailWord_532237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532237).length < 2 ^ (prefixWord ++ tailWord_532237).sum := by decide
  have hdescent : baseEnd_532237 < baseStart_532237 := by decide
  rcases family_descends (prefixWord ++ tailWord_532237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532245 : List Nat := [1, 3, 2, 1, 2, 4, 2, 2, 4]
def baseStart_532245 : Nat := 118140960795 + 532245 * 2 ^ 59
def prefixEnd_532245 : Nat := 4983230072969 + 3 ^ 40 * 532245 * 2
def baseEnd_532245 : Nat := 121465560423277921195447

theorem tailTrace_532245 : CollatzResearch.WordTrace tailWord_532245 prefixEnd_532245 121465560423277921195447 := by
  unfold tailWord_532245
  simp only [CollatzResearch.WordTrace]
  refine ⟨19412569956774740054174189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12941713304516493369449459 19412569956774740054174189)
  ·
    refine ⟨7279713733790527520315321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19412569956774740054174189 7279713733790527520315321)
    ·
      refine ⟨5459785300342895640236491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7279713733790527520315321 5459785300342895640236491)
      ·
        refine ⟨8189677950514343460354737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5459785300342895640236491 8189677950514343460354737)
        ·
          refine ⟨6142258462885757595266053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8189677950514343460354737 6142258462885757595266053)
          ·
            refine ⟨1151673461791079549112385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6142258462885757595266053 1151673461791079549112385)
            ·
              refine ⟨863755096343309661834289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151673461791079549112385 863755096343309661834289)
              ·
                refine ⟨647816322257482246375717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863755096343309661834289 647816322257482246375717)
                ·
                  refine ⟨121465560423277921195447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647816322257482246375717 121465560423277921195447)
                  ·
                    rfl

theorem cell21_532245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_532245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532245 prefixEnd_532245 := by exact prefixLift 532245
  have htrace : WordTrace (prefixWord ++ tailWord_532245) baseStart_532245 baseEnd_532245 := by
    simpa [prefixWord, tailWord_532245, baseEnd_532245] using wordTrace_append hprefix tailTrace_532245
  have hstable : (prefixWord ++ tailWord_532245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532245).length < 2 ^ (prefixWord ++ tailWord_532245).sum := by decide
  have hdescent : baseEnd_532245 < baseStart_532245 := by decide
  rcases family_descends (prefixWord ++ tailWord_532245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532273 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 7]
def baseStart_532273 : Nat := 118140960795 + 532273 * 2 ^ 59
def prefixEnd_532273 : Nat := 4983230072969 + 3 ^ 40 * 532273 * 2
def baseEnd_532273 : Nat := 121471950404756094728723

theorem tailTrace_532273 : CollatzResearch.WordTrace tailWord_532273 prefixEnd_532273 121471950404756094728723 := by
  unfold tailWord_532273
  simp only [CollatzResearch.WordTrace]
  refine ⟨19413591200673300836193473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12942394133782200557462315 19413591200673300836193473)
  ·
    refine ⟨14560193400504975627145105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19413591200673300836193473 14560193400504975627145105)
    ·
      refine ⟨10920145050378731720358829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14560193400504975627145105 10920145050378731720358829)
      ·
        refine ⟨4095054393892024395134561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10920145050378731720358829 4095054393892024395134561)
        ·
          refine ⟨3071290795419018296350921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4095054393892024395134561 3071290795419018296350921)
          ·
            refine ⟨2303468096564263722263191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3071290795419018296350921 2303468096564263722263191)
            ·
              refine ⟨3455202144846395583394787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303468096564263722263191 3455202144846395583394787)
              ·
                refine ⟨5182803217269593375092181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3455202144846395583394787 5182803217269593375092181)
                ·
                  refine ⟨121471950404756094728723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5182803217269593375092181 121471950404756094728723)
                  ·
                    rfl

theorem cell21_532273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_532273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532273 prefixEnd_532273 := by exact prefixLift 532273
  have htrace : WordTrace (prefixWord ++ tailWord_532273) baseStart_532273 baseEnd_532273 := by
    simpa [prefixWord, tailWord_532273, baseEnd_532273] using wordTrace_append hprefix tailTrace_532273
  have hstable : (prefixWord ++ tailWord_532273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532273).length < 2 ^ (prefixWord ++ tailWord_532273).sum := by decide
  have hdescent : baseEnd_532273 < baseStart_532273 := by decide
  rcases family_descends (prefixWord ++ tailWord_532273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532321 : List Nat := [1, 2, 3, 1, 1, 1, 7, 1, 4]
def baseStart_532321 : Nat := 118140960795 + 532321 * 2 ^ 59
def prefixEnd_532321 : Nat := 4983230072969 + 3 ^ 40 * 532321 * 2
def baseEnd_532321 : Nat := 121482904658718677928625

theorem tailTrace_532321 : CollatzResearch.WordTrace tailWord_532321 prefixEnd_532321 121482904658718677928625 := by
  unfold tailWord_532321
  simp only [CollatzResearch.WordTrace]
  refine ⟨19415341904499405033940817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12943561269666270022627211 19415341904499405033940817)
  ·
    refine ⟨14561506428374553775455613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19415341904499405033940817 14561506428374553775455613)
    ·
      refine ⟨5460564910640457665795855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14561506428374553775455613 5460564910640457665795855)
      ·
        refine ⟨8190847365960686498693783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5460564910640457665795855 8190847365960686498693783)
        ·
          refine ⟨12286271048941029748040675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8190847365960686498693783 12286271048941029748040675)
          ·
            refine ⟨18429406573411544622061013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12286271048941029748040675 18429406573411544622061013)
            ·
              refine ⟨431939216564333077079555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18429406573411544622061013 431939216564333077079555)
              ·
                refine ⟨647908824846499615619333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431939216564333077079555 647908824846499615619333)
                ·
                  refine ⟨121482904658718677928625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647908824846499615619333 121482904658718677928625)
                  ·
                    rfl

theorem cell21_532321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_532321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532321 prefixEnd_532321 := by exact prefixLift 532321
  have htrace : WordTrace (prefixWord ++ tailWord_532321) baseStart_532321 baseEnd_532321 := by
    simpa [prefixWord, tailWord_532321, baseEnd_532321] using wordTrace_append hprefix tailTrace_532321
  have hstable : (prefixWord ++ tailWord_532321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532321).length < 2 ^ (prefixWord ++ tailWord_532321).sum := by decide
  have hdescent : baseEnd_532321 < baseStart_532321 := by decide
  rcases family_descends (prefixWord ++ tailWord_532321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532442 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_532442 : Nat := 118140960795 + 532442 * 2 ^ 59
def prefixEnd_532442 : Nat := 4983230072969 + 3 ^ 40 * 532442 * 2
def baseEnd_532442 : Nat := 121510518507249356411711

theorem tailTrace_532442 : CollatzResearch.WordTrace tailWord_532442 prefixEnd_532442 121510518507249356411711 := by
  unfold tailWord_532442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4854938784265260674773895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12946503424707361799397053 4854938784265260674773895)
  ·
    refine ⟨7282408176397891012160843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4854938784265260674773895 7282408176397891012160843)
    ·
      refine ⟨10923612264596836518241265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7282408176397891012160843 10923612264596836518241265)
      ·
        refine ⟨8192709198447627388680949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10923612264596836518241265 8192709198447627388680949)
        ·
          refine ⟨768066487354465067688839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8192709198447627388680949 768066487354465067688839)
          ·
            refine ⟨1152099731031697601533259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768066487354465067688839 1152099731031697601533259)
            ·
              refine ⟨1728149596547546402299889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152099731031697601533259 1728149596547546402299889)
              ·
                refine ⟨1296112197410659801724917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1728149596547546402299889 1296112197410659801724917)
                ·
                  refine ⟨121510518507249356411711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1296112197410659801724917 121510518507249356411711)
                  ·
                    rfl

theorem cell21_532442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_532442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532442 prefixEnd_532442 := by exact prefixLift 532442
  have htrace : WordTrace (prefixWord ++ tailWord_532442) baseStart_532442 baseEnd_532442 := by
    simpa [prefixWord, tailWord_532442, baseEnd_532442] using wordTrace_append hprefix tailTrace_532442
  have hstable : (prefixWord ++ tailWord_532442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532442).length < 2 ^ (prefixWord ++ tailWord_532442).sum := by decide
  have hdescent : baseEnd_532442 < baseStart_532442 := by decide
  rcases family_descends (prefixWord ++ tailWord_532442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532473 : List Nat := [1, 2, 1, 3, 1, 6, 1, 2, 4]
def baseStart_532473 : Nat := 118140960795 + 532473 * 2 ^ 59
def prefixEnd_532473 : Nat := 4983230072969 + 3 ^ 40 * 532473 * 2
def baseEnd_532473 : Nat := 121517593129600191394981

theorem tailTrace_532473 : CollatzResearch.WordTrace tailWord_532473 prefixEnd_532473 121517593129600191394981 := by
  unfold tailWord_532473
  simp only [CollatzResearch.WordTrace]
  refine ⟨19420885799948734993474073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12947257199965823328982715 19420885799948734993474073)
  ·
    refine ⟨14565664349961551245105555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19420885799948734993474073 14565664349961551245105555)
    ·
      refine ⟨21848496524942326867658333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14565664349961551245105555 21848496524942326867658333)
      ·
        refine ⟨8193186196853372575371875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21848496524942326867658333 8193186196853372575371875)
        ·
          refine ⟨12289779295280058863057813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8193186196853372575371875 12289779295280058863057813)
          ·
            refine ⟨576083404466252759205835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12289779295280058863057813 576083404466252759205835)
            ·
              refine ⟨864125106699379138808753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576083404466252759205835 864125106699379138808753)
              ·
                refine ⟨648093830024534354106565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864125106699379138808753 648093830024534354106565)
                ·
                  refine ⟨121517593129600191394981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648093830024534354106565 121517593129600191394981)
                  ·
                    rfl

theorem cell21_532473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_532473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532473 prefixEnd_532473 := by exact prefixLift 532473
  have htrace : WordTrace (prefixWord ++ tailWord_532473) baseStart_532473 baseEnd_532473 := by
    simpa [prefixWord, tailWord_532473, baseEnd_532473] using wordTrace_append hprefix tailTrace_532473
  have hstable : (prefixWord ++ tailWord_532473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532473).length < 2 ^ (prefixWord ++ tailWord_532473).sum := by decide
  have hdescent : baseEnd_532473 < baseStart_532473 := by decide
  rcases family_descends (prefixWord ++ tailWord_532473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532490 : List Nat := [3, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_532490 : Nat := 118140960795 + 532490 * 2 ^ 59
def prefixEnd_532490 : Nat := 4983230072969 + 3 ^ 40 * 532490 * 2
def baseEnd_532490 : Nat := 121521472761211939611613

theorem tailTrace_532490 : CollatzResearch.WordTrace tailWord_532490 prefixEnd_532490 121521472761211939611613 := by
  unfold tailWord_532490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4855376460221786724210731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12947670560591431264561949 4855376460221786724210731)
  ·
    refine ⟨7283064690332680086316097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4855376460221786724210731 7283064690332680086316097)
    ·
      refine ⟨5462298517749510064737073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7283064690332680086316097 5462298517749510064737073)
      ·
        refine ⟨4096723888312132548552805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5462298517749510064737073 4096723888312132548552805)
        ·
          refine ⟨768135729058524852853651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4096723888312132548552805 768135729058524852853651)
          ·
            refine ⟨1152203593587787279280477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768135729058524852853651 1152203593587787279280477)
            ·
              refine ⟨432076347595420229730179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1152203593587787279280477 432076347595420229730179)
              ·
                refine ⟨648114521393130344595269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432076347595420229730179 648114521393130344595269)
                ·
                  refine ⟨121521472761211939611613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648114521393130344595269 121521472761211939611613)
                  ·
                    rfl

theorem cell21_532490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_532490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532490 prefixEnd_532490 := by exact prefixLift 532490
  have htrace : WordTrace (prefixWord ++ tailWord_532490) baseStart_532490 baseEnd_532490 := by
    simpa [prefixWord, tailWord_532490, baseEnd_532490] using wordTrace_append hprefix tailTrace_532490
  have hstable : (prefixWord ++ tailWord_532490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532490).length < 2 ^ (prefixWord ++ tailWord_532490).sum := by decide
  have hdescent : baseEnd_532490 < baseStart_532490 := by decide
  rcases family_descends (prefixWord ++ tailWord_532490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
